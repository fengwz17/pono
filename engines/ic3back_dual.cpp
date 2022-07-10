/*********************                                                  */
/*! \file ic3back_dual.cpp
** \verbatim
** contributor:
**   Weizhi Feng
** This file is based on pono project and extends algorithms. 
** \endverbatim
**
** \brief An initial implementation of the 
**        "Backward Reachability with Under Approximation" framework.
**        Starting from bad, trace back to the initial state, 
**        maintain the under approximation of bad-reachable states at each step, 
**        and check whether it is reachable from I.
**/

#include "engines/ic3back_dual.h"

#include "assert.h"
#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/term_analysis.h"

using namespace smt;
using namespace std;

namespace pono {

IC3BackDual::IC3BackDual(const Property & p, const TransitionSystem & ts,
         const smt::SmtSolver & s, PonoOptions opt)
  : super(p, ts, s, opt)
{
    engine_ = Engine::IC3BACKDUAL_ENGINE;
}

void IC3BackDual::initialize()
{
    if (initialized_) {
        return;
    }

    // boolsort_ = solver_->make_sort(BOOL);
    // solver_true_ = solver_->make_term(true);

    // TODO: needs to be considered how to do abstraction
    // abstract();

    IC3Base::initialize();

    // check whether this flavor of IC3 can be applied to this transition system
    // check_ts();

    // assert(solver_context_ == 0);  // expecting to be at base context level

    // Initialize B sequence
    // frames_back.clear();
    // frame_labels_back.clear();

    // Backward: first frame is always the bad states
    initialize_frame_back();

    vector<IC3Formula> & B0 = frames_back;

    for (size_t j = 0; j < B0.size(); ++j) 
    {
        act_map_[B0[j].term] = true;
    }

    // set of generalized inactive states
    O.clear();

}

ProverResult IC3BackDual::check_until(int k)
{
    initialize();
    // make sure derived class implemented initialize and called
    // this version of initialize with super::initialize or
    // (for experts only) set the initialized_ flag without
    // ever initializing base classes
    assert(initialized_);

    ProverResult res;
    RefineResult ref_res;
    int i = reached_k_ + 1;
    assert(reached_k_ + 1 >= 0);
    while (i <= k) {
        res = dual_step(i);

        if (res == ProverResult::FALSE) {
        assert(cex_.size());
        RefineResult s = refine();
        if (s == REFINE_SUCCESS) {
            continue;
        } else if (s == REFINE_NONE) {
            // this is a real counterexample

            // fengwz: print cex_
            // for (size_t i = 0; i < cex_.size(); ++i){
            //   std::cout << "i: " << i << cex_[i] << std::endl;
            //   std::cout << std::endl;
            // }
            // std::cout << "cex_.size(): " << cex_.size() << std::endl;
            assert(cex_.size());
            return ProverResult::FALSE;
        } else {
            assert(s == REFINE_FAIL);
            logger.log(1, "IC3Dual: refinement failure, returning unknown");
            return ProverResult::UNKNOWN;
        }
        } else {
        ++i;
        }

        if (res != ProverResult::UNKNOWN) {
        return res;
        }
    }

    return ProverResult::UNKNOWN;
}

ProverResult IC3BackDual::dual_step(int i)
{
    // IC3 procedure
    if (i <= reached_k_) {
        return ProverResult::UNKNOWN;
    }

    if (reached_k_ < 1) {
        return step_01();
    }

    // reached_k_ is the number of transitions that have been checked
    // at this point there are reached_k_ + 1 frames that don't
    // intersect bad, and reached_k_ + 2 frames overall
    assert(reached_k_ == frontier_idx());

    // blocking phase
    logger.log(1, "Blocking phase at frame {}", i);
    if (!block_all()) {
        // counter-example
        return ProverResult::FALSE;
    }

    logger.log(1, "Propagation phase at frame {}", i);

    // propagation phase
    push_frame();
    for (size_t j = 1; j < frontier_idx(); ++j) {
        if (propagate(j)) {
            assert(j + 1 < frames_.size());
            // save the invariant
            // which is the frame that just had all terms
            // from the previous frames propagated
            invar_ = get_frame_term(j + 1);
            return ProverResult::TRUE;
        }
    }
    
    // update B 
    vector<IC3Formula> & B = frames_back;
    size_t original_size = B.size();

    for (size_t j = 0; j < B.size(); ++j) 
    {
        if (act_map_[B[j].term] == true) {
            // std::cout << "Fi[" << j << "]: " << Fi[j].term << std::endl;
            if (!forward_check(i, B[j])) {
                // counter-example
                // TODO: construct the counterexample.
                return ProverResult::FALSE;
            }
        }
       
    }

     if (frames_back.size() == original_size) {
        // std::cout << "checking invar......" << std::endl;
        // if (invar_check(i + 1)) {
        //     return ProverResult::TRUE;
        // }
        return ProverResult::TRUE;
    }

    // TODO: rewrite reset_solver()
    reset_solver();

    ++reached_k_;

    return ProverResult::UNKNOWN;
}

bool IC3BackDual::block_all()
{
  assert(!solver_context_);
  ProofGoalQueue proof_goals;
  IC3Formula goal;
  while (reaches_bad(goal)) {
    assert(goal.term);            // expecting non-null
    assert(proof_goals.empty());  // bad should be the first goal each iteration

    proof_goals.new_proof_goal(goal, frontier_idx(), nullptr);

    while (!proof_goals.empty()) {
      const ProofGoal * pg = proof_goals.top();

      // fengwz: print ProofGoalQueue
      // const ProofGoal * pg_tmp = proof_goals.top();
      // int i = 0;
      // while (pg_tmp)
      // {
      //   i++;
      //   std::cout << "proof_goals idx: " << pg_tmp->idx << std::endl;
      //   pg_tmp = pg_tmp->next; 
      // }
      // std::cout << "proof_goals length: " << i << std::endl;

      if (!pg->idx) {
        // went all the way back to initial
        // need to create a new proof goal that's not managed by the queue
        reconstruct_trace(pg, cex_);

        // in case this is spurious, clear the queue of proof goals
        // which might not have been precise
        // TODO might have to change this if there's an algorithm
        // that refines but can keep proof goals around
        proof_goals.clear();

        return false;
      }

      if (is_blocked(pg)) {
        logger.log(3,
                   "Skipping already blocked proof goal <{}, {}>",
                   pg->target.term,
                   pg->idx);
        // remove the proof goal since it has already been blocked
        assert(pg == proof_goals.top());
        proof_goals.pop();
        continue;
      }

      IC3Formula collateral;  // populated by rel_ind_check
      if (rel_ind_check(pg->idx, pg->target, collateral)) {
        // this proof goal can be blocked
        assert(!solver_context_);
        assert(collateral.term);
        logger.log(
            3, "Blocking term at frame {}: {}", pg->idx, pg->target.term);

        // remove the proof goal now that it has been blocked
        assert(pg == proof_goals.top());
        proof_goals.pop();

        if (options_.ic3_indgen_) {
          collateral = inductive_generalization(pg->idx, collateral);
        } else {
          // just negate the term
          collateral = ic3formula_negate(collateral);
        }

        size_t idx = find_highest_frame(pg->idx, collateral);
        assert(idx >= pg->idx);

        assert(collateral.disjunction);
        assert(collateral.term);
        assert(collateral.children.size());
        constrain_frame(idx, collateral);

        // re-add the proof goal at a higher frame if not blocked
        // up to the frontier
        if (idx < frontier_idx()) {
          assert(!pg->target.disjunction);
          proof_goals.new_proof_goal(pg->target, idx + 1, pg->next);
        }

      } else {
        // could not block this proof goal
        assert(collateral.term);
        proof_goals.new_proof_goal(collateral, pg->idx - 1, pg);
      }
    }  // end while(!proof_goals.empty())

    assert(!(goal = IC3Formula()).term);  // in debug mode, reset it
  }                                       // end while(reaches_bad(goal))

  assert(proof_goals.empty());
  return true;
}

bool IC3BackDual::reaches_bad(IC3Formula & out)
{
    push_solver_context();
    // assert the last frame (conjunction over clauses)
    assert_frame_labels(frontier_idx());
    // see if it can reach bad in one step
    // solver_->assert_formula(ts_.next(bad_));
    // replace bad to B
    Term B = get_back_frame_term(false);
    solver_->assert_formula(ts_.next(B));
    solver_->assert_formula(trans_label_);
    Result r = check_sat();

    if (r.is_sat()) {
    out = get_model_ic3formula();
    assert(out.term);
    assert(out.children.size());
    assert(ic3formula_check_valid(out));

    if (options_.ic3_pregen_) {
        // try to generalize if predecessor generalization enabled
        // predecessor_generalization_and_fix(frames_.size(), bad_, out);
        predecessor_generalization_and_fix(frames_.size(), B, out);
    }

    assert(out.term);
    assert(out.children.size());
    assert(ic3formula_check_valid(out));
    }

    pop_solver_context();

    assert(!r.is_unknown());
    return r.is_sat();

}

void IC3BackDual::predecessor_generalization(size_t i,
                                     const Term & c,
                                     IC3Formula & pred)
{
    // std::cout << "call IC3BackDuall::predecessor_generalization\n" << std::endl;
    // TODO: change this so we don't have to depend on the solver context to be
    // sat
    assert(i > 0);
    assert(!pred.disjunction);

    const UnorderedTermSet & statevars = ts_.statevars();
    TermVec input_lits = get_input_values();
    TermVec next_lits = get_next_state_values();
    const TermVec & cube_lits = pred.children;

    if (i == 1) {
        // don't need to generalize if i == 1
        // the predecessor is an initial state
        return;
    }

    Term formula = make_and(input_lits);
    if (ts_.is_deterministic()) {
        // \varphi = pred /\ i /\ T /\ \neg c', where c = B
        // should try \varphi = pred /\ i /\ \forall X'(\neg T \/ \neg B')

        // NOTE: need to use full trans, not just trans_label_ here
        //       because we are passing it to the reducer_
        formula = solver_->make_term(And, formula, ts_.trans());
        formula =
            solver_->make_term(And, formula, solver_->make_term(Not, ts_.next(c)));
    } else {
        formula = solver_->make_term(And, formula, make_and(next_lits));

        // preimage formula
        // NOTE: because this will be negated, it is important to use the
        // whole frame and trans, not just the labels
        // because label is: trans_label_ -> trans
        // so if it is negated, that doesn't force trans to be false
        // the implication could be more efficient than iff so we want to leave it
        // that way
        Term pre_formula = get_frame_term(i - 1);
        pre_formula = solver_->make_term(And, pre_formula, ts_.trans());
        pre_formula =
            solver_->make_term(And, pre_formula, solver_->make_term(Not, c));
        pre_formula = solver_->make_term(And, pre_formula, ts_.next(c));
        formula =
            solver_->make_term(And, formula, solver_->make_term(Not, pre_formula));
    }
    // TODO: consider adding functional pre-image here
    //       not sure if it makes sense to have at the boolean level

    TermVec red_cube_lits, rem_cube_lits;
    reducer_.reduce_assump_unsatcore(
        formula, cube_lits, red_cube_lits, &rem_cube_lits);

    // should need some assumptions
    // formula should not be unsat on its own
    assert(red_cube_lits.size() > 0);

    pred = ic3formula_conjunction(red_cube_lits);
    // expecting a Cube here
    assert(!pred.disjunction);

    // add goal to act(B)
    act_map_[pred.term] = true;
}

bool IC3BackDual::forward_check(size_t k, const IC3Formula & t)
{
    push_solver_context();

    // init
    solver_->assert_formula(init_label_);

    // trans
    solver_->assert_formula(trans_label_);
    // solver_->assert_formula(ts_.trans());

    // t'
    solver_->assert_formula(ts_.next(t.term));
    Result r = check_sat();
    if (r.is_sat()) {
        // TODO: construct conterexample
        pop_solver_context();
        return FALSE;
    }
    else {
        pop_solver_context();
    }

    push_solver_context();

    // act(Bk) \cup O
    Term BkO = get_back_frame_term(true);
    // std::cout << "Osize: " << O.size() << std::endl;
    for (const auto & u : O) {
        // std::cout << "u.term " << u.term << std::endl;
        BkO = solver_->make_term(Or, BkO, u.term);
    } 
    
    // // not B[k]
    // solver_->assert_formula(
    //         solver_->make_term(Not, get_back_frame_term(k))
    // );

    // not(act(Bk) \cup O)
    solver_->assert_formula(solver_->make_term(Not, BkO));

    // trans
    solver_->assert_formula(trans_label_);

    // // t'
    // solver_->assert_formula(ts_.next(t.term));

    // std::cout << "t'" << ts_.next(t.term) << std::endl;

    // use the unsat core of t'
    TermVec assumps_t;
    Term lblt, ttnext;
    for (const auto & tt : t.children) {
        ttnext = ts_.next(tt);
        lblt = label(ttnext);
        if (lblt != ttnext && !is_global_label(lblt)) {
            // only need to add assertion if the label is not the same as ccnext
            // could be the same if ccnext is already a literal
            // and is not already in a global assumption
            solver_->assert_formula(solver_->make_term(Implies, lblt, ttnext));
        }
      assumps_t.push_back(lblt);
    }

    // r = check_sat();
    Result rr = check_sat_assuming(assumps_t);

    if (rr.is_sat()) {
        IC3Formula s = get_model_ic3formula();
        TermVec input_lits = get_input_values();
        Term input_formula = make_and(input_lits);
       
        pop_solver_context();

        IC3Formula out = generate(s, input_formula, k);  

        // std::cout << "before extending ..." << std::endl;
        
        // vector<IC3Formula> Fk1 = frames_back.at(k+1);
        // for (size_t j = 0; j < Fk1.size(); ++j)
        // {
        //     std::cout << "F" << k+1 << "[" << j << "]: " << Fk1[j].term << std::endl;
        // }
        
        // add out to B
        act_map_[out.term] = true;
        extend_frame_back(out);

        // add out to PO ?

    
        // vector<IC3Formula> & Fk1 = frames_back.at(k+1);

        // std::cout << "after extending ..." << std::endl;

        // for (size_t j = 0; j < Fk1.size(); ++j)
        // {
        //     std::cout << "F" << k+1 << "[" << j << "]: " << Fk1[j].term << " " << Fk1[j].act << std::endl;
        // }
    }
    else{    
        assert(rr.is_unsat());
        act_map_[t.term] = false;
       
        // add unsat core \bar{t} to O
        UnorderedTermSet core_t;
        solver_->get_unsat_assumptions(core_t);
        TermVec gen_t;
        TermVec rem_t;

        assert(assumps_t.size() == t.children.size());
        
        for (size_t i = 0; i < assumps_t.size(); ++i) {
            if (core_t.find(assumps_t.at(i)) == core_t.end()) {
                rem_t.push_back(t.children.at(i));
            } else {
                gen_t.push_back(t.children.at(i));
            }
        }

        fix_if_intersects_initial(gen_t, rem_t);
        assert(gen_t.size() >= core_t.size());
        IC3Formula tbar = ic3formula_conjunction(gen_t);
         
        // O.push_back(tbar);

        // std::cout << "ccccc" << std::endl;
        bool flag = false;
        for (const auto & oo : O) {
            if (tbar.term == oo.term) {
                flag = true;
                break;
            }
        }
        if (flag == false) {
            O.push_back(tbar);
        }

    
        pop_solver_context();
        // TODO: get the unsat core \bar{t} of t that can reach B0
        //   add \bar{t} to Bk-1, Bk, Bk+1
        
    }   
    

    return TRUE;

}

void IC3BackDual::initialize_frame_back()
{
    // assert(frame_labels_back.size() == frames_back.size());

    // frames_back.push_back({});
    TermVec badTermVec = {bad_};
    IC3Formula bad = ic3formula_conjunction(badTermVec);

    frames_back.push_back(bad);

}

Term IC3BackDual::get_back_frame_term(bool act)
{
    // B is DNF
    Term res = solver_true_;
    res = solver_->make_term(Not, res);

    if (act) {
        for (const auto & u : frames_back) {
            if (act_map_[u.term] == true) {
                res = solver_->make_term(Or, res, u.term);
            }
        }
    }
    else {
        for (const auto &u : frames_back) {
            res = solver_->make_term(Or, res, u.term);
        }
    }

    return res;
}

IC3Formula IC3BackDual::generate(const IC3Formula & s, Term input_formula, size_t k)
{
    IC3Formula out;
    push_solver_context();
    
    // assumps_.clear();
    // use assumptions for s
    TermVec assumps;
    // assumps_.clear();
    
    Term lbl;

    for (const auto & ss : s.children) {
        lbl = label(ss);
        if (lbl != ss && !is_global_label(lbl)){
            solver_->assert_formula(solver_->make_term(Implies, lbl, ss));
        }
        assumps.push_back(lbl);
        // std::cout << "lbl: " << lbl << std::endl;
        // std::cout << "ss: " << ss << std::endl;
    }

    // input
    solver_->assert_formula(input_formula);
   
    // trans
    solver_->assert_formula(ts_.trans());
    // solver_->assert_formula(trans_label_);

    // \neg B[k]'
    solver_->assert_formula(ts_.next(
            solver_->make_term(Not, get_back_frame_term(false))));

    // solver_->assert_formula(s.term);

    // Term formula = input_formula;
    // formula = solver_->make_term(And, formula, ts_.trans());
    // formula = solver_->make_term(And, formula, 
    //     ts_.next(solver_->make_term(Not, get_back_frame_term(k))));

    // std::cout << "T: " << ts_.trans() << std::endl;
    // std::cout << "input: " << input_formula << std::endl; 
    // std::cout << "\\neg B'[k]: " << ts_.next(
    //         solver_->make_term(Not, get_back_frame_term(k)))<< std::endl;

    // std::cout << "s: " << s.term << std::endl; 

    Result r = check_sat_assuming(assumps);
    // Result r = check_sat();

    assert(r.is_unsat());
    if (r.is_sat()){
        throw PonoException("s \\wedge i \\wedge T \\wedge \\neg B'_{k} should be UNSAT");
    }
    else{
        // std::cout << "unsat core is not used" << std::endl;
        // assert(r.is_unsat());
        // out = s;
        assert(r.is_unsat());
        UnorderedTermSet core;
        solver_->get_unsat_assumptions(core);
        assert(core.size());
        // std::cout << "core.size(): " << core.size() << std::endl;

        // std::cout << "core: " << std::endl;
        // for (auto& corei :core)
        // {
        //     std::cout << corei << " " << std::endl;
        // }
        
        TermVec gen;
        TermVec rem;

        assert(assumps.size() == s.children.size());
        for (size_t i = 0; i < assumps.size(); ++i) {
            if (core.find(assumps.at(i)) == core.end()) {
                rem.push_back(s.children.at(i));
            } 
            else {
                gen.push_back(s.children.at(i));
            }
        }  

        // reduced unsat core
        Term notBnext = ts_.next(solver_->make_term(Not, get_back_frame_term(false)));
        Term formula = make_and({input_formula, 
                                 ts_.trans(), 
                                 notBnext}) ;

        TermVec red_cube_lits, rem_cube_lits;
        reducer_.reduce_assump_unsatcore(
            formula, gen, red_cube_lits, NULL, options_.ic3_gen_max_iter_);
        
        out = ic3formula_conjunction(red_cube_lits);

    }
    pop_solver_context();

    return out;
}

void IC3BackDual::extend_frame_back(const IC3Formula & s) {
    bool flag = false;
    vector<IC3Formula> Fk = frames_back;
    for (size_t j = 0; j < Fk.size(); ++j)
    {
        if (s.term == Fk[j].term)
        {
            flag = true;
            break;
        }
    }
    if (flag == false)
    {
        // solver_->assert_formula(
        //     solver_->make_term(Implies, frame_labels_back.at(k), s.term));
        frames_back.push_back(s);
    }   
}

// bool IC3BackDual::is_global_label_back(const Term & l) const
// {
//   return (l == trans_label_ || l == bad_label_
//           || std::count(frame_labels_back.begin(), frame_labels_back.end(), l));
// }



}