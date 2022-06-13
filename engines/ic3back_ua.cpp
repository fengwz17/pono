/*********************                                                  */
/*! \file ic3back_ua.cpp
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

#include "engines/ic3back_ua.h"

#include "assert.h"
#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/term_analysis.h"

using namespace smt;
using namespace std;

namespace pono {

IC3BackUa::IC3BackUa(const Property & p, const TransitionSystem & ts,
         const smt::SmtSolver & s, PonoOptions opt)
  : super(p, ts, s, opt)
{
    engine_ = Engine::IC3BACKUA_ENGINE;
}

void IC3BackUa::initialize()
{
    if (initialized_) {
        return;
    }

    boolsort_ = solver_->make_sort(BOOL);
    solver_true_ = solver_->make_term(true);

    // TODO: needs to be considered how to do abstraction
    // abstract();

    Prover::initialize();

    // check whether this flavor of IC3 can be applied to this transition system
    check_ts();

    assert(solver_context_ == 0);  // expecting to be at base context level

    frames_.clear();
    frame_labels_.clear();

    // Backward: first frame is always the bad states
    push_frame();

    solver_->assert_formula(
        solver_->make_term(Implies, frame_labels_.at(0), bad_));
    // push_frame();

    // set semantics of TS labels
    assert(!init_label_);
    assert(!trans_label_);
    assert(!bad_label_);
    // Backward: frame 0 label is identical to bad label
    bad_label_ = frame_labels_[0];

    trans_label_ = solver_->make_symbol("__trans_label", boolsort_);
    solver_->assert_formula(
        solver_->make_term(Implies, trans_label_, ts_.trans()));

    // Backward: we record init state as "init_label_", but "init_label_" is not B[0]
    init_label_ = solver_->make_symbol("__init_label", boolsort_);
    solver_->assert_formula(solver_->make_term(Implies, init_label_, ts_.init()));

    // // bits
    // Term bv1 = solver_->make_term(1, solver_->make_sort(BV, 1));

    // assert(!state_bits_.size());
    // for (const auto & sv : ts_.statevars()) {
    //     const Sort & sort = sv->get_sort();
    //     if (sort == boolsort_) {
    //     state_bits_.push_back(sv);
    //     } else {
    //     assert(sort->get_sort_kind() == BV);
    //     for (size_t i = 0; i < sort->get_width(); ++i) {
    //         state_bits_.push_back(solver_->make_term(
    //             Equal, solver_->make_term(Op(Extract, i, i), sv), bv1));
    //     }
    //     }
    // }
}

ProverResult IC3BackUa::check_until(int k)
{
    initialize();

    assert(initialized_);

    ProverResult res;
    int i = reached_k_ + 1;
    assert(reached_k_ + 1 >= 0);
    while(i <= k) {
        res = back_step(i);

        if (res == ProverResult::FALSE) {
            assert(cex_.size());
            return ProverResult::FALSE;
        }
        else {
            ++i;
        }

        if (res != ProverResult::UNKNOWN) {
            return res;
        }
    }

    return ProverResult::UNKNOWN;
}

ProverResult IC3BackUa::back_step(int i)
{
    // if (i <= reached_k_)
    // {
    //     return ProverResult::UNKNOWN;
    // }

    // isSAT(I /\ B[0]) or isSAT(I /\ T /\ B[0]')
    if (reached_k_ < 1)
    {
        if (!base_check())
        {
            logger.log(1, "Return UNSAFE in base_check");
            return ProverResult::FALSE;
        }
    }

    // std::cout << "reached_k_" << reached_k_ << std::endl;
    

    // reached_k_ is the number of transitions that have been checked,
    //  currently, there are reached_k_ + 1 frames in total 
    // at this point, we check each state t of B[k]
    // if isSAT(I /\ T /\ t') return UNSAFE
    // else if isSAT(\neg B[k] /\ T /\ t') extend B[k+1]
    // TODO: unsat core and optimaizations
    logger.log(1, "Check init-reachable phase at frame {}", i);

    push_frame();

    // std::cout << "current frames_.size(): " << frames_.size() << std::endl;

    // for (size_t k = 0; k < frames_.size(); ++k)
    // {
    //     vector<IC3Formula> Fk = frames_.at(k);
    //     for (size_t j = 0; j < Fk.size(); ++j)
    //     {
    //         std::cout << "F" << k << "[" << j << "]: " << Fk[j].term << std::endl;
    //     }
    // }

    const vector<IC3Formula> & Fi = frames_.at(i);

    for (size_t j = 0; j < Fi.size(); ++j) 
    {
        // std::cout << "Fi[" << j << "]: " << Fi[j].term << std::endl;
        if (!forward_check(i, Fi[j])) {
            // counter-example
            // TODO: construct the counterexample.
            return ProverResult::FALSE;
        }
    }

    // std::cout << "---------------- after checking ----------------" << std::endl;
    // std::cout << "current frames_.size(): " << frames_.size() << std::endl;
    // for (size_t k = 0; k < frames_.size(); ++k)
    // {
    //     vector<IC3Formula> Fk = frames_.at(k);
    //     for (size_t j = 0; j < Fk.size(); ++j)
    //     {
    //         std::cout << "F" << k << "[" << j << "]: " << Fk[j].term << std::endl;
    //     }
    // }

    // std::cout << "frames_.at(i): " << frames_.at(i).size() << " frames_.at(i+1): " << frames_.at(i+1).size() << std::endl;

    // check if Bi = Bi+1 and isUNSAT(not Bi+1 /\ T /\ B'i+1)
    if (frames_.at(i).size() == frames_.at(i + 1).size()) {
        std::cout << "checking invar......" << std::endl;
        if (invar_check(i + 1)) {
            return ProverResult::TRUE;
        }
    }

    // TODO: rewrite reset_solver()
    // reset_solver();

    ++reached_k_;

    return ProverResult::UNKNOWN;
}

bool IC3BackUa::base_check()
{
    assert(reached_k_ < 1);
    if (reached_k_ < 0) {
        logger.log(1, "Checking if initial states satisfy bad property");

        push_solver_context();

        // Backward: init is bad_label 
        solver_->assert_formula(init_label_);
        solver_->assert_formula(bad_label_);

        // check isSAT(I /\ B0)
        Result r = check_sat();
        if (r.is_sat()) {
            pop_solver_context();
            // trace is only one bad state that intersects with initial
            cex_.clear();
            cex_.push_back(bad_);
            return false;
        } else {
            assert(r.is_unsat());
            reached_k_ = 0;  // keep reached_k_ aligned with number of frames
        }
        pop_solver_context();
    }

    // Check isSAT(I /\ T /\ B0')
    assert(reached_k_ == 0);
    logger.log(1, "Checking if inital states can violate property in one-step");

    push_solver_context();
    // solver_->assert_formula(ts_.init());
    solver_->assert_formula(init_label_);
    // solver_->assert_formula(ts_.trans());
    solver_->assert_formula(trans_label_);
    // solver_->assert_formula(ts_.next(bad_));
    solver_->assert_formula(ts_.next(bad_label_));
    
    Result r = check_sat();
    if (r.is_sat()) {
        // TODO: construct counterexample
        // const IC3Formula &c = get_model_ic3formula();
        pop_solver_context();
        // ProofGoal * pg = new ProofGoal(c, 0, nullptr);
        // reconstruct_trace(pg, cex_);
        // delete pg;
        return false;
    } else {
        assert(r.is_unsat());
        // reached_k_ = 1;  // keep reached_k_ aligned with number of frames
    }
    pop_solver_context();

    return true;
}

bool IC3BackUa::forward_check(size_t k, const IC3Formula & t)
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

    // not B[k]
    solver_->assert_formula(
            solver_->make_term(Not, get_frame_term(k))
    );

    // trans
    solver_->assert_formula(trans_label_);
    // solver_->assert_formula(ts_.trans());

    // t'
    solver_->assert_formula(ts_.next(t.term));

    // std::cout << "t'" << ts_.next(t.term) << std::endl;

    r = check_sat();
    if (r.is_sat()) {
        // TODO: generalization(s)
        // s = a and b and c
        // drop a, b and c = generalization(s), check SAT?
        IC3Formula s = get_model_ic3formula();
        TermVec input_lits = get_input_values();
        Term input_formula = make_and(input_lits);
        // std::cout << "start generating..." << std::endl;
        pop_solver_context();
        IC3Formula out = generate(s, input_formula, k);  

        // std::cout << "before extending ..." << std::endl;
        
        // vector<IC3Formula> Fk1 = frames_.at(k+1);
        // for (size_t j = 0; j < Fk1.size(); ++j)
        // {
        //     std::cout << "F" << k+1 << "[" << j << "]: " << Fk1[j].term << std::endl;
        // }
        
        // add out to Bi+1
        extend_frame(k + 1, out);

        // Fk1 = frames_.at(k+1);

        // std::cout << "after extending ..." << std::endl;

        // for (size_t j = 0; j < Fk1.size(); ++j)
        // {
        //     std::cout << "F" << k+1 << "[" << j << "]: " << Fk1[j].term << std::endl;
        // }
    }
    else{
        pop_solver_context();
        // TODO: get the unsat core \bar{t} of t that can reach B0
        //   add \bar{t} to Bk-1, Bk, Bk+1
    }   
    

    return TRUE;

}

bool IC3BackUa::invar_check(size_t k)
{
    push_solver_context();

    // not B[k]
    solver_->assert_formula(
            solver_->make_term(Not, get_frame_term(k)));

    // trans
    solver_->assert_formula(trans_label_);
    // solver_->assert_formula(ts_.trans());

    // B[k]
    solver_->assert_formula(ts_.next(get_frame_term(k)));

    Result r = check_sat();

    if (r.is_sat()) {
        // TODO: the SAT result can be used in the unsat core \bar{t} part
        pop_solver_context();
        return FALSE;
    }
    else {
        pop_solver_context();
        return TRUE;
    }
}

void IC3BackUa::push_frame()
{
  assert(frame_labels_.size() == frames_.size());

  frame_labels_.push_back(
      solver_->make_symbol("__frame_label_" + std::to_string(frames_.size()),
                           solver_->make_sort(BOOL)));
  // frames_.push_back({});
  TermVec badTermVec = {bad_};
  IC3Formula bad = ic3formula_disjunction(badTermVec);
  if (frames_.size() == 0)
  {
      frames_.push_back({bad});
  }
  else
  {
      frames_.push_back(frames_.at(frames_.size() - 1));
  }
  
  if (frames_.size() > 1) {
    // always start (non-initial) frame the same as the last frame
    Term last_frame_term = get_frame_term(frames_.size() - 1);
    solver_->assert_formula(
        solver_->make_term(Implies, frame_labels_.back(), last_frame_term));
  }
}

Term IC3BackUa::get_frame_term(size_t i) const
{
    if (i == 0) {
        // F[0] is always the bad states constraint
        return bad_;
    }

    Term res = solver_true_;
    res = solver_->make_term(Not, res);
    // for (size_t j = i; j < frames_.size(); ++j) {
    for (const auto &u : frames_[i]) {
        res = solver_->make_term(Or, res, u.term);
        // }
    }

    // the property is implicitly part of the frame
    // res = solver_->make_term(And, res, smart_not(bad_));
    return res;
}

IC3Formula IC3BackUa::generate(IC3Formula & s, Term input_formula, size_t k)
{
    /*
    // std::cout << "s: " << s.term << std::endl;
    IC3Formula gen = s;
    Term dropped;
    UnorderedTermSet necessary;

    size_t i = 0;
    while (i < gen.children.size() && gen.children.size() > 1) {
        
        // try dropping i
        // std::cout << "i: " << i << std::endl;
        dropped = gen.children.at(i);
        // std::cout << "dropped: " << dropped << std::endl;
        if (necessary.find(dropped) != necessary.end()) {
            // can not drop
            i++;
            continue;
        }

        IC3Formula tmp = gen;
        // tmp.children.erase(tmp.children.begin() + i);
        // tmp.children.push_back(solver_->make_term(Not, dropped));
        tmp.children.at(i) = solver_->make_term(Not, dropped);
        tmp = ic3formula_conjunction(tmp.children);

        push_solver_context();

        // std::cout << "tmp: " << tmp.term << std::endl;
        // std::cout << "trans: " << ts_.trans() << std::endl;
        // std::cout << "B[k]': " << ts_.next(get_frame_term(k)) << std::endl;
        // std::cout << "Bk: " << ts_.next(get_frame_term(k)) << std::endl;

        solver_->assert_formula(tmp.term);

        // trans
        solver_->assert_formula(trans_label_);

        // B[k]'
        solver_->assert_formula(ts_.next(get_frame_term(k)));

        // std::cout << "start checking... " << std::endl;

        Result r = check_sat();
        if (r.is_sat()) {
            gen.children.erase(gen.children.begin() + i);
            gen = ic3formula_conjunction(gen.children);
        }
        else {
           necessary.insert(dropped);
        }
        pop_solver_context();
        i++;
    }

    gen = ic3formula_conjunction(gen.children);

    // std::cout << "gen: " << gen.term << std::endl;
    
    return gen;
    */
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
    // solver_->assert_formula(ts_.trans());
    solver_->assert_formula(trans_label_);

    // \neg B[k]'
    solver_->assert_formula(ts_.next(
            solver_->make_term(Not, get_frame_term(k))));

    // solver_->assert_formula(s.term);

    // Term formula = input_formula;
    // formula = solver_->make_term(And, formula, ts_.trans());
    // formula = solver_->make_term(And, formula, 
    //     ts_.next(solver_->make_term(Not, get_frame_term(k))));

    // std::cout << "T: " << ts_.trans() << std::endl;
    // std::cout << "input: " << input_formula << std::endl; 
    // std::cout << "\\neg B'[k]: " << ts_.next(
    //         solver_->make_term(Not, get_frame_term(k)))<< std::endl;

    // std::cout << "s: " << s.term << std::endl; 

    Result r = check_sat_assuming(assumps);
    // Result r = check_sat();
    assert(r.is_unsat());
    if (r.is_sat()){
        throw PonoException("s \\wedge i \\wedge T \\wedge \\neg B'_{k} must be UNSAT");
    }
    else if (options_.ic3_unsatcore_gen_){
        // std::cout << r << std::endl;
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

        // std::cout << "formula: " << formula << std::endl; 
        // TermVec red_cube_lits, rem_cube_lits;
        // reducer_.reduce_assump_unsatcore(
        //     formula, assumps, red_cube_lits, &rem_cube_lits);

        // should need some assumptions
        // formula should not be unsat on its own
        // assert(red_cube_lits.size() > 0);


        // // std::cout << "h1" << std::endl;
        // std::cout << "rem: " << make_and(rem) << std::endl;
        // std::cout << "gen: " << make_and(gen) << std::endl;

        // Term formula = get_frame_term(k);

        // // formula = solver_->make_term(And, formula, make_and(gen));
        
        // bool unsat = reducer_.reduce_assump_unsatcore(formula, rem, gen);
        // assert(unsat);
        
        // std::cout << "gen: " << make_and(gen) << std::endl;
        // assert(gen.size() >= core.size());
        
        out = ic3formula_conjunction(gen);
        // out = ic3formula_conjunction(red_cube_lits);
        // std::cout << "out: " << out.term << std::endl;
    }
    else{
        std::cout << "unsat core is not used" << std::endl;
        assert(r.is_unsat());
        out = s;
    }
    pop_solver_context();

    return out;
}

void IC3BackUa::reset_solver()
{
    assert(solver_context_ == 0);

    if (failed_to_reset_solver_) {
        // don't even bother trying
        // this solver doesn't support reset_assertions
        return;
    }

    try {
        solver_->reset_assertions();

        // Now need to add back in constraints at context level 0
        logger.log(2, "IC3Base: Reset solver and now re-adding constraints.");

        // define init, trans, and bad labels
        assert(bad_label_ == frame_labels_.at(0));
        solver_->assert_formula(
            solver_->make_term(Implies, init_label_, ts_.init()));

        solver_->assert_formula(
            solver_->make_term(Implies, trans_label_, ts_.trans()));

        solver_->assert_formula(solver_->make_term(Implies, bad_label_, bad_));

        Term prop = smart_not(bad_);
        for (size_t i = 0; i < frames_.size(); ++i) {
            assert(i < frame_labels_.size());
            // all frames except for F[0] include the property
            // but it's not stored in frames_ because it's not guaranteed to
            // be a valid IC3Formula
            if (i) {
                solver_->assert_formula(
                    solver_->make_term(Implies, frame_labels_.at(i), bad_));
            }

            // add all other constraints from the frame
            for (const auto & constraint : frames_.at(i)) {
                constrain_frame_label(i, constraint);
            }
        }
    }
    catch (SmtException & e) {
        logger.log(1,
                "Failed to reset solver (underlying solver must not support "
                "it). Disabling solver resets for rest of run.");
        failed_to_reset_solver_ = true;
    }

    num_check_sat_since_reset_ = 0;

}

void IC3BackUa::extend_frame(size_t k, const IC3Formula & s) {
    bool flag = false;
    vector<IC3Formula> Fk = frames_.at(k);
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
        solver_->assert_formula(
            solver_->make_term(Implies, frame_labels_.at(k), s.term));
        frames_.at(k).push_back(s);
    }   
}
}