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
    engine_ = Engine::IC3BackUa_ENGINE;
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
    }

    return ProverResult::UNKNOWN;
}

ProverResult IC3BackUa::back_step(int i)
{
    if (i <= reached_k_)
    {
        return ProverResult::UNKNOWN;
    }

    // isSAT(I /\ B[0]) or isSAT(I /\ T /\ B[0]')
    if (reached_k_ < 1)
    {
        if (!base_check());
        {
            return ProverResult::FALSE;
        }
    }

    // reached_k_ is the number of transitions that have been checked,
    //  currently, there are reached_k_ + 1 frames in total 
    // at this point, we check each state t of B[k]
    // if isSAT(I /\ T /\ t') return UNSAFE
    // else if isSAT(\neg B[k] /\ T /\ t') extend B[k+1]
    // TODO: unsat core and optimaizations
    logger.log(1, "Check init-reachable phase at frame {}", i);

    const vector<IC3Formula> & Fi = frames_.at(i);
    IC3Formula out = get_model_ic3formula();

    for (size_t j = 0; j < Fi.size(); ++j) 
    {
        if (!check(i, Fi[j], out)) {
            // counter-example
            // TODO: construct the counterexample.
            return ProverResult::FALSE;
        }
        else {
            // add out to Bi+1
            constrain_frame(i + 1, out, false);
        }
    }

    logger.log(1, "current phase at frame {}", i);

    // check if Bi = Bi+1 and isUNSAT(not Bi+1 /\ T /\ B'i+1)
    if (frames_.at(i).size() == frames_.at(i + 1).size()) {
        if (invar_check(i + 1)) {
            return ProverResult::TRUE;
        }
    }

    // TODO: rewrite reset_solver()
    reset_solver();

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
            return FALSE;
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
    solver_->assert_formula(init_label_);
    solver_->assert_formula(trans_label_);
    solver_->assert_formula(ts_.next(bad_));
    Result r = check_sat();
    if (r.is_sat()) {
        // TODO: construct counterexample
        // const IC3Formula &c = get_model_ic3formula();
        pop_solver_context();
        // ProofGoal * pg = new ProofGoal(c, 0, nullptr);
        // reconstruct_trace(pg, cex_);
        // delete pg;
        return FALSE;
    } else {
        assert(r.is_unsat());
        // reached_k_ = 1;  // keep reached_k_ aligned with number of frames
    }
    pop_solver_context();

    return true;
}
 
bool IC3BackUa::check(size_t k, const IC3Formula & t, IC3Formula & out)
{
    push_solver_context();

    // init
    solver_->assert_formula(init_label_);

    // trans
    solver_->assert_formula(trans_label_);

    // t'
    solver_->assert_formula(ts_.next(t.term));
    Result r = check_sat();
    if (r.is_sat()) {
        // TODO: construct conterexample
        pop_solver_context();
        return FALSE;
    }
    else {
        push_solver_context();

        // not B[k]
        solver_->assert_formula(
                solver_->make_term(Not, get_frame_term(k))
        );

        // trans
        solver_->assert_formula(trans_label_);

        // t'
        solver_->assert_formula(ts_.next(t.term));
        Result r = check_sat();
        if (r.is_sat()) {
            // TODO: generalization(s)
            // s = a and b and c
            // drop a, b and c = generalization(s), check SAT?
            IC3Formula s = get_model_ic3formula();
            out = generate(s);  
        }
        else{
            // TODO: get the unsat core \bar{t} of t that can reach B0
            //   add \bar{t} to Bk-1, Bk, Bk+1
        }   
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

    // B[k]
    solver_->assert_formula(ts_.next(get_frame_term(k)));

    Result r = check_sat();

    if (r.is_sat()) {
        // TODO: the SAT result can be used in the unsat core \bar{t} part
        return FALSE;
    }
    else {
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
  IC3Formula bad = ic3formula_conjunction(badTermVec);
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
    for (size_t j = i; j < frames_.size(); ++j) {
        for (const auto &u : frames_[j]) {
        res = solver_->make_term(And, res, u.term);
        }
    }

    // the property is implicitly part of the frame
    // res = solver_->make_term(And, res, smart_not(bad_));
    return res;
}

IC3Formula IC3BackUa::generate(IC3Formula & s)
{
    return s;
}

}