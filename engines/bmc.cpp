/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Ahmed Irfan, Makai Mann
 ** This file is part of the pono project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include "bmc.h"
#include "utils/logger.h"

#include <time.h>

// fwz:recording the time that the solver takes in each step
clock_t cc1, cc2, cc3, cc4;

using namespace smt;

namespace pono {

Bmc::Bmc(const Property & p, const TransitionSystem & ts,
         const SmtSolver & solver, PonoOptions opt)
  : super(p, ts, solver, opt)
{
  engine_ = Engine::BMC;
}

Bmc::~Bmc() {}

void Bmc::initialize()
{
  if (initialized_) {
    return;
  }

  super::initialize();

  // NOTE: There's an implicit assumption that this solver is only used for
  // model checking once Otherwise there could be conflicting assertions to
  // the solver or it could just be polluted with redundant assertions in the
  // future we can use solver_->reset_assertions(), but it is not currently
  // supported in boolector
  solver_->assert_formula(unroller_.at_time(ts_.init(), 0));
  // std::cout << "init " << " ts_.init(): " << ts_.init() << std::endl;
}

ProverResult Bmc::check_until(int k)
{
  // cc1 = clock();
  initialize();
 //  cc2 = clock();
  // std::cout << " initialize(): " << ((double) cc2 - cc1)/CLOCKS_PER_SEC << std::endl;
  for (int i = reached_k_ + 1; i <= k; ++i) {
    if (!step(i)) {
      compute_witness();
      return ProverResult::FALSE;
    }
  }
  return ProverResult::UNKNOWN;
}

bool Bmc::step(int i)
{
  if (i <= reached_k_) {
    return true;
  }

  bool res = true;
  if (i > 0) {
    // std::cout << "trans " << i << " ts_.trans(): " << ts_.trans() << std::endl;
    solver_->assert_formula(unroller_.at_time(ts_.trans(), i - 1));
  }

  solver_->push();
  logger.log(1, "Checking bmc at bound: {}", i);
  // std::cout << "checking " << i << " bad_: " << bad_ << std::endl;
  solver_->assert_formula(unroller_.at_time(bad_, i));
  // std::cout << " i: " << i << " solver_->assert_formula(bad_): " << ((double) cc4 - cc3)/CLOCKS_PER_SEC << std::endl;
  cc3 = clock();
  Result r = solver_->check_sat();
  cc4 = clock();
  std::cout << " i: " << i << " solver_->check_sat(): " << ((double) cc4 - cc3)/CLOCKS_PER_SEC << std::endl;
  
  if (r.is_sat()) {
    res = false;
  } else {
    solver_->pop();
    ++reached_k_;
  }

  return res;
}

}  // namespace pono
