/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Weizhi Feng, Yicheng Liu
 ** This file is part of the pono project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 ** Unroll the btor file into smtlib format,
 ** and translate smtlib to polynomials.
 **
 **/

#include "muldiv_verify.h"

#include "utils/logger.h"

using namespace smt;

namespace pono {

MulDivVerify::MulDivVerify(const Property & p,
                           const TransitionSystem & ts,
                           const SmtSolver & solver,
                           PonoOptions opt)
    : super(p, ts, solver, opt)
{
  engine_ = Engine::MULDIV;
}

MulDivVerify::~MulDivVerify() {}

void MulDivVerify::initialize()
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
  // solver_->assert_formula(unroller_.at_time(ts_.init(), 0));

  std::cout << unroller_.at_time(ts_.init(), 0) << std::endl;
  std::cout << std::endl;
}

ProverResult MulDivVerify::check_until(int k)
{
  initialize();

  for (int i = reached_k_ + 1; i <= k; ++i) {
    step(i);
  }
  return ProverResult::UNKNOWN;
}

void MulDivVerify::step(int i)
{
  if (i <= reached_k_) {
    return;
  }

  bool res = true;
  if (i > 0) {
    // solver_->assert_formula(unroller_.at_time(ts_.trans(), i - 1));
    std::cout << unroller_.at_time(ts_.trans(), i - 1) << std::endl;
    std::cout << std::endl;

    smt::Term u = unroller_.at_time(ts_.trans(), i - 1);
    DFS(u);
  }

  // solver_->push();
  logger.log(1, "Unrolling MulDivVerify at bound: {}", i);
  // solver_->assert_formula(unroller_.at_time(bad_, i));
  //   Result r = solver_->check_sat();
  //   if (r.is_sat()) {
  //     res = false;
  //   } else {
  //     solver_->pop();
  //     ++reached_k_;
  //   }
  ++reached_k_;

  // return res;
}

smt::TermVec MulDivVerify::getChildren(smt::Term t)
{
  smt::TermVec children;
  for (auto child : t) {
    children.push_back(child);
  }
  return children;
}

void MulDivVerify::DFS(smt::Term root)
{
  smt::TermVec children = getChildren(root);
  logger.log(1, "root.op: {}", root->get_op());
  for (size_t i = 0; i < children.size(); i++) {
    logger.log(1, "child_{} : {}", i, children[i]);
  }
  std::cout << std::endl;
  for (auto child : children) {
    DFS(child);
  }
}

}  // namespace pono
