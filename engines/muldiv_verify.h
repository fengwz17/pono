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
 **/

#pragma once

#include "engines/prover.h"
#include "smt-switch/utils.h"

namespace pono {

class MulDivVerify : public Prover
{
 public:
  MulDivVerify(const Property & p,
               const TransitionSystem & ts,
               const smt::SmtSolver & solver,
               PonoOptions opt = PonoOptions());

  ~MulDivVerify();

  typedef Prover super;

  void initialize() override;

  ProverResult check_until(int k) override;
  void DFS(smt::Term root);
  smt::TermVec getChildren(smt::Term t);

 protected:
  void step(int i);

};  // class MulDivVerify

}  // namespace pono
