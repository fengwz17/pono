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

#include <map>
#include <set>

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
  void translate(smt::Term root);
  smt::TermVec getChildren(smt::Term t);
  bool LeafNode(smt::Term node);
  void translatePoly(smt::Term node);
  void setIndex(smt::Term nodeTerm);
  std::string getNodeName(smt::Term node);
  void printSMTFormula(int k, int flag);
  void singularSolver();
  void recordNodeName(smt::Term node);
  void record(int i);
  void dumpPreDefine();
  void dumpPostDefine();

  std::map<std::string, int> opCounter;
  std::map<smt::Term, std::string> termIndex;
  std::set<std::string> varName;
  std::vector<smt::Term> nodeName;

  int poly_counter = 0;

 protected:
  void step(int i);

};  // class MulDivVerify

}  // namespace pono
