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

#include <fstream>

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

  // std::cout << "(assert " << unroller_.at_time(ts_.init(), 0) << " )"
  //           << std::endl;
  // std::cout << std::endl;
  opCounter.clear();
  termIndex.clear();
}

void MulDivVerify::printSMTFormula(int k, int flag)
{
  if (flag == 0) {
    std::ofstream openfile("unrollerFile_" + std::to_string(k) + ".smt2");
    openfile << "(set-logic QF_BV)\n";

    for (int i = 0; i <= k; i++) {
      for (const auto & sv : ts_.statevars()) {
        openfile << "(declare-fun " << sv << "@" << i << " () "
                 << sv->get_sort() << ")\n";
      }

      for (const auto & inv : ts_.inputvars()) {
        openfile << "(declare-fun " << inv << "@" << i << " () "
                 << inv->get_sort() << ")\n";
      }
    }

    openfile << "(assert (= " << unroller_.at_time(ts_.init(), 0)
             << " #b1 ))\n";
    openfile.close();
  }

  if (flag > 0) {
    std::ofstream openfile("unrollerFile_" + std::to_string(k) + ".smt2",
                           std::ios::app);
    openfile << "(assert (= " << unroller_.at_time(ts_.trans(), flag - 1)
             << " #b1 ))\n";
    openfile.close();
  }

  if (flag == -1) {
    std::ofstream openfile("unrollerFile_" + std::to_string(k) + ".smt2",
                           std::ios::app);
    openfile << "(assert (= " << unroller_.at_time(bad_, k) << " #b1 ))\n";
    openfile << "(check-sat)\n";
    openfile.close();
  }
}

ProverResult MulDivVerify::check_until(int k)
{
  initialize();

  // print smt formula
  if (options_.print_smt_formula) {
    printSMTFormula(k, 0);
  }

  logger.log(2, "{}\n", unroller_.at_time(ts_.init(), 0));

  varName.clear();
  nodeName.clear();

  reached_k_ = k;
  poly_counter = 0;

  std::ofstream openfile("singular_poly");
  openfile.close();

  // // define ring
  // for (int i = 1; i <= k; ++i) {
  //   record(i);
  // }
  // std::ofstream openfile("singular_poly");  //, std::ios::app);
  // openfile << "ring r=integer, (";
  // for (int i = 0; i < varName.size() - 2; i++) {
  //   openfile << varName[i] << ", ";
  // }
  // openfile << varName[varName.size() - 1] << "), dp;\n";
  // openfile.close();

  // translate to polynomials
  for (int i = 0; i <= k; ++i) {
    step(i);
  }

  // dump property and other neccessary defination
  dumpPostDefine();

  // dump ring and variables defination
  dumpPreDefine();

  if (options_.print_smt_formula) {
    printSMTFormula(k, -1);
  }

  singularSolver();

  logger.log(2, "{}\n", unroller_.at_time(bad_, k));

  return ProverResult::UNKNOWN;
}

void MulDivVerify::step(int i)
{
  if (i > 0) {
    // solver_->assert_formula(unroller_.at_time(ts_.trans(), i - 1));

    // print smt formula
    if (options_.print_smt_formula) {
      printSMTFormula(reached_k_, i);
    }

    logger.log(2, "{}\n", unroller_.at_time(ts_.trans(), i - 1));

    smt::Term u = unroller_.at_time(ts_.trans(), i - 1);

    translatePoly(u);
  }

  logger.log(2, "Unrolling MulDivVerify at bound: {}", i);
}

smt::TermVec MulDivVerify::getChildren(smt::Term t)
{
  smt::TermVec children;
  for (auto child : t) {
    children.push_back(child);
  }
  return children;
}

void MulDivVerify::translatePoly(smt::Term root)
{
  smt::TermVec children = getChildren(root);

  // print base information in each node
  logger.log(3, "root.op: {}", root->get_op());
  logger.log(3, "root.sort.width: {}", root->get_sort()->get_width());

  for (size_t i = 0; i < children.size(); i++) {
    logger.log(3, "childTerm_{} : {}", i, children[i]);
  }
  logger.log(3, "\n");

  // record all nodeName

  // translate
  translate(root);

  for (auto child : children) {
    translatePoly(child);
  }
}

bool MulDivVerify::LeafNode(smt::Term node)
{
  if (node->get_op() == NUM_OPS_AND_NULL) {
    return true;
  }
  return false;
}

std::string MulDivVerify::getNodeName(smt::Term node)
{
  // if node is LeafNode, nodeName = node->to_string()
  //   else, nodeName = node->get_op().to_string()
  std::string nodeName = node->get_op().to_string();

  if (LeafNode(node)) {
    nodeName = node->to_string();
    // if (nodeName == "#b0") {
    //   nodeName = "0";
    // }
  }

  if (node->get_op().prim_op == Extract) {
    nodeName = "extract";
  }

  if (node->get_op() == Equal) {
    nodeName = "equal";
  }

  return nodeName + termIndex[node];
}

void MulDivVerify::setIndex(smt::Term nodeTerm)
{
  std::string opName = nodeTerm->get_op().to_string();
  if (nodeTerm->get_op().prim_op == Extract) {
    opName = "extract";
  }
  if (!LeafNode(nodeTerm)) {
    if (opCounter.count(opName) == 0) {
      termIndex[nodeTerm] = "_0";
      opCounter[opName] = 0;
    } else {
      if (termIndex.count(nodeTerm) == 0) {
        opCounter[opName]++;
        termIndex[nodeTerm] = "_" + std::to_string(opCounter[opName]);
      }
    }
  } else {
    termIndex[nodeTerm] = "";
  }
}

void MulDivVerify::translate(smt::Term node)
{
  std::ofstream openfile("singular_poly", std::ios::app);

  if (!LeafNode(node)) {
    openfile << "poly f" << poly_counter << " = ";
    smt::TermVec children = getChildren(node);

    // Binary
    // c = a * b
    // a * (1-a) = 1
    // b * (1-b) = 1
    if (node->get_op() == BVAnd) {
      setIndex(node);
      setIndex(children[0]);
      setIndex(children[1]);
      openfile << getNodeName(node) << " - " << getNodeName(children[0])
               << " * " << getNodeName(children[1]) << ";\n";
      // logger.log(1,
      //            "{} = {} * {}\n",
      //            getNodeName(node),
      //            getNodeName(children[0]),
      //            getNodeName(children[1]));
      // logger.log(1,
      //            "{}_{} * (1 - {}_{}) = 1)\n",
      //            getNodeName(children[0]),
      //            termIndex[children[0]],
      //            getNodeName(children[0]),
      //            termIndex[children[0]]);
      // logger.log(1,
      //            "{}_{} * (1 - {}_{}) = 1)\n",
      //            getNodeName(children[1]),
      //            termIndex[children[1]],
      //            getNodeName(children[1]),
      //            termIndex[children[1]]);
    }

    // c = a + b
    else if (node->get_op() == BVAdd) {
      setIndex(node);
      setIndex(children[0]);
      setIndex(children[1]);
      openfile << getNodeName(node) << " - (" << getNodeName(children[0])
               << " + " << getNodeName(children[1]) << ");\n";
    }

    // c = a * 2^len(b) + b
    else if (node->get_op() == Concat) {
      setIndex(node);
      setIndex(children[0]);
      setIndex(children[1]);
      int loLen = children[1]->get_sort()->get_width();
      // logger.log(1,
      //            "{} = {} * 2^{} + {}\n",
      //            getNodeName(node),
      //            getNodeName(children[0]),
      //            loLen,
      //            getNodeName(children[1]));
      openfile << getNodeName(node) << " - (2^" << loLen << " * "
               << getNodeName(children[0]) << " + " << getNodeName(children[1])
               << ");\n";

    }

    // a = b
    else if (node->get_op() == Equal) {
      // setIndex(node);
      setIndex(children[0]);
      setIndex(children[1]);
      std::string left = getNodeName(children[0]);
      std::string right = getNodeName(children[1]);
      // logger.log(1, "{} = {}\n", left, right);
      openfile << getNodeName(children[0]) << " - " << getNodeName(children[1])
               << ";\n";
    }

    // c = 1 if a <= b
    // c = 0 if a > b
    // b - a = diff - 2^len(b) * (1 - c)
    // c = 1 b = a + diff
    // c = 0 b + 2^len(b) = a + diff
    else if (node->get_op() == BVUlt) {
      setIndex(children[0]);
      setIndex(children[1]);
      std::string left = getNodeName(children[0]);
      std::string right = getNodeName(children[1]);
      int len = children[1]->get_sort()->get_width();
      openfile << getNodeName(children[1]) << " - " << getNodeName(children[0])
               << " - " << getNodeName(node) << "_diff + 2^" << len << " * "
               << "( 1 - " << getNodeName(node) << ");\n";
      varName.insert(getNodeName(node) + "_diff");
    }

    // unary
    // c = (extract u l) a
    // a = hi * 2^u + c * 2^l + lo
    else if (node->get_op().prim_op == Extract) {
      int u = node->get_op().idx0;
      int l = node->get_op().idx1;
      setIndex(node);
      setIndex(children[0]);
      // logger.log(1,
      //            "{} = {}_hi * 2^{} + {} * 2^{} + {}_lo\n",
      //            getNodeName(children[0]),
      //            getNodeName(node),
      //            u,
      //            getNodeName(node),
      //            l,
      //            getNodeName(node));
      if (l == 0) {
        openfile << getNodeName(children[0]) << " - (2^" << u + 1 << " * "
                 << getNodeName(node) << "_hi"
                 << " + 2^" << l << " * " << getNodeName(node) << ");\n";
        varName.insert(getNodeName(node) + "_hi");
      } else if (u == node->get_sort()->get_width() - 1) {
        openfile << getNodeName(children[0]) << " - (2^" << l << " * "
                 << getNodeName(node) << " + " << getNodeName(node)
                 << "_lo);\n";
        varName.insert(getNodeName(node) + "_lo");
      } else {
        openfile << getNodeName(children[0]) << " - (2^" << u + 1 << " * "
                 << getNodeName(node) << "_hi"
                 << " + 2^" << l << " * " << getNodeName(node) << " + "
                 << getNodeName(node) << "_lo);\n";
        varName.insert(getNodeName(node) + "_hi");
        varName.insert(getNodeName(node) + "_lo");
      }
    }

    // c = not a
    else if (node->get_op() == BVNot) {
      setIndex(node);
      setIndex(children[0]);
      // logger.log(1, "{} = -{}\n", getNodeName(node),
      // getNodeName(children[0]));
      openfile << getNodeName(node) << " + " << getNodeName(children[0])
               << ";\n";
    }

    // trinary
    // c = ite(cond, a, b)
    // c = cond * a + (1 - cond) * b
    else if (node->get_op() == Ite) {
      setIndex(node);
      setIndex(children[0]);
      setIndex(children[1]);
      setIndex(children[2]);
      // logger.log(1,
      //            "{} = {} * {} + (1 - {}) * {}\n",
      //            getNodeName(node),
      //            getNodeName(children[0]),
      //            getNodeName(children[1]),
      //            getNodeName(children[0]),
      //            getNodeName(children[1]));
      openfile << getNodeName(node) << " - " << getNodeName(children[0])
               << " * " << getNodeName(children[1]) << " - "
               << "(1 - " << getNodeName(children[0]) << ") * "
               << getNodeName(children[1]) << ";\n";
    }

    else {
      logger.log(1, "operator {} to be supported...", node->get_op());
      // std::cout << "node->get_sort(): " << node->get_sort() << std::endl;
      // std::cout << node->get_sort()->to_string() << std::endl;
      // std::cout << node->get_op().idx0 << " " << node->get_op().idx1 << " "
      //           << node->get_op().prim_op << " " <<
      //           node->get_op().to_string()
      //           << std::endl;
    }
  }

  if (!LeafNode(node)) {
    poly_counter++;
  }

  openfile.close();
  std::cout << getNodeName(node) << std::endl;
  varName.insert(getNodeName(node));
}

void MulDivVerify::dumpPreDefine()
{
  std::ofstream tmpfile("singular_command");

  tmpfile << "ring r=integer, (";
  // for (int i = 0; i < varName.size() - 1; i++) {
  //   tmpfile << varName[i] << ", ";
  // }
  // tmpfile << varName[varName.size() - 1] << "), dp;\n";
  for (auto var : varName) {
    tmpfile << var << ", ";
  }
  tmpfile << "x), dp;\n";

  std::ifstream openfile("singular_poly");
  std::string line;
  while (getline(openfile, line)) {
    tmpfile << line << "\n";
  }
  tmpfile.close();
}

void MulDivVerify::dumpPostDefine()
{
  std::ofstream openfile("singular_poly", std::ios::app);
  openfile << "ideal f" << poly_counter << " = ";
  for (int i = 0; i < poly_counter - 1; i++) {
    openfile << "f" << i << ", ";
  }
  openfile << "f" << poly_counter - 1 << ";\n";
  std::string propPoly;
  std::cin >> propPoly;
  openfile << "poly g = " << propPoly << ";\n";
  openfile << "ideal fI = groebner(f" << poly_counter << ");\n";
  openfile << "reduce(g, fI);\n";
  openfile.close();
}

void MulDivVerify::singularSolver()
{
  std::string singular_command =
      "Singular -c 'execute(read(\"singular_test\"));quit;' > singular_output";

  system(singular_command.c_str());

  // std::string result_command = "tail -2 singular_output | head -n 1";
  std::ifstream FILE("singular_output");
  std::string line, tmp_line;
  while (getline(FILE, line)) {
    if (line == "Auf Wiedersehen.") break;
    tmp_line = line;
  }
  if (tmp_line == "0") {
    std::cout << "Singular result: safe.\n";
  } else {
    std::cout << "Singular result: unknown\n";
  }
}

}  // namespace pono
