/*********************                                                  */
/*! \file ic3backbits_dual.h
** \verbatim
** Top contributors (to current version):
**   Weizhi Feng
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bit-level IC3 Back Under Approximation implementation that splits bitvector variables
**        into the individual bits for bit-level cubes/clauses
**        However, the transition system itself still uses bitvectors
**
**        Refer to the implementation of ic3bits.
**/

#pragma once

#include "engines/ic3back_dual.h"

namespace pono {

class IC3BackBitsDual : public IC3BackDual
{
 public:
  // itp_se is the SolverEnum for the interpolator

  IC3BackBitsDual(const Property & p,
          const TransitionSystem & ts,
          const smt::SmtSolver & s,
          PonoOptions opt = PonoOptions());

  virtual ~IC3BackBitsDual() {}

  typedef IC3BackDual super;

  void initialize() override;

 protected:
  smt::TermVec state_bits_;  ///< boolean variables + bit-vector variables
                             ///< split into individual bits

  // virtual method overrides

  IC3Formula get_model_ic3formula() const override;

  bool ic3formula_check_valid(const IC3Formula & u) const override;

  void check_ts() const override;
};

}  // namespace pono
