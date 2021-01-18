/*********************                                                  */
/*! \file mod_init_prop.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Ahmed Irfan
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Replace initial state and property constraints with boolean variables.
**
**
**/

#pragma once

#include "core/ts.h"
#include "smt-switch/utils.h"
#include "utils/logger.h"
#include "utils/term_analysis.h"

namespace pono {

smt::Term modify_init_and_prop(TransitionSystem & ts, const smt::Term & prop)
{
  logger.log(1, "Modifying init and prop");

  // copy constraints from before we start modifying the system
  std::vector<std::pair<smt::Term, bool>> constraints = ts.constraints();

  // replace prop if it's not already a literal
  smt::Sort boolsort = ts.make_sort(smt::BOOL);
  smt::Term new_prop = prop;
  if (!is_lit(prop, boolsort)) {
    new_prop = ts.make_statevar("__propvar", boolsort);
    ts.assign_next(new_prop, prop);
  }

  // replace initial states
  // will become the new initial state, by itself
  smt::Term fake_init =
      ts.make_statevar("__fake_init", ts.make_sort(smt::BOOL));

  // indicator for the actual initial state constraints
  // which will be true in the second state of the execution
  smt::Term initstate =
      ts.make_statevar("__initstate", ts.make_sort(smt::BOOL));

  smt::Term init = ts.init();
  smt::TermVec init_constraints;
  conjunctive_partition(init, init_constraints, true);

  // add initial state constraints for initstate1
  for (const auto & ic : init_constraints) {
    assert(ts.only_curr(ic));
    ts.add_constraint(ts.make_term(smt::Implies, initstate, ic), true);
  }

  // NOTE: relies on feature of ts to not add constraint to init
  for (const auto & e : constraints) {
    ts.add_constraint(ts.make_term(smt::Implies, initstate, e.first), e.second);
  }

  ts.assign_next(fake_init, ts.make_term(false));
  ts.assign_next(initstate,
                 fake_init);  // becomes true one state after fake_init

  // adding the constraints above might have put constraints in init
  // overwrite that now
  ts.set_init(fake_init);
  ts.constrain_init(ts.make_term(smt::Not, initstate));
  ts.constrain_init(new_prop);

  return new_prop;
}

// optimization to assume the property in the pre-state
// although confusing, this is sound as long as you always check
// for a property violation over the next-state variables
void prop_in_trans(TransitionSystem & ts, const smt::Term & prop)
{
  // NOTE: CRUCIAL that we pass false here
  // cannot add to init or the next states
  // passing false prevents that
  ts.add_constraint(prop, false);
}

}  // namespace pono
