/*********************                                                  */
/*! \file ic3back_ua.h
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
#pragma once

#include <algorithm>
#include <queue>

#include "engines/prover.h"
#include "smt-switch/utils.h"
#include "engines/ic3.h"
#include "engines/ic3bits.h"

namespace pono {

class IC3BackUa : public IC3
{
  public:

    IC3BackUa(const Property & p,
            const TransitionSystem & ts,
            const smt::SmtSolver & s,
            PonoOptions opt = PonoOptions());

    virtual ~IC3BackUa() {}

    typedef IC3 super;

  protected:

    // B0 = bad
    void initialize() override;

    ProverResult check_until(int k) override;

    /** Perform a Backward step
     *  @param i
     */
    ProverResult back_step(int i); 

    /** Perform the base step (zero case),
     *  check if B0 intersects with I.
     */
    bool base_check();

    /** Perform checking on each state t \in B[k]
     *  @param k, t
     *  @return 
     *   if not isSAT(I /\ T /\ t'), return false
     *   else if isSAT(not B[k] /\ T /\ t'), add \bar{s} to B[k+1]
     *   else if \bar{t} can reach B[0], add \bar{t} to B[k-1], B[k], B[k+1]
     */
    bool check(size_t k, const IC3Formula & t);

    // /** isSAT(s /\ T /\ t')
    //  *  @param 
    //  *  @return s
    //  */
    // bool IC3BackUa::reach_check(size_t i, 
    //                                  const IC3Formula & t,
    //                                  IC3Formula & s,
    //                                  bool get_pred = true);

    bool invar_check(size_t k);
    
    void push_frame();

    smt::Term get_frame_term(size_t i) const;

    IC3Formula generate(IC3Formula & s);

    void reset_solver();

};
 
} // namespace pono