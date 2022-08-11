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
#include <map>

#include "engines/prover.h"
#include "smt-switch/utils.h"
#include "engines/ic3.h"
#include "engines/ic3bits.h"

#include <cvc5/cvc5.h>

namespace pono {

class IC3BackProp : public IC3
{
  public:

    IC3BackProp(const Property & p,
            const TransitionSystem & ts,
            const smt::SmtSolver & s,
            PonoOptions opt = PonoOptions());

    virtual ~IC3BackProp() {}

    typedef IC3 super;

  protected:

    // B0 = bad
    void initialize() override;

    ProverResult check_until(int k) override;

    /** Perform a Backward step
     *  @param i
     */
    ProverResult back_step(int & i); 

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
    bool forward_check(size_t k, const IC3Formula & t);

    // /** isSAT(s /\ T /\ t')
    //  *  @param 
    //  *  @return s
    //  */
    // bool IC3BackProp::reach_check(size_t i, 
    //                                  const IC3Formula & t,
    //                                  IC3Formula & s,
    //                                  bool get_pred = true);

    // bool invar_check(size_t k);
    
    void push_frame();

    smt::Term get_frame_term(size_t i) const;

    // s /\ i |= \exists X'(T /\ Bk-1')
    // \bar{s} /\ i /\ \forall X'(\neg T \/ \neg Bk-1')
    IC3Formula print_generate_input(const IC3Formula & s, smt::Term input, size_t k);

    IC3Formula generate_from_qbf(const IC3Formula & s, size_t k);

    // s |= \exists i, X'(T /\ Bk-1')
    // \bar{s} /\ \forall i, X'(\neg T \/ \neg Bk-1')
    IC3Formula print_generate(const IC3Formula & s, size_t k);

    IC3Formula reduce_generate(const IC3Formula & s, size_t k, smt::Term input, smt::TermVec core);
   

    // void reset_solver();

    void extend_frame(size_t k, const IC3Formula & s);

    // void act(IC3Formula & t);
    // void inact(IC3Formula & t);

    std::map<smt::Term, bool> act_map_;

    std::vector<IC3Formula> O;

    smt::Term get_act_frame_term(size_t i); 

    void propagate(IC3Formula & s, size_t i);

    bool invar_check(size_t k);

    IC3Formula print_formula(const IC3Formula & s, smt::Term input, size_t k);

    void generate_quantified_formula(const IC3Formula & s, size_t k);

    inline long mid_num(const std::string& s) {
        return std::strtol(&s[s.find('_') + 1], nullptr, 10);
    }

};
 
} // namespace pono