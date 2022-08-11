/*********************                                                  */
/*! \file ic3back_dual.h
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

namespace pono {

class IC3BackDual : public IC3
{
  public:

    IC3BackDual(const Property & p,
            const TransitionSystem & ts,
            const smt::SmtSolver & s,
            PonoOptions opt = PonoOptions());

    virtual ~IC3BackDual() {}

    typedef IC3 super;

  protected:

    // B = bad
    void initialize() override;

    ProverResult check_until(int k) override;

    /** Perform a dual step
     *  @param i
     */
    ProverResult dual_step(int i); 

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

    bool forward_check_prop();

    IC3Formula print_generate_input(const IC3Formula & s, smt::Term input);

    inline long mid_num(const std::string& s) {
        return std::strtol(&s[s.find('_') + 1], nullptr, 10);
    }

    // /** isSAT(s /\ T /\ t')
    //  *  @param 
    //  *  @return s
    //  */
    // bool IC3BackDual::reach_check(size_t i, 
    //                                  const IC3Formula & t,
    //                                  IC3Formula & s,
    //                                  bool get_pred = true);
    void predecessor_generalization(size_t i,
                                  const smt::Term & c,
                                  IC3Formula & pred) override;
                                  

    void initialize_frame_back();

    smt::Term get_back_frame_term(bool act);

    IC3Formula generate(const IC3Formula & s, smt::Term, size_t k);

    void extend_frame_back(const IC3Formula & s);

    // void act(IC3Formula & t);
    // void inact(IC3Formula & t);

    std::map<smt::Term, bool> act_map_;

    std::vector<IC3Formula> O;

    // std::vector<std::vector<IC3Formula>> frames_back;
    // smt::TermVec frame_labels_back; 

    // maintain only one B frame
    std::vector<IC3Formula> frames_back;

    bool is_global_label_back(const smt::Term & l) const;

    bool block_all();

    bool reaches_bad(IC3Formula & out);


};
 
} // namespace pono