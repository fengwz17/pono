/*********************                                                  */
/*! \file ic3back_ua.cpp
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

#include "engines/ic3back_prop.h"

#include "assert.h"
#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/term_analysis.h"
#include <fstream>

using namespace smt;
using namespace std;

namespace pono {

IC3BackProp::IC3BackProp(const Property & p, const TransitionSystem & ts,
         const smt::SmtSolver & s, PonoOptions opt)
  : super(p, ts, s, opt)
{
    engine_ = Engine::IC3BACKPROP_ENGINE;
}

void IC3BackProp::initialize()
{
    if (initialized_) {
        return;
    }

    boolsort_ = solver_->make_sort(BOOL);
    solver_true_ = solver_->make_term(true);

    // TODO: needs to be considered how to do abstraction
    // abstract();

    Prover::initialize();

    // check whether this flavor of IC3 can be applied to this transition system
    check_ts();

    assert(solver_context_ == 0);  // expecting to be at base context level

    frames_.clear();
    frame_labels_.clear();

    // Backward: first frame is always the bad states
    push_frame();

    vector<IC3Formula> & B0 = frames_.at(0);

    solver_->assert_formula(
        solver_->make_term(Implies, frame_labels_.at(0), bad_));
    // push_frame();

    // set semantics of TS labels
    assert(!init_label_);
    assert(!trans_label_);
    assert(!bad_label_);
    // Backward: frame 0 label is identical to bad label
    bad_label_ = frame_labels_[0];

    trans_label_ = solver_->make_symbol("__trans_label", boolsort_);
    solver_->assert_formula(
        solver_->make_term(Implies, trans_label_, ts_.trans()));

    // Backward: we record init state as "init_label_", but "init_label_" is not B[0]
    init_label_ = solver_->make_symbol("__init_label", boolsort_);
    solver_->assert_formula(solver_->make_term(Implies, init_label_, ts_.init()));

}

ProverResult IC3BackProp::check_until(int k)
{
    initialize();

    assert(initialized_);

    ProverResult res;
    // int i = reached_k_ + 1;
    int i = 1;
    assert(reached_k_ + 1 >= 0);
    push_frame();
    while(i <= k) {
        // std::cout << "i: " << i << std::endl;
        res = back_step(i);

        if (res == ProverResult::FALSE) {
            assert(cex_.size());
            return ProverResult::FALSE;
        }
        // else {
        //     ++i;
        // }

        if (res != ProverResult::UNKNOWN) {
            return res;
        }
    }

    return ProverResult::UNKNOWN;
}

ProverResult IC3BackProp::back_step(int & i)
{  
    // if (i <= reached_k_)
    // {
    //     return ProverResult::UNKNOWN;
    // }

    // isSAT(I /\ B[0]) or isSAT(I /\ T /\ B[0]')
    if (reached_k_ < 1)
    {
        if (!base_check())
        {
            logger.log(1, "Return UNSAFE in base_check");
            return ProverResult::FALSE;
        }
    }

    // std::cout << "reached_k_" << reached_k_ << std::endl;
    

    // reached_k_ is the number of transitions that have been checked,
    //  currently, there are reached_k_ + 1 frames in total 
    // at this point, we check each state t of B[k]
    // if isSAT(I /\ T /\ t') return UNSAFE
    // else if isSAT(\neg B[k] /\ T /\ t') extend B[k+1]
    // TODO: unsat core and optimaizations
    logger.log(1, "Check init-reachable phase at frame {}", i);

    
    
    push_solver_context();

    // not init
    solver_->assert_formula(solver_->make_term(Not, init_label_));

    // not Bk
    solver_->assert_formula(
            solver_->make_term(Not, get_frame_term(i)));

    // TermVec input_lits = get_input_values();
    // Term input_formula = make_and(input_lits);

    // solver_->assert_formula(input_formula);

    // trans
    // solver_->assert_formula(trans_label_);
    solver_->assert_formula(ts_.trans());

    // Bk-1'
    solver_->assert_formula(ts_.next(get_frame_term(i - 1)));

    Result r = check_sat();
    if (r.is_sat()) {
        IC3Formula s = get_model_ic3formula();

        TermVec input_lits = get_input_values();
        Term input_formula = make_and(input_lits);


        pop_solver_context();
        
        // for (const auto & ss : s.children){
        //     std::cout << "ss: " << ss << std::endl;
        // } 
        // std::cout << "........after generating.........\n";
        // IC3Formula out = print_generate_input(s, input_formula, i);  
        IC3Formula out = print_generate(s, i);
        // IC3Formula out = generate_from_qbf(s, i);
        // IC3Formula out = s;

        push_solver_context();

        solver_->assert_formula(init_label_);
        solver_->assert_formula(ts_.trans());
        solver_->assert_formula(ts_.next(out.term));       

        Result rr = check_sat();
        if (rr.is_sat()) {
            pop_solver_context();
            return ProverResult::FALSE;
        }
        pop_solver_context();

        // std::cout << "B" << i << ": " << get_frame_term(i) << std::endl;
        
        extend_frame(i, out);

        // std::cout << "..............extending...........\n";

        // std::cout << "B" << i <<": " << get_frame_term(i) << std::endl;

        propagate(out, i - 1);

    } else if (invar_check(i)) {

        pop_solver_context();

        // push_solver_context();

        // solver_->assert_formula(ts_.init());

        // solver_->assert_formula(ts_.trans());

        // // Bk'
        // solver_->assert_formula(ts_.next(get_frame_term(i)));

        // Result rrr = check_sat();
        // std::cout << "rrr: " << rrr << std::endl;

        return ProverResult::TRUE;
    } else {
        pop_solver_context();
        push_frame();
        ++reached_k_;
        ++i;
        // std::cout << "i: " << i << std::endl;
    }

    return ProverResult::UNKNOWN;
}

bool IC3BackProp::base_check()
{
    assert(reached_k_ < 1);
    if (reached_k_ < 0) {
        logger.log(1, "Checking if initial states satisfy bad property");

        push_solver_context();

        // Backward: init is bad_label 
        solver_->assert_formula(init_label_);
        solver_->assert_formula(bad_label_);

        // check isSAT(I /\ B0)
        Result r = check_sat();
        if (r.is_sat()) {
            pop_solver_context();
            // trace is only one bad state that intersects with initial
            cex_.clear();
            cex_.push_back(bad_);
            return false;
        } else {
            assert(r.is_unsat());
            reached_k_ = 0;  // keep reached_k_ aligned with number of frames
        }
        pop_solver_context();
    }

    // Check isSAT(I /\ T /\ B0')
    assert(reached_k_ == 0);
    logger.log(1, "Checking if inital states can violate property in one-step");

    push_solver_context();
    // solver_->assert_formula(ts_.init());
    solver_->assert_formula(init_label_);
    // solver_->assert_formula(ts_.trans());
    solver_->assert_formula(trans_label_);
    // solver_->assert_formula(ts_.next(bad_));
    solver_->assert_formula(ts_.next(bad_label_));
    
    Result r = check_sat();
    if (r.is_sat()) {
        // TODO: construct counterexample
        // const IC3Formula &c = get_model_ic3formula();
        pop_solver_context();
        // ProofGoal * pg = new ProofGoal(c, 0, nullptr);
        // reconstruct_trace(pg, cex_);
        // delete pg;
        return false;
    } else {
        assert(r.is_unsat());
        reached_k_ = 1;  // keep reached_k_ aligned with number of frames
    }
    pop_solver_context();

    return true;
}

void IC3BackProp::push_frame()
{
    assert(frame_labels_.size() == frames_.size());

    frame_labels_.push_back(
        solver_->make_symbol("__frame_label_" + std::to_string(frames_.size()),
                            solver_->make_sort(BOOL)));
    // frames_.push_back({});
    TermVec badTermVec = {bad_};
    IC3Formula bad = ic3formula_conjunction(badTermVec);

    if (frames_.size() == 0)
    {
        frames_.push_back({bad});
    }
    else
    {
        frames_.push_back(frames_.at(frames_.size() - 1));
    }

    if (frames_.size() > 1) {
        // always start (non-initial) frame the same as the last frame
        Term last_frame_term = get_frame_term(frames_.size() - 1);
        solver_->assert_formula(
            solver_->make_term(Implies, frame_labels_.back(), last_frame_term));
    }


}

Term IC3BackProp::get_frame_term(size_t i) const
{
    Term res = solver_true_;
    res = solver_->make_term(Not, res);
    // for (size_t j = i; j < frames_.size(); ++j) {
    for (const auto &u : frames_[i]) {
        res = solver_->make_term(Or, res, u.term);
        // }
    }

    // the property is implicitly part of the frame
    // res = solver_->make_term(And, res, smart_not(bad_));
    return res;
}


IC3Formula IC3BackProp::print_generate_input(const IC3Formula & s, smt::Term input, size_t k)
{
    // IC3Formula out;
    std::map<size_t, Term> smap;
    string filename = "QBF_" + std::to_string(k) + ".smt2";
    ofstream openfile(filename);
    openfile << "(set-option :produce-unsat-cores true)\n";
    openfile << "(set-logic ALL)\n";

    for (const auto & in : ts_.inputvars()) {
        openfile << "(declare-fun " << in << " () " << in->get_sort() << ")\n";
    }

    for (const auto & sv : ts_.statevars()) {
        openfile << "(declare-fun " << sv << " () " << sv->get_sort() << ")\n";
    }

    for (const auto & sv : ts_.statevars()) {
        openfile << "(declare-fun " << ts_.next(sv) << " () " << sv->get_sort() << ")\n";
    }

    for (const auto & ss : s.children) {
        openfile << "(assert (! " << ss << " :named" <<  " ss_" << ss->get_id() << "))\n";
        smap[ss->get_id()] = ss;
    }
    
    openfile << "(assert " << input << ")\n";
    Term notT = solver_->make_term(Not, ts_.trans());
    Term notB = solver_->make_term(Not, ts_.next(get_frame_term(k -1)));
    Term notTnotB = solver_->make_term(Or, notT, notB);
    // Term TB = solver_->make_term(And, trans_label_, ts_.next(get_frame_term(k-1)));

    // solver_->dump_smt2("QBF.smt2");

    openfile << "(assert (forall (";

    // TermVec para;
    
    for (const auto & sv : ts_.statevars()) {
        Term nsv = ts_.next(sv);

        // Term t = solver_->make_param(nsv->to_string(), nsv->get_sort());

        // para.push_back(t);
        // std::cout << t << std::endl;

        openfile << "(" << nsv->to_string() << " " << nsv->get_sort() << ")";
    }
    openfile << ")\n";
    openfile << notTnotB << "))\n";

    // para.push_back(notTnotB);
    // solver_->assert_formula(solver_->make_term(Forall, para));
    // solver_->assert_formula(s.term);
    
    // for (size_t i = 0; i < para.size(); ++i)
    // {
    //     std::cout << "para[" << i << "] " << para[i] << std::endl;
    // }

    // notTnotB = solver_->make_term(Forall, para);

    // std::cout << notTnotB << std::endl;
    // solver_->assert_formula(notTnotB);
    // openfile << solver_->make_term(Not, ts_.trans()) << '\n';
    // openfile << solver_->make_term(Not, ts_.next(get_frame_term(k - 1))) << '\n';

    // openfile.close();
    // Result r = check_sat();
    // std::cout << "r: " << r << std::endl;

    openfile << "(check-sat)\n";
    openfile << "(get-unsat-core)\n";
    openfile.close();

    char buf[1024];
    string result, term;
    /// std::vector<size_t> coreid;
    TermVec core;
    string command = "cvc5 " + filename;
    FILE * p = popen(command.c_str(), "r");
    while(fgets(buf, 1024, p) != NULL) {
        // std::cout << "buf: " << buf << std::endl;
        // if (buf[1] == 's') {
        //     result = buf;
        //     break;
        // }
        if (buf[1] == 's') {
            result = buf;
            core.push_back(smap[mid_num(result)]);
        }
        
    }

    pclose(p);

    // istringstream record(result);
    // while (record >> term) {

    //     core.push_back(smap[mid_num(term)]);
    // }
    // for (int i = 0; i < core.size(); ++i) {
    //     std::cout << core[i] << "\n";
    // }
    IC3Formula out = reduce_generate(s, k, input, core);
    // IC3Formula out = ic3formula_conjunction(core);

    // for (const auto & ss : s.children){
    //     if (ss->get_id() == size_t())
    // }

    return out;
}

// get reduced unsat core 
IC3Formula IC3BackProp::generate_from_qbf(const IC3Formula & s, size_t k)
{
    push_solver_context();
    Term notT = solver_->make_term(Not, ts_.trans());
    Term notB = solver_->make_term(Not, ts_.next(get_frame_term(k -1)));
    Term notTnotB = solver_->make_term(Or, notT, notB);
    
    TermVec param_vec;
    param_vec.clear();
    
    for (const auto & in : ts_.inputvars()) {
        Term t = solver_->make_param(in->to_string(), in->get_sort());
        param_vec.push_back(t);
    }
    
    // for (const auto & sv : ts_.statevars()) {
    //     Term t = solver_->make_param(sv->to_string(), sv->get_sort());
    //     param_vec.push_back(t);
    // }
    
    for (const auto & sv : ts_.statevars()) {
        Term nsv = ts_.next(sv);
        Term t = solver_->make_param(nsv->to_string(), nsv->get_sort());
        param_vec.push_back(t);
    }
    param_vec.push_back(notTnotB);
    solver_->assert_formula(s.term);
    Term q = solver_->make_term(Forall, param_vec);
    std::cout << "s: " << s.term << std::endl;
    std::cout << "q: " << q << std::endl;
    solver_->assert_formula(q);
    Result r = check_sat();
    std::cout << "r: " << r << std::endl;
    pop_solver_context();
    return s;
}

IC3Formula IC3BackProp::print_generate(const IC3Formula & s, size_t k)
{
    // IC3Formula out;
    std::map<size_t, Term> smap;
    string filename = "QBF_" + std::to_string(k) + ".smt2";
    ofstream openfile(filename);
    openfile << "(set-option :produce-unsat-cores true)\n";
    openfile << "(set-logic ALL)\n";

    for (const auto & in : ts_.inputvars()) {
        openfile << "(declare-fun " << in << " () " << in->get_sort() << ")\n";
    }

    for (const auto & sv : ts_.statevars()) {
        openfile << "(declare-fun " << sv << " () " << sv->get_sort() << ")\n";
    }

    for (const auto & sv : ts_.statevars()) {
        openfile << "(declare-fun " << ts_.next(sv) << " () " << sv->get_sort() << ")\n";
    }

    for (const auto & ss : s.children) {
        openfile << "(assert (! " << ss << " :named" <<  " ss_" << ss->get_id() << "))\n";
        smap[ss->get_id()] = ss;
    }
    
    Term notT = solver_->make_term(Not, ts_.trans());
    Term notB = solver_->make_term(Not, ts_.next(get_frame_term(k -1)));
    Term notTnotB = solver_->make_term(Or, notT, notB);
    // Term TB = solver_->make_term(And, trans_label_, ts_.next(get_frame_term(k-1)));

    // solver_->dump_smt2("QBF.smt2");

    openfile << "(assert (forall (";

    TermVec para;
    
    for (const auto & sv : ts_.statevars()) {
        Term nsv = ts_.next(sv);

        Term t = solver_->make_param(nsv->to_string(), nsv->get_sort());

        para.push_back(t);
        std::cout << t << std::endl;

        openfile << "(" << nsv->to_string() << " " << nsv->get_sort() << ")";
    }

    for (const auto & iv : ts_.inputvars()) {
        openfile << "(" << iv->to_string() << " " << iv->get_sort() << ")";
    }

    openfile << ")\n";
    openfile << notTnotB << "))\n";

    para.push_back(notTnotB);
    std::cout << "notT: " << notTnotB << std::endl;
    solver_->assert_formula(solver_->make_term(Forall, para));
    // solver_->assert_formula(s.term);
    
    // for (size_t i = 0; i < para.size(); ++i)
    // {
    //     std::cout << "para[" << i << "] " << para[i] << std::endl;
    // }

    // notTnotB = solver_->make_term(Forall, para);

    // std::cout << notTnotB << std::endl;
    // solver_->assert_formula(notTnotB);
    // openfile << solver_->make_term(Not, ts_.trans()) << '\n';
    // openfile << solver_->make_term(Not, ts_.next(get_frame_term(k - 1))) << '\n';

    // openfile.close();
    // Result r = check_sat();
    // std::cout << "r: " << r << std::endl;

    openfile << "(check-sat)\n";
    openfile << "(get-unsat-core)\n";
    openfile.close();

    char buf[1024];
    string result, term;
    /// std::vector<size_t> coreid;
    TermVec core;
    string command = "cvc5 " + filename;
    FILE * p = popen(command.c_str(), "r");
    while(fgets(buf, 1024, p) != NULL) {
        // std::cout << "buf: " << buf << std::endl;
        // if (buf[1] == 's') {
        //     result = buf;
        //     break;
        // }
        if (buf[1] == 's') {
            result = buf;
            core.push_back(smap[mid_num(result)]);
        }
        
    }

    pclose(p);

    // istringstream record(result);
    // while (record >> term) {

    //     core.push_back(smap[mid_num(term)]);
    // }
    // for (int i = 0; i < core.size(); ++i) {
    //     std::cout << core[i] << "\n";
    // }

    // IC3Formula out = reduce_generate(s, k, core);
    IC3Formula out = ic3formula_conjunction(core);

    // for (const auto & ss : s.children){
    //     if (ss->get_id() == size_t())
    // }

    return out;
}

IC3Formula IC3BackProp::reduce_generate(const IC3Formula & s, size_t k, smt::Term input, TermVec core) {
    // IC3Formula out;
    int iter = 1;
    std::map<size_t, Term> smap;
    //  for (int i = 0; i < core.size(); ++i) {
    //     std::cout << core[i] << "\n";
    // }
    string filename = "QBF_" + std::to_string(k) + ".smt2";
    while (iter > 0)
    {
        smap.clear(); 
   
        ofstream openfile(filename);
        openfile << "(set-option :produce-unsat-cores true)\n";
        openfile << "(set-logic ALL)\n";

        for (const auto & in : ts_.inputvars()) {
            openfile << "(declare-fun " << in << " () " << in->get_sort() << ")\n";
        }

        for (const auto & sv : ts_.statevars()) {
            openfile << "(declare-fun " << sv << " () " << sv->get_sort() << ")\n";
        }

        for (const auto & sv : ts_.statevars()) {
            openfile << "(declare-fun " << ts_.next(sv) << " () " << sv->get_sort() << ")\n";
        }

        for (int i = 0; i < core.size(); ++i) {
            openfile << "(assert (! " << core[i] << " :named" <<  " ss_" << core[i]->get_id() << "))\n";
            smap[core[i]->get_id()] = core[i];
        }
        openfile << "(assert " << input << ")\n";
        Term notT = solver_->make_term(Not, ts_.trans());
        Term notB = solver_->make_term(Not, ts_.next(get_frame_term(k -1)));
        Term notTnotB = solver_->make_term(Or, notT, notB);
        // Term TB = solver_->make_term(And, trans_label_, ts_.next(get_frame_term(k-1)));

        // solver_->dump_smt2("QBF.smt2");

        openfile << "(assert (forall (";

        // TermVec para;
        
        for (const auto & sv : ts_.statevars()) {
            Term nsv = ts_.next(sv);

            // Term t = solver_->make_param(nsv->to_string(), nsv->get_sort());

            // para.push_back(t);
            // std::cout << t << std::endl;

            openfile << "(" << nsv->to_string() << " " << nsv->get_sort() << ")";
        }

        // for (const auto & iv : ts_.inputvars()) {
        //     openfile << "(" << iv->to_string() << " " << iv->get_sort() << ")";
        // }

        openfile << ")\n";
        openfile << notTnotB << "))\n";

        openfile << "(check-sat)\n";
        openfile << "(get-unsat-core)\n";
        openfile.close();

        char buf[1024];
        string result, term;
        /// std::vector<size_t> coreid;

    // TermVec core;
        core.clear();
        string command = "cvc5 " + filename;
        FILE * p = popen(command.c_str(), "r");
        while(fgets(buf, 1024, p) != NULL) {
            // std::cout << "buf: " << buf << std::endl;
            // if (buf[1] == 's') {
            //     result = buf;
            //     break;
            // }
            if (buf[1] == 's') {
                result = buf;
                core.push_back(smap[mid_num(result)]);
            }
            
        }

        pclose(p);
        iter--;

    }
    
    
    // istringstream record(result);
    // while (record >> term) {

    //     core.push_back(smap[mid_num(term)]);
    // }
    // for (int i = 0; i < core.size(); ++i) {
    //     std::cout << core[i] << "\n";
    // }
    IC3Formula out = ic3formula_conjunction(core);

    // for (const auto & ss : s.children){
    //     if (ss->get_id() == size_t())
    // }

    return out;
}

void IC3BackProp::extend_frame(size_t k, const IC3Formula & s) {
    bool flag = false;
    vector<IC3Formula> Fk = frames_.at(k);
    for (size_t j = 0; j < Fk.size(); ++j)
    {
        if (s.term == Fk[j].term)
        {
            flag = true;
            break;
        }
    }
    if (flag == false)
    {
        solver_->assert_formula(
            solver_->make_term(Implies, frame_labels_.at(k), s.term));
        frames_.at(k).push_back(s);
    }   
}

void IC3BackProp::propagate(IC3Formula & s, size_t i) {
    if (i > 0) {
        push_solver_context();
        solver_->assert_formula(s.term);
        solver_->assert_formula(ts_.trans());
        solver_->assert_formula(ts_.next(get_frame_term(i - 1)));
        Result rp = check_sat();
        pop_solver_context();
        if (rp.is_sat()) {
            extend_frame(i, s);
            propagate(s, i - 1);
        }
    }    
}

bool IC3BackProp::invar_check(size_t i) {
    // std::cout << "B" << i << ": " << get_frame_term(i) << std::endl;
    // std::cout << "B" << i - 1 << ": " << get_frame_term(i-1) << std::endl;
    vector<IC3Formula> Fi = frames_[i];
    vector<IC3Formula> Fi1 = frames_[i - 1];
    if (Fi.size() != Fi1.size()) {
        return false;
    }
    else {
        for (size_t k = 0; k < Fi.size(); ++k) {
            if (Fi[k].term != Fi1[k].term) {
                return false;
            }
        }
    }
    return true;
}

IC3Formula IC3BackProp::print_formula(const IC3Formula & s, smt::Term input, size_t k) {
    // push_solver_context();
    std::map<size_t, Term> smap;
    string filename = "QBF_" + std::to_string(k) + ".smt2";
    ofstream openfile(filename);
    openfile << "(set-option :produce-unsat-cores true)\n";
    openfile << "(set-logic ALL)\n";

    for (const auto & in : ts_.inputvars()) {
        openfile << "(declare-fun " << in << " () " << in->get_sort() << ")\n";
    }

    for (const auto & sv : ts_.statevars()) {
        openfile << "(declare-fun " << sv << " () " << sv->get_sort() << ")\n";
    }

    for (const auto & sv : ts_.statevars()) {
        openfile << "(declare-fun " << ts_.next(sv) << " () " << sv->get_sort() << ")\n";
    }

    for (const auto & ss : s.children) {
        openfile << "(assert (! " << ss << " :named" <<  " ss_" << ss->get_id() << "))\n";
        smap[ss->get_id()] = ss;
    }
    
    openfile << "(assert " << input << ")\n";
    Term notT = solver_->make_term(Not, ts_.trans());
    Term notB = solver_->make_term(Not, ts_.next(get_frame_term(k -1)));
    Term notTnotB = solver_->make_term(Or, notT, notB);
    // Term TB = solver_->make_term(And, trans_label_, ts_.next(get_frame_term(k-1)));

    // solver_->dump_smt2("QBF.smt2");
    openfile << "(assert (forall (";

    // TermVec para;
    
    for (const auto & in : ts_.inputvars()) {
        // Term t = solver_->make_param(nsv->to_string(), nsv->get_sort());

        // para.push_back(t);
        // std::cout << t << std::endl;

        openfile << "(" << in->to_string() << " " << in->get_sort() << ")";
    }
    openfile << ")\n";

    openfile << "(assert (forall (";

    // TermVec para;
    
    for (const auto & sv : ts_.statevars()) {
        Term nsv = ts_.next(sv);

        // Term t = solver_->make_param(nsv->to_string(), nsv->get_sort());

        // para.push_back(t);
        // std::cout << t << std::endl;

        openfile << "(" << nsv->to_string() << " " << nsv->get_sort() << ")";
    }
    openfile << ")\n";
    openfile << notTnotB << "))\n";

    // para.push_back(notTnotB);
    // solver_->assert_formula(solver_->make_term(Forall, para));
    // solver_->assert_formula(s.term);
    
    // for (size_t i = 0; i < para.size(); ++i)
    // {
    //     std::cout << "para[" << i << "] " << para[i] << std::endl;
    // }

    // notTnotB = solver_->make_term(Forall, para);

    // std::cout << notTnotB << std::endl;
    // solver_->assert_formula(notTnotB);
    // openfile << solver_->make_term(Not, ts_.trans()) << '\n';
    // openfile << solver_->make_term(Not, ts_.next(get_frame_term(k - 1))) << '\n';

    // openfile.close();
    // Result r = check_sat();
    // std::cout << "r: " << r << std::endl;

    openfile << "(check-sat)\n";
    openfile << "(get-unsat-core)\n";
    openfile.close();

    char buf[1024];
    string result, term;
    /// std::vector<size_t> coreid;
    TermVec core;
    string command = "../deps/cvc5/build/bin/cvc5 " + filename;
    FILE * p = popen(command.c_str(), "r");
    while(fgets(buf, 1024, p) != NULL) {
        // std::cout << "buf: " << buf << std::endl;
        // if (buf[1] == 's') {
        //     result = buf;
        //     break;
        // }
        if (buf[1] == 's') {
            result = buf;
            core.push_back(smap[mid_num(result)]);
        }
        
    }

    pclose(p);

    // istringstream record(result);
    // while (record >> term) {

    //     core.push_back(smap[mid_num(term)]);
    // }
    // for (int i = 0; i < core.size(); ++i) {
    //     std::cout << core[i] << "\n";
    // }
    IC3Formula out = ic3formula_conjunction(core);

    // for (const auto & ss : s.children){
    //     if (ss->get_id() == size_t())
    // }
    return out;
}


void IC3BackProp::generate_quantified_formula(const IC3Formula & s, size_t k) {
    // push_solver_context();
    // IC3Formula out;
    std::map<size_t, Term> smap;
    string filename = "QBF_" + std::to_string(k) + ".smt2";
    ofstream openfile(filename);
    openfile << "(set-option :produce-unsat-cores true)\n";
    openfile << "(set-logic ALL)\n";

    for (const auto & in : ts_.inputvars()) {
        openfile << "(declare-fun " << in << " () " << in->get_sort() << ")\n";
    }

    for (const auto & sv : ts_.statevars()) {
        openfile << "(declare-fun " << sv << " () " << sv->get_sort() << ")\n";
    }

    for (const auto & sv : ts_.statevars()) {
        openfile << "(declare-fun " << ts_.next(sv) << " () " << sv->get_sort() << ")\n";
    }

    for (const auto & ss : s.children) {
        openfile << "(assert (! " << ss << " :named" <<  " ss_" << ss->get_id() << "))\n";
        smap[ss->get_id()] = ss;
    }
    
    Term notT = solver_->make_term(Not, ts_.trans());
    Term notB = solver_->make_term(Not, ts_.next(get_frame_term(k -1)));
    Term notTnotB = solver_->make_term(Or, notT, notB);
    // Term TB = solver_->make_term(And, trans_label_, ts_.next(get_frame_term(k-1)));

    // solver_->dump_smt2("QBF.smt2");

    openfile << "(assert (forall (";

    TermVec para;
    
    for (const auto & sv : ts_.statevars()) {
        Term nsv = ts_.next(sv);

        Term t = solver_->make_param(nsv->to_string(), nsv->get_sort());

        para.push_back(t);
        std::cout << t << std::endl;

        openfile << "(" << nsv->to_string() << " " << nsv->get_sort() << ")";
    }

    for (const auto & iv : ts_.inputvars()) {
        openfile << "(" << iv->to_string() << " " << iv->get_sort() << ")";
    }

    openfile << ")\n";
    openfile << notTnotB << "))\n";

    para.push_back(notTnotB);
    std::cout << "notT: " << notTnotB << std::endl;
    solver_->assert_formula(solver_->make_term(Forall, para));
    // solver_->assert_formula(s.term);
    
    // for (size_t i = 0; i < para.size(); ++i)
    // {
    //     std::cout << "para[" << i << "] " << para[i] << std::endl;
    // }

    // notTnotB = solver_->make_term(Forall, para);

    // std::cout << notTnotB << std::endl;
    // solver_->assert_formula(notTnotB);
    // openfile << solver_->make_term(Not, ts_.trans()) << '\n';
    // openfile << solver_->make_term(Not, ts_.next(get_frame_term(k - 1))) << '\n';

    // openfile.close();
    // Result r = check_sat();
    // std::cout << "r: " << r << std::endl;

    openfile << "(check-sat)\n";
    openfile << "(get-unsat-core)\n";
    openfile.close();

    char buf[1024];
    string result, term;
    /// std::vector<size_t> coreid;
    TermVec core;
    string command = "cvc5 " + filename;
    FILE * p = popen(command.c_str(), "r");
    while(fgets(buf, 1024, p) != NULL) {
        // std::cout << "buf: " << buf << std::endl;
        // if (buf[1] == 's') {
        //     result = buf;
        //     break;
        // }
        if (buf[1] == 's') {
            result = buf;
            core.push_back(smap[mid_num(result)]);
        }
        
    }

    pclose(p);

    // istringstream record(result);
    // while (record >> term) {

    //     core.push_back(smap[mid_num(term)]);
    // }
    // for (int i = 0; i < core.size(); ++i) {
    //     std::cout << core[i] << "\n";
    // }

    // IC3Formula out = reduce_generate(s, k, core);
    IC3Formula out = ic3formula_conjunction(core);

    // for (const auto & ss : s.children){
    //     if (ss->get_id() == size_t())
    // }

    return out;

}

}