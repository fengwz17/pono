from libcpp.string cimport string
from libcpp.unordered_map cimport unordered_map
from libcpp.unordered_set cimport unordered_set

from smt_switch cimport c_Sort, c_Term, c_SmtSolver, c_TermVec, c_UnorderedTermMap

ctypedef unordered_set[c_Term] c_UnorderedTermSet


cdef extern from "ts.h" namespace "cosa":
    cdef cppclass TransitionSystem:
        TransitionSystem(c_SmtSolver & s) except +
        void set_init(const c_Term & init) except +
        void constrain_init(const c_Term & constraint) except +
        void assign_next(const c_Term & state, const c_Term & val) except +
        void add_invar(const c_Term & constraint) except +
        void constrain_inputs(const c_Term & constraint) except +
        void add_constraint(const c_Term & constraint) except +
        void name_term(const string name, const c_Term & t) except +
        c_Term make_input(const string name, const c_Sort & sort) except +
        c_Term make_state(const string name, const c_Sort & sort) except +
        c_Term curr(const c_Term & term) except +
        c_Term next(const c_Term & term) except +
        bint is_curr_var(const c_Term & sv) except +
        bint is_next_var(const c_Term & sv) except +
        c_SmtSolver & solver() except +
        const c_UnorderedTermSet & states() except +
        const c_UnorderedTermSet & inputs() except +
        c_Term init() except +
        c_Term trans() except +
        const c_UnorderedTermMap & state_updates() except +
        unordered_map[string, c_Term] & named_terms() except +
        bint is_functional() except +


cdef extern from "rts.h" namespace "cosa":
    cdef cppclass RelationalTransitionSystem(TransitionSystem):
        RelationalTransitionSystem(c_SmtSolver & s) except +
        void set_behavior(const c_Term & init, const c_Term & trans) except +
        void set_trans(const c_Term & trans) except +
        void constrain_trans(const c_Term & constraint) except +


cdef extern from "fts.h" namespace "cosa":
    cdef cppclass FunctionalTransitionSystem(TransitionSystem):
        FunctionalTransitionSystem(c_SmtSolver & s) except +


cdef extern from "prop.h" namespace "cosa":
    cdef cppclass Property:
        Property(const TransitionSystem& ts, c_Term p) except +
        const c_Term prop() except +
        const TransitionSystem & transition_system() except +


cdef extern from "unroller.h" namespace "cosa":
    cdef cppclass Unroller:
        pass


cdef extern from "bmc.h" namespace "cosa":
    cdef cppclass Bmc:
        pass


cdef extern from "kinduction.h" namespace "cosa":
    cdef cppclass KInduction:
        pass


cdef extern from "interpolantmc.h" namespace "cosa":
    cdef cppclass InterpolantMC:
        pass
