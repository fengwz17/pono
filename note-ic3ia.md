# Calling IC3IA with msat
```
./pono -e ic3ia --smt-solver msat filename
```

make_prover
prover->check_until(pono_options.bound_)
    IC3IA::initialize()
        IC3Base::initialize()
            IC3IA::abstract()

    IC3Base::step(int i)
        IC3Base::block_all()

            // If rel_ind_check returns true, c can be blocked
            IC3Base::rel_ind_check(i, c, out, get_pred)

            // c is disjunction and can be blocked
            IC3Base::inductive_generalization(size_t i, const IC3Formula & c)

    IC3IA::refine()




## pono.cpp 
```
prover = make_prover(eng, p, ts, s, pono_options);
```

```
ProverResult r;
else
{
    // call IC3Base::check_until
    r = prover->check_until(pono_options.bound_);
}
```

## make_provers.cpp  
```
return make_shared<IC3IA>(p, ts, slv, opts);
```

## ic3base.cpp 
```
ProverResult IC3Base::check_until(int k)
{
    // call IC3IA::initialize()
    initialize();
}
```

```
void IC3Base::initialize()
{
    // call IC3IA::abstract()
    abstract();

    
}
```

```
bool IC3Base::block_all()
{
    // ture iff bad is reachable from a state in the frontier
    // goal is a formula to populate with a state in the frontier that can reach bad in one step
    // if return true, it will call IC3Base::predecessor_generalization_and_fix
    while (reaches_bad(goal))
    {

    }

}
```

```
void IC3Base::predecessor_generalization_and_fix(size_t i, const Term & c, IC3Formula & pred)
{

}
```

## ic3base.h
``` 
// e.g. use "std::cout >>  out.term" to print the term of IC3Formula & out
struct IC3Formula
{

}
```

```
/**
 * Priority queue of proof obligations inspired by open-source ic3ia
 * implementation
 */
struct ProofGoalQueue
{
  private:
    // Type is ProofGoal *, the ProofGoal with the lowest index has the largest priority
    std::priority_queue<ProofGoal *, std::vector<ProofGoal *>, ProofGoalOrder>
      queue_;

}
```


## ic3ia.cpp
```
void IC3IA::initialize()
{
    // call IC3Base::initialize()
    super::initialize();
}
```

```
void IC3IA::abstract()
{
    // does the abstraction and return a set of concrete boolean symbols
    // set abstract transtition relation ts_
    const UnorderTerSet &bool_symbols = ia_.do_abstraction();


    // ts_.trans(): with '^' in ".next"
    get_free_symbolic_consts(ts_.init(), used_symbols);
    get_free_symbolic_consts(ts_.trans(), used_symbols);
    get_free_symbolic_consts(bad_, used_symbols);

}
```

## 