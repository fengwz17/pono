# Calling IC3IA with msat
```
./pono -e ic3ia --smt-solver msat filename
```

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
