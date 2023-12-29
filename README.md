# magma-integration

Example:
```
> F<x> := RationalDifferentialField(RationalField());
> f := 3*x^5 - 2*x^4 - x^3 + 2*x^2 - 2*x + 2;
> g := x^6 - x^5 + x^4 - x^3;
> RationalIntegral(f/g);
log(x^3 - x^2 + x - 1) + 1/x^2
```
