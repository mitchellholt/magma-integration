# magma-integration

Example:
```
> F<x> := RationalDifferentialField(RationalField());
> f := 2*x + 1;
> g := x^2 - 2;
> integral, logs := RationalIntegral(f/g);
> L := Parent(integral);
> K := ConstantField(L);
> AssignNames(~K, ["a"]);
> AssignNames(~L, [Sprintf("log(%o)", arg) : arg in logs]);
> integral;
1/4*(a + 4)*log(x - a) + 1/4*(-a + 4)*log(x + a)
```
