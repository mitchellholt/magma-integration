# magma-integration

Example:
```
> F<x> := RationalDifferentialField(RationalField());
>
> f := 2*x + 1;
> g := x^2 - 2;
> integral, logs := RationalIntegral(f/g);
> ReadableRationalIntegral(integral, logs);
1/4*(a + 4)*log(x - a) + 1/4*(-a + 4)*log(x + a)
>
> f := 3*x^5 - 2*x^4 - x^3 + 2*x^2 - 2*x + 2;
> g := x^6 - x^5 + x^4 - x^3;
> int, logs := RationalIntegral(f/g);
> ReadableRationalIntegral(int, logs);
log(x^3 - x^2 + x - 1) + 1/x^2
>
> f := 4*x^7 - 16*x^6 + 28*x^5 - 351*x^3 + 588*x^2 - 738;
> g := 2*x^7 - 8*x^6 + 14*x^5 - 40*x^4 + 82*x^3 - 76*x^2 + 120*x - 144;
> int, logs := RationalIntegral(f/g);
> ReadableRationalIntegral(int, logs);
(2*x^5 + 24/11*x^4 - 204/11*x^3 - 126/11*x^2 + 1123/22*x + 345/22)/(x^4 - 3*x^3 
+ 3*x^2 - 8*x + 12)
> #logs;
0
```
