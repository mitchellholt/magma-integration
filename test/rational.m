F<x> := RationalDifferentialField(RationalField());

f := 2*x + 1;
g := x^2 - 2;
integral := RationalIntegral(f/g);
error if Derivative(integral) ne Parent(integral) ! (f/g), Derivative(integral), f/g;

f := 3*x^5 - 2*x^4 - x^3 + 2*x^2 - 2*x + 2;
g := x^6 - x^5 + x^4 - x^3;
integral := RationalIntegral(f/g);
error if Derivative(integral) ne Parent(integral) ! (f/g), Derivative(integral), f/g;

f := 4*x^7 - 16*x^6 + 28*x^5 - 351*x^3 + 588*x^2 - 738;
g := 2*x^7 - 8*x^6 + 14*x^5 - 40*x^4 + 82*x^3 - 76*x^2 + 120*x - 144;
integral := RationalIntegral(f/g);
error if Derivative(integral) ne Parent(integral) ! (f/g), Derivative(integral), f/g;

f := 6*x^5 - 4*x^4 - 32*x^3 + 12*x^2 + 34*x - 24;
g := x^6 - 8*x^4 + 17*x^2 - 8;
integral := RationalIntegral(f/g);
error if Derivative(integral) ne Parent(integral) ! (f/g), Derivative(integral), f/g;
