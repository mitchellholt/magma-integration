F<x> := RationalDifferentialField(RationalField());

// Polynomials
G<g> := TranscendentalLogarithmicExtension(F, 1/x);

// integrate log x
poly := g;
elementary, integral := IntegrateLogarithmicPolynomial(g);
assert elementary;
error if Derivative(integral) ne Parent(integral) ! g, "Test failed", Derivative(integral), g;

// integrate log x / (x + 1)
poly := G ! (g/(x + 1));
assert not IntegrateLogarithmicPolynomial(poly);


// Rothstein-Trager
// integrate 1/(xlog(x))
is_poly, num := IsPolynomial(G!(1/x));
assert is_poly;
is_poly, denom := IsPolynomial(g);
assert is_poly;
assert Degree(denom) eq 1;

elementary, logs := LogarithmicRothsteinTrager(G, num, denom);
assert elementary;
error if #logs ne 1, "Test failed", logs;
deriv := logs[1][1] * (Derivative(logs[1][2])/(logs[1][2]));
intrep := Parent(deriv)!(1/(x*g));
error if deriv ne intrep, "Test failed", deriv, intrep;


// Tests for full rational integration routine
// integrate 1/(xlog(x))
h := G!(1/(x*g));
elementary, integral := LogarithmicIntegral(h);
assert elementary;
assert Derivative(integral) eq Parent(integral)!h;

// integrate 1/(x + 1) inside Q(x, log x) (should work fine)
h := G!(1/(x + 1));
elementary, integral := LogarithmicIntegral(h);
assert elementary;
assert G!Derivative(integral) eq h;

// integrate 1/log(x)
h := G!(1/g);
elementary, integarl := LogarithmicIntegral(h);
assert not elementary;

// integrate log(log(x))
H := TranscendentalLogarithmicExtension(G, G!(1/(x*g)));
elementary, integral := LogarithmicIntegral(H.1);
assert not elementary;

// Geddes example 12.11
A<a> := TranscendentalLogarithmicExtension(F, F!(1/(x + 1/2)));
B<b> := TranscendentalLogarithmicExtension(A, A!(1/x));
fn := (((1/2)*a - x)/((x + 1/2)^2 * a^2) + 4/x)*b^2
    + (((x^2 + x + 1)*a + x^2 - 1)/((x + 1/2)^2) + 2/((x + 1/2)*a) + 4/x)*b
    + ((x - 1/x)*a)/(x + 1/2) + 1/((x + 1/2)*a) + (1/2)/(x*(x + 1/2))
    + 1/(x + 1/2);
// NameField(~B);
// print B!fn;
elementary, integral := LogarithmicIntegral(B!fn);
assert elementary;
assert Derivative(integral) eq Parent(integral)!fn;
