F<x> := RationalDifferentialField(RationalField());

// Polynomials
G<g> := TranscendentalLogarithmicExtension(F, 1/x);

// integrate log x
poly := g;
is_elementary, integral := IntegrateLogarithmicPolynomial(g);
assert is_elementary;
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

integrable, logs := LogarithmicRothsteinTrager(G, num, denom);
assert integrable;
error if #logs ne 1, "Test failed", logs;
deriv := logs[1][1] * (Derivative(logs[1][2])/(logs[1][2]));
intrep := Parent(deriv)!(1/(x*g));
error if deriv ne intrep, "Test failed", deriv, intrep;
