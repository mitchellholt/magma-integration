F<x> := RationalDifferentialField(RationalField());

// Polynomials
G<g> := TranscendentalLogarithmicExtension(F, x);

// integrate log x
poly := g;
is_elementary, integral := IntegrateLogarithmicPolynomial(g);
assert is_elementary;
error if Derivative(integral) ne Parent(integral) ! g, Derivative(integral), g;

// integrate log x / (x + 1)
poly := G ! (g/(x + 1));
assert not IntegrateLogarithmicPolynomial(poly);


// Rothstein-Trager
// integrate 1/(xlog(x))
is_poly, num := IsPolynomial(G!1);
assert is_poly;
is_poly, denom := IsPolynomial(G!(x*g));
assert is_poly;
assert Degree(denom) eq 1;

P := Parent(num);
inj := hom< P -> G | G.1 >;
itegrable, logs := LogarithmicRothsteinTrager(num, denom, inj);
assert integrable;
assert #logs eq 1;
deriv := logs[1][1] * (Derivative(logs[1][2])/(logs[1][2]));
intrep := Parent(deriv)!(inj(num)/inj(denom));
error if deriv ne intrep, deriv, intrep;
