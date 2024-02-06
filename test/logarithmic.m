F<x> := RationalDifferentialField(RationalField());

// Polynomials
G<g> := TranscendentalLogarithmicExtension(F, x);

poly := g;
is_elementary, integral := IntegrateLogarithmicPolynomial(g);
assert is_elementary;
error if Derivative(integral) ne Parent(integral) ! g, Derivative(integral), g;

poly := G ! (g/(x + 1));
assert not IntegrateLogarithmicPolynomial(poly);
