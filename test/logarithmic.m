F<x> := RationalDifferentialField(RationalField());

// Polynomials
G<g> := LogarithmicExtension(F, 1/x);

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
assert Derivative(integral) eq Parent(integral)!h;

// integrate 1/log(x)
h := G!(1/g);
elementary, integarl := LogarithmicIntegral(h);
assert not elementary;

// integrate log(log(x))
H := LogarithmicExtension(G, G!(1/(x*g)));
elementary, integral := LogarithmicIntegral(H.1);
assert not elementary;

// integrate log(x)^2/x^3
h := G!(g^2/x^3);
elementary, integral := LogarithmicIntegral(h);
assert elementary;
// For whatever reason, the signs are incorrect on all coeffs of the polynomial
// (in log(x)) EXCEPT the leading one?
assert Derivative(integral) eq Parent(integral)!h;

// Geddes example 12.11
A<a> := LogarithmicExtension(F, F!(1/(x + 1/2)));
B<b> := LogarithmicExtension(A, A!(1/x));
fn := (((1/2)*a - x)/((x + 1/2)^2 * a^2) + 4/x)*b^2
    + (((x^2 + x + 1)*a + x^2 - 1)/((x + 1/2)^2) + 2/((x + 1/2)*a) + 4/x)*b
    + ((x - 1/x)*a)/(x + 1/2) + 1/((x + 1/2)*a) + (1/2)/(x*(x + 1/2))
    + 1/(x + 1/2);

// actual answer
C<c>, logs := LogarithmicExtension(B, B!(1/(B!(x + 1/2)*a)));
assert #logs eq 3;
actual_integral := 4/3*b^3
    + (x/((x + 1/2)*a) + 2)*b^2
    + (((x^2 - 1)*a)/(x + 1/2) + 1)*b
    + c;
error if B!Derivative(C!actual_integral) ne B!fn,
      "integrand or actual integral is incorrect";

elementary, integral := LogarithmicIntegral(B!fn);
assert elementary; // fails
assert Derivative(integral) eq Parent(integral)!fn;
