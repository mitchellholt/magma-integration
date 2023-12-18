function UnsafeRothsteinTrager(f, g)
    K := BaseRing(f);
    PP<y, z> := PolynomialRing(K, 2);

    // Lift f, g from K[x] to K[x, y]
    a := MultivariatePolynomial(PP, f, 1);
    b := MultivariatePolynomial(PP, g, 1);

    r := UnivariatePolynomial(Resultant(a - z * Derivative(b, y), b, y));
    print r;
    F, roots := SplittingField(r: Abs := true, Opt := true); // can we name the algebraic extensions?
    // Would be nice if x was replaced with the label of the indeterminant
    // in the input
    P<x>, hom := ChangeRing(PolynomialRing(K), F);

    return [<c, GCD(hom(f) - c * hom(Derivative(g)), hom(g))> : c in roots], F;
end function;


intrinsic RothsteinTrager(num :: RngUPolElt, denom :: RngUPolElt) -> SeqEnum, FldAlg
{
    Perform the Rothstein-Trager algorithm on the numerate, denominator input.
    Return a list of <constant, logarithm argument> pairs.
}
    // verify that the conditions of the theorem are met.
    require num ne 0 : "Input is the zero polynomial";
    require Type(num) eq Type(denom): "Polynomials are not from the same ring";
    require Type(num) eq RngUPolElt: "Polynomials are not univariate";
    require Degree(num) lt Degree(denom): "Degree of argument 1 must be less than degree argument 2";
    require GCD(num, denom) eq 1: "Polynomials must be coprime";
    require LeadingCoefficient(denom) eq 1: "Argument 2 must be monic";
    require IsSquarefree(denom): "Argument 2 must be squarefree";

    return UnsafeRothsteinTrager(num, denom);
end intrinsic;


intrinsic RationalIntegral(f :: FldFunRatUElt) -> FldFunRatUElt, SeqEnum
{
    Integrate the given rational function. Return the part of the integral in
    the function field (up to some algebraic extensions of the constant field),
    a list of <constant, logarithm argument> pairs and the new constant field.
}
    K := BaseRing(Denominator(f)); // constant field
    F := FieldOfFractions(PolynomialRing(K));
    if f eq 0 then
        return F ! 0;
    end if;

    // write f as a + p/q, deg p < deg q, (p, q) = 1, q monic.
    p := Numerator(f); // numerator of rational part of input
    q := Denominator(f); // denominator of rational part of input
    a, r := Quotrem(p, q); // a is polynomial part of input
    g := GCD(r, q) * LeadingCoefficient(q); // note the GCD is monic
    p := r / g;
    q := q / g; // monic

    rational_part := elt< F | Integral(a), 1>; // rational part of integral f
    sfp := SquarefreePartialFractionDecomposition(p/q); // [<factor, power, numerator>]
    // partial fractions trick
    log_part := [];
    for term in sfp do
        tm := term;
        while tm[2] gt 1 do
            c, s, t := XGCD(tm[1], Derivative(tm[1]));
            rational_part +:= elt< F | (-tm[3] * t) / (tm[2] - 1), tm[1]^(tm[2] - 1)>;
            tm[3] *:= s + (Derivative(t) / (tm[2] - 1));
            tm[2] -:= 1;
        end while;
        log_part cat:= UnsafeRothsteinTrager(tm[3], tm[1]);
    end for;

    return rational_part, log_part;
end intrinsic;
