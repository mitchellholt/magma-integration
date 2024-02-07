intrinsic LogarithmicRothsteinTrager(
        F :: RngDiff,
        num :: RngUPolElt,
        denom :: RngUPolElt) -> BoolElt, SeqEnum
{
    Use the logarithmic Rothstein-Trager theorem to find if inclusion(num/denom)
    has an elementary integral. If it does, return true and an elementary
    integral (represented as a sequence of < coefficient, logarithm > pairs).
    Otherwise, return false.
}
    P := Parent(num);

    require IsLogarithmic(F)
        : "Inputs do not come from a logarithmic differential field";
    require P eq Parent(denom) and denom ne 0
        : "Bad inputs";
    require GCD(num, denom) eq 1
            and Degree(num) lt Degree(denom)
            and LeadingCoefficient(denom) eq 1
        : "Inputs do not satisfy the assumptions for Rothstein-Trager";

    inclusion := hom< P -> F | F.1 >;
    _, denom_derivative := IsPolynomial(Derivative(inclusion(denom)));

    PP := PolynomialRing(CoefficientRing(P), 2);

    a := MultivariatePolynomial(PP, num, 1);
    b := MultivariatePolynomial(PP, denom, 1);
    b_derivative := MultivariatePolynomial(PP, denom_derivative, 1);
    r := UnivariatePolynomial(Resultant(a - PP.2 * b_derivative, b, PP.1));

    // Integral is elementary iff r/lc(r) has constant coefficients
    r := r/LeadingCoefficient(r);
    coeffs := Coefficients(r);
    K := ConstantField(F);
    for coeff in coeffs do
        if not IsCoercible(K, coeff) then
            return false, [];
        end if;
    end for;
    ChangeUniverse(~coeffs, K);
    C, roots := SplittingField(Polynomial(coeffs): Abs := true, Opt := true);

    G := ExtendConstantField(F, C);
    Q := ChangeRing(P, G);

    return true, [ < c, GCD(Q!num - c * Q!denom_derivative, Q!denom) > : c in roots ];
end intrinsic;

intrinsic IntegrateLogarithmicPolynomial(f :: RngDiffElt: all_logarithms := [])
    -> BoolElt, RngDiffElt, SeqEnum
{
    In K(x, M1, ..., Mn), assert that Mn is logarithmic and that f is a
    polynomial in K(x, M1, ..., M(n-1))[Mn]. If f has an elementary integral,
    return true, an integral, and a list of all the logarithms appearing in the
    parent differential field of the solution. Otherwise, return false.
}
    // See working from 06/02/2024 in notebook for derivation of algorithm
    // TODO supply all_logarithms to ElementaryIntegral to speed up
    F := Parent(f);

    require IsLogarithmic(F) : "The last generator is not logarithmic";

    PrevFld := CoefficientRing(F);

    is_poly, poly := IsPolynomial(f);
    require is_poly : "Argument is not a polynomial";

    // find all the logarithms, if no list has been provided
    if #all_logarithms eq 0 then
        all_logarithms := AllLogarithms(F);
    end if;

    if poly eq 0 then return true, F ! poly, all_logarithms; end if;
    integral := F ! 0; // placeholder value
    deg := Degree(poly);
    // REMEMBER 1 INDEXING HERE!!!!
    ps := Coefficients(poly);
    ChangeUniverse(~ps, F);
    qs := [ CoefficientRing(F) | 0 : _ in [ 0 .. deg + 1 ] ];

    // calculate the two leading terms
    is_elementary, integral, logs := ElementaryIntegral(PrevFld ! ps[deg + 1]);

    if not is_elementary then
        return false, integral, all_logarithms;
    elif #logs gt #all_logarithms then
        return false, integral, all_logarithms;
    elif #logs eq #all_logarithms and Derivative(F.1) ne Derivative(logs[#logs]) then
        return false, integral, all_logarithms;
    end if;

    is_poly, poly := IsPolynomial(F ! integral); // this had better be coercible
    if not IsPolynomial(f) or Degree(poly) gt 1 then
        return false, integral, all_logarithms;
    end if;
    qs[deg + 2] := -Coefficient(poly, 1)/(deg + 1);
    qs[deg + 1] := Coefficient(poly, 0);

    // calculate the remaining non-zero terms
    i := deg - 1; // the index for q_i is i + 1 rip
    while i gt 0 do
        is_elementary, integral, logs := ElementaryIntegral(
                PrevFld ! (ps[i + 1] + (i + 1)*qs[i + 2]*Derivative(F.1)));
        if not is_elementary then
            return false, integral, all_logarithms;
        elif #logs gt #all_logarithms then
            return false, integral, all_logarithms;
        elif #logs eq #all_logarithms and Universe(logs) ! F.1 notin logs then
            return false, integral, all_logarithms;
        end if;

        is_poly, poly := IsPolynomial(F ! integral);
        if not is_poly(f) or Degree(poly) gt 1 then
            return false, integral, all_logarithms;
        end if;
        qs[i + 2] +:= -Coefficient(poly, 1)/(i + 1);
        qs[i + 1] := Coefficient(poly, 0);
        i -:= 1;
    end while;

    is_elementary, integral, logs := ElementaryIntegral(
                PrevFld ! (ps[1] + (1)*qs[i + 2]*Derivative(F.1)));
    if not is_elementary then
        return false, integral, all_logarithms;
    end if;
    integral *:= -1;

    G := Parent(integral);
    if not IsCoercible(G, F.1) then
        G, logs, rep := TranscendentalLogarithmicExtension(
            G, G ! Derivative(F.1): logarithms := logs);
        // TODO implement this
        error if rep ne G.1,
            "Not implemented. TODO need F.1 to be the transcendental stored";
    end if;

    ChangeUniverse(~qs, G);
    for i in [ 0 .. deg + 1 ] do
        integral +:= qs[i + 1] * G.1^i;
    end for;

    return true, integral, logs;
end intrinsic;


intrinsic LogarithmicIntegral(f :: RngDiffElt: all_logarithms := []) -> BoolElt, RngDiffElt, SeqEnum
{ Integrate the given logarithmic function }
    // TODO hermite and Rothstein-Trager
    return IntegrateLogarithmicPolynomial(f: all_logarithms := all_logarithms);
end intrinsic;
