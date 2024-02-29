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
    denom_derivative := P!denom_derivative; // idk why we don't have equality by default

    PP<y, z> := PolynomialRing(CoefficientRing(P), 2);

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
    Q := ChangeRing(P, CoefficientRing(G));
    inclusion := hom< Q -> G | G.1 >;

    return true,
        [
            < c, inclusion(GCD(Q!num - c * Q!denom_derivative, Q!denom)) >
            : c in roots
        ];
end intrinsic;

intrinsic IntegrateLogarithmicPolynomial(f :: RngDiffElt: all_logarithms := [])
    -> BoolElt, RngDiffElt, SeqEnum
{
    In K(x, M1, ..., Mn), assert that Mn is logarithmic and that f is a
    polynomial in K(x, M1, ..., M(n-1))[Mn]. If f has an elementary integral,
    return true, an integral, and a list of all the logarithms appearing in the
    parent differential field of the solution. Otherwise, return false.
}
    // See section 5.1 of report for derivation
    F := Parent(f);

    require IsLogarithmic(F) : "The last generator is not logarithmic";

    PrevFld := CoefficientRing(F);

    is_poly, poly := IsPolynomial(f);
    require is_poly : "Argument is not a polynomial";

    // find all the logarithms, if no list has been provided
    if #all_logarithms eq 0 then
        all_logarithms := AllLogarithms(F);
    end if;

    prev_logarithms := all_logarithms[[ 1 .. #all_logarithms - 1]];

    if poly eq 0 then return true, F ! poly, all_logarithms; end if;
    integral := F ! 0; // placeholder value
    deg := Degree(poly);
    if deg eq 0 then
        // special case - can just integrate in the previous field
        return ElementaryIntegral(PrevFld!f);
    end if;
    // REMEMBER 1 INDEXING HERE!!!!
    ps := Coefficients(poly);
    ChangeUniverse(~ps, F);
    qs := [ CoefficientRing(F) | 0 : _ in [ 0 .. deg + 1 ] ];

    // calculate the two leading terms
    is_elementary, integral, logs := ElementaryIntegral(
             PrevFld ! ps[deg + 1]: all_logarithms := prev_logarithms);

    if not is_elementary then
        return false, integral, all_logarithms;
    elif #logs gt #all_logarithms then
        return false, integral, all_logarithms;
    elif #logs eq #all_logarithms and Derivative(F.1) ne Derivative(logs[#logs]) then
        return false, integral, all_logarithms;
    end if;

    is_poly, poly := IsPolynomial(F ! integral); // this had better coerce correctly
    if not IsPolynomial(f) or Degree(poly) gt 1 then
        return false, integral, all_logarithms;
    end if;
    qs[deg + 2] := Coefficient(poly, 1)/(deg + 1);
    if Derivative(qs[deg + 2]) ne 0 then
        return false, integral, all_logarithms;
    end if;
    qs[deg + 1] := Coefficient(poly, 0);

    // calculate the remaining non-zero terms
    i := deg - 1; // the index for q_i is i + 1 rip
    while i gt 0 do
        is_elementary, integral, logs := ElementaryIntegral(
                PrevFld ! (ps[i + 1] + (i + 1)*qs[i + 2]*Derivative(F.1)):
                all_logarithms := prev_logarithms);
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
                PrevFld ! (ps[1] + qs[2]*Derivative(F.1)):
                all_logarithms := prev_logarithms);
    if not is_elementary then
        return false, integral, all_logarithms;
    end if;
    integral *:= -1;

    G := Parent(integral);
    if not IsCoercible(G, F.1) then // this could make some errors
        G, logs, rep := LogarithmicExtension(
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
{
    Integrate the given logarithmic function. Return the integral and all of the
    logarithms used.
}

    F := Parent(f);

    require IsField(F) and NumberOfGenerators(F) eq 1
        : "Bad format for differential field";

    if #all_logarithms eq 0 then
        all_logarithms := AllLogarithms(F);
    end if;

    if f eq 0
        then return true, f, all_logarithms;
    end if;

    plyfrac := AsFraction(f);
    num := UnivariatePolynomial(Numerator(plyfrac));
    denom := UnivariatePolynomial(Denominator(plyfrac));
    R := Parent(num/denom);
    injection := hom< R -> F | F.1 >;
    poly_part, num := Quotrem(num, denom);
    elementary, integral, all_logarithms := IntegrateLogarithmicPolynomial(
            injection(poly_part): all_logarithms := all_logarithms);
    
    if not elementary then
        return false, f, all_logarithms;
    end if;

    if num eq 0 then
        return true, integral, all_logarithms;
    end if;

    injection := hom< R -> Parent(integral) | F.1 >;
    F := Parent(integral);

    for term in SquarefreePartialFractionDecomposition(num/denom) do
        tm := term;
        while tm[2] gt 1 do
            _, s, t := XGCD(tm[1], Derivative(tm[1]));
            s *:= tm[3];
            t *:= tm[3];
            integral +:= injection(elt< R | -t/(tm[2] - 1), tm[1]^(tm[2] - 1)>);
            tm[3] := s + (Derivative(t) / (tm[2] - 1));
            tm[2] -:= 1;
        end while;

        if (tm[3] eq 0) then
            continue;
        end if; // integral is rational

        elementary, new_logs := LogarithmicRothsteinTrager(F, tm[3], tm[1]);
        if not elementary then
            return false, f, all_logarithms;
        end if;

        C := Parent(new_logs[1][1]);

        K := ConstantField(F);
        if Type(K) ne FldNum then
            F := ExtendConstantField(F, C);
            ChangeUniverse(~all_logarithms, F);
        elif Type(C) eq FldNum then
            F := ExtendConstantField(F, Compositum(K, C));
            ChangeUniverse(~all_logarithms, F);
        end if;

        for log in new_logs do
            F, all_logarithms, log_rep := LogarithmicExtension(
                    F,
                    F!(Derivative(log[2])/log[2]):
                    logarithms := all_logarithms);
            integral := F!integral + (F!log[1] * log_rep);
        end for;
    end for;

    return true, integral, all_logarithms;
end intrinsic;
