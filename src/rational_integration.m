function UnsafeRothsteinTrager(f, g: dbg := false)
    K := BaseRing(f);
    PP := PolynomialRing(K, 2);

    // Lift f, g from K[x] to K[x, y]
    a := MultivariatePolynomial(PP, f, 1);
    b := MultivariatePolynomial(PP, g, 1);

    r := UnivariatePolynomial(Resultant(a - PP.2 * Derivative(b, PP.1), b, PP.1));
    if dbg then
        printf "Res is %o", r;
    end if;
    F, roots := SplittingField(r: Abs := true, Opt := true);
    if dbg then
        printf "Splitting field defined by %o", DefiningPolynomial(F);
    end if;
    G := ChangeRing(PolynomialRing(K), F);

    return [<c, GCD((G ! f) - c * (G !(Derivative(g))), (G ! g))> : c in roots];
end function;


intrinsic RothsteinTrager(num :: RngUPolElt, denom :: RngUPolElt) -> SeqEnum
{
    Perform the Rothstein-Trager algorithm on the numerator, denominator input.
    Return a list of <constant, logarithm argument> pairs.
}
    // verify that the input is well-formed and that the conditions of the
    // theorem are met.
    require denom ne 0 : "Denominator is the zero polynomial";
    require num ne 0 : "Input must be non-zero";
    require IsField(BaseRing(num)) and Parent(num) cmpeq Parent(denom)
        : "inputs must come from the same field";
    require Degree(num) lt Degree(denom)
        : "Degree of argument 1 must be less than degree argument 2";
    require GCD(num, denom) eq 1: "Polynomials must be coprime";
    require LeadingCoefficient(denom) eq 1: "Denominator must be monic";
    require IsSquarefree(denom): "Denominator must be squarefree";

    return UnsafeRothsteinTrager(num, denom);
end intrinsic;


intrinsic RationalIntegral(f :: RngDiffElt) -> RngDiffElt, SeqEnum
{
    Integrate the given rational function using Hermite's method and
    Rothstein-Trager. Return the integral and all of the logarithms used.

    All algorithms here are taked from Algorithms for Computer Algebra
    (Geddes et al)
}
    F := Parent(f);
    plyfrac := AsFraction(f);
    R := Parent(plyfrac);

    require Rank(R) eq 1 and CoefficientRing(R) eq ConstantField(F)
        : "Argument is not a rational function"; // not sure if this will work?

    if f eq 0
        then return f, [];
    end if;

    num := Numerator(plyfrac);
    denom := Denominator(plyfrac);

    // fast simplification; works assuming gcd(num, denom) = 1
    poly_part, num := Quotrem(num, denom);

    rational_part := R!Integral(poly_part);
    log_part := F!0;

    all_logarithms := [F|]; // list of all logarithms used. Universe is always F

    for term in SquarefreePartialFractionDecomposition(num/denom) do
        // Hermite reduction step
        tm := term; // tm = <factor, power, numerator>, can't mutate term
        while tm[2] gt 1 do
            _, s, t := XGCD(tm[1], Derivative(tm[1]));
            s *:= tm[3];
            t *:= tm[3];
            rational_part +:= elt< R | -t/(tm[2] - 1), tm[1]^(tm[2] - 1)>;
            tm[3] := s + (Derivative(t) / (tm[2] - 1));
            tm[2] -:= 1;
        end while;

        if (tm[3] eq 0) then
            continue;
        end if; // integral is rational

        logs := UnsafeRothsteinTrager(tm[3], tm[1]);
        C := Parent(logs[1][1]); // note logs is always non-empty

        K := ConstantField(F);
        if Type(K) ne FldNum then // no algebraic extensions
            F := ExtendConstantField(F, C); // might be trivial
            ChangeUniverse(~all_logarithms, F);
        elif Type(C) eq FldNum then // both K, C have alg. exts.
            F := ExtendConstantField(F, Compositum(K, C));
            ChangeUniverse(~all_logarithms, F);
        end if; // last case is C = K = Q, so nothing to do there

        for log in logs do // log is < constant, log argument > pair
            F, all_logarithms, log_rep := TranscendentalLogarithmicExtension(
                    F,
                    F!(Derivative(log[2])/log[2]):
                    logarithms := all_logarithms);
            log_part := F!log_part + (F!log[1] * log_rep);
        end for;
    end for;

    return F!rational_part + log_part, all_logarithms;
end intrinsic;
