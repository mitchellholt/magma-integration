function UnsafeRothsteinTrager(f, g: Label := "")
    K := BaseRing(f);
    PP := PolynomialRing(K, 2);

    // Lift f, g from K[x] to K[x, y]
    a := MultivariatePolynomial(PP, f, 1);
    b := MultivariatePolynomial(PP, g, 1);

    r := UnivariatePolynomial(Resultant(a - PP.2 * Derivative(b, PP.1), b, PP.1));
    printf "ROTH num: %o, denom %o, res: %o", f, g, r;
    F, roots := SplittingField(r: Abs := true, Opt := true);
    G := ChangeRing(PolynomialRing(K), F);

    if #Label gt 0 then AssignNames(~G, [Label]); end if; // sensible printing

    return [<c, GCD((G ! f) - c * (G !(Derivative(g))), (G ! g))> : c in roots];
end function;


intrinsic RothsteinTrager(num :: RngUPolElt, denom :: RngUPolElt) -> SeqEnum
{
    Perform the Rothstein-Trager algorithm on the numerate, denominator input.
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
    require LeadingCoefficient(denom) eq 1: "Argument 2 must be monic";
    require IsSquarefree(denom): "Argument 2 must be squarefree";

    return UnsafeRothsteinTrager(num, denom);
end intrinsic;


function ConstantExtensionWithLabels(F, K)
    G, hm := ConstantFieldExtension(F, K);
    AssignNames(~G, [Sprint(F.1)]);
    return G, hm;
end function;


function LogarithmicExtensionWithLabels(F, logarithm_arg)
end function;


intrinsic RationalIntegral(f :: RngDiffElt) -> RngDiffElt, SeqEnum
{
    Integrate the given rational function using Hermite's method and
    Rothstein-Trager. Return the integral and the arguments to every logarithm
    used (for naming purposes).

    This function assumes that:
        - Every rational function is always represented such that the numerator
          and denominator have GCD 1, and the denominator is monic.

    All algorithms here are taked from Algorithms for Computer Algebra
    (Geddes et al)
}
    require IsAlgebraicDifferentialField(Parent(f))
        : "Input must be an algebraic differential field";

    F := Parent(f);

    require Type(BaseRing(ConstantField(F))) eq FldRat
        : "Constant field is not a finite extension of Q";

    if f eq 0 then return f; end if;

    // bit of a hack, shouldn't need to do this in logarithmic or exponential
    // cases, fingers crossed we can just use Eltseq there. Note that R always
    // has a different variable name to F, this is really annoying
    R := RationalFunctionField(ConstantField(F));
    num := Numerator(R ! f);
    denom := Denominator(R ! f);

    // fast simplification; works assuming gcd(num, denom) = 1
    poly_part, num := Quotrem(num, denom);

    rational_part := elt< R | Integral(poly_part), 1>;
    all_logs := [];

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

        if (tm[3] eq 0) then continue; end if;
        logs := UnsafeRothsteinTrager(tm[3], tm[1]: Label := Sprint(F.1));
        C := Parent(logs[1][1]); // note logs is non-empty

        // expand constant field of F as needed
        if Type(ConstantField(F)) ne FldNum then // no alg. extensions
            F := ConstantExtensionWithLabels(F, C); // might be trivial
        elif Type(C) eq FldNum then // both ConstantField(F), C have alg. exts.
            F := ConstantExtensionWithLabels(F, Compositum(ConstantField(F), C));
        end if; // last case is C = Q, so nothing to do there

        // add logs to list for now
        all_logs cat:= logs;
    end for;

    if #all_logs eq 0 then return F ! rational_part, all_logs; end if;

    P := PolynomialRing(F, #all_logs);
    log_derivs := [Derivative(F ! l[2])/(F ! l[2]) : l in all_logs];
    L := DifferentialFieldExtension(ChangeUniverse(log_derivs, P));

    return (L ! rational_part) + &+[L.i * (L ! all_logs[i][1]) : i in [1 .. #all_logs]],
        [l[2] : l in all_logs];
end intrinsic;


intrinsic ReadableRationalIntegral(int :: RngDiffElt, logs :: SeqEnum) -> MonStgElt
{ Return a readable string representation of a rational int. }
    if #logs eq 0 then return Sprint(int); end if;
    L := Parent(int);
    K := ConstantField(L);
    if Type(K) eq FldNum then
        AssignNames(~K, ["a"]);
        AssignNames(~L, [Sprintf("log(%o)", arg) : arg in logs]);
        return Sprintf("%o where a has minimal polynomial %o",
                int, DefiningPolynomial(K));
    else
        AssignNames(~L, [Sprintf("log(%o)", arg) : arg in logs]);
        return Sprint(int);
    end if;
end intrinsic
