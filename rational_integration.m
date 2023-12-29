function UnsafeRothsteinTrager(f, g)
    K := BaseRing(f);
    PP<y, z> := PolynomialRing(K, 2);

    // Lift f, g from K[x] to K[x, y]
    a := MultivariatePolynomial(PP, f, 1);
    b := MultivariatePolynomial(PP, g, 1);

    r := UnivariatePolynomial(Resultant(a - z * Derivative(b, y), b, y));
    F, roots := SplittingField(r: Abs := true, Opt := true); // can we name the algebraic extensions?
    // Would be nice if x was replaced with the label of the indeterminant
    // in the input
    _, hom := ChangeRing(PolynomialRing(K), F);

    return [<c, GCD(hom(f) - c * hom(Derivative(g)), hom(g))> : c in roots], F;
end function;


intrinsic RothsteinTrager(num :: RngUPolElt, denom :: RngUPolElt) -> SeqEnum, FldAlg
{
    Perform the Rothstein-Trager algorithm on the numerate, denominator input.
    Return a list of <constant, logarithm argument> pairs.
}
    // verify that the input is well-formed and that the conditions of the
    // theorem are met.
    require denom ne 0 : "Denominator is the zero polynomial";
    require num ne 0 : "Input is the zero polynomial";
    require IsField(BaseRing(num)) and IsField(BaseRing(denom))
        : "inputs must come from a field";
    require BaseRing(num) eq BaseRing(denom)
        : "Polynomials must come from the same field";
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
    L := LogarithmicFieldExtension(
            F, F ! (Derivative(logarithm_arg) / logarithm_arg));
    AssignNames(~L, [Sprintf("log(%o)", logarithm_arg)]);
    return L;
end function;


intrinsic RationalIntegral(f :: RngDiffElt, F :: RngDiff) -> RngDiffElt, RngDiff, Map
{
    Integrate the given rational function using Hermite's method and then
    Rothstein-Trager for the rational part.

    This function assumes that:
        - Every rational function is always represented such that the numerator
          and denominator have GCD 1, and the denominator is monic.

    All algorithms here are taked from Algorithms for Computer Algebra
    (Geddes et al)
}
    require IsAlgebraicDifferentialField(F)
        : "Input must be an algebraic differential field";
    require f in F : "first input is not a member of the second";
    // not sure if this is sufficient for F to be finite algebraic over Q, need to test
    require Type(BaseRing(ConstantField(F))) eq FldRat
        : "Constant field is not a finite extension of Q";

    if f eq F ! 0 then return f; end if;

    // bit of a hack, shouldn't need to do this in logarithmic or exponential
    // cases, fingers crossed we can just use Eltseq there.
    R := RationalFunctionField(ConstantField(F));
    num := Numerator(R ! f);
    denom := Denominator(R ! f);

    // fast simplification; works assuming gcd(num, denom) = 1
    poly_part, num := Quotrem(num, denom);

    // G will to be final diff field, hm always homomorphism F to (current) G
    G, hm := ConstantExtensionWithLabels(F, ConstantField(F));

    rational_part := elt< R | Integral(poly_part), 1>;
    logarithmic_part := G ! 0;

    for term in SquarefreePartialFractionDecomposition(num/denom) do
        tm := term; // tm = <factor, power, numerator>, can't mutate term
        while tm[2] gt 1 do
            // Hermite reduction step
            c, s, t := XGCD(tm[1], Derivative(tm[1]));
            rational_part +:= elt< R | (-tm[3] * t) / (tm[2] - 1), tm[1]^(tm[2] - 1)>;
            tm[3] *:= s + (Derivative(t) / (tm[2] - 1));
            tm[2] -:= 1;
        end while;

        if (tm[3] eq 0) then continue; end if;

        logs, ConstFld := UnsafeRothsteinTrager(tm[3], tm[1]);

        // expand constant field of G as needed
        if Type(ConstantField(G)) ne FldNum then // no alg. extensions
            G, hm := ConstantExtensionWithLabels(F, ConstFld); // might be trivial
        elif Type(ConstFld) eq FldNum then // both G, ConstFld have alg. exts.
            G, hm := ConstantExtensionWithLabels(
                    F, Compositum(ConstantField(G), ConstFld));
        end if; // last case is ConstFld = Q, so nothing to do there

        // add necessary logarithmic extensions
        for log in logs do // log is <constant, arg> pair
            G := LogarithmicExtensionWithLabels(G, log[2]);
            logarithmic_part := (G ! logarithmic_part) + (G ! log[1])*G.1;
        end for;

    end for;
    return logarithmic_part + (G ! rational_part), G, hm;
end intrinsic;
