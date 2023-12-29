function UnsafeRothsteinTrager(f, g)
    K := BaseRing(f);
    PP := PolynomialRing(K, 2);

    // Lift f, g from K[x] to K[x, y]
    a := MultivariatePolynomial(PP, f, 1);
    b := MultivariatePolynomial(PP, g, 1);

    r := UnivariatePolynomial(Resultant(a - PP.2 * Derivative(b, PP.1), b, PP.1));
    F, roots := SplittingField(r: Abs := true, Opt := true);
    G := ChangeRing(PolynomialRing(K), F);

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
    require IsField(BaseRing(num)) and IsField(BaseRing(denom))
        : "inputs must come from a field";
    require Parent(num) eq Parent(denom)
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


intrinsic RationalIntegral(f :: RngDiffElt) -> RngDiffElt
{
    Integrate the given rational function using Hermite's method and
    Rothstein-Trager.

    This function assumes that:
        - Every rational function is always represented such that the numerator
          and denominator have GCD 1, and the denominator is monic.

    All algorithms here are taked from Algorithms for Computer Algebra
    (Geddes et al)
}
    require IsAlgebraicDifferentialField(Parent(f))
        : "Input must be an algebraic differential field";
    // not sure if this is sufficient for Parent(f) to be finite algebraic over
    // Q, need to test
    require Type(BaseRing(ConstantField(Parent(f)))) eq FldRat
        : "Constant field is not a finite extension of Q";

    if f eq 0 then return f; end if;

    F := Parent(f);
    // bit of a hack, shouldn't need to do this in logarithmic or exponential
    // cases, fingers crossed we can just use Eltseq there.
    R := RationalFunctionField(ConstantField(F));
    num := Numerator(R ! f);
    denom := Denominator(R ! f);

    // fast simplification; works assuming gcd(num, denom) = 1
    poly_part, num := Quotrem(num, denom);

    rational_part := elt< R | Integral(poly_part), 1>;
    logarithmic_part := F ! 0;

    for term in SquarefreePartialFractionDecomposition(num/denom) do
        // Hermite reduction step
        tm := term; // tm = <factor, power, numerator>, can't mutate term
        while tm[2] gt 1 do
            c, s, t := XGCD(tm[1], Derivative(tm[1]));
            rational_part +:= elt< R | (-tm[3] * t) / (tm[2] - 1), tm[1]^(tm[2] - 1)>;
            tm[3] *:= s + (Derivative(t) / (tm[2] - 1));
            tm[2] -:= 1;
        end while;

        if (tm[3] eq 0) then continue; end if;
        logs := UnsafeRothsteinTrager(tm[3], tm[1]); // note logs is non-empty
        C := Parent(logs[1][1]);

        // expand constant field of F as needed
        if Type(ConstantField(F)) ne FldNum then // no alg. extensions
            F := ConstantExtensionWithLabels(F, C); // might be trivial
        elif Type(C) eq FldNum then // both ConstantField(F), C have alg. exts.
            F := ConstantExtensionWithLabels(F, Compositum(ConstantField(F), C));
        end if; // last case is C = Q, so nothing to do there

        // add necessary logarithmic extensions
        for log in logs do // log is <constant, arg> pair
            F := LogarithmicExtensionWithLabels(F, log[2]); // F.1 is new log
            logarithmic_part := (F ! logarithmic_part) + (F ! log[1])*F.1;
        end for;

    end for;
    return logarithmic_part + (F ! rational_part);
end intrinsic;
