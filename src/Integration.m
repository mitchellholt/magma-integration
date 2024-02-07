intrinsic ElementaryIntegral(f :: RngDiffElt: all_logarithms := []) -> BoolElt, RngDiffElt, SeqEnum
{
    Return if the given elementary function has an elementary integral. If it
    does, return an integral and a list of all the logarithms needed to generate
    the smallest extension of the field that the input comes from.
}
    // TODO add exponential case
    F := Parent(f);

    require IsField(F) and NumberOfGenerators(F) eq 1
        : "Bad format for differential field";

    if IsLogarithmic(F) then
        return LogarithmicIntegral(f: all_logarithms := all_logarithms);
    else
        integral, logs := RationalIntegral(f);
        return true, integral, logs;
    end if;
end intrinsic;


intrinsic NameField(~F :: RngDiff: FirstExtName := "x", AlgNumName := "a")
{
    Using sensible defaults, name the transcendental generators of F.

    FirstExtName is the name to be assigned to the (unique) transcendental over
    the constant field which has derivative 1.

    AlgNumName is the name of the algeraic generator of the constant field (if
    any).
}
    if IsPolyFractionField(F) then
        AssignNames(~F, [ FirstExtName ]);
        R := RationalFunctionField(BaseRing(UnderlyingField(F)));
        AssignNames(~R, [ FirstExtName ]); // cringe edge case strikes again
        K := ConstantField(F);
        AssignNames(~K, [ AlgNumName ]);
    else
        G := CoefficientRing(F);
        NameField(~G);
        if IsLogarithmic(F) then
            // if logs are independent this doesn't work. TODO keep taking
            // coefficient rings until G!Denominator(AsFraction(G!Derivative(F.1)))
            // is non-constant
            AssignNames(~F, [
                Sprintf("log(%o)", G!Denominator(AsFraction(G!Derivative(F.1))))
            ]);
        else
            // Exponential case. This is possibly expensive
            // TODO figure out a better way I guess. Note that the user
            // DEFINITELY knows the name of this exponential, so could just cop
            // out and get them to input?
            integrable, itg := ElementaryIntegral(Derivative(F.1)/F.1);
            assert integrable;
            AssignNames(~F, [ Sprintf("exp(%o)", itg) ]);
        end if;
    end if;
end intrinsic;
