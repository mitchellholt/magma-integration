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
