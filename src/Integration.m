intrinsic ElementaryIntegral(f :: RngDiffElt: logarithms := []) -> Bool, RngDiffElt, SeqEnum
{
    Return if the given elementary function has an elementary integral. If it
    does, return an integral and a list of all the logarithms needed to generate
    the smallest extension of the field that the input comes from.
}
    // TODO add exponential case
    F := Parent(f);

    if IsLogarithmic(F) then
        return LogarithmicIntegral(f, logarithms);
    else
        integral, logs := RationalIntegral(f);
        return true, integral, logs;
    end if;
end intrinsic;
