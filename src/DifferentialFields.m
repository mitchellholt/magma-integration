intrinsic AsFraction(f :: RngDiffElt) -> FldFunRatElt
{
    Assume the argument is from a field of the form L = F(x) for some
    differential field F. Return the argument as an element of the rational
    function field F(x).
}
    F := Parent(f);
    R := UnderlyingRing(F);
    
    require IsField(R)
        : "The argument must come from a differential ring that can be coerced \
        into a field.";

    return RationalFunctionField(R) ! f;
end intrinsic;


intrinsic TranscendentalLogarithmicExtension(F :: RngDiff, f :: RngDiffElt:
        err := true,
        logarithms := []) -> RngDiff, SeqEnum
{
    Compute the differential extension field F(L), where L is logarithmic over
    F with derivative f'/f. If L is not transcendental, throw a runtime err if
    err, otherwise return F. Also return all of the logarithms of F(L).
}
    require Parent(f) cmpeq F
        : "Argument to be given to the new logarithm does not belong to the \
        given differential field";
    require Derivative(f) ne 0 : "Argument cannot be constant";

    // TODO search for all logarithmic extensions
    // TODO implement Risch stuff.

    fld := LogarithmicFieldExtension(F, Derivative(f)/f);
    // little bug fix, courtesy of Nils Bruin. Should work
    fld`Generators := [ fld | c : c in OrderedGenerators(UnderlyingField(fld)) ];
    assert Derivative(fld.1) eq fld ! (Derivative(f)/f); // just to make sure it worked lol
    // all arguments are copied, so we own logarithms.
    ChangeUniverse(~logarithms, fld);
    Append(~logarithms, f);
    return fld, logarithms;
end intrinsic;
