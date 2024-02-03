intrinsic AsFraction(f :: RngDiffElt) -> FldFunRatElt
{
    Assume the argument is from a field of the form L = F(x) for some
    differntial field F. Return the argument as an element of the rational
    function field F(x).
}
    F := Parent(f);
    R := UnderlyingRing(F);
    
    require IsField(R)
        : "The argument must come from a differential ring that can be coerced \
        into a field.";

    // This happens when F is a differential field. For some reason it works
    // here, so we don't even need to call AsFraction, can just use numerator
    // and denominator on f
    if ISA(Type(R), FldFunRat) then return R ! f; end if;

    // hopefully don't need to create a homormophism as well?
    // AAAH why is this necessary?? It is only in the case of F(x) that this is
    // necessary
    return RationalFunctionField(BaseRing(R)) ! f;
end intrinsic;


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                    LOGARITHMIC DIFFERENTIAL FIELDS                        //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////


intrinsic IsLogarithmic(F :: RngDiff) -> Bool
{
    Let F be a field of the form K(x, M1, ..., Mn). Return if M_n is logarithmic
    over F.
}
    require IsField(F) : "Input must be a differential field";
    require NumberOfGenerators(F) eq 1 : "Bad format for differential field";

    if not ISA(Type(UnderlyingRing(F)), FldFunRat) then return false; end if;
    G := BaseRing(F);

    require NumberOfGenerators(G) eq 1 : "Bad format for differential field";

    // should be true iff Derivative(F.1) in G. Need to ignore coerced value
    inBaseField, _ :=  IsCoercible(G, Derivative(F.1));
    return inBaseField;
end intrinsic;


intrinsic AllLogarithms(F :: RngDiff) -> SeqEnum
{ Give a list of all of the logarithmic generators of F }
    // TODO!
    return [];
end intrinsic;


intrinsic IsTranscendentalLogarithm(new :: RngDiffElt, logarithms :: SeqEnum) -> SeqEnum
{
    Given a potential new logarithm argument to be put over a differential field,
    use the Risch Structure Theorem to check if the new logarithm is
    transcendental. If not, return the product combination in the differetial
    field equal to the new argument.

    Assume that logarithms is an algebraically independent set over its
    universe.
}
    // TODO!
    return [];
end intrinsic;


intrinsic TranscendentalLogarithmicExtension(F :: RngDiff, f :: RngDiffElt:
        logarithms := []) -> RngDiff, SeqEnum
{
    Compute the differential extension field F(L), where L is logarithmic over
    F with derivative f'/f. If L is not transcendental, remove it. Otherwise
    return F(L). Also return all of the logarithms of F(L).
}
    require Parent(f) cmpeq F
        : "Argument to be given to the new logarithm does not belong to the \
        given differential field";
    require Derivative(f) ne 0 : "Argument cannot be constant";

    if #logarithms eq 0 then
        logarithms := AllLogarithms(F);
    end if;

    assert Universe(logarithms) eq F;

    if not IsTranscendentalLogarithm(f, logarithms) then
        return F, logarithms;
    end if;

    fld := LogarithmicFieldExtension(F, Derivative(f)/f);
    // little bug fix, courtesy of Nils Bruin. Should work
    fld`Generators := [ fld | c : c in OrderedGenerators(UnderlyingField(fld)) ];
    assert Derivative(fld.1) eq fld ! (Derivative(f)/f); // just to make sure it worked lol
    // all arguments are copied, so we own logarithms.
    ChangeUniverse(~logarithms, fld);
    Append(~logarithms, f);
    return fld, logarithms;
end intrinsic;
