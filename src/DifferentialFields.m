function IsPolyFractionField(F)
    return not ISA(Type(UnderlyingRing(F)), FldFunRat);
end function;


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

    require NumberOfGenerators(F) eq 1 : "Bad format for differential field";

    // This happens when F is a differential field. For some reason it works
    // here, so we don't even need to call AsFraction, can just use numerator
    // and denominator on f
    if ISA(Type(R), FldFunRat) then return R ! f; end if;

    // hopefully don't need to create a homormophism as well?
    // AAAH why is this necessary?? It is only in the case of F(x) that this is
    // necessary
    return RationalFunctionField(BaseRing(R)) ! f;
end intrinsic;


intrinsic IsPolynomial(f :: RngDiffElt) -> BoolElt, RngUPolElt
{
    Return if the input is a polynomial over the first generator of the field.
    If it is, also return its representation as a polynomial.
}
    frac := AsFraction(f);
    if Denominator(frac) ne 1 then return false, frac; end if;
    // If can't coerce poly into Parent(F), also return a homomorphism and
    // include note in report
    return true, UnivariatePolynomial(Numerator(frac));
end intrinsic;


intrinsic ExtendConstantField(F :: RngDiff, C :: Fld) -> RngDiff
{
    Same as ConstantFieldExtension, but works for any well-constructed
    differential field.

    Ideally, this function would be replaced by a generalised version of
    ConstantFieldExtension.
}
    require IsField(F) and NumberOfGenerators(F) eq 1
        : "Bad format for differential field";

    if IsPolyFractionField(F) then
        return ConstantFieldExtension(F, C);
    end if;

    PrevFld := CoefficientRing(F);
    G := ExtendConstantField(PrevFld, C);
    if IsLogarithmic(F) then
        G := TranscendentalLogarithmicExtension(G, G!Derivative(F.1));
    else
        G := TranscendentalExponentialExtension(G, G!Derivative(F.1)/F.1);
    end if;

    return G;
end intrinsic;


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                    LOGARITHMIC DIFFERENTIAL FIELDS                        //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////


intrinsic IsLogarithmic(F :: RngDiff) -> BoolElt
{
    Determine if F is of the form G(L) for some elementary function field G
    and elementary function L which is transcendental over G.
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
{
    Give an ordered sequence of all of the derivatives of the logarithmic
    generators of F.
}
    logarithms := [F|];
    while not IsPolyFractionField(F) do
        if IsLogarithmic(F) then
            Append(~logarithms, F.1);
        end if;
        F := CoefficientRing(F);
    end while;
    Reverse(~logarithms);
    return logarithms;
end intrinsic;


intrinsic IsTranscendentalLogarithm(new :: RngDiffElt, logarithms :: SeqEnum) -> SeqEnum
{
    Given the derivative of a new logarithm over a differential field, use the
    Risch Structure Theorem to check if the new logarithm is transcendental. If
    it is, return the empty sequence. If not, return the product combination as
    a list of < factor, non-zero power > pairs in the differential field equal
    to the new argument.

    Assume that logarithms is an algebraically independent set over
    Universe(logarithms) and that each element of logarithms is non-constant.
}
    F := Universe(logarithms);

    require F eq Parent(new) : "New logarithm does not have a derivative in \
            the same field as the other logarithms";
    require ISA(Type(F), RngDiff) and IsField(F)
        : "logarithms do not come from a differential field";
    require NumberOfGenerators(F) eq 1 : "Bad format for differential field";

    // TODO construct the Z-module with 1 and all of the elementary generators
    // of F as a basis. Use Risch to set up a linear system for the new
    // logarithm, and that there is no solution with a positive coefficient for
    // the term corresponding to new and non-negative coefficients elsewhere.
    for log in logarithms do
        if Derivative(log) eq new then
            return [ <log, 1 > ];
        end if;
    end for;

    // logarithm is transcendental
    return [];
end intrinsic;


intrinsic TranscendentalLogarithmicExtension(F :: RngDiff, f :: RngDiffElt:
        logarithms := []) -> RngDiff, SeqEnum, RngDiffElt
{
    Return the differential extension field F(L), where L is logarithmic over
    F with derivative f. Also return all of the logarithms of F(L) and the
    representation of L inside of F(L) (which may be transcendental over F or an
    element of F).
}
    require f ne 0 : "Constants must not be transcendental over Q";
    require Parent(f) cmpeq F : "Argument to be given to the new logarithm \
        does not belong to the given differential field";

    if #logarithms eq 0 then
        logarithms := AllLogarithms(F);
    end if;

    require Universe(logarithms) eq F
        : "universe of logarithms is not the input field";

    prod_comb := IsTranscendentalLogarithm(f, logarithms);
    if #prod_comb gt 0 then
        return F, logarithms, F ! &+[ tm[1]*tm[2] : tm in prod_comb ];
    end if;

    fld := LogarithmicFieldExtension(F, f);
    // little bug fix, courtesy of Nils Bruin. Check it worked with assertion
    fld`Generators := [ fld | c : c in OrderedGenerators(UnderlyingField(fld)) ];
    assert Derivative(fld.1) eq fld!f;
    // all arguments are copied, so we own logarithms.
    ChangeUniverse(~logarithms, fld);
    Append(~logarithms, fld.1);
    return fld, logarithms, fld.1;
end intrinsic;


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                    EXPONENTIAL DIFFERENTIAL FIELDS                        //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////


intrinsic TranscendentalExponentialExtension(F :: RngDiff, f :: RngDiffElt:
        exponentials := []) -> RngDiff, SeqEnum, RngDiffElt
{
    TODO
    idk how this will work yet rip, this is completely filler code
}
    G := ExponentialFieldExtension(F, f);
    ChangeUniverse(~exponentials, G);
    Append(~exponentials, G.1); // dodgy?
    return G, exponentials, G.1;
end intrinsic;
