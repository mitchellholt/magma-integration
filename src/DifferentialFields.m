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
    if Denominator(f) ne 1 then return false, frac; end if;
    // If can't coerce poly into Parent(F), also return a homomorphism and
    // include note in report
    return true, UnivariatePolynomial(Numerator(f));
end intrinsic;


intrinsic ExtendConstantField(F :: RngDiff, C :: Fld) -> RngDiff, Map
{
    Same as ConstantFieldExtension, but works for any well-constructed
    differential field.

    NOTE: THE CURRENT IMPLEMENTATION MAY BE VERY EXPENSIVE BECAUSE OF ALL THE
    CLOSURES. Ideally, this function would be replaced by an efficient and
    generalised version of ConstantFieldExtension.
}
    require IsField(F) and NumberOfGenerators(F) eq 1
        : "Bad format for differential field";

    if IsPolyFractionField(F) then
        return ConstantFieldExtension(F, C);
    end if;

    PrevFld := CoefficientRing(F);
    G, inj := ExtendConstantField(PrevFld, C);
    FNew := G;
    if IsLogarithmic(F) then
        FNew := TranscendentalLogarithmicExtension(G,
                inj(PrevFld ! Denominator(Derivative(F.1))));
    else
        FNew := TranscendentalExponentialExtension(G, G!Derivative(F.1)/F.1);
    end if;

    return FNew, hom< F -> FNew | inj, FNew.1 >;
end intrinsic;


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                    LOGARITHMIC DIFFERENTIAL FIELDS                        //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////


intrinsic IsLogarithmic(F :: RngDiff) -> BoolElt
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
{ Give an ordered sequence of all of the logarithmic generators of F. }
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
    Given a potential new logarithm argument to be put over a differential field,
    use the Risch Structure Theorem to check if the new logarithm is
    transcendental. If it is, return the empty sequence. If not, return the
    product combination as a list of < factor, non-zero power > pairs in the
    differetial field equal to the new argument.

    Assume that [log(f) : f in logarithms] is an algebraically independent set
    over Universe(logarithms). Also assume that each f in logarithms is
    non-constant.
}
    F := Universe(logarithms);
    require ISA(Type(F), RngDiff) and IsField(F)
        : "logarithms do not come from a differential field";
    // TODO construct the Z-module with 1 and all of the elementary generators
    // of F as a basis. Use Risch to set up a linear system for the new
    // logarithm, and that there is no solution with a positive coefficient for
    // the term corresponding to new and non-negative coefficients elsewhere.
    if new in logarithms then
        return [ F | < new, 1 > ];
    else
        return [F|];
    end if;
end intrinsic;


intrinsic TranscendentalLogarithmicExtension(F :: RngDiff, f :: RngDiffElt:
        logarithms := []) -> RngDiff, SeqEnum, RngDiffElt
{
    Compute the differential extension field F(L), where L is logarithmic over
    F with derivative f'/f. If L is not transcendental, remove it. Otherwise
    return F(L). Also return all of the logarithms of F(L) and the
    representation of L inside of F(L) (which may be a transcendental over F or
    an element of F)
}
    require Derivative(f) ne 0 : "Constants must not be transcendental over Q";
    require Parent(f) cmpeq F
        : "Argument to be given to the new logarithm does not belong to the \
        given differential field";

    if #logarithms eq 0 then
        logarithms := AllLogarithms(F);
    end if;

    require Universe(logarithms) eq F
        : "universe of logarithms is not the input field";

    prod_comb := IsTranscendentalLogarithm(f, logarithms);
    if #prod_comb gt 0 then
        return F, logarithms, F ! &*[ tm[1]^tm[2] : tm in prod_comb ];
    end if;

    fld := LogarithmicFieldExtension(F, Derivative(f)/f);
    // little bug fix, courtesy of Nils Bruin. Check it worked with assertion
    fld`Generators := [ fld | c : c in OrderedGenerators(UnderlyingField(fld)) ];
    assert Derivative(fld.1) eq fld ! (Derivative(f)/f);
    // all arguments are copied, so we own logarithms.
    ChangeUniverse(~logarithms, fld);
    Append(~logarithms, f);
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
