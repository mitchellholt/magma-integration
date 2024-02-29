intrinsic IsPolyFractionField(F :: RngDiff) -> BoolElt
{ Determine if the input is K(x) for a constant field K }
    return not ISA(Type(UnderlyingRing(F)), FldFunRat);
end intrinsic;


intrinsic AsFraction(f :: RngDiffElt) -> FldFunRatElt
{
    Return the representation of f as a fraction.
}
    F := Parent(f);
    R := UnderlyingRing(F);
    
    require IsField(R) and NumberOfGenerators(F) eq 1
        : "Bad format for differential field";

    // This happens when F is a differential field. For some reason it works
    // here, so we don't even need to call AsFraction, can just use numerator
    // and denominator on f
    if ISA(Type(R), FldFunRat)
        then return R ! f;
    end if;

    // hopefully don't need to create a homormophism as well?
    // would be nice if we could do UnderlyingRing(F)!f here
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
        G := LogarithmicExtension(G, G!Derivative(F.1));
    else
        G := ExponentialExtension(G, G!Derivative(F.1)/F.1);
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

    // Need to check if the degree of the numerator of the derivative of F.1 is
    // zero in the corresponding fraction field.
    frac := AsFraction(Derivative(F.1));
    return Degree(Numerator(frac)) eq 0;
end intrinsic;


intrinsic AllLogarithms(F :: RngDiff) -> SeqEnum
{
    Give an ordered sequence of all of the logarithmic generators of F.
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


intrinsic LogarithmicExtension(F :: RngDiff, f :: RngDiffElt:
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


intrinsic ExponentialExtension(F :: RngDiff, f :: RngDiffElt:
        exponentials := []) -> RngDiff, SeqEnum, RngDiffElt
{
    TODO
    idk how this will work yet rip, this is completely filler code
}
    G := ExponentialFieldExtension(F, f);
    G`Generators := [ G | c : c in OrderedGenerators(UnderlyingField(G)) ];
    assert G!(Derivative(G.1)/(G.1)) eq G!f;
    ChangeUniverse(~exponentials, G);
    Append(~exponentials, G.1); // dodgy?
    return G, exponentials, G.1;
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
            rep := G!Denominator(AsFraction(G!Derivative(F.1)));
            while rep eq 1 do
                G := CoefficientRing(G);
                rep := G!Denominator(AsFraction(G!Derivative(F.1)));
            end while;
            AssignNames(~F, [ Sprintf("log(%o)", rep) ]);
        else
            // Exponential case. This is possibly expensive
            // TODO figure out a better way I guess. Note that the user
            // DEFINITELY knows the name of this exponential, so could just cop
            // out and get them to input?
            error "not implemented";
        end if;
    end if;
end intrinsic;
