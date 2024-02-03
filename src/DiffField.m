declare type MonArg;

declare attributes MonArg:
    ExtensionType, // "exp" or "log". Ideally would use an enum or have MonArg
                   // hiding in C
    Argument;      // The argument (not derivative of the monomial)


intrinsic MonomialArgument(extType :: MonStgElt, arg :: RngDiffElt) -> MonArg
{
    Create a monomial to be used as an extension over the parent of the
    argument. extType must be one of the string literals "exp" or "log".
}
    require extType eq "exp" or extType eq "log"
        : "Bad Extension Type.";
    require IsAlgebraicDifferentialField(Parent(arg))
        : "arg must come from an algebraic differential field";
    require Derivative(arg) ne 0
        : "arg cannot be a constant";
    M := New(MonArg);
    M`ExtensionType := extType;
    M`Argument := arg;
    return M;
end intrinsic;


intrinsic MonomialArg(m :: MonArg) -> RngDiffElt
{ Return the argument of the monomial }
    return m`Argument;
end intrinsic;


intrinsic IsLogarithmic(m :: MonArg) -> BoolElt
{ Return whether m is a logarithmic (or primitive) monomial }
    return m`ExtensionType eq "log";
end intrinsic;


intrinsic IsExponential(m :: MonArg) -> BoolElt
{ Return whether m is an exponential monomial }
    return m`ExtensionType eq "exp";
end intrinsic;


intrinsic ChangeUnderlyingField(m :: MonArg, F :: RngDiff) -> MonArg
{ Change the underlying field the argument to this monomial comes from }
    require IsCoercible(F, m`Argument)
        : "Monomial argument cannot be coerced to this field";
    return MonomialArgument(m`ExtensionType, F ! (m`Argument));
end intrinsic;


intrinsic Print(m :: MonArg)
{ Print m}
    arg := m`Argument;
    if IsLogarithmic(m) then
        printf "log(%o)", arg;
    else
        printf "exp(%o)", arg;
    end if;
end intrinsic;


intrinsic AllTranscendental(to_check :: [MonArg]: known := []) -> Tup
{
    Use the Risch Structure Theorem to check if the given tower of monomials are
    indeed transcendental over their base field.
    Returns the first monomial which is not transcendental and an offending
    linear/ product combination. If no such monomial exists, return the empty
    tuple.
}
    // TODO if there is time
    if #to_check eq 0 then return <>; end if;
    return <>;
end intrinsic;


declare type DiffField[DiffFieldElt];


declare attributes DiffField:
    MonomialTower,          // The monomials in the current differential field.
    ActualRngDiff,          // The underlying representation of this field as an
                            // RngDiff
    UnderlyingRatFuncField; // The underlying rational function field


function UnsafeDiffField(baseField, monomials)
    G := New(DiffField);
    G`MonomialTower := monomials;

    if #monomials gt 0 then
        P := PolynomialRing(baseField, #monomials);
        derivs := [];
        for i in [ 1 .. #monomials ] do
            arg := baseField ! MonomialArg(monomials[i]);
            if IsExponential(monomials[i]) then
                derivs cat:= [ Derivative(arg) * P.i ];
            else
                derivs cat:= [ Derivative(arg) / arg ];
            end if;
        end for;
        
        G`ActualRngDiff := DifferentialFieldExtension(ChangeUniverse(derivs, P));
        G`UnderlyingRatFuncField := FieldOfFractions(P);
    else
        G`ActualRngDiff := baseField;
        G`UnderlyingRatFuncField := RationalFunctionField(ConstantField(baseField));
    end if;
    return G;
end function;


intrinsic DifferentialField(F :: RngDiff) -> DiffField
{ Construct a differential field over F }
    require IsAlgebraicDifferentialField(F)
        : "Base ring must be an algebraic differential field";
    require Type(BaseRing(ConstantField(F))) eq FldRat
        : "Constant field is not a finite extension of Q";
    return UnsafeDiffField(F, []);
end intrinsic;


intrinsic Monomials(F :: DiffField) -> SeqEnum
{ Return the monomials generating this field }
    return F`MonomialTower;
end intrinsic;


intrinsic Generators(F :: DiffField) -> SetEnum
{ Return the generators of the differential field }
    return Generators(F`ActualRngDiff);
end intrinsic;


intrinsic ConstantField(F :: DiffField) -> Fld
{ Return the constant field of F }
    return ConstantField(F`ActualRngDiff);
end intrinsic;


intrinsic BaseField(F :: DiffField) -> Rng
{ Return the base field of F }
    if #(F`MonomialTower) eq 0 then
        return F`ActualRngDiff;
    else
        return BaseField(F`ActualRngDiff);
    end if;
end intrinsic;


intrinsic RationalField(F :: DiffField) -> DiffField
{ Return the underlying rational function field }
    return F`UnderlyingRatFuncField;
end intrinsic;


intrinsic ExtendConstantField(F :: DiffField, C :: Fld) -> DiffField
{ Return a new differential field, with the constant field extended to C }
    G := ConstantFieldExtension(BaseField(F), C); // error checking happens here
    return UnsafeDiffField(G, F`MonomialTower); // shouldn't throw
end intrinsic;


intrinsic MonomialExtension(F :: DiffField, monomials :: [MonArg]:
                      fix_err := false) -> DiffField, Map
{
    Return a new differential field which has the monomial extensions of the
    given differential field as well as the new monomial extensions.

    If fix_err is true, do not error when some new monomial is not
    transcendental. Instead, simply remove the monomial from the sequence.
}
    require forall{ m : m in monomials | Parent(MonomialArg(m)) cmpeq BaseField(F) }
        : "All new monomials must come from the base field  of the given \
        differential field";
    
    trans_check := AllTranscendental(monomials: known := F`MonomialTower);
    if fix_err then
        while #trans_check gt 0 do
            Exclude(~monomials, trans_check[1]);
            trans_check := AllTranscendental(monomials: known := F`MonomialTower);
        end while;
    else
        require #trans_check eq 0
            : Sprintf("MonArg %o is not transcental: %o",
                    trans_check[1], trans_check[2]);
    end if;

    if #monomials eq 0 then return F; end if;

    G := UnsafeDiffField(BaseField(F), F`MonomialTower cat monomials);
    
    // create a homomorphism from the underlying function field of F into that
    // of G. Note that Existing Magma type RngDiff has no analogue of this.
    n := #F`MonomialTower;
    R := F`UnderlyingRatFuncField;
    S := G`UnderlyingRatFuncField;
    if n eq 0 then
        hm := hom< R -> S | S ! (BaseField(F).1) >;
        fn := map< F -> G | a :-> G ! hm(AsFraction(a)) >; // should preserve hom property
        return G, fn;
    else
        hm := hom< R -> S | [ S.i : i in [ 1 .. n ] ] >;
        fn := map< F -> G | a :-> G ! hm(AsFraction(a)) >;
        return G, fn;
    end if;
end intrinsic;


intrinsic Print(F :: DiffField)
{ Print F }
    printf "Differential field with base field\n%o\nand monomial extensions %o",
        F`ActualRngDiff, F`MonomialTower;
end intrinsic;


// y no work so good? Assigns, but does not then accept assigned names as input.
// Moreover, does not allow inline assignment using <>
intrinsic AssignNames(~F :: DiffField, names :: [MonStgElt])
{ Assign names to the generators of the differential field }
    AssignNames(~(F`ActualRngDiff), names);
end intrinsic;


intrinsic '.'(F :: DiffField, i :: RngIntElt) -> DiffFieldElt
{ Return the ith generator of F }
    return F ! (F`ActualRngDiff).i;
end intrinsic;


intrinsic LastGenerator(F :: DiffField) -> DiffFieldElt
{ Return the final generator of F }
    return F.(#Generators(F));
end intrinsic;

intrinsic Subfield(F :: DiffField, i :: RngIntElt) -> DiffField
{
    Let F = K(x, M1, ..., Mi, ..., Mn).
    Return K(x, M1, ..., M(i - 1), M(i + 1), ..., Mn).
}
    require i gt 0 : "Invalid index into the monomials";
    monomials := Monomials(F);
    n := #monomials;
    require i le n : "The differential field deos not have enough monomials";
    return UnsafeDiffField(BaseField(F),
            [ monomials[j] : j in [1 .. n] | j ne i ]);
end intrinsic;


intrinsic Polynomial(f :: DiffFieldElt, i :: RngIntElt) -> RngUPolElt, Map
{
    Let F be the parent of f with F = K(x, M1, ..., Mi, ..., Mn). Attempt to
    write f as a polynomial p in K(x, M1, ..., M(i - 1), M(i + 1), ..., Mn)[Mi].
    If this is possible, return p and the inclusion map from Parent(p) to F.
    Otherwise, throw a runtime error.
}
    F := Parent(f);
    require i gt 0 : "Invalid index into the monomials";
    require i le #Monomials(F)
        : "The differential field deos not have enough monomials";

    frac := AsFraction(f);
    num := Polynomial(Coefficients(Numerator(frac), i));
    den := Polynomial(Coefficients(Denominator(frac), i));
    require Degree(den) eq 0 : "Input is not a polynomial in the last monomial";

    BaseFld := Subfield(F, i);
    P, plyhm := ChangeRing(Parent(num), RationalField(BaseFld));
    R := RationalField(F);
    coeffMap := map< RationalField(BaseFld) -> R | a :-> R!a>;
    inclusion := hom< P -> R | coeffMap, R.i>;
    return plyhm(num/den), map< P -> F | a :-> F ! inclusion(a) >;
end intrinsic;


// not sure if this messes up how equality is implemented under the hood or is
// inconsistent with the existing implementation
intrinsic 'eq'(F :: DiffField, G :: DiffField) -> BoolElt
{ Return if F eq G }
    return F`ActualRngDiff eq G`ActualRngDiff;
end intrinsic;


intrinsic 'cmpeq'(F :: DiffField, G :: DiffField) -> BoolElt
{ Return if F cmpeq G }
    return F`ActualRngDiff cmpeq G`ActualRngDiff;
end intrinsic;


/*
 * Parent: must be the DiffField this elt belongs to, NOT the
 *  DiffField`ActualRngDiff.
 * ActualRngDiffElt: The representation of this object as an element of
 *  the parent's ActualRngDiff.
 */
declare attributes DiffFieldElt:
    Parent,             // must be the DiffField this elt belongs to, NOT the
                        // DiffField`ActualRngDiff.
    ActualRngDiffElt;   // The representation of this object as an element of
                        // the parent's ActualRngDiff.


function CreateElement(F, actualDiffElt)
    // Create the element actualDiffElt inside F
    f := New(DiffFieldElt);
    f`Parent := F;
    f`ActualRngDiffElt := actualDiffElt;
    return f;
end function;


intrinsic IsCoercible(F :: DiffField, x :: .) -> BoolElt, .
{
    Return whether x is coercible into F, and the result if so.
}
    rngDiff := F`ActualRngDiff;
    if Type(x) eq DiffFieldElt then
        if x`Parent cmpeq F then
            return true, x;
        elif IsCoercible(rngDiff, x`ActualRngDiffElt) then
            return true, CreateElement(F, rngDiff ! x`ActualRngDiffElt);
        end if;
    elif IsCoercible(rngDiff, x) then
        return true, CreateElement(F, rngDiff ! x);
    end if;
    return false, "coercion failed";
end intrinsic;


intrinsic '!'(F :: DiffField, x :: .) -> DiffFieldElt
{ Coerce x into F }
    b, y := IsCoercible(F, x);
    require b: "Illegal coercion";
    return y;
end intrinsic;


intrinsic Print(x :: DiffFieldElt)
{ Print x }
    printf "%o", x`ActualRngDiffElt;
end intrinsic;


intrinsic Parent(x :: DiffFieldElt) -> DiffField
{ Parent of x }
    return x`Parent;
end intrinsic;


intrinsic '+'(x :: DiffFieldElt, y :: DiffFieldElt) -> DiffFieldElt
{ Return x + y }
    F := Parent(x);
    require F cmpeq Parent(y) : "Incompatible arguments";
    return CreateElement(F, x`ActualRngDiffElt + y`ActualRngDiffElt);
end intrinsic;


intrinsic '-'(x :: DiffFieldElt, y :: DiffFieldElt) -> DiffFieldElt
{ Return x - y }
    F := Parent(x);
    require F cmpeq Parent(y) : "Incompatible arguments";
    return CreateElement(F, x`ActualRngDiffElt - y`ActualRngDiffElt);
end intrinsic;


intrinsic '*'(x :: DiffFieldElt, y :: DiffFieldElt) -> DiffFieldElt
{ Return x * y }
    F := Parent(x);
    require F cmpeq Parent(y) : "Incompatible arguments";
    return CreateElement(F, x`ActualRngDiffElt * y`ActualRngDiffElt);
end intrinsic;


intrinsic '/'(x :: DiffFieldElt, y :: DiffFieldElt) -> DiffFieldElt
{ Return x / y }
    F := Parent(x);
    require F cmpeq Parent(y) : "Incompatible arguments";
    return CreateElement(F, x`ActualRngDiffElt / y`ActualRngDiffElt);
end intrinsic;


intrinsic Derivative(x :: DiffFieldElt) -> DiffFieldElt
{ Return the derivative of x }
    return CreateElement(Parent(x), Derivative(x`ActualRngDiffElt));
end intrinsic;


intrinsic AsFraction(x :: DiffFieldElt) -> DiffFieldElt, DiffFieldElt
{
    Return the fraction representation of the given DiffFieldElt.
}
    return (Parent(x)`UnderlyingRatFuncField) ! (x`ActualRngDiffElt);
end intrinsic;


// not sure if this messes up how equality is implemented under the hood or is
// inconsistent with the existing implementation
intrinsic 'eq'(x :: DiffFieldElt, y :: .) -> BoolElt
{ Return if x and y are equal }
    b, yy :=  IsCoercible(Parent(x), y);
    require b : "Cannot coerce second argument to first";
    return x`ActualRngDiffElt eq yy`ActualRngDiffElt;
end intrinsic;


intrinsic 'eq'(x :: ., y :: DiffFieldElt) -> BoolElt
{ Return if x and y are equal }
    return y eq x;
end intrinsic;


intrinsic 'cmpeq'(x :: DiffFieldElt, y :: .) -> BoolElt
{ Return x cmpeq y }
    b, yy :=  IsCoercible(Parent(x), y);
    return b and x`ActualRngDiffElt eq yy`ActualRngDiffElt;
end intrinsic;


intrinsic 'cmpeq'(x :: ., y :: DiffFieldElt) -> BoolElt
{ Return if x cmpeq y }
    return y cmpeq x;
end intrinsic;
