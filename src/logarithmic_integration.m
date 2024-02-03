intrinsic IntegrateLogarithmicPolynomial(f :: DiffFieldElt: all_logarithms := [])
    -> Bool, DiffFieldElt, SeqEnum
{
    In K(x, M1, ..., Mn), assert that Mn is logarithmic and that f is a
    polynomial in K(x, M1, ..., M(n-1))[Mn]. If f has an elementary integral,
    return true, the integral, and a list of all the logarithms appearing in the
    integral. Otherwise, return false and two values which can be anything.
}
    F := Parent(f);

    require IsLogarithmic(F) : "The last generator is not logarithmic";
    require Denominator(f) eq 1 : "Argument is not a polynomial";

    // find all the logarithms, if no list has been provided
    if #all_logarithms eq 0 then
        all_logarithms := CheckLogarithms(F);
    end if;

    poly := Numerator(f);
    if poly eq 0 then return true, poly, all_logarithms; end if;
    integral; // value of an elementary integral, if any
    deriv := Derivative(F.n);
    deg := Degree(p);
    qs := [ Codomain(inclusion) | 0 : _ in [1 .. deg + 1] ];

    // special case for two leading coefficients
    elementary, lcint := ElementaryIntegral(inclusion(Coefficient(p, deg)))
    if not elementary then return false, integral; end if;
    F := Parent(lcint); // might change F if there is a constant field extension
    if #Monomials(F) gt n then return false, integral; end if;

    // update inclusion and qs as the constant field may have been extended
    lcint, inclusion := Polynomial(lcint, n);
    ChangeUniverse(~qs, Codomain(inclusion));

    qs[deg + 1] := inclusion(Coefficient(lcint, 1)/(deg + 1));
    qs[deg] := inclusion(Coefficient(lcint, 0));
end intrinsic;
