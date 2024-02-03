intrinsic IntegrateLogarithmicPolynomial(f :: DiffFieldElt) -> Bool, DiffFieldElt
{
    In a DiffField K(x, M1, ..., Mn), assert that Mn is logarithmic and that
    f is a polynomial in K(x, M1, ..., M(n-1))[Mn]. If f has an elementary
    integral, return true and the integral. Otherwise, return false and an
    uninitialised value.
}
    F := Parent(f);
    monomials := Monomials(F);
    n := #monomials;
    require n gt 0 and IsLogarithmic(monomials[n])
        : "The last monomial in the tower is not logarithmic";

    p, inclusion := Polynomial(f, n); // throws if not poly
    integral; // DO NOT ASSIGN TO THIS VALUE UNTIL THE END
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
