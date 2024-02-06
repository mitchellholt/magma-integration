intrinsic IntegrateLogarithmicPolynomial(f :: RngDiffElt: all_logarithms := [])
    -> Bool, RngDiffElt, SeqEnum
{
    In K(x, M1, ..., Mn), assert that Mn is logarithmic and that f is a
    polynomial in K(x, M1, ..., M(n-1))[Mn]. If f has an elementary integral,
    return true, an integral, and a list of all the logarithms appearing in the
    parent differential field of the solution. Otherwise, return false.
}
    // See working from 06/02/2024 in notebook for derivation of algorithm
    F := Parent(f);

    // Could check if we can coerce the argument down to a field in the tower
    // that is logarithmic?
    require IsLogarithmic(F) : "The last generator is not logarithmic";

    is_poly, poly := IsPolynomial(f);
    require is_poly : "Argument is not a polynomial";

    // find all the logarithms, if no list has been provided
    if #all_logarithms eq 0 then
        all_logarithms := AllLogarithms(F);
    end if;

    if poly eq 0 then return true, poly, all_logarithms; end if;
    integral; // value of an elementary integral, if any
    deg := Degree(poly);
    // REMEMBER 1 INDEXING HERE!!!!
    ps := Coefficients(poly);
    qs := [ CoefficientRing(F) | 0 : _ in [ 0 .. deg + 1 ] ];

    // calculate the two leading terms
    is_elementary, integral, logs := ElementaryIntegral(ps[deg + 1]);
    if not is_elementary then
        return false, integral, all_logarithms;
    elif #logs gt #all_logarithms then
        return false, integral, all_logarithms;
    elif #logs eq #all_logarithms and Universe(logs) ! F.1 notin logs then
        return false, integral, all_logarithms;
    end if;

    is_poly, poly := IsPolynomial(F ! itg); // this had better be coercible
    if not is_poly(f) or Degree(poly) gt 1 then
        return false, integral, all_logarithms;
    end if;
    qs[deg + 2] := -Coefficient(poly, 1)/(deg + 1);
    qs[deg + 1] := Coefficient(poly, 0);

    // calculate the remaining non-zero terms
    i := deg - 1; // the index for q_i is i + 1 rip
    while i gt 0 do
        is_elementary, integral, logs := ElementaryIntegral(ps[i + 1]);
        if not is_elementary then
            return false, integral, all_logarithms;
        elif #logs gt #all_logarithms then
            return false, integral, all_logarithms;
        elif #logs eq #all_logarithms and Universe(logs) ! F.1 notin logs then
            return false, integral, all_logarithms;
        end if;

        is_poly, poly := IsPolynomial(F ! itg);
        if not is_poly(f) or Degree(poly) gt 1 then
            return false, integral, all_logarithms;
        end if;
        qs[i + 2] +:= -Coefficient(poly, 1)/(i + 1);
        qs[i + 1] := Coefficient(poly, 0);
    end while;

    is_elementary, integral, logs := ElementaryIntegral(ps[i + 1]);
    if not is_elementary then
        return false, integral, all_logarithms;
    end if;

    G := Parent(integral);
    for i in [ 0 .. deg + 1 ] do
        integral +:= G ! (qs[i + 1] * F.1^i);
    end for;

    return true, integral, logs;
end intrinsic;
