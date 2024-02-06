177,0
S,AsFraction,Assume the argument is from a field of the form L = F(x) for some differntial field F. Return the argument as an element of the rational function field F(x),0,1,0,0,0,0,0,0,0,194,,-41,-38,-38,-38,-38,-38
S,IsPolynomial,"Return if the input is a polynomial over the first generator of the field. If it is, also return its representation as a polynomial",0,1,0,0,0,0,0,0,0,194,,37,312,-38,-38,-38,-38
S,IsLogarithmic,"Let F be a field of the form K(x, M1, ..., Mn). Return if M_n is logarithmic over F",0,1,0,0,0,0,0,0,0,193,,37,-38,-38,-38,-38,-38
S,AllLogarithms,Give an ordered sequence of all of the logarithmic generators of F,0,1,0,0,0,0,0,0,0,193,,82,-38,-38,-38,-38,-38
S,IsTranscendentalLogarithm,"Given a potential new logarithm argument to be put over a differential field, use the Risch Structure Theorem to check if the new logarithm is transcendental. If it is, return the empty sequence. If not, return the product combination as a list of < factor, non-zero power > pairs in the differetial field equal to the new argument. Assume that [log(f) : f in logarithms] is an algebraically independent set over Universe(logarithms). Also assume that each f in logarithms is non-constant",0,2,0,0,0,0,0,0,0,82,,0,0,194,,82,-38,-38,-38,-38,-38
S,TranscendentalLogarithmicExtension,"Compute the differential extension field F(L), where L is logarithmic over F with derivative f'/f. If L is not transcendental, remove it. Otherwise return F(L). Also return all of the logarithms of F(L) and the representation of L inside of F(L) (which may be a transcendental over F or an element of F)",0,2,0,0,0,0,0,0,0,194,,0,0,193,,193,82,194,-38,-38,-38
