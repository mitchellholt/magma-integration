177,0
T,MonArg,-,0
A,MonArg,2,ExtensionType,Argument
S,MonomialArg,"Create a monomial to be used as an extension over the parent of the argument. extType must be one of the string literals ""exp"" or ""log""",0,2,0,0,0,0,0,0,0,194,,0,0,298,,MonArg,-38,-38,-38,-38,-38
S,MonomialType,Return the type of the monomial,0,1,0,0,0,0,0,0,0,MonArg,,298,-38,-38,-38,-38,-38
S,MonomialArg,Return the argument of the monomial,0,1,0,0,0,0,0,0,0,MonArg,,194,-38,-38,-38,-38,-38
S,ChangeUnderlyingField,Change the underlying field the argument to this monomial comes from,0,2,0,0,0,0,0,0,0,193,,0,0,MonArg,,MonArg,-38,-38,-38,-38,-38
S,Print,Print m,0,1,0,0,1,0,0,0,0,MonArg,,-38,-38,-38,-38,-38,-38
T,DiffField,DiffFieldElt,0
A,DiffField,2,MonomialTower,ActualRngDiff
S,AllTranscendental,"Use the Risch Structure Theorem to check if the given tower of monomials are indeed transcendental over their base field. Returns the first monomial which is not transcendental and an offending linear/ product combination. If no such monomial exists, return the empty tuple",1,0,1,82,0,MonArg,1,0,0,0,0,0,0,0,82,,303,-38,-38,-38,-38,-38
S,DifferentialField,"Construct a differential field with the given monomial tower, checking that each extension is transcendental over the previous",1,0,1,82,0,MonArg,1,0,0,0,0,0,0,0,82,,DiffField,-38,-38,-38,-38,-38
S,Monomials,Return the monomials generating this field,0,1,0,0,0,0,0,0,0,DiffField,,82,-38,-38,-38,-38,-38
S,Generators,Return the generators of the differential field,0,1,0,0,0,0,0,0,0,DiffField,,83,-38,-38,-38,-38,-38
S,ConstantField,Return the constant field of F,0,1,0,0,0,0,0,0,0,DiffField,,-24,-38,-38,-38,-38,-38
S,BaseField,Return the base field of F,0,1,0,0,0,0,0,0,0,DiffField,,-44,-38,-38,-38,-38,-38
S,ExtendConstantField,"Return a new differential field, with the constant field extended to C",0,2,0,0,0,0,0,0,0,-24,,0,0,DiffField,,DiffField,-38,-38,-38,-38,-38
S,MonomialExtension,Return a new differential field which has the monomial extensions of the given differential field as well as the new monomial extensions,1,1,1,82,0,MonArg,2,0,0,0,0,0,0,0,82,,0,0,DiffField,,DiffField,-38,-38,-38,-38,-38
S,Print,Print F,0,1,0,0,1,0,0,0,0,DiffField,,-38,-38,-38,-38,-38,-38
S,AssignNames,Assign names to the generators of the differential field,1,1,1,82,0,298,2,0,0,1,0,0,0,0,82,,1,1,DiffField,,-38,-38,-38,-38,-38,-38
S,.,Return the ith generator of F,0,2,0,0,0,0,0,0,0,148,,0,0,DiffField,,DiffFieldElt,-38,-38,-38,-38,-38
A,DiffFieldElt,2,Parent,ActualRngDiffElt
S,IsCoercible,"Return whether x is coercible into F, and the result if so",0,2,0,0,0,0,0,0,0,-1,,0,0,DiffField,,36,-1,-38,-38,-38,-38
S,Print,Print x,0,1,0,0,1,0,0,0,0,DiffFieldElt,,-38,-38,-38,-38,-38,-38
S,Parent,Parent of x,0,1,0,0,0,0,0,0,0,DiffFieldElt,,DiffField,-38,-38,-38,-38,-38
S,+,Return x + y,0,2,0,0,0,0,0,0,0,DiffFieldElt,,0,0,DiffFieldElt,,DiffFieldElt,-38,-38,-38,-38,-38
S,-,Return x - y,0,2,0,0,0,0,0,0,0,DiffFieldElt,,0,0,DiffFieldElt,,DiffFieldElt,-38,-38,-38,-38,-38
S,*,Return x * y,0,2,0,0,0,0,0,0,0,DiffFieldElt,,0,0,DiffFieldElt,,DiffFieldElt,-38,-38,-38,-38,-38
S,/,Return x / y,0,2,0,0,0,0,0,0,0,DiffFieldElt,,0,0,DiffFieldElt,,DiffFieldElt,-38,-38,-38,-38,-38
S,Derivative,Return the derivative of x,0,1,0,0,0,0,0,0,0,DiffFieldElt,,DiffFieldElt,-38,-38,-38,-38,-38
