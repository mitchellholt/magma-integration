Attach("src/DifferentialFields.m");
Attach("src/Integration.m");
Attach("src/logarithmic_integration.m");
Attach("src/rational_integration.m");
F<x> := RationalDifferentialField(RationalField());
G<g> := LogarithmicExtension(F, 1/x);
