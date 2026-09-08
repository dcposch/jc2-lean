import Max11UnconditionalAssemblyScratch

/-!
# Max-11: plane Keller pairs of partial `y`-degree at most eleven generate

Solution module for the Palomar registration.  The headline theorem is
`Max11DegreeRoutes.Max11PlaneKellerGenerationWithClassicalInterfaces`
(in `Max11UnconditionalAssemblyScratch`): every plane Keller pair whose
partial `y`-degrees are both at most eleven generates `K[x,y]`, given only the
two classical inputs declared as explicit hypotheses there — the canonical
prime-total-degree-gcd theorem and the published standard-endpoint
obstruction.  All five primitive gcd-two leaves `(4,6)`, `(4,10)`, `(6,8)`,
`(6,10)`, `(8,10)` are proved internally by the imported closure.
-/
