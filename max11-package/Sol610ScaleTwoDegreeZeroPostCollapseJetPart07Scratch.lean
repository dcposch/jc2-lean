import Sol610ScaleTwoDegreeZeroPostCollapseJetPart01Scratch

noncomputable section
namespace Max11DegreeRoutes
open scoped Polynomial
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroPostCollapseJetMap610

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Ring homomorphisms commute with the explicit post-collapse quotient. -/
theorem degreeZeroPostCollapseJetQuotient610_map
    (f : R →+* S)
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : R) :
    f (degreeZeroPostCollapseJetQuotient610 h w1 a42 p32 p21 p1 p0 s2 u2
        b63 q53 q41 q3 q2 q1 lambda) =
      degreeZeroPostCollapseJetQuotient610 (f h) (f w1) (f a42) (f p32)
        (f p21) (f p1) (f p0) (f s2) (f u2) (f b63) (f q53) (f q41)
        (f q3) (f q2) (f q1) (f lambda) := by
  simp only [degreeZeroPostCollapseJetQuotient610, map_add, map_sub, map_neg,
    map_mul, map_pow, map_ofNat]

end DegreeZeroPostCollapseJetMap610

end Max11DegreeRoutes
