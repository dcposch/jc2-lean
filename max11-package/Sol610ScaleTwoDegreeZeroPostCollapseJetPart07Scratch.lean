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
  simp only [degreeZeroPostCollapseJetQuotient610,
    degreeZeroPostCollapseJetQuotient610c0, degreeZeroPostCollapseJetQuotient610c1, degreeZeroPostCollapseJetQuotient610c2, degreeZeroPostCollapseJetQuotient610c3, degreeZeroPostCollapseJetQuotient610c4, degreeZeroPostCollapseJetQuotient610c5, degreeZeroPostCollapseJetQuotient610c6, degreeZeroPostCollapseJetQuotient610c7, degreeZeroPostCollapseJetQuotient610c8, degreeZeroPostCollapseJetQuotient610c9, degreeZeroPostCollapseJetQuotient610c10, degreeZeroPostCollapseJetQuotient610c11, degreeZeroPostCollapseJetQuotient610c12, degreeZeroPostCollapseJetQuotient610c13, degreeZeroPostCollapseJetQuotient610c14, degreeZeroPostCollapseJetQuotient610c15, degreeZeroPostCollapseJetQuotient610c16, degreeZeroPostCollapseJetQuotient610c17, degreeZeroPostCollapseJetQuotient610c18, degreeZeroPostCollapseJetQuotient610c19, degreeZeroPostCollapseJetQuotient610c20, degreeZeroPostCollapseJetQuotient610c21, degreeZeroPostCollapseJetQuotient610c22, degreeZeroPostCollapseJetQuotient610c23, degreeZeroPostCollapseJetQuotient610c24, degreeZeroPostCollapseJetQuotient610c25, degreeZeroPostCollapseJetQuotient610c26, degreeZeroPostCollapseJetQuotient610c27, degreeZeroPostCollapseJetQuotient610c28, degreeZeroPostCollapseJetQuotient610c29, degreeZeroPostCollapseJetQuotient610c30, degreeZeroPostCollapseJetQuotient610c31, degreeZeroPostCollapseJetQuotient610c32, degreeZeroPostCollapseJetQuotient610c33, degreeZeroPostCollapseJetQuotient610c34, degreeZeroPostCollapseJetQuotient610c35, degreeZeroPostCollapseJetQuotient610c36, degreeZeroPostCollapseJetQuotient610c37, degreeZeroPostCollapseJetQuotient610c38, degreeZeroPostCollapseJetQuotient610c39, degreeZeroPostCollapseJetQuotient610c40, degreeZeroPostCollapseJetQuotient610c41, degreeZeroPostCollapseJetQuotient610c42, degreeZeroPostCollapseJetQuotient610c43, degreeZeroPostCollapseJetQuotient610c44, degreeZeroPostCollapseJetQuotient610c45, degreeZeroPostCollapseJetQuotient610c46, degreeZeroPostCollapseJetQuotient610c47, map_add, map_sub, map_neg,
    map_mul, map_pow, map_ofNat]

end DegreeZeroPostCollapseJetMap610

end Max11DegreeRoutes
