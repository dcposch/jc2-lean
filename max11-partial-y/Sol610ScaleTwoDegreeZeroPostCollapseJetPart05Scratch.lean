import Sol610ScaleTwoDegreeZeroPostCollapseJetPart01Scratch

noncomputable section
namespace Max11DegreeRoutes
open scoped Polynomial
set_option maxRecDepth 100000000
set_option maxHeartbeats 800000000

section DegreeZeroPostCollapseJetEval610

variable {k : Type*} [CommRing k]

/-- Evaluation commutes with the explicit degree-zero post-collapse
quotient. -/
theorem degreeZeroPostCollapseJetQuotient610_eval
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda a : k) :
    (degreeZeroPostCollapseJetQuotient610 h w1 a42 p32 p21 p1 p0 s2 u2
        b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)).eval a =
      degreeZeroPostCollapseJetQuotient610 (h.eval a) (w1.eval a)
        (a42.eval a) (p32.eval a) (p21.eval a) (p1.eval a) (p0.eval a)
        (s2.eval a) (u2.eval a) (b63.eval a) (q53.eval a) (q41.eval a)
        (q3.eval a) (q2.eval a) (q1.eval a) lambda := by
  simp only [degreeZeroPostCollapseJetQuotient610,
    degreeZeroPostCollapseJetQuotient610c0, degreeZeroPostCollapseJetQuotient610c1, degreeZeroPostCollapseJetQuotient610c2, degreeZeroPostCollapseJetQuotient610c3, degreeZeroPostCollapseJetQuotient610c4, degreeZeroPostCollapseJetQuotient610c5, degreeZeroPostCollapseJetQuotient610c6, degreeZeroPostCollapseJetQuotient610c7, degreeZeroPostCollapseJetQuotient610c8, degreeZeroPostCollapseJetQuotient610c9, degreeZeroPostCollapseJetQuotient610c10, degreeZeroPostCollapseJetQuotient610c11, degreeZeroPostCollapseJetQuotient610c12, degreeZeroPostCollapseJetQuotient610c13, degreeZeroPostCollapseJetQuotient610c14, degreeZeroPostCollapseJetQuotient610c15, degreeZeroPostCollapseJetQuotient610c16, degreeZeroPostCollapseJetQuotient610c17, degreeZeroPostCollapseJetQuotient610c18, degreeZeroPostCollapseJetQuotient610c19, degreeZeroPostCollapseJetQuotient610c20, degreeZeroPostCollapseJetQuotient610c21, degreeZeroPostCollapseJetQuotient610c22, degreeZeroPostCollapseJetQuotient610c23, degreeZeroPostCollapseJetQuotient610c24, degreeZeroPostCollapseJetQuotient610c25, degreeZeroPostCollapseJetQuotient610c26, degreeZeroPostCollapseJetQuotient610c27, degreeZeroPostCollapseJetQuotient610c28, degreeZeroPostCollapseJetQuotient610c29, degreeZeroPostCollapseJetQuotient610c30, degreeZeroPostCollapseJetQuotient610c31, degreeZeroPostCollapseJetQuotient610c32, degreeZeroPostCollapseJetQuotient610c33, degreeZeroPostCollapseJetQuotient610c34, degreeZeroPostCollapseJetQuotient610c35, degreeZeroPostCollapseJetQuotient610c36, degreeZeroPostCollapseJetQuotient610c37, degreeZeroPostCollapseJetQuotient610c38, degreeZeroPostCollapseJetQuotient610c39, degreeZeroPostCollapseJetQuotient610c40, degreeZeroPostCollapseJetQuotient610c41, degreeZeroPostCollapseJetQuotient610c42, degreeZeroPostCollapseJetQuotient610c43, degreeZeroPostCollapseJetQuotient610c44, degreeZeroPostCollapseJetQuotient610c45, degreeZeroPostCollapseJetQuotient610c46, degreeZeroPostCollapseJetQuotient610c47, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_C]

end DegreeZeroPostCollapseJetEval610

end Max11DegreeRoutes
