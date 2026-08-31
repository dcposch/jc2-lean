import FiniteC4Extraction

/-! # Weight-five `c4` common-root lifting identities

Once the three normal coordinates reach half the weight-five pole scale,
the four literal scaled Faber equations produce the exact arbitrary-`c4`
Kuranishi packet on their residues.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Once the three normal coordinates reach half the weight-five pole scale,
the four literal scaled Faber equations produce the exact arbitrary-`c4`
Kuranishi packet on their residues. -/
theorem c4LeadingFaberRowsAt_of_bounds
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (hnormal2 : (↑((5 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal2.1.orderTop)
    (hnormal1 : (↑((5 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal1.1.orderTop)
    (hnormal0 : (↑((5 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal0.1.orderTop) :
    let T := S.transverseFactorOfBounds ((5 * F.scale.p) / 2)
      (div_pos (mul_pos (by norm_num) F.scale.hp) (by norm_num))
      hnormal2 hnormal1 hnormal0
    GCD369CubeC4LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C4 := by
  dsimp only
  let T := S.transverseFactorOfBounds ((5 * F.scale.p) / 2)
    (div_pos (mul_pos (by norm_num) F.scale.hp) (by norm_num))
    hnormal2 hnormal1 hnormal0
  apply T.c4LeadingFaberRowsAt C4
  · have hz := (F.c4NCoeff_zero C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc3 hc2 hc1 hr1 hr2 hr3 hr4).1
    rw [hc4,
      F.scale.weightedRegular_constant_eq_monomial_sq 5 (by norm_num) C4] at hz
    have hTdelta : T.delta = (5 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1
    all_goals norm_num
    all_goals ring_nf
  · have hz := (F.c4NCoeff_zero C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc3 hc2 hc1 hr1 hr2 hr3 hr4).2.1
    rw [hc4,
      F.scale.weightedRegular_constant_eq_monomial_sq 5 (by norm_num) C4] at hz
    have hTdelta : T.delta = (5 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1
    all_goals norm_num
    all_goals ring_nf
  · have hz := (F.c4NCoeff_zero C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc3 hc2 hc1 hr1 hr2 hr3 hr4).2.2.1
    rw [hc4,
      F.scale.weightedRegular_constant_eq_monomial_sq 5 (by norm_num) C4] at hz
    have hTdelta : T.delta = (5 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1
    all_goals norm_num
    all_goals ring_nf
  · have hz := (F.c4NCoeff_zero C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc3 hc2 hc1 hr1 hr2 hr3 hr4).2.2.2
    rw [hc4,
      F.scale.weightedRegular_constant_eq_monomial_sq 5 (by norm_num) C4] at hz
    have hTdelta : T.delta = (5 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1
    all_goals norm_num
    all_goals ring_nf

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.c4LeadingFaberRowsAt_of_bounds
