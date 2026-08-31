import FiniteC2Extraction

/-! # Weight-seven `c2` common-root lifting identities

Once the three normal coordinates reach half the weight-seven pole scale,
the four literal scaled Faber equations produce the exact arbitrary-`c2`
Kuranishi packet on their residues.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Once the three normal coordinates reach half the weight-seven pole scale,
the four literal scaled Faber equations produce the exact arbitrary-`c2`
Kuranishi packet on their residues. -/
theorem c2LeadingFaberRowsAt_of_bounds
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C2 C1 R1 R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (hnormal2 : (↑((7 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal2.1.orderTop)
    (hnormal1 : (↑((7 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal1.1.orderTop)
    (hnormal0 : (↑((7 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal0.1.orderTop) :
    let T := S.transverseFactorOfBounds ((7 * F.scale.p) / 2)
      (div_pos (mul_pos (by norm_num) F.scale.hp) (by norm_num))
      hnormal2 hnormal1 hnormal0
    GCD369CubeC2LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C2 := by
  dsimp only
  let T := S.transverseFactorOfBounds ((7 * F.scale.p) / 2)
    (div_pos (mul_pos (by norm_num) F.scale.hp) (by norm_num))
    hnormal2 hnormal1 hnormal0
  apply T.c2LeadingFaberRowsAt C2
  · have hz := (F.c2NCoeff_zero C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc1 hr1 hr2 hr3 hr4).1
    rw [hc2,
      F.scale.weightedRegular_constant_eq_monomial_sq 7 (by norm_num) C2] at hz
    have hTdelta : T.delta = (7 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1; norm_num; ring_nf
  · have hz := (F.c2NCoeff_zero C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc1 hr1 hr2 hr3 hr4).2.1
    rw [hc2,
      F.scale.weightedRegular_constant_eq_monomial_sq 7 (by norm_num) C2] at hz
    have hTdelta : T.delta = (7 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1; norm_num; ring_nf
  · have hz := (F.c2NCoeff_zero C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc1 hr1 hr2 hr3 hr4).2.2.1
    rw [hc2,
      F.scale.weightedRegular_constant_eq_monomial_sq 7 (by norm_num) C2] at hz
    have hTdelta : T.delta = (7 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1; norm_num; ring_nf
  · have hz := (F.c2NCoeff_zero C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc1 hr1 hr2 hr3 hr4).2.2.2
    rw [hc2,
      F.scale.weightedRegular_constant_eq_monomial_sq 7 (by norm_num) C2] at hz
    have hTdelta : T.delta = (7 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz using 1; norm_num; ring_nf

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.c2LeadingFaberRowsAt_of_bounds
