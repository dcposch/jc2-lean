import FiniteEarlyLoadRouting
import FiniteSourceElimination

/-! # The tied weight-one load

At `p = 2 * delta`, a nonzero `d` load supplies the arbitrary-load
no-common-root certificate on the half-scale normal jet.  The literal sextic
equation then forces the moving cubic to have order `delta / 2`; the reduced
ninth-Faber equation excludes that exact order before the load scale.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- The tied weight-one load cannot be nonzero. -/
theorem TransverseScale.d_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : F.scale.p = 2 * T.delta) :
    D = 0 := by
  obtain ⟨hn2, hn1, hn0⟩ := T.normal_orderTop_lower
  have hb2 : (↑(F.scale.p / 2) : WithTop ℚ) ≤ S.normal2.1.orderTop := by
    rw [htie]
    norm_num
    exact hn2
  have hb1 : (↑(F.scale.p / 2) : WithTop ℚ) ≤ S.normal1.1.orderTop := by
    rw [htie]
    norm_num
    exact hn1
  have hb0 : (↑(F.scale.p / 2) : WithTop ℚ) ≤ S.normal0.1.orderTop := by
    rw [htie]
    norm_num
    exact hn0
  let U := S.transverseFactorOfBounds (F.scale.p / 2)
    (div_pos F.scale.hp (by norm_num)) hb2 hb1 hb0
  have hUdelta : U.delta = T.delta := by
    dsimp only [U, transverseFactorOfBounds]
    rw [htie]
    ring
  have hrows : GCD369CubeDLeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v D := by
    simpa only [U] using S.dLeadingFaberRowsAt_of_bounds F hscale
      D C7 C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hb2 hb1 hb0
  by_contra hD
  have hnocommon := GCD369CubeDLeadingFaberRowsAt_noCommonRoot
    (GCD369CubeHahnRegular.constantCoeff U.Xn)
    (GCD369CubeHahnRegular.constantCoeff U.Yn)
    (GCD369CubeHahnRegular.constantCoeff U.Zn)
    S.u S.v D hD S.hprojective hrows
  let x : GCD369CubeHahnRegular k := S.normal.sextic.regularX
  let B : GCD369CubeHahnRegular k :=
    U.Xn * x ^ 2 + U.Yn * x + U.Zn
  have hB0 : GCD369CubeHahnRegular.constantCoeff B ≠ 0 := by
    intro hzero
    apply hnocommon (GCD369CubeHahnRegular.constantCoeff x)
    · simpa [x, GCD369CubeHahnRegular.constantCoeff,
        GCD369CubeHahnSexticValueData.regularX] using S.leadingCubicRoot
    · simpa only [B, x, map_add, map_mul, map_pow] using hzero
  have hBorder : B.1.orderTop = (↑(0 : ℚ) : WithTop ℚ) :=
    (GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero B hB0).1
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial U.delta U.hdelta.le
  have hH := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) U.delta U.hdelta.le
  have hphiEq : S.transverseValue = H * B := by
    simpa only [H, B, x] using U.transverseValue_eq
  have hHB := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    H B U.delta 0 hH.1 hBorder
  have hphiOrder : S.transverseValue.1.orderTop =
      (↑U.delta : WithTop ℚ) := by
    rw [hphiEq]
    simpa only [add_zero] using hHB.1
  have hKne : S.cubicValue.1 ≠ 0 := by
    intro hKzero
    have hsource := S.commonNormalEquation_orderTop_lower
    change (↑(6 * S.normal.sextic.scale.p) : WithTop ℚ) ≤
      (S.cubicValue.1 ^ 2 + S.transverseValue.1).orderTop at hsource
    rw [hKzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
      hphiOrder, hscale, hUdelta, htie, WithTop.coe_le_coe] at hsource
    nlinarith [T.hdelta]
  let alpha : ℚ := S.cubicValue.1.order
  let a : k := S.cubicValue.1.leadingCoeff
  have hKorder : S.cubicValue.1.orderTop =
      (↑alpha : WithTop ℚ) := by
    exact (HahnSeries.order_eq_orderTop_of_ne_zero hKne).symm
  have halpha : 0 < alpha := by
    have hpos := GCD369CubeHahnRegular.orderTop_pos_of_constantCoeff_zero
      S.cubicValue S.constantCoeff_cubicValue_zero
    rw [hKorder, WithTop.coe_lt_coe] at hpos
    exact hpos
  have ha : a ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hKne
  have halt := S.commonNormal_orderAlternative alpha U.delta
    hKorder hphiOrder
  have hresonance : 2 * alpha = U.delta := by
    rcases halt with hfar | hcancel
    · have hmin : min (2 * alpha) U.delta ≤ U.delta := min_le_right _ _
      have himpossible := hfar.trans hmin
      rw [hscale, htie, hUdelta] at himpossible
      nlinarith [T.hdelta]
    · exact hcancel.1
  apply U.reducedFaberNine_inconsistent_of_exact_cubic_order
    alpha 0 a halpha ha hKorder rfl
  · exact (show (↑(0 : ℚ) : WithTop ℚ) ≤
      (GCD369CubeHahnRegular.ratCast (3 / 8) * U.Xn *
        (U.Xn * S.normal.sextic.regularX + 2 * U.Yn)).1.orderTop from
      (GCD369CubeHahnRegular.ratCast (3 / 8) * U.Xn *
        (U.Xn * S.normal.sextic.regularX + 2 * U.Yn)).2)
  · nlinarith [U.hdelta]
  · rw [hscale, htie]
    nlinarith [hresonance, hUdelta, T.hdelta]

/-- Together with the strict routing lemma, the entire branch in which the
weight-one load arrives no later than the first normal quadratic forces
`d = 0`. -/
theorem TransverseScale.d_eq_zero_at_or_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (hle : F.scale.p ≤ 2 * T.delta) :
    D = 0 := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact T.d_eq_zero_before_transverse F hscale
      D C7 C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hlt
  · exact T.d_eq_zero_at_transverse F hscale
      D C7 C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 heq

end GCD369CubeHahnCommonValueData

namespace GCD369CubePolynomialSource

/-- Literal finite-pole form of the complete `p ≤ 2 * delta` routing
theorem. -/
theorem finite_d_eq_zero_at_or_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (T : (S.finiteCommonValueData a hpole).TransverseScale)
    (hle : (S.finiteFaberPoleData a hpole).scale.p ≤ 2 * T.delta) :
    S.faberConstantParameters.d = 0 := by
  let C := S.finiteCommonValueData a hpole
  let F := S.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  change F.scale.p ≤ 2 * T.delta at hle
  exact T.d_eq_zero_at_or_before_transverse F rfl
    P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
    R.rho1 R.rho2 R.rho3 R.rho4
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.d)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c7)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c5)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c4)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c3)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c2)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c1)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho1)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho2)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho3)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho4)
    hle

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.d_eq_zero_at_transverse
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.d_eq_zero_at_or_before_transverse
#print axioms
  GCD369CubePolynomialSource.finite_d_eq_zero_at_or_before_transverse
