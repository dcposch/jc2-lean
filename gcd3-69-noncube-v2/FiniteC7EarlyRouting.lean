import FiniteEarlyLoadTied
import FiniteC7RootLift
import FiniteC7SourceElimination

/-! # Routing the weight-two `c7` load

After the weight-one parameter has vanished, `c7` is the next possible
source load.  This file routes that load against the canonical transverse
normal scale.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If the weight-two `c7` load arrives strictly before the canonical
transverse normal, its coefficient vanishes. -/
theorem TransverseScale.c7_eq_zero_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
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
    (hbefore : F.scale.p < T.delta) :
    C7 = 0 := by
  obtain ⟨hn2, hn1, hn0⟩ := T.normal_orderTop_lower
  have hload : (2 * F.scale.p) / 2 < T.delta := by
    linarith
  have hb2 : (↑((2 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal2.1.orderTop :=
    (WithTop.coe_le_coe.mpr hload.le).trans hn2
  have hb1 : (↑((2 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal1.1.orderTop :=
    (WithTop.coe_le_coe.mpr hload.le).trans hn1
  have hb0 : (↑((2 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal0.1.orderTop :=
    (WithTop.coe_le_coe.mpr hload.le).trans hn0
  let U := S.transverseFactorOfBounds ((2 * F.scale.p) / 2)
    (div_pos (mul_pos (by norm_num : (0 : ℚ) < 2) F.scale.hp)
      (by norm_num)) hb2 hb1 hb0
  have hX : GCD369CubeHahnRegular.constantCoeff U.Xn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [GCD369CubeHahnRegular.constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hload).trans_le hn2
  have hY : GCD369CubeHahnRegular.constantCoeff U.Yn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [GCD369CubeHahnRegular.constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hload).trans_le hn1
  have hZ : GCD369CubeHahnRegular.constantCoeff U.Zn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [GCD369CubeHahnRegular.constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hload).trans_le hn0
  have hrows : GCD369CubeC7LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v C7 := by
    simpa only [U] using S.c7LeadingFaberRowsAt_of_bounds F hscale
      C7 C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hb2 hb1 hb0
  by_contra hC7
  have hnocommon := GCD369CubeC7LeadingFaberRowsAt_noCommonRoot
    (GCD369CubeHahnRegular.constantCoeff U.Xn)
    (GCD369CubeHahnRegular.constantCoeff U.Yn)
    (GCD369CubeHahnRegular.constantCoeff U.Zn)
    S.u S.v C7 hC7 S.hprojective hrows
  apply hnocommon
    (GCD369CubeHahnRegular.constantCoeff S.normal.sextic.regularX)
    S.leadingCubicRoot
  rw [hX, hY, hZ]
  ring

/-- If the weight-two `c7` load ties the canonical transverse normal, its
coefficient also vanishes.  The vanished weight-one source term extends the
ninth-Faber coefficient gap to the weight-two threshold. -/
theorem TransverseScale.c7_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hdNormal : S.normal.d = 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
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
    (htie : F.scale.p = T.delta) :
    C7 = 0 := by
  obtain ⟨hn2, hn1, hn0⟩ := T.normal_orderTop_lower
  have hb2 : (↑((2 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal2.1.orderTop := by
    rw [htie]
    norm_num
    exact hn2
  have hb1 : (↑((2 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal1.1.orderTop := by
    rw [htie]
    norm_num
    exact hn1
  have hb0 : (↑((2 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal0.1.orderTop := by
    rw [htie]
    norm_num
    exact hn0
  let U := S.transverseFactorOfBounds ((2 * F.scale.p) / 2)
    (div_pos (mul_pos (by norm_num : (0 : ℚ) < 2) F.scale.hp)
      (by norm_num)) hb2 hb1 hb0
  have hUdelta : U.delta = T.delta := by
    dsimp only [U, transverseFactorOfBounds]
    rw [htie]
    ring
  have hrows : GCD369CubeC7LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v C7 := by
    simpa only [U] using S.c7LeadingFaberRowsAt_of_bounds F hscale
      C7 C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hb2 hb1 hb0
  by_contra hC7
  have hnocommon := GCD369CubeC7LeadingFaberRowsAt_noCommonRoot
    (GCD369CubeHahnRegular.constantCoeff U.Xn)
    (GCD369CubeHahnRegular.constantCoeff U.Yn)
    (GCD369CubeHahnRegular.constantCoeff U.Zn)
    S.u S.v C7 hC7 S.hprojective hrows
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
  apply U.reducedFaberNine_inconsistent_of_exact_cubic_order_before_c7
    hdNormal alpha 0 a halpha ha hKorder rfl
  · exact (show (↑(0 : ℚ) : WithTop ℚ) ≤
      (GCD369CubeHahnRegular.ratCast (3 / 8) * U.Xn *
        (U.Xn * S.normal.sextic.regularX + 2 * U.Yn)).1.orderTop from
      (GCD369CubeHahnRegular.ratCast (3 / 8) * U.Xn *
        (U.Xn * S.normal.sextic.regularX + 2 * U.Yn)).2)
  · nlinarith [U.hdelta]
  · rw [hscale, htie]
    nlinarith [hresonance, hUdelta, T.hdelta]

/-- The complete weight-two active-load branch: once `d=0`, arrival of
`c7` no later than the transverse normal forces `c7=0`. -/
theorem TransverseScale.c7_eq_zero_at_or_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hdNormal : S.normal.d = 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
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
    (hle : F.scale.p ≤ T.delta) :
    C7 = 0 := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact T.c7_eq_zero_before_transverse F hscale
      C7 C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hlt
  · exact T.c7_eq_zero_at_transverse F hscale
      C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 hdNormal
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 heq

end GCD369CubeHahnCommonValueData

namespace GCD369CubePolynomialSource

/-- Literal finite-pole form of strict weight-two routing. -/
theorem finite_c7_eq_zero_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (T : (S.finiteCommonValueData a hpole).TransverseScale)
    (hd : S.faberConstantParameters.d = 0)
    (hbefore : (S.finiteFaberPoleData a hpole).scale.p < T.delta) :
    S.faberConstantParameters.c7 = 0 := by
  let C := S.finiteCommonValueData a hpole
  let F := S.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  change F.scale.p < T.delta at hbefore
  have hfd : F.d = GCD369CubeHahnRegular.constant 0 := by
    have hfdP : F.d = GCD369CubeHahnRegular.constant P.d := by
      exact GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.d
    rw [hd] at hfdP
    exact hfdP
  exact T.c7_eq_zero_before_transverse F rfl
    P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
    R.rho1 R.rho2 R.rho3 R.rho4 hfd
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
    hbefore

/-- Literal finite-pole form of complete weight-two routing. -/
theorem finite_c7_eq_zero_at_or_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (T : (S.finiteCommonValueData a hpole).TransverseScale)
    (hd : S.faberConstantParameters.d = 0)
    (hle : (S.finiteFaberPoleData a hpole).scale.p ≤ T.delta) :
    S.faberConstantParameters.c7 = 0 := by
  let C := S.finiteCommonValueData a hpole
  let F := S.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  change F.scale.p ≤ T.delta at hle
  have hfd : F.d = GCD369CubeHahnRegular.constant 0 := by
    have hfdP : F.d = GCD369CubeHahnRegular.constant P.d := by
      exact GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.d
    rw [hd] at hfdP
    exact hfdP
  have hnd : C.normal.d = 0 := by
    have hndP : C.normal.d = GCD369CubeHahnRegular.constant P.d := by
      exact GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.d
    rw [hd] at hndP
    simpa using hndP
  exact T.c7_eq_zero_at_or_before_transverse F rfl
    P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
    R.rho1 R.rho2 R.rho3 R.rho4 hnd hfd
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
  GCD369CubeHahnCommonValueData.TransverseScale.c7_eq_zero_before_transverse
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.c7_eq_zero_at_transverse
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.c7_eq_zero_at_or_before_transverse
#print axioms GCD369CubePolynomialSource.finite_c7_eq_zero_before_transverse
#print axioms
  GCD369CubePolynomialSource.finite_c7_eq_zero_at_or_before_transverse
