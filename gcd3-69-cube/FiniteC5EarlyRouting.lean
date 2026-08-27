import FiniteArbitraryLoadStrict
import FiniteArbitraryLoadTied
import FiniteC5RootLift
import FiniteC5SourceElimination

/-! # Routing the weight-four `c5` load

After the weight-one and weight-two parameters have vanished, `c5` is the
next possible source load.  Its factor scale is `2p`.  Strictly before the
canonical transverse normal, the arbitrary-load common-root obstruction
kills it; at equality, the literal source coefficient gap kills the forced
cubic resonance.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If the weight-four `c5` load arrives strictly before the canonical
transverse normal, its coefficient vanishes. -/
theorem TransverseScale.c5_eq_zero_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (hbefore : 2 * F.scale.p < T.delta) :
    C5 = 0 := by
  obtain ⟨hn2, hn1, hn0⟩ := T.normal_orderTop_lower
  have hs : 0 < (4 * F.scale.p) / 2 := by
    exact div_pos (mul_pos (by norm_num) F.scale.hp) (by norm_num)
  have hload : (4 * F.scale.p) / 2 < T.delta := by
    linarith
  have hb2 : (↑((4 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal2.1.orderTop :=
    (WithTop.coe_le_coe.mpr hload.le).trans hn2
  have hb1 : (↑((4 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal1.1.orderTop :=
    (WithTop.coe_le_coe.mpr hload.le).trans hn1
  have hb0 : (↑((4 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal0.1.orderTop :=
    (WithTop.coe_le_coe.mpr hload.le).trans hn0
  let U := S.transverseFactorOfBounds ((4 * F.scale.p) / 2)
    hs hb2 hb1 hb0
  have hrows : GCD369CubeC5LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v C5 := by
    simpa only [U] using S.c5LeadingFaberRowsAt_of_bounds F hscale
      C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hb2 hb1 hb0
  by_contra hC5
  let load : GCD369CubeArbitraryEarlyFaberLoad
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v :=
    .c5 C5 hC5 S.hprojective hrows
  apply T.arbitraryEarlyLoad_strict_before_transverse
    ((4 * F.scale.p) / 2) hs hload
  simpa only [U] using load

/-- If the weight-four `c5` load ties the canonical transverse normal, its
coefficient also vanishes. -/
theorem TransverseScale.c5_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 2 * F.scale.p = T.delta) :
    C5 = 0 := by
  obtain ⟨hn2, hn1, hn0⟩ := T.normal_orderTop_lower
  have hs : 0 < (4 * F.scale.p) / 2 := by
    exact div_pos (mul_pos (by norm_num) F.scale.hp) (by norm_num)
  have hb2 : (↑((4 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal2.1.orderTop := by
    rw [show (4 * F.scale.p) / 2 = 2 * F.scale.p by ring, htie]
    exact hn2
  have hb1 : (↑((4 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal1.1.orderTop := by
    rw [show (4 * F.scale.p) / 2 = 2 * F.scale.p by ring, htie]
    exact hn1
  have hb0 : (↑((4 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal0.1.orderTop := by
    rw [show (4 * F.scale.p) / 2 = 2 * F.scale.p by ring, htie]
    exact hn0
  let U := S.transverseFactorOfBounds ((4 * F.scale.p) / 2)
    hs hb2 hb1 hb0
  have hUdelta : U.delta = T.delta := by
    dsimp only [U, transverseFactorOfBounds]
    rw [show (4 * F.scale.p) / 2 = 2 * F.scale.p by ring, htie]
  have hrows : GCD369CubeC5LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v C5 := by
    simpa only [U] using S.c5LeadingFaberRowsAt_of_bounds F hscale
      C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hb2 hb1 hb0
  by_contra hC5
  let load : GCD369CubeArbitraryEarlyFaberLoad
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v :=
    .c5 C5 hC5 S.hprojective hrows
  have hbeforeSource : U.delta < 6 * S.normal.sextic.scale.p := by
    rw [hUdelta, ← htie, hscale]
    nlinarith [F.scale.hp]
  obtain ⟨alpha, a, halpha, ha, hKorder, hlcK, hresonance⟩ :=
    U.cubic_resonance_of_arbitraryEarlyLoad load hbeforeSource
  apply U.reducedFaberNine_inconsistent_of_exact_cubic_order_before_c5
    hdNormal hc7Normal alpha 0 a halpha ha hKorder hlcK
  · exact (show (↑(0 : ℚ) : WithTop ℚ) ≤
      (GCD369CubeHahnRegular.ratCast (3 / 8) * U.Xn *
        (U.Xn * S.normal.sextic.regularX + 2 * U.Yn)).1.orderTop from
      (GCD369CubeHahnRegular.ratCast (3 / 8) * U.Xn *
        (U.Xn * S.normal.sextic.regularX + 2 * U.Yn)).2)
  · nlinarith [U.hdelta]
  · rw [hscale]
    nlinarith [hresonance, hUdelta, htie, F.scale.hp]

/-- The complete weight-four active-load branch: once `d=c7=0`, arrival of
`c5` no later than the transverse normal forces `c5=0`. -/
theorem TransverseScale.c5_eq_zero_at_or_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (hle : 2 * F.scale.p ≤ T.delta) :
    C5 = 0 := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact T.c5_eq_zero_before_transverse F hscale
      C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hlt
  · exact T.c5_eq_zero_at_transverse F hscale
      C5 C4 C3 C2 C1 R1 R2 R3 R4 hdNormal hc7Normal
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 heq

end GCD369CubeHahnCommonValueData

namespace GCD369CubePolynomialSource

/-- Literal finite-pole form of strict weight-four routing. -/
theorem finite_c5_eq_zero_before_transverse
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
    (hc7 : S.faberConstantParameters.c7 = 0)
    (hbefore :
      2 * (S.finiteFaberPoleData a hpole).scale.p < T.delta) :
    S.faberConstantParameters.c5 = 0 := by
  let F := S.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  change 2 * F.scale.p < T.delta at hbefore
  have hfd : F.d = GCD369CubeHahnRegular.constant 0 := by
    have hfdP : F.d = GCD369CubeHahnRegular.constant P.d :=
      GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.d
    rw [hd] at hfdP
    exact hfdP
  have hfc7 : F.c7 = GCD369CubeHahnRegular.constant 0 := by
    have hfc7P : F.c7 = GCD369CubeHahnRegular.constant P.c7 :=
      GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c7
    rw [hc7] at hfc7P
    exact hfc7P
  exact T.c5_eq_zero_before_transverse F rfl
    P.c5 P.c4 P.c3 P.c2 P.c1
    R.rho1 R.rho2 R.rho3 R.rho4 hfd hfc7
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

/-- Literal finite-pole form of complete weight-four routing. -/
theorem finite_c5_eq_zero_at_or_before_transverse
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
    (hc7 : S.faberConstantParameters.c7 = 0)
    (hle : 2 * (S.finiteFaberPoleData a hpole).scale.p ≤ T.delta) :
    S.faberConstantParameters.c5 = 0 := by
  let C := S.finiteCommonValueData a hpole
  let F := S.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  change 2 * F.scale.p ≤ T.delta at hle
  have hfd : F.d = GCD369CubeHahnRegular.constant 0 := by
    have hfdP : F.d = GCD369CubeHahnRegular.constant P.d :=
      GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.d
    rw [hd] at hfdP
    exact hfdP
  have hfc7 : F.c7 = GCD369CubeHahnRegular.constant 0 := by
    have hfc7P : F.c7 = GCD369CubeHahnRegular.constant P.c7 :=
      GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c7
    rw [hc7] at hfc7P
    exact hfc7P
  have hnd : C.normal.d = 0 := by
    have hndP : C.normal.d = GCD369CubeHahnRegular.constant P.d :=
      GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.d
    rw [hd] at hndP
    simpa using hndP
  have hnc7 : C.normal.c7 = 0 := by
    have hnc7P : C.normal.c7 = GCD369CubeHahnRegular.constant P.c7 :=
      GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c7
    rw [hc7] at hnc7P
    simpa using hnc7P
  exact T.c5_eq_zero_at_or_before_transverse F rfl
    P.c5 P.c4 P.c3 P.c2 P.c1
    R.rho1 R.rho2 R.rho3 R.rho4 hnd hnc7 hfd hfc7
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
  GCD369CubeHahnCommonValueData.TransverseScale.c5_eq_zero_before_transverse
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.c5_eq_zero_at_transverse
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.c5_eq_zero_at_or_before_transverse
#print axioms GCD369CubePolynomialSource.finite_c5_eq_zero_before_transverse
#print axioms
  GCD369CubePolynomialSource.finite_c5_eq_zero_at_or_before_transverse
