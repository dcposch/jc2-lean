import FiniteEarlyLoadTied
import FiniteC7EarlyRouting
import FiniteC5EarlyRouting
import FiniteC4EarlyRouting
import FiniteC4EarlyNormal

/-! # The simple-root early-load fan through weight five

If the limiting common cubic is nonsingular, every zero-load alternative
before weights `1, 2, 4, 5` is impossible.  The corresponding active load
must therefore arrive no later than the first transverse normal, and the
four verified routing theorems successively kill `d`, `c7`, `c5`, and `c4`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- On the nonsingular common-cubic branch, the complete recursive fan
through the weight-five load forces the first four active parameters to
vanish. -/
theorem TransverseScale.earlyLoads_zero_through_c4_of_discriminant_ne_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hdNormal : S.normal.d = GCD369CubeHahnRegular.constant D)
    (hc7Normal : S.normal.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5Normal : S.normal.c5 = GCD369CubeHahnRegular.constant C5)
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
    (hdisc : 4 * S.u ^ 3 + 27 * S.v ^ 2 ≠ 0) :
    D = 0 ∧ C7 = 0 ∧ C5 = 0 ∧ C4 = 0 := by
  have hp_d : F.scale.p ≤ 2 * T.delta := by
    by_contra hnot
    have hearly : 2 * T.delta < F.scale.p := lt_of_not_ge hnot
    exact hdisc (T.discriminant_zero_before_d F hscale
      D C7 C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hearly)
  have hD : D = 0 := T.d_eq_zero_at_or_before_transverse F hscale
    D C7 C5 C4 C3 C2 C1 R1 R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hp_d
  have hfd : F.d = GCD369CubeHahnRegular.constant 0 := by
    rw [hd, hD]
  have hfd0 : F.d = 0 := by simpa using hfd
  have hnd : S.normal.d = 0 := by
    rw [hdNormal, hD]
    simp
  have hp_c7 : F.scale.p ≤ T.delta := by
    by_contra hnot
    have hlt : T.delta < F.scale.p := lt_of_not_ge hnot
    have hearly : 2 * T.delta < 2 * F.scale.p := by linarith
    exact hdisc (T.discriminant_zero_before_c7 F hscale hfd0 hearly)
  have hC7 : C7 = 0 := T.c7_eq_zero_at_or_before_transverse F hscale
    C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 hnd
    hfd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hp_c7
  have hfc7 : F.c7 = GCD369CubeHahnRegular.constant 0 := by
    rw [hc7, hC7]
  have hfc70 : F.c7 = 0 := by simpa using hfc7
  have hnc7 : S.normal.c7 = 0 := by
    rw [hc7Normal, hC7]
    simp
  have hp_c5 : 2 * F.scale.p ≤ T.delta := by
    by_contra hnot
    have hlt : T.delta < 2 * F.scale.p := lt_of_not_ge hnot
    have hearly : 2 * T.delta < 4 * F.scale.p := by linarith
    exact hdisc (T.discriminant_zero_before_c5 F hscale hfd0 hfc70 hearly)
  have hC5 : C5 = 0 := T.c5_eq_zero_at_or_before_transverse F hscale
    C5 C4 C3 C2 C1 R1 R2 R3 R4 hnd hnc7
    hfd hfc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hp_c5
  have hfc5 : F.c5 = GCD369CubeHahnRegular.constant 0 := by
    rw [hc5, hC5]
  have hfc50 : F.c5 = 0 := by simpa using hfc5
  have hnc5 : S.normal.c5 = 0 := by
    rw [hc5Normal, hC5]
    simp
  have hp_c4 : (5 * F.scale.p) / 2 ≤ T.delta := by
    by_contra hnot
    have hlt : T.delta < (5 * F.scale.p) / 2 := lt_of_not_ge hnot
    have hearly : 2 * T.delta < 5 * F.scale.p := by linarith
    exact hdisc (T.discriminant_zero_before_c4 F hscale
      hfd0 hfc70 hfc50 hearly)
  have hC4 : C4 = 0 := T.c4_eq_zero_at_or_before_transverse F hscale
    C4 C3 C2 C1 R1 R2 R3 R4 hnd hnc7 hnc5
    hfd hfc7 hfc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hp_c4
  exact ⟨hD, hC7, hC5, hC4⟩

end GCD369CubeHahnCommonValueData

namespace GCD369CubePolynomialSource

/-- Literal finite-pole form of the nonsingular early-load fan through
weight five. -/
theorem finite_earlyLoads_zero_through_c4_of_discriminant_ne_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (T : (S.finiteCommonValueData a hpole).TransverseScale)
    (hdisc :
      4 * (S.finiteCommonValueData a hpole).u ^ 3 +
        27 * (S.finiteCommonValueData a hpole).v ^ 2 ≠ 0) :
    S.faberConstantParameters.d = 0 ∧
      S.faberConstantParameters.c7 = 0 ∧
      S.faberConstantParameters.c5 = 0 ∧
      S.faberConstantParameters.c4 = 0 := by
  let C := S.finiteCommonValueData a hpole
  let F := S.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  exact T.earlyLoads_zero_through_c4_of_discriminant_ne_zero F rfl
    P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
    R.rho1 R.rho2 R.rho3 R.rho4
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.d)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c7)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c5)
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
    hdisc

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.earlyLoads_zero_through_c4_of_discriminant_ne_zero
#print axioms
  GCD369CubePolynomialSource.finite_earlyLoads_zero_through_c4_of_discriminant_ne_zero
