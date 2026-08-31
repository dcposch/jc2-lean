import FiniteFanThroughC4
import FiniteC2EarlyNormal
import FiniteC2EarlyRouting
import FiniteTargetNormalizedParameters

/-! # The simple-root early-load fan through weight seven

After the first-target translation has put the source on the `c₃ = 0`
slice, the nonsingular common-cubic fan continues from `c4` to `c2`.
The zero-load alternative before weight seven is singular, while arrival of
the active `c2` load at or before the first transverse normal kills `c2`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- On the nonsingular common-cubic branch in the `c₃ = 0` gauge, the
recursive fan through weight seven forces `d`, `c7`, `c5`, `c4`, and `c2`
to vanish. -/
theorem TransverseScale.earlyLoads_zero_through_c2_of_discriminant_ne_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D C7 C5 C4 C2 C1 R1 R2 R3 R4 : k)
    (hdNormal : S.normal.d = GCD369CubeHahnRegular.constant D)
    (hc7Normal : S.normal.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5Normal : S.normal.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4Normal : S.normal.c4 = GCD369CubeHahnRegular.constant C4)
    (hd : F.d = GCD369CubeHahnRegular.constant D)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (hdisc : 4 * S.u ^ 3 + 27 * S.v ^ 2 ≠ 0) :
    D = 0 ∧ C7 = 0 ∧ C5 = 0 ∧ C4 = 0 ∧ C2 = 0 := by
  obtain ⟨hD, hC7, hC5, hC4⟩ :=
    T.earlyLoads_zero_through_c4_of_discriminant_ne_zero F hscale
      D C7 C5 C4 0 C2 C1 R1 R2 R3 R4
      hdNormal hc7Normal hc5Normal
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hdisc
  have hfd : F.d = GCD369CubeHahnRegular.constant 0 := by rw [hd, hD]
  have hfc7 : F.c7 = GCD369CubeHahnRegular.constant 0 := by rw [hc7, hC7]
  have hfc5 : F.c5 = GCD369CubeHahnRegular.constant 0 := by rw [hc5, hC5]
  have hfc4 : F.c4 = GCD369CubeHahnRegular.constant 0 := by rw [hc4, hC4]
  have hfd0 : F.d = 0 := by simpa using hfd
  have hfc70 : F.c7 = 0 := by simpa using hfc7
  have hfc50 : F.c5 = 0 := by simpa using hfc5
  have hfc40 : F.c4 = 0 := by simpa using hfc4
  have hfc30 : F.c3 = 0 := by simpa using hc3
  have hnd : S.normal.d = 0 := by rw [hdNormal, hD]; simp
  have hnc7 : S.normal.c7 = 0 := by rw [hc7Normal, hC7]; simp
  have hnc5 : S.normal.c5 = 0 := by rw [hc5Normal, hC5]; simp
  have hnc4 : S.normal.c4 = 0 := by rw [hc4Normal, hC4]; simp
  have hp_c2 : (7 * F.scale.p) / 2 ≤ T.delta := by
    by_contra hnot
    have hlt : T.delta < (7 * F.scale.p) / 2 := lt_of_not_ge hnot
    have hearly : 2 * T.delta < 7 * F.scale.p := by linarith
    exact hdisc (T.discriminant_zero_before_c2 F hscale
      hfd0 hfc70 hfc50 hfc40 hfc30 hearly)
  have hC2 : C2 = 0 := T.c2_eq_zero_at_or_before_transverse F hscale
    C2 C1 R1 R2 R3 R4 hnd hnc7 hnc5 hnc4
    hfd hfc7 hfc5 hfc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hp_c2
  exact ⟨hD, hC7, hC5, hC4, hC2⟩

end GCD369CubeHahnCommonValueData

namespace GCD369CubePolynomialSource

/-- Literal target-normalized form of the nonsingular early-load fan through
weight seven.  Faber uniqueness transports the result back to the original
source parameters. -/
theorem finite_targetNormalized_earlyLoads_zero_through_c2_of_discriminant_ne_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hd : S.faberConstantParameters.d = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 4)).order < 0)
    (T : (S.targetNormalizedSource.finiteCommonValueData a hpole).TransverseScale)
    (hdisc :
      4 * (S.targetNormalizedSource.finiteCommonValueData a hpole).u ^ 3 +
        27 * (S.targetNormalizedSource.finiteCommonValueData a hpole).v ^ 2 ≠ 0) :
    S.faberConstantParameters.d = 0 ∧
      S.faberConstantParameters.c7 = 0 ∧
      S.faberConstantParameters.c5 = 0 ∧
      S.faberConstantParameters.c4 = 0 ∧
      S.faberConstantParameters.c2 = 0 := by
  let U := S.targetNormalizedSource
  let C := U.finiteCommonValueData a hpole
  let F := U.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let Q := U.faberConstantParameters
  let R := U.faberFirstIntegralConstants
  obtain ⟨hQd, hQc7, _hQc6, hQc5, hQc4, hQc3, hQc2,
      _hQc1, _hQc0⟩ := S.targetNormalizedCanonicalParameters hd
  have hfan := T.earlyLoads_zero_through_c2_of_discriminant_ne_zero F rfl
    Q.d Q.c7 Q.c5 Q.c4 Q.c2 Q.c1 R.rho1 R.rho2 R.rho3 R.rho4
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a Q.d)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a Q.c7)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a Q.c5)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a Q.c4)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a Q.d)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a Q.c7)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a Q.c5)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a Q.c4)
    (by
      change GCD369CubeHahnRegular.ofRatFuncConstant a Q.c3 =
        GCD369CubeHahnRegular.constant 0
      rw [hQc3]
      exact GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a (0 : k))
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a Q.c2)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a Q.c1)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho1)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho2)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho3)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho4)
    hdisc
  rcases hfan with ⟨_hQd0, hQc70, hQc50, hQc40, hQc20⟩
  rw [hQc7] at hQc70
  rw [hQc5] at hQc50
  rw [hQc4] at hQc40
  rw [hQc2] at hQc20
  exact ⟨hd, hQc70, hQc50, hQc40, hQc20⟩

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.earlyLoads_zero_through_c2_of_discriminant_ne_zero
#print axioms
  GCD369CubePolynomialSource.finite_targetNormalized_earlyLoads_zero_through_c2_of_discriminant_ne_zero
