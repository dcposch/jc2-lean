import FiniteFanThroughRho2
import FaberLaterSource
import FaberLaterPolynomialExclusion

/-! # Handoff from the nonsingular early-load fan to the later fibre

The target-normalized fan through weight eleven kills every early Faber load
on a nonsingular finite pole.  Uniqueness of the Faber parameters identifies
those vanishing first integrals with the explicit `d = c₃ = 0` constants, so
the same pole lands on the later `(rho3, rho4)` fibre.  Retaining the original
DS boundary on the fully zero specialization then excludes the source.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- The explicit target-normalized first integrals agree with the canonical
peeling of the translated source.  Only the four invariants enter the later
fibre, so the unused normal-form bookkeeping parameters are discarded. -/
theorem targetNormalizedFirstIntegralConstants_eq
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hd : S.faberConstantParameters.d = 0) :
    (S.targetNormalizedFirstIntegralConstants hd).rho1 =
      S.targetNormalizedSource.faberFirstIntegralConstants.rho1 ∧
    (S.targetNormalizedFirstIntegralConstants hd).rho2 =
      S.targetNormalizedSource.faberFirstIntegralConstants.rho2 ∧
    (S.targetNormalizedFirstIntegralConstants hd).rho3 =
      S.targetNormalizedSource.faberFirstIntegralConstants.rho3 ∧
    (S.targetNormalizedFirstIntegralConstants hd).rho4 =
      S.targetNormalizedSource.faberFirstIntegralConstants.rho4 := by
  let U := S.targetNormalizedSource
  let N := S.targetNormalizedFaberNormalForm hd
  let R := S.targetNormalizedFirstIntegralConstants hd
  let Q := U.faberFirstIntegralConstants
  obtain ⟨hdN, hc7N, _hc6N, hc5N, hc4N, hc3N, hc2N, hc1N, _hc0N⟩ :=
    GCD369CubeFaberNormalForm.parameters_unique U.faberNormalForm N
  have h1 : R.rho1 = Q.rho1 := by
    apply RatFunc.C_injective
    have hQ := Q.hrho1
    have hR := R.hrho1
    rw [hdN, hc7N, hc5N, hc4N, hc3N, hc2N, hc1N] at hQ
    exact hR.symm.trans hQ
  have h2 : R.rho2 = Q.rho2 := by
    apply RatFunc.C_injective
    have hQ := Q.hrho2
    have hR := R.hrho2
    rw [hdN, hc7N, hc5N, hc4N, hc3N, hc2N, hc1N] at hQ
    exact hR.symm.trans hQ
  have h3 : R.rho3 = Q.rho3 := by
    apply RatFunc.C_injective
    have hQ := Q.hrho3
    have hR := R.hrho3
    rw [hdN, hc7N, hc5N, hc4N, hc3N, hc2N, hc1N] at hQ
    exact hR.symm.trans hQ
  have h4 : R.rho4 = Q.rho4 := by
    apply RatFunc.C_injective
    have hQ := Q.hrho4
    have hR := R.hrho4
    rw [hdN, hc7N, hc5N, hc4N, hc3N, hc2N, hc1N] at hQ
    exact hR.symm.trans hQ
  exact ⟨h1, h2, h3, h4⟩

/-- After the nonsingular fan through weight eleven, the barred weight-eight
parameter vanishes because both `c1` and `c7` are already zero. -/
theorem targetNormalizedLater_c1bar_of_earlyLoads
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hc7 : S.faberConstantParameters.c7 = 0)
    (hc1 : S.faberConstantParameters.c1 = 0) :
    S.faberConstantParameters.c1 -
      7 * S.faberConstantParameters.c7 *
        S.faberConstantParameters.c3 / 9 = 0 := by
  rw [hc1, hc7]
  simp

/-- Literal later-fibre handoff of the nonsingular early-load fan through
weight eleven.  The resulting source is the complete later Faber invariant
source attached to the original polynomial data. -/
noncomputable def finite_targetNormalizedLaterInvariantSource_of_discriminant_ne_zero
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
    GCD369CubeLaterInvariantSource (RatFunc k) := by
  obtain ⟨_hd0, hc7, hc5, hc4, hc2, hc1, hrho1, hrho2⟩ :=
    S.finite_targetNormalized_earlyLoads_zero_through_rho2_of_discriminant_ne_zero
      a hd hpole T hdisc
  obtain ⟨h1, h2, _h3, _h4⟩ := S.targetNormalizedFirstIntegralConstants_eq hd
  exact S.targetNormalizedLaterInvariantSource hd hc7 hc5 hc4 hc2
    (S.targetNormalizedLater_c1bar_of_earlyLoads hc7 hc1)
    (h1.trans hrho1) (h2.trans hrho2)

/-- On a nonsingular finite pole of the target-normalized source, the
early-load fan through weight eleven lands on the later Faber fibre, which
is empty as soon as the original DS boundary is supplied on the fully zero
specialization. -/
theorem finite_targetNormalizedLater_empty_of_discriminant_ne_zero
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
        27 * (S.targetNormalizedSource.finiteCommonValueData a hpole).v ^ 2 ≠ 0)
    (boundary :
      6 * (S.targetNormalizedFirstIntegralConstants hd).rho3 = 0 →
      6 * (S.targetNormalizedFirstIntegralConstants hd).rho4 = 0 →
      GCD369CubeDSBoundarySource k) : False := by
  obtain ⟨_hd0, hc7, hc5, hc4, hc2, hc1, hrho1, hrho2⟩ :=
    S.finite_targetNormalized_earlyLoads_zero_through_rho2_of_discriminant_ne_zero
      a hd hpole T hdisc
  obtain ⟨h1, h2, _h3, _h4⟩ := S.targetNormalizedFirstIntegralConstants_eq hd
  exact S.targetNormalizedLater_empty hd hc7 hc5 hc4 hc2
    (S.targetNormalizedLater_c1bar_of_earlyLoads hc7 hc1)
    (h1.trans hrho1) (h2.trans hrho2) boundary

/-- Boundary-free literal endpoint of the nonsingular fan.  The finite
original-polynomial boundary now eliminates the zero-invariant DS sheet
internally, so a nonconstant source cannot have such a pole. -/
theorem finite_targetNormalizedLater_empty_without_boundary_of_discriminant_ne_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k)
    (hsdegree : 0 < S.s.natDegree) (a : k)
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
    False := by
  obtain ⟨_hd0, hc7, hc5, hc4, hc2, hc1, hrho1, hrho2⟩ :=
    S.finite_targetNormalized_earlyLoads_zero_through_rho2_of_discriminant_ne_zero
      a hd hpole T hdisc
  obtain ⟨h1, h2, _h3, _h4⟩ := S.targetNormalizedFirstIntegralConstants_eq hd
  exact S.targetNormalizedLater_empty_without_boundary hsdegree hd
    hc7 hc5 hc4 hc2
    (S.targetNormalizedLater_c1bar_of_earlyLoads hc7 hc1)
    (h1.trans hrho1) (h2.trans hrho2)

end GCD369CubePolynomialSource

#print axioms
  GCD369CubePolynomialSource.targetNormalizedFirstIntegralConstants_eq
#print axioms
  GCD369CubePolynomialSource.finite_targetNormalizedLaterInvariantSource_of_discriminant_ne_zero
#print axioms
  GCD369CubePolynomialSource.finite_targetNormalizedLater_empty_of_discriminant_ne_zero
#print axioms
  GCD369CubePolynomialSource.finite_targetNormalizedLater_empty_without_boundary_of_discriminant_ne_zero
