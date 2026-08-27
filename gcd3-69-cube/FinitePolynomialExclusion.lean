import FiniteSingularFanThroughRho2
import FiniteExactSquareExclusion
import FiniteFanLaterHandoff

/-! # Finite-pole exclusion of a nonconstant cube source

Every literal nonconstant source has a finite normalized-coefficient pole.
The exact-square normal fallback is impossible, so the pole has a first
transverse scale.  The singular timing fan kills all Faber loads through
`rho2`, and the boundary-free later-fibre theorem supplies the contradiction.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- A finite normalized-coefficient pole always has a genuine first
transverse scale: otherwise all three exact normals vanish and the normalized
sextic is a forbidden cubic square. -/
theorem finite_transverseScale_nonempty
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    Nonempty (S.finiteCommonValueData a hpole).TransverseScale := by
  let C := S.finiteCommonValueData a hpole
  by_cases h2 : C.normal2 = 0
  · by_cases h1 : C.normal1 = 0
    · by_cases h0 : C.normal0 = 0
      · exact False.elim (S.finite_exactNormals_zero_inconsistent
          a hpole h2 h1 h0)
      · exact ⟨C.transverseScale (Or.inr (Or.inr h0))⟩
    · exact ⟨C.transverseScale (Or.inr (Or.inl h1))⟩
  · exact ⟨C.transverseScale (Or.inl h2)⟩

/-- The first Faber load vanishes at any finite pole of a literal source. -/
theorem finite_source_forces_d_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    S.faberConstantParameters.d = 0 := by
  obtain ⟨T⟩ := S.finite_transverseScale_nonempty a hpole
  exact S.finite_singular_source_forces_d_eq_zero a hpole T

/-- Literal target-normalized form of the complete timing fan.  No
discriminant assumption remains: each possible first nonzero load is
excluded directly by its source-facing singular assembly. -/
theorem finite_targetNormalized_singular_earlyLoads_zero_through_rho2
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
    (T : (S.targetNormalizedSource.finiteCommonValueData a hpole).TransverseScale) :
    S.faberConstantParameters.d = 0 ∧
      S.faberConstantParameters.c7 = 0 ∧
      S.faberConstantParameters.c5 = 0 ∧
      S.faberConstantParameters.c4 = 0 ∧
      S.faberConstantParameters.c2 = 0 ∧
      S.faberConstantParameters.c1 = 0 ∧
      S.targetNormalizedSource.faberFirstIntegralConstants.rho1 = 0 ∧
      S.targetNormalizedSource.faberFirstIntegralConstants.rho2 = 0 := by
  let U := S.targetNormalizedSource
  let F := U.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let Q := U.faberConstantParameters
  let R := U.faberFirstIntegralConstants
  obtain ⟨hQd, hQc7, _hQc6, hQc5, hQc4, hQc3, hQc2,
      hQc1, _hQc0⟩ := S.targetNormalizedCanonicalParameters hd
  have hfan := T.singular_earlyLoads_zero_through_rho2 F rfl
    Q.d Q.c7 Q.c5 Q.c4 Q.c2 Q.c1 R.rho1 R.rho2 R.rho3 R.rho4
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
  rcases hfan with ⟨_hQd0, hQc70, hQc50, hQc40, hQc20, hQc10, hR10, hR20⟩
  rw [hQc7] at hQc70
  rw [hQc5] at hQc50
  rw [hQc4] at hQc40
  rw [hQc2] at hQc20
  rw [hQc1, hQc70] at hQc10
  simp at hQc10
  exact ⟨hd, hQc70, hQc50, hQc40, hQc20, hQc10, hR10, hR20⟩

/-- A literal `(6,9)` polynomial cube source cannot have a nonconstant
common cube root. -/
theorem nonconstant_cube_root_impossible
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : 0 < S.s.natDegree) :
    False := by
  obtain ⟨a0, hpole0⟩ := S.finiteNormalizedCoeffPole_of_nonconstant hsdegree
  have hd : S.faberConstantParameters.d = 0 :=
    S.finite_source_forces_d_eq_zero a0 hpole0
  let U := S.targetNormalizedSource
  have hsdegreeU : 0 < U.s.natDegree := by
    simpa [U, targetNormalizedSource] using hsdegree
  obtain ⟨a, hpole⟩ := U.finiteNormalizedCoeffPole_of_nonconstant hsdegreeU
  obtain ⟨T⟩ := U.finite_transverseScale_nonempty a hpole
  obtain ⟨_hd0, hc7, hc5, hc4, hc2, hc1, hrho1, hrho2⟩ :=
    S.finite_targetNormalized_singular_earlyLoads_zero_through_rho2
      a hd hpole T
  obtain ⟨h1, h2, _h3, _h4⟩ := S.targetNormalizedFirstIntegralConstants_eq hd
  exact S.targetNormalizedLater_empty_without_boundary hsdegree hd
    hc7 hc5 hc4 hc2
    (S.targetNormalizedLater_c1bar_of_earlyLoads hc7 hc1)
    (h1.trans hrho1) (h2.trans hrho2)

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.finite_transverseScale_nonempty
#print axioms GCD369CubePolynomialSource.finite_source_forces_d_eq_zero
#print axioms
  GCD369CubePolynomialSource.finite_targetNormalized_singular_earlyLoads_zero_through_rho2
#print axioms GCD369CubePolynomialSource.nonconstant_cube_root_impossible
