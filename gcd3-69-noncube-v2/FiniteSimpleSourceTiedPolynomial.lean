import FiniteSimpleSourceTiedFromSource
import FiniteLateDoublePolynomial

/-! # Polynomial-source wrapper for the tied late simple-root obstruction -/

noncomputable section

namespace GCD369CubePolynomialSource

/-- Canonical finite-place data exclude the tied simple-root residue packet
once the canonical weight-one parameter has vanished. -/
theorem finite_simpleRoot_tied_inconsistent_from_source
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (T : (S.finiteCommonValueData a hpole).TransverseScale)
    (hd : S.faberConstantParameters.d = 0)
    (hp : (S.finiteFaberPoleData a hpole).scale.p = 3 * T.delta) :
    False := by
  let C := S.finiteCommonValueData a hpole
  let F := S.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  have hfd : F.d = 0 := by
    have hfdP : F.d = GCD369CubeHahnRegular.constant P.d :=
      GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.d
    rw [hd] at hfdP
    simpa using hfdP
  change F.scale.p = 3 * T.delta at hp
  obtain ⟨r0, hr0, hA0, hu, hv, hY, hZ, hx⟩ :=
    S.finite_source_coordinate_is_simpleRoot_at_or_after_cubic a hpole T
      (by rw [← hp])
  exact T.factor.simpleRoot_tied_inconsistent_from_source F rfl
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
    (by simpa only [GCD369CubeHahnCommonValueData.TransverseScale.factor]
      using hp)
    r0 (GCD369CubeHahnRegular.constantCoeff T.Xn) hr0 hA0
    (by rw [C.constantCoeff_cubicU]; exact hu)
    (by rw [C.constantCoeff_cubicV]; exact hv)
    hx rfl
    (by simpa only [GCD369CubeHahnCommonValueData.TransverseScale.factor]
      using hY)
    (by simpa only [GCD369CubeHahnCommonValueData.TransverseScale.factor]
      using hZ)

end GCD369CubePolynomialSource

#print axioms
  GCD369CubePolynomialSource.finite_simpleRoot_tied_inconsistent_from_source
