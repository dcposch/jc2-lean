import FiniteSimpleSourceStrictFromSource
import FiniteLateDoublePolynomial

/-! # Polynomial-source wrapper for the strict late simple-root obstruction

Literal Faber constants from a polynomial source instantiate every regular
parameter of `TransverseFactor.simpleRoot_strictLate_inconsistent_from_source`.
The first-jet scale bound `3 * delta < p` remains a hypothesis.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- Canonical finite-place data exclude the remaining simple-root residue
packet in the strict branch; only the cubic-scale inequality
`3 * delta < p` on the first transverse jet remains as a hypothesis. -/
theorem finite_simpleRoot_strictLate_inconsistent_from_source
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (T : (S.finiteCommonValueData a hpole).TransverseScale)
    (hp : 3 * T.delta < (S.finiteFaberPoleData a hpole).scale.p) :
    False := by
  let C := S.finiteCommonValueData a hpole
  let F := S.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  change 3 * T.delta < F.scale.p at hp
  obtain ⟨r0, hr0, hA0, hu, hv, hY, hZ, hx⟩ :=
    S.finite_source_coordinate_is_simpleRoot_at_or_after_cubic a hpole T
      (le_of_lt hp)
  exact T.factor.simpleRoot_strictLate_inconsistent_from_source F rfl
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
  GCD369CubePolynomialSource.finite_simpleRoot_strictLate_inconsistent_from_source
