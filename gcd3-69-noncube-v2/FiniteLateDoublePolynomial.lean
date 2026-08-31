import FiniteLateDoubleSource

/-! # Polynomial-source wrapper for the late zero-load simple root

Literal Faber constants from a polynomial source instantiate every regular
parameter of `TransverseScale.source_coordinate_is_simpleRoot_at_or_after_cubic`.
The first-jet scale bound `3 * delta ≤ p` remains a hypothesis.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- Canonical finite-place data reduce the late zero-load root split to the
recovered simple-root residue packet; only the cubic-scale inequality on the
first transverse jet remains as a hypothesis. -/
theorem finite_source_coordinate_is_simpleRoot_at_or_after_cubic
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (T : (S.finiteCommonValueData a hpole).TransverseScale)
    (hp : 3 * T.delta ≤ (S.finiteFaberPoleData a hpole).scale.p) :
    let C := S.finiteCommonValueData a hpole
    let x := GCD369CubeHahnRegular.constantCoeff
      C.normal.sextic.regularX
    ∃ r : k, r ≠ 0 ∧
      GCD369CubeHahnRegular.constantCoeff T.Xn ≠ 0 ∧
      C.u = -3 * r ^ 2 ∧ C.v = 2 * r ^ 3 ∧
      GCD369CubeHahnRegular.constantCoeff T.Yn =
        r * GCD369CubeHahnRegular.constantCoeff T.Xn ∧
      GCD369CubeHahnRegular.constantCoeff T.Zn =
        -2 * r ^ 2 * GCD369CubeHahnRegular.constantCoeff T.Xn ∧
      x = -2 * r := by
  dsimp only
  let C := S.finiteCommonValueData a hpole
  let F := S.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  change 3 * T.delta ≤ F.scale.p at hp
  change
    let x := GCD369CubeHahnRegular.constantCoeff
      C.normal.sextic.regularX
    ∃ r : k, r ≠ 0 ∧
      GCD369CubeHahnRegular.constantCoeff T.Xn ≠ 0 ∧
      C.u = -3 * r ^ 2 ∧ C.v = 2 * r ^ 3 ∧
      GCD369CubeHahnRegular.constantCoeff T.Yn =
        r * GCD369CubeHahnRegular.constantCoeff T.Xn ∧
      GCD369CubeHahnRegular.constantCoeff T.Zn =
        -2 * r ^ 2 * GCD369CubeHahnRegular.constantCoeff T.Xn ∧
      x = -2 * r
  exact T.source_coordinate_is_simpleRoot_at_or_after_cubic F rfl
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
    hp

end GCD369CubePolynomialSource

#print axioms
  GCD369CubePolynomialSource.finite_source_coordinate_is_simpleRoot_at_or_after_cubic
