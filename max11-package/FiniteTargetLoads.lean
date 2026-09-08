import FiniteActiveSource

/-! # First rho1/rho2 target loads at a finite common-cubic pole

The normal coordinates have already been factored at a prescribed positive
Hahn scale.  This file records the source-facing first-`rho1` and first-`rho2`
packets: four primitive zero-high numerator coefficients at exponent
`2 * delta` are exactly the arbitrary-`T` Faber rows used by the audited
algebraic exclusion.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonValueData

/-- The four primitive zero-high Hahn coefficients, with first-row value
`62208 * R` and the remaining three rows zero, are exactly the source-facing
first `rho1` Faber row packet on the residue jet. -/
theorem TransverseFactor.rhoOneLeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (R : k)
    (h1 : (729 * GCD369CubeFaberN1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 62208 * R)
    (h2 : (2187 * GCD369CubeFaberN2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : (GCD369CubeFaberN3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : (6561 * GCD369CubeFaberN4
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeRhoOneLeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v R := by
  dsimp [GCD369CubeRhoOneLeadingFaberRowsAt]
  have hc := GCD369CubeFaberCommonNormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.zeroHighN1Coeff]
    exact h1
  · rw [hc2, ← T.zeroHighN2Coeff]
    exact h2
  · rw [hc3, ← T.zeroHighN3Coeff]
    exact h3
  · rw [hc4, ← T.zeroHighN4Coeff]
    exact h4

/-- The four primitive zero-high Hahn coefficients, with second-row value
`186624 * R` and the remaining three rows zero, are exactly the source-facing
first `rho2` Faber row packet on the residue jet. -/
theorem TransverseFactor.rhoTwoLeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (R : k)
    (h1 : (729 * GCD369CubeFaberN1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : (2187 * GCD369CubeFaberN2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 186624 * R)
    (h3 : (GCD369CubeFaberN3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : (6561 * GCD369CubeFaberN4
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeRhoTwoLeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v R := by
  dsimp [GCD369CubeRhoTwoLeadingFaberRowsAt]
  have hc := GCD369CubeFaberCommonNormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.zeroHighN1Coeff]
    exact h1
  · rw [hc2, ← T.zeroHighN2Coeff]
    exact h2
  · rw [hc3, ← T.zeroHighN3Coeff]
    exact h3
  · rw [hc4, ← T.zeroHighN4Coeff]
    exact h4

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.rhoOneLeadingFaberRowsAt
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.rhoTwoLeadingFaberRowsAt
