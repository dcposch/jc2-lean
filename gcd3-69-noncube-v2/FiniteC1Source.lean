import FiniteActiveSource

/-! # First `c1` Faber load at a finite common-cubic pole

The normal coordinates have already been factored at a prescribed positive
Hahn scale.  This file continues the source-facing active-load bridge by
proving that a `c1` constant, scaled to the square of that monomial (so
that `T.delta` represents half the load scale), gives exactly the four
arbitrary-`c1` Kuranishi rows used by the audited algebraic exclusion.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonValueData

theorem TransverseFactor.c1N1Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C1 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC1N1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      2592 * (8 * C1 * S.u -
        9 * S.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        18 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        9 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    10368 * S.normal.sextic.scale.regular4
  change
    (729 * GCD369CubeFaberN1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C1 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff]
  have hload :
      ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C1 * P).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        C1 * GCD369CubeHahnRegular.constantCoeff P := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C1 P
  rw [hload]
  dsimp only [P]
  simp only [map_mul, map_ofNat]
  change _ + C1 * (10368 * S.normal.sextic.scale.leading4) = _
  rw [S.ha4]
  dsimp only [GCD369CubeNormalRow1]
  ring

theorem TransverseFactor.c1N2Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C1 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC1N2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -7776 * (-8 * C1 * S.v +
        9 * S.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        18 * S.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        18 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    31104 * S.normal.sextic.scale.regular3
  change
    (2187 * GCD369CubeFaberN2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C1 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C1 P]
  dsimp only [P]
  simp only [map_mul, map_ofNat]
  change _ + C1 * (31104 * S.normal.sextic.scale.leading3) = _
  rw [S.ha3]
  dsimp only [GCD369CubeNormalRow2]
  ring

theorem TransverseFactor.c1N3Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C1 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC1N3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    41472 * S.normal.sextic.scale.regular2 -
      10368 * S.normal.sextic.scale.regular4 ^ 2
  have hzero :
      (243 * GCD369CubeFaberN3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        31104 * GCD369CubeNormalRow3
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v := by
    calc
      _ = (243 : k) *
          (GCD369CubeFaberN3
            S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
            S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
            S.normal.sextic.scale.regular4).1.coeff
              (((2 : ℕ) : ℚ) * T.delta) :=
        GCD369CubeHahnRegular.coeff_nat_mul 243 _ _
      _ = _ := by rw [T.zeroHighN3Coeff]; ring
  change
    (243 * GCD369CubeFaberN3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C1 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C1 P]
  dsimp only [P]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  change _ + C1 *
    (41472 * S.normal.sextic.scale.leading2 -
      10368 * S.normal.sextic.scale.leading4 ^ 2) = _
  rw [S.ha2, S.ha4]
  ring

theorem TransverseFactor.c1N4Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C1 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC1N4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      23328 * (8 * C1 * S.u * S.v +
        27 * S.u * S.v *
          (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        18 * S.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        36 * S.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) -
        18 * S.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 -
        18 * S.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    279936 * S.normal.sextic.scale.regular1 -
      93312 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4
  change
    (6561 * GCD369CubeFaberN4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C1 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C1 P]
  dsimp only [P]
  simp only [map_sub, map_mul, map_ofNat]
  change _ + C1 *
    (279936 * S.normal.sextic.scale.leading1 -
      93312 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4) = _
  rw [S.ha1, S.ha3, S.ha4]
  dsimp only [GCD369CubeNormalRow4]
  ring

/-- Vanishing of the four literal quadratic Hahn coefficients is exactly
the source-facing arbitrary-`c1` Faber row packet. -/
theorem TransverseFactor.c1LeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C1 : k)
    (h1 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC1N1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC1N2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC1N3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC1N4
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeC1LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C1 := by
  dsimp [GCD369CubeC1LeadingFaberRowsAt]
  have hc := GCD369CubeFaberC1NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C1
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.c1N1Coeff C1]
    exact h1
  · rw [hc2, ← T.c1N2Coeff C1]
    exact h2
  · rw [hc3, ← T.c1N3Coeff C1]
    exact h3
  · rw [hc4, ← T.c1N4Coeff C1]
    exact h4

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c1N1Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c1N2Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c1N3Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c1N4Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c1LeadingFaberRowsAt
