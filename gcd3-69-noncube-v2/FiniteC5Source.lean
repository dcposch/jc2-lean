import FiniteActiveSource

/-! # First `c5` Faber load at a finite common-cubic pole

The normal coordinates have already been factored at a prescribed positive
Hahn scale.  This file continues the source-facing active-load bridge by
proving that a weight-four `c5` constant, scaled to the square of that
monomial (so that `T.delta` represents half the weight-four scale), gives
exactly the four arbitrary-`c5` Kuranishi rows used by the audited algebraic
exclusion.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonValueData

theorem TransverseFactor.c5N1Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C5 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC5N1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -96 * (40 * C5 * S.u ^ 3 - 360 * C5 * S.v ^ 2 +
        243 * S.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
          486 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (GCD369CubeHahnRegular.constantCoeff T.Zn) -
          243 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    51840 * S.normal.sextic.scale.regular0 -
      8640 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 -
      4320 * S.normal.sextic.scale.regular3 ^ 2 +
      1680 * S.normal.sextic.scale.regular4 ^ 3
  change
    (729 * GCD369CubeFaberN1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C5 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff]
  have hload :
      ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C5 * P).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        C5 * GCD369CubeHahnRegular.constantCoeff P := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C5 P
  rw [hload]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C5 *
    (51840 * S.normal.sextic.scale.leading0 -
      8640 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading4 -
      4320 * S.normal.sextic.scale.leading3 ^ 2 +
      1680 * S.normal.sextic.scale.leading4 ^ 3) = _
  rw [S.ha0, S.ha2, S.ha3, S.ha4]
  dsimp only [GCD369CubeNormalRow1]
  ring

theorem TransverseFactor.c5N2Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C5 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC5N2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -864 * (40 * C5 * S.u ^ 2 * S.v +
        81 * S.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
          162 * S.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (GCD369CubeHahnRegular.constantCoeff T.Yn) -
          162 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
            (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    -25920 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular4 -
      25920 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 +
      15120 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4 ^ 2
  change
    (2187 * GCD369CubeFaberN2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C5 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C5 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change _ + C5 *
    (-25920 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading4 -
      25920 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading3 +
      15120 * S.normal.sextic.scale.leading3 *
          S.normal.sextic.scale.leading4 ^ 2) = _
  rw [S.ha1, S.ha2, S.ha3, S.ha4]
  dsimp only [GCD369CubeNormalRow2]
  ring

theorem TransverseFactor.c5N3Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C5 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC5N3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    -34560 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular3 -
      17280 * S.normal.sextic.scale.regular2 ^ 2 +
      14400 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 ^ 2 +
      17280 * S.normal.sextic.scale.regular3 ^ 2 *
        S.normal.sextic.scale.regular4 -
      2520 * S.normal.sextic.scale.regular4 ^ 4
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
      GCD369CubeHahnRegular.constant C5 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C5 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change _ + C5 *
    (-34560 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading3 -
      17280 * S.normal.sextic.scale.leading2 ^ 2 +
      14400 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading4 ^ 2 +
      17280 * S.normal.sextic.scale.leading3 ^ 2 *
          S.normal.sextic.scale.leading4 -
      2520 * S.normal.sextic.scale.leading4 ^ 4) = _
  rw [S.ha1, S.ha2, S.ha3, S.ha4]
  ring

theorem TransverseFactor.c5N4Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C5 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC5N4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (40 * C5 * S.u ^ 3 * S.v - 80 * C5 * S.v ^ 3 -
        243 * S.u * S.v *
          (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        162 * S.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) +
        324 * S.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        162 * S.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
        162 * S.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    -233280 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular2 +
      58320 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular4 ^ 2 +
      155520 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 +
      25920 * S.normal.sextic.scale.regular3 ^ 3 -
      45360 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4 ^ 3
  change
    (6561 * GCD369CubeFaberN4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C5 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C5 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change _ + C5 *
    (-233280 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading2 +
      58320 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading4 ^ 2 +
      155520 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading3 *
            S.normal.sextic.scale.leading4 +
      25920 * S.normal.sextic.scale.leading3 ^ 3 -
      45360 * S.normal.sextic.scale.leading3 *
          S.normal.sextic.scale.leading4 ^ 3) = _
  rw [S.ha1, S.ha2, S.ha3, S.ha4]
  dsimp only [GCD369CubeNormalRow4]
  ring

/-- Vanishing of the four literal quadratic Hahn coefficients is exactly
the source-facing arbitrary-`c5` Faber row packet. -/
theorem TransverseFactor.c5LeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C5 : k)
    (h1 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC5N1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC5N2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC5N3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC5N4
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeC5LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C5 := by
  dsimp [GCD369CubeC5LeadingFaberRowsAt]
  have hc := GCD369CubeFaberC5NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C5
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.c5N1Coeff C5]
    exact h1
  · rw [hc2, ← T.c5N2Coeff C5]
    exact h2
  · rw [hc3, ← T.c5N3Coeff C5]
    exact h3
  · rw [hc4, ← T.c5N4Coeff C5]
    exact h4

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c5N1Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c5N2Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c5N3Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c5N4Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c5LeadingFaberRowsAt
