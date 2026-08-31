import FiniteActiveSource

/-! # First `c4` Faber load at a finite common-cubic pole

The normal coordinates have already been factored at a prescribed positive
Hahn scale.  This file continues the source-facing active-load bridge by
proving that a weight-two `c4` constant, scaled to the square of that
monomial, gives exactly the four arbitrary-`c4` Kuranishi rows used by the
audited algebraic exclusion.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonValueData

theorem TransverseFactor.c4N1Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C4 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC4N1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C4)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      864 * (32 * C4 * S.u * S.v - 27 * S.u *
        (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        54 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        27 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    41472 * S.normal.sextic.scale.regular1 -
      13824 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4
  change
    (729 * GCD369CubeFaberN1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C4 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff]
  have hload :
      ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C4 * P).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        C4 * GCD369CubeHahnRegular.constantCoeff P := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C4 P
  rw [hload]
  dsimp only [P]
  simp only [map_sub, map_mul, map_ofNat]
  change _ + C4 *
    (41472 * S.normal.sextic.scale.leading1 -
      13824 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4) = _
  simp only [S.ha1, S.ha3, S.ha4]
  dsimp only [GCD369CubeNormalRow1]
  ring

theorem TransverseFactor.c4N2Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C4 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC4N2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C4)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -288 * (32 * C4 * S.u ^ 3 - 144 * C4 * S.v ^ 2 +
        243 * S.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
          486 * S.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (GCD369CubeHahnRegular.constantCoeff T.Yn) -
          486 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
            (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    124416 * S.normal.sextic.scale.regular0 -
      41472 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 -
      20736 * S.normal.sextic.scale.regular3 ^ 2 +
      9216 * S.normal.sextic.scale.regular4 ^ 3
  change
    (2187 * GCD369CubeFaberN2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C4 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C4 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C4 *
    (124416 * S.normal.sextic.scale.leading0 -
      41472 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading4 -
      20736 * S.normal.sextic.scale.leading3 ^ 2 +
      9216 * S.normal.sextic.scale.leading4 ^ 3) = _
  simp only [S.ha0, S.ha2, S.ha3, S.ha4]
  dsimp only [GCD369CubeNormalRow2]
  ring

theorem TransverseFactor.c4N3Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C4 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC4N3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C4)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    -27648 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular4 -
      55296 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 +
      27648 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4 ^ 2
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
      GCD369CubeHahnRegular.constant C4 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C4 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change _ + C4 *
    (-27648 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading4 -
      55296 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading3 +
      27648 * S.normal.sextic.scale.leading3 *
          S.normal.sextic.scale.leading4 ^ 2) = _
  simp only [S.ha1, S.ha2, S.ha3, S.ha4]
  ring

theorem TransverseFactor.c4N4Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C4 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC4N4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C4)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (8 * C4 * S.u ^ 4 - 96 * C4 * S.u * S.v ^ 2 -
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
    -186624 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular3 -
      186624 * S.normal.sextic.scale.regular2 ^ 2 +
      124416 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 ^ 2 +
      124416 * S.normal.sextic.scale.regular3 ^ 2 *
        S.normal.sextic.scale.regular4 -
      20736 * S.normal.sextic.scale.regular4 ^ 4
  change
    (6561 * GCD369CubeFaberN4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C4 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C4 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change _ + C4 *
    (-186624 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading3 -
      186624 * S.normal.sextic.scale.leading2 ^ 2 +
      124416 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading4 ^ 2 +
      124416 * S.normal.sextic.scale.leading3 ^ 2 *
          S.normal.sextic.scale.leading4 -
      20736 * S.normal.sextic.scale.leading4 ^ 4) = _
  simp only [S.ha1, S.ha2, S.ha3, S.ha4]
  dsimp only [GCD369CubeNormalRow4]
  ring

/-- Vanishing of the four literal quadratic Hahn coefficients is exactly
the source-facing arbitrary-`c4` Faber row packet. -/
theorem TransverseFactor.c4LeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C4 : k)
    (h1 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC4N1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C4)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC4N2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C4)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC4N3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C4)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC4N4
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C4)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeC4LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C4 := by
  dsimp [GCD369CubeC4LeadingFaberRowsAt]
  have hc := GCD369CubeFaberC4NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C4
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.c4N1Coeff C4]
    exact h1
  · rw [hc2, ← T.c4N2Coeff C4]
    exact h2
  · rw [hc3, ← T.c4N3Coeff C4]
    exact h3
  · rw [hc4, ← T.c4N4Coeff C4]
    exact h4

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c4N1Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c4N2Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c4N3Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c4N4Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c4LeadingFaberRowsAt
