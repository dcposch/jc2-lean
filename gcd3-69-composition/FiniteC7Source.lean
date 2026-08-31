import FiniteActiveSource

/-! # First `c7` Faber load at a finite common-cubic pole

The normal coordinates have already been factored at a prescribed positive
Hahn scale.  This file continues the source-facing active-load bridge by
proving that a weight-two `c7` constant, scaled to the square of that
monomial, gives exactly the four arbitrary-`c7` Kuranishi rows used by the
audited algebraic exclusion.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonValueData

theorem TransverseFactor.c7N1Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -32 * (56 * C7 * S.u ^ 4 - 1008 * C7 * S.u * S.v ^ 2 +
        GCD369CubeNormalRow1
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    12096 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular4 +
      12096 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular3 +
      6048 * S.normal.sextic.scale.regular2 ^ 2 -
      5040 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 ^ 2 -
      5040 * S.normal.sextic.scale.regular3 ^ 2 *
        S.normal.sextic.scale.regular4 +
      770 * S.normal.sextic.scale.regular4 ^ 4
  change
    (729 * GCD369CubeFaberN1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff]
  have hload :
      ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C7 * P).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        C7 * GCD369CubeHahnRegular.constantCoeff P := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P
  rw [hload]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (12096 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading4 +
      12096 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading3 +
      6048 * S.normal.sextic.scale.leading2 ^ 2 -
      5040 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading4 ^ 2 -
      5040 * S.normal.sextic.scale.leading3 ^ 2 *
          S.normal.sextic.scale.leading4 +
      770 * S.normal.sextic.scale.leading4 ^ 4) = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

theorem TransverseFactor.c7N2Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -96 * (224 * C7 * S.u ^ 3 * S.v - 336 * C7 * S.v ^ 3 +
        729 * S.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
          1458 * S.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (GCD369CubeHahnRegular.constantCoeff T.Yn) -
          1458 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
            (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    36288 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular3 +
      36288 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular2 -
      15120 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular4 ^ 2 -
      30240 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
      5040 * S.normal.sextic.scale.regular3 ^ 3 +
      9240 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4 ^ 3
  change
    (2187 * GCD369CubeFaberN2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (36288 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading3 +
      36288 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading2 -
      15120 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading4 ^ 2 -
      30240 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading3 *
            S.normal.sextic.scale.leading4 -
      5040 * S.normal.sextic.scale.leading3 ^ 3 +
      9240 * S.normal.sextic.scale.leading3 *
          S.normal.sextic.scale.leading4 ^ 3) = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  dsimp only [GCD369CubeNormalRow2]
  ring

theorem TransverseFactor.c7N3Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    48384 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular2 -
      12096 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular4 ^ 2 +
      24192 * S.normal.sextic.scale.regular1 ^ 2 -
      32256 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
      16128 * S.normal.sextic.scale.regular2 ^ 2 *
        S.normal.sextic.scale.regular4 -
      20160 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 ^ 2 +
      8960 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 ^ 3 +
      15120 * S.normal.sextic.scale.regular3 ^ 2 *
        S.normal.sextic.scale.regular4 ^ 2 -
      1232 * S.normal.sextic.scale.regular4 ^ 5
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
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (48384 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading2 -
      12096 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading4 ^ 2 +
      24192 * S.normal.sextic.scale.leading1 ^ 2 -
      32256 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading3 *
            S.normal.sextic.scale.leading4 -
      16128 * S.normal.sextic.scale.leading2 ^ 2 *
          S.normal.sextic.scale.leading4 -
      20160 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading3 ^ 2 +
      8960 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading4 ^ 3 +
      15120 * S.normal.sextic.scale.leading3 ^ 2 *
          S.normal.sextic.scale.leading4 ^ 2 -
      1232 * S.normal.sextic.scale.leading4 ^ 5) = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

theorem TransverseFactor.c7N4Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -288 * (224 * C7 * S.u ^ 4 * S.v - 1008 * C7 * S.u * S.v ^ 3 -
        2187 * S.u * S.v *
          (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        1458 * S.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) +
        2916 * S.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        1458 * S.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
        1458 * S.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    326592 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular1 -
      108864 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
      163296 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular2 * S.normal.sextic.scale.regular4 -
      81648 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular3 ^ 2 +
      37800 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular4 ^ 3 -
      108864 * S.normal.sextic.scale.regular2 ^ 2 *
        S.normal.sextic.scale.regular3 +
      136080 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 2 +
      45360 * S.normal.sextic.scale.regular3 ^ 3 *
        S.normal.sextic.scale.regular4 -
      27720 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4 ^ 4
  change
    (6561 * GCD369CubeFaberN4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (326592 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading1 -
      108864 * S.normal.sextic.scale.leading0 *
          S.normal.sextic.scale.leading3 *
            S.normal.sextic.scale.leading4 -
      163296 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading2 *
            S.normal.sextic.scale.leading4 -
      81648 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading3 ^ 2 +
      37800 * S.normal.sextic.scale.leading1 *
          S.normal.sextic.scale.leading4 ^ 3 -
      108864 * S.normal.sextic.scale.leading2 ^ 2 *
          S.normal.sextic.scale.leading3 +
      136080 * S.normal.sextic.scale.leading2 *
          S.normal.sextic.scale.leading3 *
            S.normal.sextic.scale.leading4 ^ 2 +
      45360 * S.normal.sextic.scale.leading3 ^ 3 *
          S.normal.sextic.scale.leading4 -
      27720 * S.normal.sextic.scale.leading3 *
          S.normal.sextic.scale.leading4 ^ 4) = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  dsimp only [GCD369CubeNormalRow4]
  ring

/-- Vanishing of the four literal quadratic Hahn coefficients is exactly
the source-facing arbitrary-`c7` Faber row packet. -/
theorem TransverseFactor.c7LeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C7 : k)
    (h1 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC7N1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC7N2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC7N3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC7N4
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeC7LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C7 := by
  dsimp [GCD369CubeC7LeadingFaberRowsAt]
  have hc := GCD369CubeFaberC7NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C7
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.c7N1Coeff C7]
    exact h1
  · rw [hc2, ← T.c7N2Coeff C7]
    exact h2
  · rw [hc3, ← T.c7N3Coeff C7]
    exact h3
  · rw [hc4, ← T.c7N4Coeff C7]
    exact h4

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c7N1Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c7N2Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c7N3Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c7N4Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c7LeadingFaberRowsAt
