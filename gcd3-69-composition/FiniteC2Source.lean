import FiniteActiveSource

/-! # First `c2` Faber load at a finite common-cubic pole

The normal coordinates have already been factored at a prescribed positive
Hahn scale.  This file continues the source-facing active-load bridge by
proving that a weight-two `c2` constant, scaled to the square of that
monomial, gives exactly the four arbitrary-`c2` Kuranishi rows used by the
audited algebraic exclusion.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonValueData

theorem TransverseFactor.c2N1Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (-16 * C2 * S.v +
        9 * S.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        18 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) -
        9 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    20736 * S.normal.sextic.scale.regular3
  change
    (729 * GCD369CubeFaberN1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff]
  have hload :
      ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C2 * P).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        C2 * GCD369CubeHahnRegular.constantCoeff P := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P
  rw [hload]
  dsimp only [P]
  simp only [map_mul, map_ofNat]
  change _ + C2 * (20736 * S.normal.sextic.scale.leading3) = _
  rw [S.ha3]
  dsimp only [GCD369CubeNormalRow1]
  ring

theorem TransverseFactor.c2N2Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (8 * C2 * S.u ^ 2 +
        27 * S.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        54 * S.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        54 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    62208 * S.normal.sextic.scale.regular2 -
      20736 * S.normal.sextic.scale.regular4 ^ 2
  change
    (2187 * GCD369CubeFaberN2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P]
  dsimp only [P]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  change _ + C2 *
    (62208 * S.normal.sextic.scale.leading2 -
      20736 * S.normal.sextic.scale.leading4 ^ 2) = _
  rw [S.ha2, S.ha4]
  dsimp only [GCD369CubeNormalRow2]
  ring

theorem TransverseFactor.c2N3Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    82944 * S.normal.sextic.scale.regular1 -
      41472 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4
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
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P]
  dsimp only [P]
  simp only [map_sub, map_mul, map_ofNat]
  change _ + C2 *
    (82944 * S.normal.sextic.scale.leading1 -
      41472 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4) = _
  rw [S.ha1, S.ha3, S.ha4]
  ring

theorem TransverseFactor.c2N4Coeff
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (16 * C2 * S.u ^ 3 - 72 * C2 * S.v ^ 2 -
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
    559872 * S.normal.sextic.scale.regular0 -
      186624 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 -
      93312 * S.normal.sextic.scale.regular3 ^ 2 +
      41472 * S.normal.sextic.scale.regular4 ^ 3
  change
    (6561 * GCD369CubeFaberN4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C2 *
    (559872 * S.normal.sextic.scale.leading0 -
      186624 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading4 -
      93312 * S.normal.sextic.scale.leading3 ^ 2 +
      41472 * S.normal.sextic.scale.leading4 ^ 3) = _
  rw [S.ha0, S.ha2, S.ha3, S.ha4]
  dsimp only [GCD369CubeNormalRow4]
  ring

/-- Vanishing of the four literal quadratic Hahn coefficients is exactly
the source-facing arbitrary-`c2` Faber row packet. -/
theorem TransverseFactor.c2LeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (C2 : k)
    (h1 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N4
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeC2LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C2 := by
  dsimp [GCD369CubeC2LeadingFaberRowsAt]
  have hc := GCD369CubeFaberC2NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C2
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.c2N1Coeff C2]
    exact h1
  · rw [hc2, ← T.c2N2Coeff C2]
    exact h2
  · rw [hc3, ← T.c2N3Coeff C2]
    exact h3
  · rw [hc4, ← T.c2N4Coeff C2]
    exact h4

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c2N1Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c2N2Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c2N3Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c2N4Coeff
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.c2LeadingFaberRowsAt
