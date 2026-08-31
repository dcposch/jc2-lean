import FiniteCommonSource

/-! # Quadratic-scale Hahn coefficient of the fourth moving-root row

The first three exact rows at twice the common monomial are already
recorded by `doubleBlowup_quadratic_coefficients`.  The fourth row is the
remaining finite identity needed by the weight-two quadratic load: after
the two kernel remainders have acquired a second copy of that monomial, its
coefficient at `2 * mu` is the same second-correction polynomial that the
finite `c7` algebra uses.
-/

noncomputable section

namespace GCD369CubeHahnRegular

/-- The leading quadratic polynomial of the exact fourth moving-root row. -/
theorem doubleBlowup_quadratic_row4_leading
    {R : Type*} [CommRing R] (A r q b : R) :
    4374 * (-3 * r ^ 2) * (A * r * q + 5 * r * b ^ 2) =
      -13122 * A * r ^ 3 * q - 65610 * r ^ 3 * b ^ 2 := by
  ring

/-- Once the two kernel remainders contain a second copy of the common
monomial, the coefficient of the fourth exact row at `2 * mu` is the
finite-dimensional second-correction polynomial
`-13122 * A0 * r0 ^ 3 * q0 - 65610 * r0 ^ 3 * b0 ^ 2`. -/
theorem doubleBlowup_quadratic_row4_coefficient
    {k : Type*} [Field k] [CharZero k]
    (mu : ℚ) (hmu : 0 < mu)
    (A r d b q : GCD369CubeHahnRegular k) :
    let M := monomial mu hmu.le
    let D := M ^ 2 * d
    let B := M * b
    let C := M ^ 2 * q - M * r * b
    let A0 := constantCoeff A
    let r0 := constantCoeff r
    let b0 := constantCoeff b
    let q0 := constantCoeff q
    (4374 * (-3 * r ^ 2 + D) *
        (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
          3 * A * B * D - 3 * B * C)).1.coeff (2 * mu) =
      -13122 * A0 * r0 ^ 3 * q0 - 65610 * r0 ^ 3 * b0 ^ 2 := by
  dsimp only
  let M : GCD369CubeHahnRegular k := monomial mu hmu.le
  let D : GCD369CubeHahnRegular k := M ^ 2 * d
  let B : GCD369CubeHahnRegular k := M * b
  let C : GCD369CubeHahnRegular k := M ^ 2 * q - M * r * b
  let R4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * r ^ 2 + D) *
      (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
        3 * A * B * D - 3 * B * C)
  let K : GCD369CubeHahnRegular k := A * r * q + 5 * r * b ^ 2
  let E : GCD369CubeHahnRegular k := 3 * A * b * d - 3 * b * q
  let K4 : GCD369CubeHahnRegular k :=
    -13122 * A * r ^ 3 * q - 65610 * r ^ 3 * b ^ 2
  let E4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * r ^ 2 * E + M * d * K + M ^ 2 * d * E)
  have hS :
      A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
          3 * A * B * D - 3 * B * C =
        M ^ 2 * K + M ^ 3 * E := by
    dsimp only [D, B, C, K, E]
    ring
  have hlead : 4374 * (-3 * r ^ 2) * K = K4 := by
    simpa only [K, K4] using doubleBlowup_quadratic_row4_leading A r q b
  have hmul :
      4374 * (-3 * r ^ 2 + D) * (M ^ 2 * K + M ^ 3 * E) =
        M ^ 2 * (4374 * (-3 * r ^ 2) * K) + M ^ 3 * E4 := by
    dsimp only [D, E4]
    ring
  have hfac : R4 = M ^ 2 * K4 + M ^ 3 * E4 := by
    dsimp only [R4]
    rw [hS, hmul, hlead]
  have hc := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * mu)) hfac
  have hmain := coeff_monomial_pow_mul_at mu hmu 2 K4
  have hhigh := coeff_monomial_pow_mul_of_lt mu hmu 2 3 (by norm_num) E4
  change (M ^ 2 * K4).1.coeff (2 * mu) = constantCoeff K4 at hmain
  change (M ^ 3 * E4).1.coeff (2 * mu) = 0 at hhigh
  change R4.1.coeff (2 * mu) =
    (M ^ 2 * K4).1.coeff (2 * mu) + (M ^ 3 * E4).1.coeff (2 * mu) at hc
  rw [hmain, hhigh, add_zero] at hc
  simpa only [R4, K4, D, B, C, M, map_sub, map_mul, map_pow, map_ofNat,
    map_neg] using hc

end GCD369CubeHahnRegular

#print axioms GCD369CubeHahnRegular.doubleBlowup_quadratic_row4_leading
#print axioms GCD369CubeHahnRegular.doubleBlowup_quadratic_row4_coefficient
