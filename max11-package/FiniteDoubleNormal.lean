import FiniteEarlyNormal

/-! # The ramified double-normal cubic obstruction

The unique zero-load normal at a double cubic lies in the radical of the
third quadratic normal row.  Consequently every second-order correction
drops out one order later, while the explicit cubic remainder contributes
`-64 A^3`.  This is the structural source of the audited `-1/16` entry.
-/

noncomputable section
open Polynomial

/-- The double-root zero-load normal `A * (1,r,-2r^2)` is in the radical of
the third quadratic normal row, not merely on its zero locus. -/
theorem GCD369CubeDoubleRootNormalRow3_radical
    {R : Type*} [CommRing R] (r A h X1 Y1 Z1 : R) :
    GCD369CubeNormalRow3
        (A + h * X1) (r * A + h * Y1) (-2 * r ^ 2 * A + h * Z1)
        (-3 * r ^ 2) (2 * r ^ 3) =
      h ^ 2 * GCD369CubeNormalRow3 X1 Y1 Z1
        (-3 * r ^ 2) (2 * r ^ 3) := by
  dsimp only [GCD369CubeNormalRow3]
  ring

set_option maxRecDepth 10000 in
/-- In the exact third zero-high Faber expansion, the coefficient one order
beyond a double-normal first jet is `-64 A^3`, independently of all three
next normalized coefficients. -/
theorem GCD369CubeDoubleRootNormal_primitiveN3_cubicCoeff
    {K : Type*} [Field K] [CharZero K]
    (r A X1 Y1 Z1 : K) :
    let h : K[X] := X
    let Xn : K[X] := C A + h * C X1
    let Yn : K[X] := C (r * A) + h * C Y1
    let Zn : K[X] := C (-2 * r ^ 2 * A) + h * C Z1
    (128 * GCD369CubeNormalRow3 Xn Yn Zn (C (-3 * r ^ 2))
          (C (2 * r ^ 3)) * h ^ 2 -
        64 * Xn ^ 3 * h ^ 3).coeff 3 = -64 * A ^ 3 := by
  dsimp only
  have hrad :
      GCD369CubeNormalRow3
          (C A + X * C X1) (C (r * A) + X * C Y1)
          (C (-2 * r ^ 2 * A) + X * C Z1)
          (C (-3 * r ^ 2)) (C (2 * r ^ 3)) =
        X ^ 2 * GCD369CubeNormalRow3 (C X1) (C Y1) (C Z1)
          (C (-3 * r ^ 2)) (C (2 * r ^ 3)) := by
    simpa only [map_mul, map_pow, map_neg, map_ofNat] using
      (GCD369CubeDoubleRootNormalRow3_radical
        (C r) (C A) X (C X1) (C Y1) (C Z1))
  rw [hrad]
  norm_num [coeff_sub, coeff_mul_X_pow', coeff_X_pow_mul',
    coeff_zero_eq_eval_zero]

/-- The cubic coefficient in the primitive third row cannot vanish when the
first double-normal coefficient is nonzero. -/
theorem GCD369CubeDoubleRootNormal_primitiveN3_cubic_ne_zero
    {K : Type*} [Field K] [CharZero K]
    (r A X1 Y1 Z1 : K) (hA : A ≠ 0) :
    let h : K[X] := X
    let Xn : K[X] := C A + h * C X1
    let Yn : K[X] := C (r * A) + h * C Y1
    let Zn : K[X] := C (-2 * r ^ 2 * A) + h * C Z1
    (128 * GCD369CubeNormalRow3 Xn Yn Zn (C (-3 * r ^ 2))
          (C (2 * r ^ 3)) * h ^ 2 -
        64 * Xn ^ 3 * h ^ 3).coeff 3 ≠ 0 := by
  dsimp only
  rw [GCD369CubeDoubleRootNormal_primitiveN3_cubicCoeff]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hA)

#print axioms GCD369CubeDoubleRootNormalRow3_radical
#print axioms GCD369CubeDoubleRootNormal_primitiveN3_cubicCoeff
#print axioms GCD369CubeDoubleRootNormal_primitiveN3_cubic_ne_zero
