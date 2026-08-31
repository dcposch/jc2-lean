import FiniteDoubleC5LoadPolys
import FiniteLoadAnnihilation

/-! # The weight-four `c5` load in the second double-root blowup

After the weight-one and weight-two parameters have vanished, the next
possible interruption of a transverse double-root jet is the weight-four
parameter `c5`.  This file records the finite residue algebra for that
interruption.

The first two theorems exclude a `c5`-load arriving at the linear or quadratic
stage strictly before the intrinsic cubic.  At the cubic resonance the
linear stage is still inconsistent.  The final theorem deliberately does
not claim an inconsistency: when the `c5`-load, the quadratic correction, and
the intrinsic cubic all arrive together, the four invariant rows leave one
explicit residual equation.  The literal source/root boundary must exclude
that last resonance.

The third invariant row carries no cubic-sheet `c5` remainder.  The four
double-root remainder constants are the exact specializations recorded by
`GCD369Cube_c5LoadRemainders_doubleRoot`: `241920 r^6`, `-622080 r^7`,
`0`, and `7257600 r^9`.
-/

noncomputable section

/-- A nonzero `c5`-load cannot first meet the linearized double-root chart
strictly before the intrinsic cubic.  The constants are the exact
specializations of the first two pure-load remainders at
`U = -3*r^2`, `V = 2*r^3`. -/
theorem GCD369CubeDoubleBlowup_c5Load_linear_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) +
        241920 * r ^ 6 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) - 622080 * r ^ 7 * T = 0)
    (h3 : -2 * A ^ 2 * r ^ 2 * d = 0) : False := by
  have hload : (-1347840 : K) * r ^ 8 * T = 0 := by
    linear_combination -3 * r ^ 2 * h1 + r * h2 - 11664 * h3
  rcases mul_eq_zero.mp hload with hc | hT0
  · norm_num at hc
    exact hr hc
  · exact hT hT0

/-- A nonzero `c5`-load cannot first meet the quadratic correction strictly
before the intrinsic cubic.  The third row carries no load remainder; the
fourth row is then incompatible with the first two loaded rows. -/
theorem GCD369CubeDoubleBlowup_c5Load_quadratic_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) +
        241920 * r ^ 6 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) - 622080 * r ^ 7 * T = 0)
    (_h3 : -2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) +
        7257600 * r ^ 9 * T = 0) : False := by
  have hload : (21565440 : K) * r ^ 9 * T = 0 := by
    linear_combination 36 * r ^ 3 * h1 - 9 * r ^ 2 * h2 + h4
  rcases mul_eq_zero.mp hload with hc | hT0
  · norm_num at hc
    exact hr hc
  · exact hT hT0

/-- Even when the intrinsic cubic arrives simultaneously, a `c5`-load cannot
meet the *linear* correction stage. -/
theorem GCD369CubeDoubleBlowup_c5Load_linear_atCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) +
        241920 * r ^ 6 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) - 622080 * r ^ 7 * T = 0)
    (h3 : 128 * (-2 * A ^ 2 * r ^ 2 * d) - 64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * (r * B + C)) -
        314928 * (r * A) * A ^ 2 + 7257600 * r ^ 9 * T = 0) : False := by
  have hcubic : (-221616 : K) * r * A ^ 3 = 0 := by
    linear_combination
      -12 * r ^ 3 * h1 +
      7 * r ^ 2 * h2 -
      1458 * r * h3 + h4
  rcases mul_eq_zero.mp hcubic with hc | hA3
  · norm_num at hc
    exact hr hc
  · exact (pow_ne_zero 3 hA) hA3

/-- At the unique triple resonance (the `c5`-load, the quadratic correction,
and the intrinsic cubic all have the same order), the four invariant rows
force this residual equation.  It is a genuine survivor of the four-row
algebra, not a contradiction. -/
theorem GCD369CubeDoubleBlowup_c5Load_balanced_resonance_relation
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) +
        241920 * r ^ 6 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) - 622080 * r ^ 7 * T = 0)
    (h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * (r * A) * A ^ 2 + 7257600 * r ^ 9 * T = 0) :
    r * (19 * A ^ 3 + 432 * r ^ 2 * B ^ 2) = 0 := by
  linear_combination
    (-1 / 11664) *
      (-12 * r ^ 3 * h1 +
       7 * r ^ 2 * h2 -
       1458 * r * h3 +
       h4)

#print axioms GCD369CubeDoubleBlowup_c5Load_linear_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c5Load_quadratic_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c5Load_linear_atCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c5Load_balanced_resonance_relation
