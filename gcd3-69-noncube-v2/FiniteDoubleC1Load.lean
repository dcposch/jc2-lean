import FiniteDoubleC1LoadPolys
import FiniteLoadAnnihilation

/-! # The weight-eight `c1` load in the second double-root blowup

After the lower-weight parameters have vanished, the next possible
interruption of a transverse double-root jet is the weight-eight
parameter `c1`.  This file records the finite residue algebra for that
interruption.

The first two theorems exclude a `c1`-load arriving at the linear or quadratic
stage strictly before the intrinsic cubic.  At the cubic resonance the
linear stage is still inconsistent.  The residual theorem deliberately does
not claim an inconsistency: when the `c1`-load, the quadratic correction, and
the intrinsic cubic all arrive together, the four invariant rows leave one
explicit residual equation.  The literal source/root boundary must exclude
that last resonance.

The third invariant row carries no cubic-sheet `c1` remainder.  The four
double-root remainder constants are the exact specializations recorded by
`GCD369Cube_c1LoadRemainders_doubleRoot`: `-62208 r^2`, `124416 r^3`,
`0`, and `-1119744 r^5`.
-/

noncomputable section

/-- A nonzero `c1`-load cannot first meet the linearized double-root chart
strictly before the intrinsic cubic.  The constants are the exact
specializations of the first two pure-load remainders at
`U = -3*r^2`, `V = 2*r^3`. -/
theorem GCD369CubeDoubleBlowup_c1Load_linear_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) -
        62208 * r ^ 2 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) + 124416 * r ^ 3 * T = 0)
    (h3 : -2 * A ^ 2 * r ^ 2 * d = 0) : False := by
  have hload : (311040 : K) * r ^ 4 * T = 0 := by
    linear_combination -3 * r ^ 2 * h1 + r * h2 - 11664 * h3
  rcases mul_eq_zero.mp hload with hc | hT0
  · norm_num at hc
    exact hr hc
  · exact hT hT0

/-- A nonzero `c1`-load cannot first meet the quadratic correction strictly
before the intrinsic cubic.  The third row carries no load remainder; the
fourth row is then incompatible with the first two loaded rows. -/
theorem GCD369CubeDoubleBlowup_c1Load_quadratic_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) -
        62208 * r ^ 2 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) + 124416 * r ^ 3 * T = 0)
    (_h3 : -2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        1119744 * r ^ 5 * T = 0) : False := by
  have hload : (-4478976 : K) * r ^ 5 * T = 0 := by
    linear_combination 36 * r ^ 3 * h1 - 9 * r ^ 2 * h2 + h4
  rcases mul_eq_zero.mp hload with hc | hT0
  · norm_num at hc
    exact hr hc
  · exact hT hT0

/-- Even when the intrinsic cubic arrives simultaneously, a `c1`-load cannot
meet the *linear* correction stage. -/
theorem GCD369CubeDoubleBlowup_c1Load_linear_atCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) -
        62208 * r ^ 2 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) + 124416 * r ^ 3 * T = 0)
    (h3 : 128 * (-2 * A ^ 2 * r ^ 2 * d) - 64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * (r * B + C)) -
        314928 * (r * A) * A ^ 2 - 1119744 * r ^ 5 * T = 0) : False := by
  have hcubic : (-1154736 : K) * r * A ^ 3 = 0 := by
    linear_combination
      -36 * r ^ 3 * h1 +
      27 * r ^ 2 * h2 -
      6561 * r * h3 +
      5 * h4
  rcases mul_eq_zero.mp hcubic with hc | hA3
  · norm_num at hc
    exact hr hc
  · exact (pow_ne_zero 3 hA) hA3

/-- At the unique triple resonance (the `c1`-load, the quadratic correction,
and the intrinsic cubic all have the same order), the four invariant rows
force this residual equation.  It is a genuine survivor of the four-row
algebra, not a contradiction. -/
theorem GCD369CubeDoubleBlowup_c1Load_balanced_resonance_relation
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) -
        62208 * r ^ 2 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) + 124416 * r ^ 3 * T = 0)
    (h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * (r * A) * A ^ 2 - 1119744 * r ^ 5 * T = 0) :
    r * (11 * A ^ 3 + 216 * r ^ 2 * B ^ 2) = 0 := by
  linear_combination
    (-1 / 104976) *
      (-36 * r ^ 3 * h1 +
       27 * r ^ 2 * h2 -
       6561 * r * h3 +
       5 * h4)

/-- The source endpoint has zero half-scale residue.  On that slice the
balanced `c1` relation collapses, and the four loaded rows are inconsistent. -/
theorem GCD369CubeDoubleBlowup_c1Load_balanced_resonance_Bzero_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hA : A ≠ 0) (hr : r ≠ 0) (hB : B = 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) -
        62208 * r ^ 2 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) + 124416 * r ^ 3 * T = 0)
    (h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * (r * A) * A ^ 2 - 1119744 * r ^ 5 * T = 0) : False := by
  subst B
  apply GCD369CubeDoubleBlowup_c1Load_linear_atCubic_inconsistent
    A 0 Q r d T hA hr
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3
  · linear_combination h4

#print axioms GCD369CubeDoubleBlowup_c1Load_linear_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c1Load_quadratic_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c1Load_linear_atCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c1Load_balanced_resonance_relation
#print axioms GCD369CubeDoubleBlowup_c1Load_balanced_resonance_Bzero_inconsistent
