import FiniteDoubleC2LoadPolys
import FiniteLoadAnnihilation

/-! # The weight-seven `c2` load in the second double-root blowup

After the lower-weight parameters have vanished, the next possible
interruption of a transverse double-root jet is the weight-seven
parameter `c2`.  This file records the finite residue algebra for that
interruption.

The first two theorems exclude a `c2`-load arriving at the linear or quadratic
stage strictly before the intrinsic cubic.  At the cubic resonance the
linear stage is still inconsistent.  The final theorem deliberately does
not claim an inconsistency: when the `c2`-load, the quadratic correction, and
the intrinsic cubic all arrive together, the four invariant rows leave one
explicit residual equation.  The literal source/root boundary must exclude
that last resonance.

The third invariant row carries no cubic-sheet `c2` remainder.  The four
double-root remainder constants are the exact specializations recorded by
`GCD369Cube_c2LoadRemainders_doubleRoot`: `82944 r^3`, `-186624 r^4`,
`0`, and `1866240 r^6`.
-/

noncomputable section

/-- A nonzero `c2`-load cannot first meet the linearized double-root chart
strictly before the intrinsic cubic.  The constants are the exact
specializations of the first two pure-load remainders at
`U = -3*r^2`, `V = 2*r^3`. -/
theorem GCD369CubeDoubleBlowup_c2Load_linear_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) +
        82944 * r ^ 3 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) - 186624 * r ^ 4 * T = 0)
    (h3 : -2 * A ^ 2 * r ^ 2 * d = 0) : False := by
  have hload : (-435456 : K) * r ^ 5 * T = 0 := by
    linear_combination -3 * r ^ 2 * h1 + r * h2 - 11664 * h3
  rcases mul_eq_zero.mp hload with hc | hT0
  · norm_num at hc
    exact hr hc
  · exact hT hT0

/-- A nonzero `c2`-load cannot first meet the quadratic correction strictly
before the intrinsic cubic.  The third row carries no load remainder; the
fourth row is then incompatible with the first two loaded rows. -/
theorem GCD369CubeDoubleBlowup_c2Load_quadratic_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) +
        82944 * r ^ 3 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) - 186624 * r ^ 4 * T = 0)
    (_h3 : -2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) +
        1866240 * r ^ 6 * T = 0) : False := by
  have hload : (6531840 : K) * r ^ 6 * T = 0 := by
    linear_combination 36 * r ^ 3 * h1 - 9 * r ^ 2 * h2 + h4
  rcases mul_eq_zero.mp hload with hc | hT0
  · norm_num at hc
    exact hr hc
  · exact hT hT0

/-- Even when the intrinsic cubic arrives simultaneously, a `c2`-load cannot
meet the *linear* correction stage. -/
theorem GCD369CubeDoubleBlowup_c2Load_linear_atCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) +
        82944 * r ^ 3 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) - 186624 * r ^ 4 * T = 0)
    (h3 : 128 * (-2 * A ^ 2 * r ^ 2 * d) - 64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * (r * B + C)) -
        314928 * (r * A) * A ^ 2 + 1866240 * r ^ 6 * T = 0) : False := by
  have hcubic : (-227448 : K) * r * A ^ 3 = 0 := by
    linear_combination
      -9 * r ^ 3 * h1 +
      6 * r ^ 2 * h2 -
      (10935 / 8) * r * h3 + h4
  rcases mul_eq_zero.mp hcubic with hc | hA3
  · norm_num at hc
    exact hr hc
  · exact (pow_ne_zero 3 hA) hA3

/-- At the unique triple resonance (the `c2`-load, the quadratic correction,
and the intrinsic cubic all have the same order), the four invariant rows
force this residual equation.  It is a genuine survivor of the four-row
algebra, not a contradiction. -/
theorem GCD369CubeDoubleBlowup_c2Load_balanced_resonance_relation
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) +
        82944 * r ^ 3 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) - 186624 * r ^ 4 * T = 0)
    (h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * (r * A) * A ^ 2 + 1866240 * r ^ 6 * T = 0) :
    r * (13 * A ^ 3 + 270 * r ^ 2 * B ^ 2) = 0 := by
  linear_combination
    (-1 / 17496) *
      (-9 * r ^ 3 * h1 +
       6 * r ^ 2 * h2 -
       (10935 / 8) * r * h3 +
       h4)

/-- The source endpoint has zero half-scale residue.  On that slice the
balanced `c2` relation collapses, and the four loaded rows are inconsistent. -/
theorem GCD369CubeDoubleBlowup_c2Load_balanced_resonance_Bzero_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hA : A ≠ 0) (hr : r ≠ 0) (hB : B = 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) +
        82944 * r ^ 3 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) - 186624 * r ^ 4 * T = 0)
    (h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * (r * A) * A ^ 2 + 1866240 * r ^ 6 * T = 0) : False := by
  subst B
  apply GCD369CubeDoubleBlowup_c2Load_linear_atCubic_inconsistent
    A 0 Q r d T hA hr
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3
  · linear_combination h4

#print axioms GCD369CubeDoubleBlowup_c2Load_linear_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c2Load_quadratic_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c2Load_linear_atCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c2Load_balanced_resonance_relation
#print axioms GCD369CubeDoubleBlowup_c2Load_balanced_resonance_Bzero_inconsistent
