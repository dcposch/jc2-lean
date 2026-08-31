import FiniteLoadAnnihilation
import FiniteDoubleRho1LoadPolys

/-! # The weight-ten `rho1` load in the second double-root blowup

After the lower-weight source parameters have vanished, the next possible
interruption of a transverse double-root jet is the weight-ten invariant
`rho1`.  This file records the finite residue algebra for that
interruption.

Because `rho1` is a target value rather than a high source coefficient,
only the first invariant row is loaded.  The four double-root remainder
constants are the exact specializations recorded by
`GCD369Cube_rho1LoadRemainders_doubleRoot`: `62208`, `0`, `0`, and `0`.

The first two theorems exclude a `rho1`-load arriving at the linear or
quadratic stage strictly before the intrinsic cubic.  At the cubic
resonance the linear stage is still inconsistent: rows two through four
carry no load, so they already obstruct `A ≠ 0`.  The balanced triple
resonance is a genuine survivor of the four-row algebra.  It forces two
explicit residual equations, and the source endpoint `B = 0` still
collapses them.  The remaining `B ≠ 0` chart is the last resonance a
later source/root argument must exclude.
-/

noncomputable section

/-- A nonzero `rho1`-load cannot first meet the linearized double-root chart
strictly before the intrinsic cubic.  Only the first row carries the
sparse remainder `62208 T`. -/
theorem GCD369CubeDoubleBlowup_rho1Load_linear_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) -
        62208 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) = 0)
    (h3 : -2 * A ^ 2 * r ^ 2 * d = 0) : False := by
  have hload : (186624 : K) * r ^ 2 * T = 0 := by
    linear_combination -3 * r ^ 2 * h1 + r * h2 - 11664 * h3
  rcases mul_eq_zero.mp hload with hc | hT0
  · norm_num at hc
    exact hr hc
  · exact hT hT0

/-- A nonzero `rho1`-load cannot first meet the quadratic correction strictly
before the intrinsic cubic.  The third and fourth rows carry no load
remainder, so the first row is incompatible with them. -/
theorem GCD369CubeDoubleBlowup_rho1Load_quadratic_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) -
        62208 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) = 0)
    (_h3 : -2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) = 0) :
    False := by
  have hload : (-2239488 : K) * r ^ 3 * T = 0 := by
    linear_combination 36 * r ^ 3 * h1 - 9 * r ^ 2 * h2 + h4
  rcases mul_eq_zero.mp hload with hc | hT0
  · norm_num at hc
    exact hr hc
  · exact hT hT0

/-- Even when the intrinsic cubic arrives simultaneously, a `rho1`-load
cannot meet the *linear* correction stage.  Rows two through four carry
no remainder, so they already force `A = 0`. -/
theorem GCD369CubeDoubleBlowup_rho1Load_linear_atCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (_h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) -
        62208 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) = 0)
    (h3 : 128 * (-2 * A ^ 2 * r ^ 2 * d) - 64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * (r * B + C)) -
        314928 * (r * A) * A ^ 2 = 0) : False := by
  have hcubic : (-489888 : K) * r * A ^ 3 = 0 := by
    linear_combination 6 * r ^ 2 * h2 - 2187 * r * h3 + 2 * h4
  rcases mul_eq_zero.mp hcubic with hc | hA3
  · rcases mul_eq_zero.mp hc with hn | hr0
    · norm_num at hn
    · exact hr hr0
  · exact (pow_ne_zero 3 hA) hA3

/-- At the unique triple resonance (the `rho1`-load, the quadratic
correction, and the intrinsic cubic all have the same order), the three
unloaded invariant rows force this residual equation.  It is a genuine
survivor of the four-row algebra, not a contradiction. -/
theorem GCD369CubeDoubleBlowup_rho1Load_balanced_resonance_relation
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K)
    (_h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) -
        62208 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) = 0)
    (h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * (r * A) * A ^ 2 = 0) :
    r * (7 * A ^ 3 + 108 * r ^ 2 * B ^ 2) = 0 := by
  linear_combination
    (-1 / 69984) *
      (6 * r ^ 2 * h2 - 2187 * r * h3 + 2 * h4)

/-- The same four rows also force this loaded residual.  Together with
`GCD369CubeDoubleBlowup_rho1Load_balanced_resonance_relation` it
identifies the last balanced chart `64 r^2 T + 9 A^3 = 0`. -/
theorem GCD369CubeDoubleBlowup_rho1Load_balanced_resonance_load_relation
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) -
        62208 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) = 0)
    (_h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * (r * A) * A ^ 2 = 0) :
    r * (64 * r ^ 2 * T + 9 * A ^ 3) = 0 := by
  linear_combination
    (-1 / 34992) *
      (36 * r ^ 3 * h1 - 9 * r ^ 2 * h2 + h4)

/-- The source endpoint has zero half-scale residue.  On that slice the
balanced `rho1` relation collapses, and the four loaded rows are
inconsistent. -/
theorem GCD369CubeDoubleBlowup_rho1Load_balanced_resonance_Bzero_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hA : A ≠ 0) (hr : r ≠ 0) (hB : B = 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) -
        62208 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) = 0)
    (h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * (r * A) * A ^ 2 = 0) : False := by
  subst B
  apply GCD369CubeDoubleBlowup_rho1Load_linear_atCubic_inconsistent
    A 0 Q r d T hA hr
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3
  · linear_combination h4

#print axioms GCD369CubeDoubleBlowup_rho1Load_linear_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_rho1Load_quadratic_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_rho1Load_linear_atCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_rho1Load_balanced_resonance_relation
#print axioms GCD369CubeDoubleBlowup_rho1Load_balanced_resonance_load_relation
#print axioms GCD369CubeDoubleBlowup_rho1Load_balanced_resonance_Bzero_inconsistent
