import FiniteLoadAnnihilation

/-! # The weight-one load in the second double-root blowup

If a transverse double-root jet occurs at scale `delta` with
`2 * delta < p`, then no load of weight at least two can occur through the
cubic exponent `3 * delta`.  The only possible interruption is therefore the
weight-one parameter `d`.  This file records the finite residue algebra for
that interruption.

The first two theorems exclude a `d`-load arriving at the linear or quadratic
stage strictly before the intrinsic cubic.  At the cubic resonance the
linear stage is still inconsistent.  The final theorem deliberately does
not claim an inconsistency: when the `d`-load, the quadratic correction, and
the intrinsic cubic all arrive together, the four invariant rows leave one
explicit residual equation.  The literal source/root boundary must exclude
that last resonance.
-/

noncomputable section

/-- The three pure `d`-load remainders that survive in rows one, two, and
four on the double-root sheet. -/
theorem GCD369Cube_dLoadRemainders_doubleRoot
    {R : Type*} [CommRing R] (r : R) :
    (-10240 * (-3 * r ^ 2) ^ 3 * (2 * r ^ 3) +
        30720 * (2 * r ^ 3) ^ 3 = 798720 * r ^ 9) ∧
    (2048 * (-3 * r ^ 2) ^ 5 -
        46080 * (-3 * r ^ 2) ^ 2 * (2 * r ^ 3) ^ 2 =
      -2156544 * r ^ 10) ∧
    (5120 * (-3 * r ^ 2) ^ 6 -
        184320 * (-3 * r ^ 2) ^ 3 * (2 * r ^ 3) ^ 2 +
        207360 * (2 * r ^ 3) ^ 4 = 26956800 * r ^ 12) := by
  constructor
  · ring
  constructor <;> ring

/-- A nonzero `d`-load cannot first meet the linearized double-root chart
strictly before the intrinsic cubic.  The constants are the exact
specializations of the first two pure-load remainders at
`U = -3*r^2`, `V = 2*r^3`. -/
theorem GCD369CubeDoubleBlowup_dLoad_linear_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) +
        798720 * r ^ 9 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) - 2156544 * r ^ 10 * T = 0)
    (h3 : -2 * A ^ 2 * r ^ 2 * d = 0) : False := by
  have hload : (-4552704 : K) * r ^ 11 * T = 0 := by
    linear_combination -3 * r ^ 2 * h1 + r * h2 - 11664 * h3
  rcases mul_eq_zero.mp hload with hc | hT0
  · norm_num at hc
    exact hr hc
  · exact hT hT0

/-- A nonzero `d`-load cannot first meet the quadratic correction strictly
before the intrinsic cubic.  The third row fixes the discriminant correction;
the fourth row is then incompatible with the first two loaded rows. -/
theorem GCD369CubeDoubleBlowup_dLoad_quadratic_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hB : B ≠ 0) (hr : r ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) +
        798720 * r ^ 9 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) - 2156544 * r ^ 10 * T = 0)
    (h3 : -2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) +
        26956800 * r ^ 12 * T = 0) : False := by
  have hquad : (-5196312 : K) * r ^ 3 * B ^ 2 = 0 := by
    linear_combination
      (-27 / 2) * r ^ 3 * h1 +
      (15 / 2) * r ^ 2 * h2 -
      192456 * r * h3 + h4
  rcases mul_eq_zero.mp hquad with hc | hB2
  · norm_num at hc
    exact hr hc
  · exact hB (sq_eq_zero_iff.mp hB2)

/-- Even when the intrinsic cubic arrives simultaneously, a `d`-load cannot
meet the *linear* correction stage. -/
theorem GCD369CubeDoubleBlowup_dLoad_linear_atCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) +
        798720 * r ^ 9 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) - 2156544 * r ^ 10 * T = 0)
    (h3 : 128 * (-2 * A ^ 2 * r ^ 2 * d) - 64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * (r * B + C)) -
        314928 * (r * A) * A ^ 2 + 26956800 * r ^ 12 * T = 0) : False := by
  have hcubic : (-218700 : K) * r * A ^ 3 = 0 := by
    linear_combination
      (-27 / 2) * r ^ 3 * h1 +
      (15 / 2) * r ^ 2 * h2 -
      (24057 / 16) * r * h3 + h4
  rcases mul_eq_zero.mp hcubic with hc | hA3
  · norm_num at hc
    exact hr hc
  · exact (pow_ne_zero 3 hA) hA3

/-- At the unique triple resonance (the `d`-load, the quadratic correction,
and the intrinsic cubic all have the same order), the four invariant rows
force this residual equation.  It is a genuine survivor of the four-row
algebra, not a contradiction. -/
theorem GCD369CubeDoubleBlowup_dLoad_balanced_resonance_relation
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) +
        798720 * r ^ 9 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) - 2156544 * r ^ 10 * T = 0)
    (h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * (r * A) * A ^ 2 + 26956800 * r ^ 12 * T = 0) :
    r * (25 * A ^ 3 + 594 * r ^ 2 * B ^ 2) = 0 := by
  linear_combination
    (-1 / 8748) *
      ((-27 / 2) * r ^ 3 * h1 +
       (15 / 2) * r ^ 2 * h2 -
       (24057 / 16) * r * h3 + h4)

#print axioms GCD369Cube_dLoadRemainders_doubleRoot
#print axioms GCD369CubeDoubleBlowup_dLoad_linear_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_dLoad_quadratic_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_dLoad_linear_atCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_dLoad_balanced_resonance_relation
