import FiniteDoubleLoad

/-! # Nonzero `d`-load at the quadratic stage, independently of `B`

The quadratic-before-cubic residue algebra already contradicts a nonzero
half-scale coefficient.  When that coefficient vanishes, the same four
rows collapse to the linear chart with `C = Q`, which is independently
inconsistent for a nonzero load.
-/

noncomputable section

/-- A nonzero `d`-load cannot first meet the quadratic correction strictly
before the intrinsic cubic, whether or not the half-scale coefficient
vanishes. -/
theorem GCD369CubeDoubleBlowup_dLoad_quadratic_beforeCubic_inconsistent_of_load_ne_zero
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hT : T ≠ 0) (hr : r ≠ 0)
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
  rcases eq_or_ne B 0 with hB0 | hB
  · subst hB0
    refine GCD369CubeDoubleBlowup_dLoad_linear_beforeCubic_inconsistent
      A 0 Q r d T hr hT ?_ ?_ ?_
    · linear_combination h1
    · linear_combination h2
    · linear_combination h3
  · exact GCD369CubeDoubleBlowup_dLoad_quadratic_beforeCubic_inconsistent
      A B Q r d T hB hr h1 h2 h3 h4

#print axioms
  GCD369CubeDoubleBlowup_dLoad_quadratic_beforeCubic_inconsistent_of_load_ne_zero
