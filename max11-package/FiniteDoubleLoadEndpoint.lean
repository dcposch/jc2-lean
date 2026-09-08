import FiniteDoubleLoad

/-! # The `B = 0` endpoint of the balanced `d`-load resonance

At the unique triple resonance the four invariant rows leave the residual
equation `r * (25 * A ^ 3 + 594 * r ^ 2 * B ^ 2) = 0`.  When the quadratic
half-scale coefficient vanishes, that relation is incompatible with a
nonzero double-root jet.
-/

noncomputable section

/-- The balanced `d`-load resonance is inconsistent once the quadratic
half-scale coefficient is zero. -/
theorem GCD369CubeDoubleBlowup_dLoad_balanced_resonance_Bzero_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hA : A ≠ 0) (hr : r ≠ 0) (hB : B = 0)
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
        314928 * (r * A) * A ^ 2 + 26956800 * r ^ 12 * T = 0) : False := by
  have hrel :=
    GCD369CubeDoubleBlowup_dLoad_balanced_resonance_relation
      A B Q r d T h1 h2 h3 h4
  have h25A : (25 : K) * A ^ 3 = 0 := by
    simpa [hB, hr] using hrel
  rcases mul_eq_zero.mp h25A with h25 | hA3
  · norm_num at h25
  · exact (pow_ne_zero 3 hA) hA3

#print axioms GCD369CubeDoubleBlowup_dLoad_balanced_resonance_Bzero_inconsistent
