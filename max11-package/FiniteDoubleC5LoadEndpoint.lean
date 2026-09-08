import FiniteDoubleC5Load

/-! # The `B = 0` endpoint of the balanced `c5` resonance

At the unique triple resonance the four invariant rows leave the residual
equation `r * (19 * A ^ 3 + 432 * r ^ 2 * B ^ 2) = 0`.  When the quadratic
half-scale coefficient vanishes, that relation is incompatible with a
nonzero double-root jet.
-/

noncomputable section

/-- The balanced `c5` resonance is inconsistent once the quadratic
half-scale coefficient is zero. -/
theorem GCD369CubeDoubleBlowup_c5Load_balanced_resonance_Bzero_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hA : A ≠ 0) (hr : r ≠ 0) (hB : B = 0)
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
        314928 * (r * A) * A ^ 2 + 7257600 * r ^ 9 * T = 0) : False := by
  have hrel :=
    GCD369CubeDoubleBlowup_c5Load_balanced_resonance_relation
      A B Q r d T h1 h2 h3 h4
  have h19A : (19 : K) * A ^ 3 = 0 := by
    simpa [hB, hr] using hrel
  rcases mul_eq_zero.mp h19A with h19 | hA3
  · norm_num at h19
  · exact (pow_ne_zero 3 hA) hA3

#print axioms GCD369CubeDoubleBlowup_c5Load_balanced_resonance_Bzero_inconsistent
