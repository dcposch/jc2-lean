import FiniteDoubleLiftRows

/-! # The weight-eleven `rho2` load in the second double-root blowup

Only the second primitive invariant row carries the first `rho2` load.  The
resulting quadratic residue system is inconsistent before the intrinsic
cubic; at the exact cubic tie the source endpoint `B = 0` again collapses
the balanced system.
-/

noncomputable section

/-- A nonzero `rho2` load cannot meet the quadratic double-root correction
strictly before the intrinsic cubic. -/
theorem GCD369CubeDoubleBlowup_rho2Load_quadratic_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) - 186624 * T = 0)
    (_h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) = 0) :
    False := by
  have hload : (1679616 : K) * r ^ 2 * T = 0 := by
    linear_combination 36 * r ^ 3 * h1 - 9 * r ^ 2 * h2 + h4
  rcases mul_eq_zero.mp hload with hc | hT0
  · rcases mul_eq_zero.mp hc with hn | hr2
    · norm_num at hn
    · exact (pow_ne_zero 2 hr) hr2
  · exact hT hT0

/-- At the balanced `rho2`/cubic resonance, vanishing half-scale source
residue makes the four loaded rows inconsistent. -/
theorem GCD369CubeDoubleBlowup_rho2Load_balanced_resonance_Bzero_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hA : A ≠ 0) (hr : r ≠ 0) (hB : B = 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) = 0)
    (_h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) - 186624 * T = 0)
    (h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * r * A ^ 3 = 0) : False := by
  subst B
  have hcubic : (-2099520 : K) * r * A ^ 3 = 0 := by
    linear_combination 72 * r ^ 3 * h1 - 6561 * r * h3 + 8 * h4
  rcases mul_eq_zero.mp hcubic with hc | hA3
  · rcases mul_eq_zero.mp hc with hn | hr0
    · norm_num at hn
    · exact hr hr0
  · exact (pow_ne_zero 3 hA) hA3

#print axioms
  GCD369CubeDoubleBlowup_rho2Load_quadratic_beforeCubic_inconsistent
#print axioms
  GCD369CubeDoubleBlowup_rho2Load_balanced_resonance_Bzero_inconsistent
