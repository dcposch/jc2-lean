import FiniteDoubleC4LoadPolys
import FiniteLoadAnnihilation

/-! # The weight-five `c4` load in the second double-root blowup -/

noncomputable section

theorem GCD369CubeDoubleBlowup_c4Load_linear_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) -
        165888 * r ^ 5 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) + 414720 * r ^ 6 * T = 0)
    (h3 : -2 * A ^ 2 * r ^ 2 * d = 0) : False := by
  have hload : (912384 : K) * r ^ 7 * T = 0 := by
    linear_combination -3 * r ^ 2 * h1 + r * h2 - 11664 * h3
  rcases mul_eq_zero.mp hload with hc | hT0
  · norm_num at hc
    exact hr hc
  · exact hT hT0

theorem GCD369CubeDoubleBlowup_c4Load_quadratic_beforeCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hr : r ≠ 0) (hT : T ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) -
        165888 * r ^ 5 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) + 414720 * r ^ 6 * T = 0)
    (_h3 : -2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        4665600 * r ^ 8 * T = 0) : False := by
  have hload : (-14370048 : K) * r ^ 8 * T = 0 := by
    linear_combination 36 * r ^ 3 * h1 - 9 * r ^ 2 * h2 + h4
  rcases mul_eq_zero.mp hload with hc | hT0
  · norm_num at hc
    exact hr hc
  · exact hT hT0

theorem GCD369CubeDoubleBlowup_c4Load_linear_atCubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B C r d T : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * B * r - 2 * A * C)) -
        165888 * r ^ 5 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r)) + 414720 * r ^ 6 * T = 0)
    (h3 : 128 * (-2 * A ^ 2 * r ^ 2 * d) - 64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * (r * B + C)) -
        314928 * (r * A) * A ^ 2 - 4665600 * r ^ 8 * T = 0) : False := by
  have hcubic : (-223074 : K) * r * A ^ 3 = 0 := by
    linear_combination
      (-45 / 4) * r ^ 3 * h1 +
      (27 / 4) * r ^ 2 * h2 -
      (45927 / 32) * r * h3 + h4
  rcases mul_eq_zero.mp hcubic with hc | hA3
  · norm_num at hc
    exact hr hc
  · exact (pow_ne_zero 3 hA) hA3

theorem GCD369CubeDoubleBlowup_c4Load_balanced_resonance_Bzero_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d T : K) (hA : A ≠ 0) (hr : r ≠ 0) (hB : B = 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) -
        165888 * r ^ 5 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) + 414720 * r ^ 6 * T = 0)
    (h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * (r * A) * A ^ 2 - 4665600 * r ^ 8 * T = 0) : False := by
  subst B
  apply GCD369CubeDoubleBlowup_c4Load_linear_atCubic_inconsistent
    A 0 Q r d T hA hr
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3
  · linear_combination h4

#print axioms GCD369CubeDoubleBlowup_c4Load_linear_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c4Load_quadratic_beforeCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c4Load_linear_atCubic_inconsistent
#print axioms GCD369CubeDoubleBlowup_c4Load_balanced_resonance_Bzero_inconsistent
