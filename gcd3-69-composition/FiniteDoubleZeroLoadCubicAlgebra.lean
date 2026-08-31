import FiniteDoubleRho1Load

/-! # Zero-load cubic residue algebra on the balanced double-root chart

The four invariant rows of a transverse double-root jet, with no load
remainder, are already inconsistent at the balanced cubic resonance.
Specializing the loaded residual `r * (64 r^2 T + 9 A^3) = 0` at `T = 0`
forces `9 r A^3 = 0`.
-/

noncomputable section

/-- A zero-load jet cannot occupy the balanced cubic double-root chart:
the four rows force `9 r A^3 = 0`, contradicting `A ≠ 0` and `r ≠ 0`. -/
theorem GCD369CubeDoubleBlowup_zeroLoad_balanced_cubic_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (h1 : -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * Q +
        3 * r * B ^ 2)) = 0)
    (h3 :
      128 * (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2) -
        64 * A ^ 3 = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2) -
        314928 * (r * A) * A ^ 2 = 0) : False := by
  have h1T :
      -32 * (729 * (A ^ 2 * d - 2 * A * Q - B ^ 2)) -
        62208 * (0 : K) = 0 := by
    linear_combination h1
  have hrel :=
    GCD369CubeDoubleBlowup_rho1Load_balanced_resonance_load_relation
      A B Q r d (0 : K) h1T h2 h3 h4
  have h9 : r * ((9 : K) * A ^ 3) = 0 := by
    linear_combination hrel
  rcases mul_eq_zero.mp h9 with hr0 | hA3
  · exact hr hr0
  · rcases mul_eq_zero.mp hA3 with hn | hA30
    · norm_num at hn
    · exact (pow_ne_zero 3 hA) hA30

#print axioms GCD369CubeDoubleBlowup_zeroLoad_balanced_cubic_inconsistent
