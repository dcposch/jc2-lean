import FaberFirstIntegrals

noncomputable section
open Polynomial

/-! # First-target translation in the cube Faber form

On the `d = 0` stratum, translating the first target coordinate changes only
the constant sextic coefficient and three bookkeeping parameters.  The
identity below proves directly that `c₃` can be gauged to zero while retaining
the invariant barred value of `c₁`.
-/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Exact covariance of the complete Faber polynomial under a constant
translation of the first target coordinate, on the `d = 0` stratum. -/
theorem GCD369CubeFaberNormalPolynomial_targetTranslate
    {K : Type*} [Field K] [CharZero K]
    (a0 a1 a2 a3 a4 c7 c6 c5 c4 c3 c2 c1 c0 tau : K) :
    GCD369CubeFaberNormalPolynomial
        a0 a1 a2 a3 a4 0 c7 c6 c5 c4 c3 c2 c1 c0 =
      GCD369CubeFaberNormalPolynomial
        (a0 + tau) a1 a2 a3 a4 0 c7 c6 c5 c4
        (c3 - 3 * tau / 2) c2
        (c1 - 7 * c7 * tau / 6) (c0 - c6 * tau) := by
  ext n
  by_cases hn : n ≤ 9
  · interval_cases n <;>
      norm_num [GCD369CubeFaberNormalPolynomial,
        GCD369CubeFaberNine, GCD369CubeFaberEight,
        GCD369CubeFaberSeven, GCD369CubeFaberSix,
        GCD369CubeFaberFive, GCD369CubeFaberFour,
        GCD369CubeFaberThree, GCD369CubeFaberTwo,
        GCD369CubeFaberOne, GCD369CubeDepressedSextic,
        coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_monomial] <;>
      ring_nf <;>
      norm_num [coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, coeff_add, coeff_sub, coeff_C_mul,
        coeff_C, coeff_monomial] <;>
      ring
  · have hn9 : 9 < n := by omega
    have hleft :
        (GCD369CubeFaberNormalPolynomial
          a0 a1 a2 a3 a4 0 c7 c6 c5 c4 c3 c2 c1 c0).natDegree ≤ 9 := by
      dsimp [GCD369CubeFaberNormalPolynomial,
        GCD369CubeFaberNine, GCD369CubeFaberEight,
        GCD369CubeFaberSeven, GCD369CubeFaberSix,
        GCD369CubeFaberFive, GCD369CubeFaberFour,
        GCD369CubeFaberThree, GCD369CubeFaberTwo,
        GCD369CubeFaberOne, GCD369CubeDepressedSextic]
      compute_degree
    have hright :
        (GCD369CubeFaberNormalPolynomial
          (a0 + tau) a1 a2 a3 a4 0 c7 c6 c5 c4
          (c3 - 3 * tau / 2) c2
          (c1 - 7 * c7 * tau / 6) (c0 - c6 * tau)).natDegree ≤ 9 := by
      dsimp [GCD369CubeFaberNormalPolynomial,
        GCD369CubeFaberNine, GCD369CubeFaberEight,
        GCD369CubeFaberSeven, GCD369CubeFaberSix,
        GCD369CubeFaberFive, GCD369CubeFaberFour,
        GCD369CubeFaberThree, GCD369CubeFaberTwo,
        GCD369CubeFaberOne, GCD369CubeDepressedSextic]
      compute_degree
    rw [natDegree_le_iff_coeff_eq_zero.mp hleft n hn9,
      natDegree_le_iff_coeff_eq_zero.mp hright n hn9]

/-- Choosing `tau = 2 c₃ / 3` gives the canonical `c₃ = 0` slice and
the invariant barred parameter `c₁ - 7 c₇ c₃ / 9`. -/
theorem GCD369CubeFaberNormalPolynomial_killC3
    {K : Type*} [Field K] [CharZero K]
    (a0 a1 a2 a3 a4 c7 c6 c5 c4 c3 c2 c1 c0 : K) :
    GCD369CubeFaberNormalPolynomial
        a0 a1 a2 a3 a4 0 c7 c6 c5 c4 c3 c2 c1 c0 =
      GCD369CubeFaberNormalPolynomial
        (a0 + 2 * c3 / 3) a1 a2 a3 a4 0 c7 c6 c5 c4 0 c2
        (c1 - 7 * c7 * c3 / 9) (c0 - 2 * c6 * c3 / 3) := by
  have h := GCD369CubeFaberNormalPolynomial_targetTranslate
    a0 a1 a2 a3 a4 c7 c6 c5 c4 c3 c2 c1 c0 (2 * c3 / 3)
  convert h using 1 <;> ring

#print axioms GCD369CubeFaberNormalPolynomial_targetTranslate
#print axioms GCD369CubeFaberNormalPolynomial_killC3
