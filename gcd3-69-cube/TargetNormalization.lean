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

namespace GCD369CubePolynomialSource

/-- Adding a ground-field constant to the first target coordinate does not
change its inner-source derivative. -/
@[simp] theorem sourceXDeriv_add_targetConstant
    {k : Type*} [Field k] (p : k[X][X]) (tau : k) :
    GCD369CubeSourceXDeriv (p + C (C tau)) =
      GCD369CubeSourceXDeriv p := by
  apply Polynomial.ext
  intro n
  rw [GCD369CubeSourceXDeriv_coeff,
    GCD369CubeSourceXDeriv_coeff, coeff_add]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [coeff_C, hn]

/-- The literal polynomial source after the legal first-target translation
`P ↦ P + tau`.  All actual degrees, leading cube coefficients, and the
nonzero scalar Jacobian are preserved. -/
noncomputable def targetTranslate
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    GCD369CubePolynomialSource k where
  s := S.s
  p := S.p + C (C tau)
  q := S.q
  j := S.j
  hs := S.hs
  hj := S.hj
  hp := by simpa using S.hp
  hq := S.hq
  hp6 := by simpa using S.hp6
  hq9 := S.hq9
  hjac := by
    unfold GCD369CubeBivariateJacobian
    simp only [sourceXDeriv_add_targetConstant,
      derivative_add, derivative_C, add_zero]
    exact S.hjac

@[simp] theorem targetTranslate_s
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).s = S.s := rfl

@[simp] theorem targetTranslate_p
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).p = S.p + C (C tau) := rfl

@[simp] theorem targetTranslate_q
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).q = S.q := rfl

@[simp] theorem targetTranslate_j
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).j = S.j := rfl

@[simp] theorem targetTranslate_sRat
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).sRat = S.sRat := rfl

@[simp] theorem targetTranslate_A
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).A = S.A := by
  unfold A
  rw [targetTranslate_sRat]
  simp [targetTranslate]

@[simp] theorem targetTranslate_B
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).B = S.B := rfl

@[simp] theorem targetTranslate_translation
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).translation = S.translation := by
  simp [translation]

@[simp] theorem targetTranslate_pRat
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).pRat =
      S.pRat + C (algebraMap k (RatFunc k) tau) := by
  simp [pRat, coefficientMap, targetTranslate,
    RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

@[simp] theorem targetTranslate_qRat
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).qRat = S.qRat := rfl

/-- The normalized depressed sextic changes only in its constant
coefficient under first-target translation. -/
@[simp] theorem targetTranslate_normalizedP
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).normalizedP =
      S.normalizedP + C (algebraMap k (RatFunc k) tau) := by
  simp [normalizedP, GCD369CubeSourceTransform, add_comp]

@[simp] theorem targetTranslate_normalizedP_coeff_zero
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).normalizedP.coeff 0 =
      S.normalizedP.coeff 0 + algebraMap k (RatFunc k) tau := by
  rw [targetTranslate_normalizedP]
  simp

@[simp] theorem targetTranslate_normalizedP_coeff_succ
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) (n : ℕ) :
    (S.targetTranslate tau).normalizedP.coeff (n + 1) =
      S.normalizedP.coeff (n + 1) := by
  rw [targetTranslate_normalizedP]
  simp [coeff_C]

/-- The normalized nonic is unchanged by translating the first target. -/
@[simp] theorem targetTranslate_normalizedQ
    {k : Type*} [Field k]
    (S : GCD369CubePolynomialSource k) (tau : k) :
    (S.targetTranslate tau).normalizedQ = S.normalizedQ := by
  simp [normalizedQ]

/-- Canonical literal source in the `c₃ = 0` first-target slice. -/
noncomputable def targetNormalizedSource
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    GCD369CubePolynomialSource k :=
  S.targetTranslate (2 * S.faberConstantParameters.c3 / 3)

/-- On the `d = 0` stratum, the canonical translated literal source has an
explicit Faber decomposition with `c₃ = 0`. -/
theorem targetNormalizedSource_normalizedQ
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hd : S.faberConstantParameters.d = 0) :
    let T := S.targetNormalizedSource
    let P := S.faberConstantParameters
    T.normalizedQ =
      GCD369CubeFaberNormalPolynomial
        (T.normalizedP.coeff 0) (T.normalizedP.coeff 1)
        (T.normalizedP.coeff 2) (T.normalizedP.coeff 3)
        (T.normalizedP.coeff 4)
        0 (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c6)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4) 0
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) (P.c1 - 7 * P.c7 * P.c3 / 9))
        (algebraMap k (RatFunc k) (P.c0 - 2 * P.c6 * P.c3 / 3)) := by
  let T := S.targetNormalizedSource
  let P := S.faberConstantParameters
  let N := S.faberNormalForm
  change T.normalizedQ =
    GCD369CubeFaberNormalPolynomial
      (T.normalizedP.coeff 0) (T.normalizedP.coeff 1)
      (T.normalizedP.coeff 2) (T.normalizedP.coeff 3)
      (T.normalizedP.coeff 4)
      0 (algebraMap k (RatFunc k) P.c7)
      (algebraMap k (RatFunc k) P.c6)
      (algebraMap k (RatFunc k) P.c5)
      (algebraMap k (RatFunc k) P.c4) 0
      (algebraMap k (RatFunc k) P.c2)
      (algebraMap k (RatFunc k) (P.c1 - 7 * P.c7 * P.c3 / 9))
      (algebraMap k (RatFunc k) (P.c0 - 2 * P.c6 * P.c3 / 3))
  have hdN : N.d = 0 := by
    rw [P.hd, hd, map_zero]
  have hqold : S.normalizedQ =
      GCD369CubeFaberNormalPolynomial
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        0 (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c6)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1)
        (algebraMap k (RatFunc k) P.c0) := by
    have h := N.hq
    rw [hdN, P.hc7, P.hc6, P.hc5, P.hc4, P.hc3,
      P.hc2, P.hc1, P.hc0] at h
    simpa only [GCD369CubeFaberNormalPolynomial] using h
  have hkill := GCD369CubeFaberNormalPolynomial_killC3
    (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
    (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
    (S.normalizedP.coeff 4)
    (algebraMap k (RatFunc k) P.c7)
    (algebraMap k (RatFunc k) P.c6)
    (algebraMap k (RatFunc k) P.c5)
    (algebraMap k (RatFunc k) P.c4)
    (algebraMap k (RatFunc k) P.c3)
    (algebraMap k (RatFunc k) P.c2)
    (algebraMap k (RatFunc k) P.c1)
    (algebraMap k (RatFunc k) P.c0)
  calc
    T.normalizedQ = S.normalizedQ := by
      simp [T, targetNormalizedSource]
    _ = GCD369CubeFaberNormalPolynomial
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        0 (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c6)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1)
        (algebraMap k (RatFunc k) P.c0) := hqold
    _ = GCD369CubeFaberNormalPolynomial
        (S.normalizedP.coeff 0 +
          2 * algebraMap k (RatFunc k) P.c3 / 3)
        (S.normalizedP.coeff 1) (S.normalizedP.coeff 2)
        (S.normalizedP.coeff 3) (S.normalizedP.coeff 4)
        0 (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c6)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4) 0
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1 -
          7 * algebraMap k (RatFunc k) P.c7 *
            algebraMap k (RatFunc k) P.c3 / 9)
        (algebraMap k (RatFunc k) P.c0 -
          2 * algebraMap k (RatFunc k) P.c6 *
            algebraMap k (RatFunc k) P.c3 / 3) := hkill
    _ = GCD369CubeFaberNormalPolynomial
        (T.normalizedP.coeff 0) (T.normalizedP.coeff 1)
        (T.normalizedP.coeff 2) (T.normalizedP.coeff 3)
        (T.normalizedP.coeff 4)
        0 (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c6)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4) 0
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) (P.c1 - 7 * P.c7 * P.c3 / 9))
        (algebraMap k (RatFunc k) (P.c0 - 2 * P.c6 * P.c3 / 3)) := by
      congr 1 <;>
        simp [T, targetNormalizedSource, P, map_sub, map_mul, map_div₀,
          map_ofNat] <;>
        ring

/-- Explicit normal-form witness for the canonical translated source.  Its
parameters expose literal zeroes for both `d` and `c₃`; no uniqueness or
choice property of the canonical Faber peeling is used. -/
noncomputable def targetNormalizedFaberNormalForm
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hd : S.faberConstantParameters.d = 0) :
    let T := S.targetNormalizedSource
    GCD369CubeFaberNormalForm
      (T.normalizedP.coeff 0) (T.normalizedP.coeff 1)
      (T.normalizedP.coeff 2) (T.normalizedP.coeff 3)
      (T.normalizedP.coeff 4) T.normalizedQ := by
  let T := S.targetNormalizedSource
  let P := S.faberConstantParameters
  exact {
    d := 0
    c7 := algebraMap k (RatFunc k) P.c7
    c6 := algebraMap k (RatFunc k) P.c6
    c5 := algebraMap k (RatFunc k) P.c5
    c4 := algebraMap k (RatFunc k) P.c4
    c3 := 0
    c2 := algebraMap k (RatFunc k) P.c2
    c1 := algebraMap k (RatFunc k) (P.c1 - 7 * P.c7 * P.c3 / 9)
    c0 := algebraMap k (RatFunc k) (P.c0 - 2 * P.c6 * P.c3 / 3)
    hd := GCD369CubeRatFuncDerivative_zero
    hc7 := by
      rw [RatFunc.algebraMap_eq_C]
      exact GCD369CubeRatFuncDerivative_C _
    hc6 := by
      rw [RatFunc.algebraMap_eq_C]
      exact GCD369CubeRatFuncDerivative_C _
    hc5 := by
      rw [RatFunc.algebraMap_eq_C]
      exact GCD369CubeRatFuncDerivative_C _
    hc4 := by
      rw [RatFunc.algebraMap_eq_C]
      exact GCD369CubeRatFuncDerivative_C _
    hc3 := GCD369CubeRatFuncDerivative_zero
    hc2 := by
      rw [RatFunc.algebraMap_eq_C]
      exact GCD369CubeRatFuncDerivative_C _
    hc1 := by
      rw [RatFunc.algebraMap_eq_C]
      exact GCD369CubeRatFuncDerivative_C _
    hc0 := by
      rw [RatFunc.algebraMap_eq_C]
      exact GCD369CubeRatFuncDerivative_C _
    hq := by
      simpa only [T, P, GCD369CubeFaberNormalPolynomial] using
        S.targetNormalizedSource_normalizedQ hd
  }

end GCD369CubePolynomialSource

#print axioms GCD369CubeFaberNormalPolynomial_targetTranslate
#print axioms GCD369CubeFaberNormalPolynomial_killC3
#print axioms GCD369CubePolynomialSource.targetTranslate
#print axioms GCD369CubePolynomialSource.targetNormalizedFaberNormalForm
