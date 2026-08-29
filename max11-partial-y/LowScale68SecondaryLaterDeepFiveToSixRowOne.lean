import LowScale68SecondaryLaterDeepFiveToSixEndgame

/-! # The row-one face in the later-deep five-to-six chamber

This module closes the two spurious families left by the I4/I3/row-zero
classification.  The only surviving top packet is `e = 0`, `a*b = 3*d`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSixRowOne68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The usual top-product/derivative formula remains valid when the degree
bound on the differentiated factor is zero. -/
theorem coeff_mul_mul_derivative_at_bounds_nonneg68
    (p q r : k[X]) (u v w : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hr : r.natDegree ≤ w) :
    (p * q * derivative r).coeff (u + v + w - 1) =
      p.coeff u * q.coeff v * r.coeff w * (w : k) := by
  by_cases hw : 0 < w
  · exact coeff_mul_mul_derivative_at_bounds68 p q r u v w hw hp hq hr
  · have hw0 : w = 0 := Nat.eq_zero_of_not_pos hw
    subst w
    rw [eq_C_of_natDegree_le_zero hr, derivative_C]
    simp

/-- The homogeneous row-one coefficient at the five-to-six face.  Unlike
the earlier extraction lemma, this includes the endpoint `2g = 6n`, where
`B` has degree bound zero. -/
theorem firstSecondaryCoreRowOnePolynomial68_coeff_fiveToSix
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (firstSecondaryCoreRowOnePolynomial68 A B c D e).coeff
        (12 * n - 2 * g - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by compute_degree; omega
  have hA3deg : (A ^ 3).natDegree ≤ 6 * n := by compute_degree; omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hD2deg : (D ^ 2).natDegree ≤ 10 * n - 2 * g := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hA3 : (A ^ 3).coeff (6 * n) = A.coeff (2 * n) ^ 3 := by
    have h := coeff_pow_at_bound68 A (2 * n) 3 hA
    have hi : 3 * (2 * n) = 6 * n := by omega
    simpa only [hi] using h
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hD2 : (D ^ 2).coeff (10 * n - 2 * g) =
      D.coeff (5 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 D (5 * n - g) 2 hD
    have hi : 2 * (5 * n - g) = 10 * n - 2 * g := by omega
    simpa only [hi] using h
  have h1 : (A ^ 3 * B * derivative B).coeff (12 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 3 * B.coeff (3 * n - g) ^ 2 *
        ((3 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds_nonneg68 (A ^ 3) B B
      (6 * n) (3 * n - g) (3 * n - g) hA3deg hB hB
    have hi : 6 * n + (3 * n - g) + (3 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hA3] at h
    ring_nf at h ⊢
    exact h
  have h2 : (A ^ 2 * B ^ 2 * derivative A).coeff
      (12 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 2 *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) (B ^ 2) A
      (4 * n) (6 * n - 2 * g) (2 * n) (by omega)
      hA2deg hB2deg hA
    have hi : 4 * n + (6 * n - 2 * g) + 2 * n - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hA2, hB2] at h
    exact h
  have h3 : (A ^ 2 * B * derivative D).coeff
      (12 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        D.coeff (5 * n - g) * ((5 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B D
      (4 * n) (3 * n - g) (5 * n - g) (by omega) hA2deg hB hD
    have hi : 4 * n + (3 * n - g) + (5 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hA2] at h
    exact h
  have h4 : (A ^ 2 * D * derivative B).coeff
      (12 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * D.coeff (5 * n - g) *
        B.coeff (3 * n - g) * ((3 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds_nonneg68 (A ^ 2) D B
      (4 * n) (5 * n - g) (3 * n - g) hA2deg hD hB
    have hi : 4 * n + (5 * n - g) + (3 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hA2] at h
    exact h
  have h5 : (A * c * derivative e).coeff (12 * n - 2 * g - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - g) * ((6 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A c e
      (2 * n) (4 * n - g) (6 * n - g) (by omega) hA hc he
    have hi : 2 * n + (4 * n - g) + (6 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h6 : (A * e * derivative c).coeff (12 * n - 2 * g - 1) =
      A.coeff (2 * n) * e.coeff (6 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A e c
      (2 * n) (6 * n - g) (4 * n - g) (by omega) hA he hc
    have hi : 2 * n + (6 * n - g) + (4 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h7 : (D ^ 2 * derivative A).coeff (12 * n - 2 * g - 1) =
      D.coeff (5 * n - g) ^ 2 * A.coeff (2 * n) *
        ((2 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 (D ^ 2) A
      (10 * n - 2 * g) (2 * n) (by omega) hD2deg hA
    have hi : (10 * n - 2 * g) + 2 * n - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi, hD2] at h
    exact h
  have h8 : (e * derivative e).coeff (12 * n - 2 * g - 1) =
      e.coeff (6 * n - g) ^ 2 * ((6 * n - g : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 e e
      (6 * n - g) (6 * n - g) (by omega) he he
    have hi : (6 * n - g) + (6 * n - g) - 1 =
        12 * n - 2 * g - 1 := by omega
    rw [hi] at h
    ring_nf at h ⊢
    exact h
  simp only [firstSecondaryCoreRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2, h3, h4, h5, h6, h7, h8, smul_eq_mul]
  have hg3 : g ≤ 3 * n := by omega
  have hg4 : g ≤ 4 * n := by omega
  have hg5 : g ≤ 5 * n := by omega
  have hg6 : g ≤ 6 * n := by omega
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg3]; push_cast; rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) = 4 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg4]; push_cast; rfl
  have hcast5 : (((5 * n - g : ℕ) : k)) = 5 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg5]; push_cast; rfl
  have hcast6 : (((6 * n - g : ℕ) : k)) = 6 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg6]; push_cast; rfl
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  simp only [firstSecondaryOne68]
  ring

theorem cubicHomogeneousRowOnePolynomial68_secondaryCoeff_fiveToSix
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowOnePolynomial68 A B c D e).coeff
        (12 * n - 2 * g - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hrem : (cubicRemainderRowOnePolynomial68 A B c D e).natDegree <
      12 * n - 2 * g - 1 := by
    simp only [cubicRemainderRowOnePolynomial68]
    compute_degree
    omega
  rw [cubicHomogeneousRowOnePolynomial68_eq_expanded,
    cubicHomogeneousRowOneExpandedPolynomial68, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrem, add_zero]
  exact firstSecondaryCoreRowOnePolynomial68_coeff_fiveToSix
    A B c D e n g hn hwindow hA hB hc hD he

/-- After `l=beta=delta=0`, the remaining load correction in row one has a
small exact Wronskian form. -/
theorem cubicLoadRowOnePolynomial68_zero_beta_delta_exact
    (alpha gamma epsilon zeta eta : k) (A B c D e : k[X]) :
    cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c D e =
      (2 / 3 * gamma : k) • (B * derivative D - D * derivative B) +
      (4 / 3 * gamma : k) • (A * derivative e) -
      (4 / 3 * gamma : k) • (c * derivative c) +
      (2 / 3 * epsilon : k) • (A * derivative c) +
      (2 * epsilon : k) • derivative e + zeta • derivative D := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowOnePolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68, derivative_add,
    derivative_sub, derivative_smul, derivative_mul, derivative_pow,
    derivative_C, zero_pow, zero_smul, smul_zero, zero_mul, mul_zero,
    add_zero, zero_add, sub_zero, Polynomial.C_eq_natCast,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

theorem cubicLoadRowOnePolynomial68_degree_lt_fiveToSix
    (alpha gamma epsilon zeta eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  rw [cubicLoadRowOnePolynomial68_zero_beta_delta_exact]
  compute_degree
  omega

/-- Exact `F1` extraction from the integrated row-one equation throughout
`5n < 2g ≤ 6n`. -/
theorem integratedLowerRowOnePolynomial68_fiveToSix_forces_firstSecondaryOne
    (alpha gamma epsilon zeta eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hrow : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = 0) :
    firstSecondaryOne68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon zeta eta A B c D e
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split] at hrow
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) hrow
  simp only [coeff_add, coeff_zero,
    cubicHomogeneousRowOnePolynomial68_secondaryCoeff_fiveToSix
      A B c D e n g hn hwindow hA hB hc hD he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_fiveToSix
        alpha gamma epsilon zeta eta A B c D e n g hn hwindow
        hA hB hc hD he), add_zero] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (by norm_num)

/-- Pure scalar elimination: `F1` absorbs the middle family into the main
family and contradicts the all-but-`e` family using secondary attainment. -/
theorem firstSecondaryOne68_e_c_zero_d_eq_ab_fiveToSix
    (N G a b : k) :
    firstSecondaryOne68 N G a b 0 (a * b) 0 =
      (4 : k) * a ^ 3 * b ^ 2 * (6 * N - G) := by
  simp only [firstSecondaryOne68]
  ring

theorem firstSecondaryOne68_b_c_d_zero_fiveToSix
    (N G a e : k) :
    firstSecondaryOne68 N G a 0 0 0 e =
      (27 : k) * e ^ 2 * (G - 6 * N) := by
  simp only [firstSecondaryOne68]
  ring

theorem firstSecondary_fiveToSix_classification_with_one68
    (N G a b c d e : k)
    (ha : a ≠ 0) (hgap : G - 6 * N ≠ 0)
    (hclass : (e = 0 ∧ a * b = 3 * d) ∨
      (e = 0 ∧ c = 0 ∧ a * b = d) ∨
      (b = 0 ∧ c = 0 ∧ d = 0))
    (hone : firstSecondaryOne68 N G a b c d e = 0)
    (hattain : b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0) :
    e = 0 ∧ a * b = 3 * d := by
  rcases hclass with hmain | hmiddle | hlast
  · exact hmain
  · rcases hmiddle with ⟨he0, hc0, hab⟩
    have hfac : (4 : k) * a ^ 3 * b ^ 2 * (6 * N - G) = 0 := by
      rw [← firstSecondaryOne68_e_c_zero_d_eq_ab_fiveToSix N G a b]
      simpa only [he0, hc0, hab] using hone
    have hgap' : 6 * N - G ≠ 0 := by
      intro hzero
      apply hgap
      linear_combination -hzero
    have hb : b = 0 := by
      have hleft := (mul_eq_zero.mp hfac).resolve_right hgap'
      have hcoef : (4 : k) * a ^ 3 ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 3 ha)
      have hb2 : b ^ 2 = 0 :=
        (mul_eq_zero.mp hleft).resolve_left hcoef
      simpa only [pow_two, mul_self_eq_zero] using hb2
    refine ⟨he0, ?_⟩
    rw [hb, mul_zero] at hab ⊢
    rw [← hab]
    ring
  · rcases hlast with ⟨hb0, hc0, hd0⟩
    have hfac : (27 : k) * e ^ 2 * (G - 6 * N) = 0 := by
      rw [← firstSecondaryOne68_b_c_d_zero_fiveToSix N G a e]
      simpa only [hb0, hc0, hd0] using hone
    have he0 : e = 0 := by
      have hleft := (mul_eq_zero.mp hfac).resolve_right hgap
      have he2 : e ^ 2 = 0 :=
        (mul_eq_zero.mp hleft).resolve_left (by norm_num)
      simpa only [pow_two, mul_self_eq_zero] using he2
    exact False.elim (by
      rcases hattain with hb | hc | hd | he
      · exact hb hb0
      · exact hc hc0
      · exact hd hd0
      · exact he he0)

/-- Secondary attainment sharpens the surviving family to two honest
subbranches: either both `b,d` are nonzero, or both vanish and `c` is the
attained coordinate. -/
theorem firstSecondary_mainFamily_attainment_split68
    (a b c d e : k) (ha : a ≠ 0)
    (hmain : e = 0 ∧ a * b = 3 * d)
    (hattain : b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0) :
    (b ≠ 0 ∧ d ≠ 0) ∨ (b = 0 ∧ d = 0 ∧ c ≠ 0) := by
  rcases hmain with ⟨he0, hab⟩
  by_cases hb : b = 0
  · right
    have hd : d = 0 := by
      have h3d : (3 : k) * d = 0 := by
        rw [← hab, hb, mul_zero]
      exact (mul_eq_zero.mp h3d).resolve_left (by norm_num)
    refine ⟨hb, hd, ?_⟩
    rcases hattain with hb' | hc | hd' | he'
    · exact False.elim (hb' hb)
    · exact hc
    · exact False.elim (hd' hd)
    · exact False.elim (he' he0)
  · left
    refine ⟨hb, ?_⟩
    intro hd
    have hab0 : a * b = 0 := by rw [hab, hd, mul_zero]
    exact hb ((mul_eq_zero.mp hab0).resolve_left ha)

/-- The surviving relation is algebraically saturated at this face: all five
ordinary first-secondary scalar equations vanish identically on it.  Thus a
strictly lower coefficient is genuinely needed for the next reduction. -/
theorem firstSecondary_mainFamily_saturates_face68
    (N G a b c d e : k) (he0 : e = 0) (hab : a * b = 3 * d) :
    firstSecondaryFour68 a b c d e = 0 ∧
    firstSecondaryThree68 a b c d e = 0 ∧
    firstSecondaryTwo68 N G a b c d e = 0 ∧
    firstSecondaryOne68 N G a b c d e = 0 ∧
    firstSecondaryZero68 a b c d e = 0 := by
  subst e
  simp only [firstSecondaryFour68, firstSecondaryThree68,
    firstSecondaryTwo68, firstSecondaryOne68, firstSecondaryZero68,
    mul_zero, zero_mul, add_zero, sub_zero, zero_add]
  constructor
  · linear_combination c * hab
  constructor
  · linear_combination (a * b - d) * hab
  constructor
  · linear_combination (2 * a * c * G - 8 * a * c * N) * hab
  constructor
  · linear_combination (2 * a ^ 2 * b * G - 9 * a ^ 2 * b * N -
      3 * a * d * N) * hab
  · linear_combination (a * c) * hab

set_option maxHeartbeats 24000000 in
/-- Source-facing conclusion for the whole later-deep five-to-six window:
row one removes the two extraneous top families. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_mainFamily68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g)
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_topClassification68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change
    (ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g)) ∨
    (ee.coeff (6 * n - g) = 0 ∧ ce.coeff (4 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        De.coeff (5 * n - g)) ∨
    (Be.coeff (3 * n - g) = 0 ∧ ce.coeff (4 * n - g) = 0 ∧
      De.coeff (5 * n - g) = 0) at hclass
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4 := hI4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
      hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hrow : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hl, hbeta, hdelta, hCrec, hErec] at hrow
  have hone :=
    integratedLowerRowOnePolynomial68_fiveToSix_forces_firstSecondaryOne
      alpha gamma epsilon zeta eta Ae Be ce De ee n g data.hn hwindow
      data.hA data.hB data.hc data.hD data.he hrow
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 ∨
      De.coeff (5 * n - g) ≠ 0 ∨ ee.coeff (6 * n - g) ≠ 0) at hsecondary
  have hgap : (g : k) - 6 * (n : k) ≠ 0 := by
    have hnat : g ≠ 6 * n := by omega
    intro hzero
    apply hnat
    exact_mod_cast (sub_eq_zero.mp hzero)
  exact firstSecondary_fiveToSix_classification_with_one68
    (n : k) (g : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) data.ha hgap hclass hone hsecondary.2.2.2.2.2

end LaterDeepFiveToSixRowOne68

#print axioms coeff_mul_mul_derivative_at_bounds_nonneg68
#print axioms firstSecondaryCoreRowOnePolynomial68_coeff_fiveToSix
#print axioms cubicLoadRowOnePolynomial68_zero_beta_delta_exact
#print axioms integratedLowerRowOnePolynomial68_fiveToSix_forces_firstSecondaryOne
#print axioms firstSecondary_fiveToSix_classification_with_one68
#print axioms firstSecondary_mainFamily_attainment_split68
#print axioms firstSecondary_mainFamily_saturates_face68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_mainFamily68

end Max11DegreeRoutes
