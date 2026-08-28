import LowScale68SecondaryExtraction

/-! # The last two `(6,8)` secondary one-form equations

The preceding extraction module handles both invariants and the first
one-form row.  This module performs the same load-free/load decomposition for
the remaining two rows and connects their literal polynomial coefficients to
`F1` and `F0` of `FirstSecondaryFace68`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryOneForms68

variable {k : Type*} [Field k] [CharZero k]

/-- Exact load-free second one-form after the cubic translation. -/
def cubicHomogeneousRowOnePolynomial68 (A B c D e : k[X]) : k[X] :=
  lowerRowOnePolynomial68
    (cubicHomogeneousTPolynomial68 A B c e)
    (cubicHomogeneousUPolynomial68 A B c D)
    (cubicHomogeneousVPolynomial68 A B c D e)
    ((1 / 3 : k) • A ^ 2 + c) D
    ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)

/-- Deficit-two part of the load-free second one-form. -/
def firstSecondaryCoreRowOnePolynomial68 (A B c D e : k[X]) : k[X] :=
  (-4 / 81 : k) •
    (-(4 : k) • (A ^ 3 * B * derivative B) -
      (3 : k) • (A ^ 2 * B ^ 2 * derivative A) +
      (6 : k) • (A ^ 2 * B * derivative D) +
      (6 : k) • (A ^ 2 * D * derivative B) -
      (18 : k) • (A * c * derivative e) -
      (18 : k) • (A * e * derivative c) +
      (9 : k) • (D ^ 2 * derivative A) -
      (54 : k) • (e * derivative e))

/-- Deficit-three remainder of the load-free second one-form. -/
def cubicRemainderRowOnePolynomial68 (A B c D e : k[X]) : k[X] :=
  (-4 / 81 : k) •
    (-(3 : k) • (A * B ^ 2 * derivative c) -
      (12 : k) • (A * B * c * derivative B) -
      (9 : k) • (B ^ 2 * c * derivative A) -
      (9 : k) • (B ^ 2 * derivative e) +
      (9 : k) • (B * D * derivative c) +
      (9 : k) • (B * c * derivative D) +
      (27 : k) • (D * c * derivative B) +
      (18 : k) • (c ^ 2 * derivative c))

/-- Fully expanded load-free second row. -/
def cubicHomogeneousRowOneExpandedPolynomial68
    (A B c D e : k[X]) : k[X] :=
  firstSecondaryCoreRowOnePolynomial68 A B c D e +
    cubicRemainderRowOnePolynomial68 A B c D e

set_option maxHeartbeats 4000000 in
theorem cubicHomogeneousRowOnePolynomial68_eq_expanded
    (A B c D e : k[X]) :
    cubicHomogeneousRowOnePolynomial68 A B c D e =
      cubicHomogeneousRowOneExpandedPolynomial68 A B c D e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicHomogeneousRowOnePolynomial68,
    cubicHomogeneousRowOneExpandedPolynomial68,
    firstSecondaryCoreRowOnePolynomial68,
    cubicRemainderRowOnePolynomial68,
    cubicHomogeneousTPolynomial68, cubicHomogeneousUPolynomial68,
    cubicHomogeneousVPolynomial68, lowerRowOnePolynomial68,
    derivative_add, derivative_sub, derivative_smul, derivative_mul,
    derivative_pow, derivative_C, Polynomial.C_eq_natCast,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 3000000 in
/-- The deficit-two core of the second one-form is `(-8/81) F1`. -/
theorem firstSecondaryCoreRowOnePolynomial68_coeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
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
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA3deg : (A ^ 3).natDegree ≤ 6 * n := by
    compute_degree
    omega
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
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 3) B B
      (6 * n) (3 * n - g) (3 * n - g) (by omega) hA3deg hB hB
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
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) D B
      (4 * n) (5 * n - g) (3 * n - g) (by omega) hA2deg hD hB
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
    rw [Nat.cast_sub hg3]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) = 4 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg4]
    push_cast
    rfl
  have hcast5 : (((5 * n - g : ℕ) : k)) = 5 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg5]
    push_cast
    rfl
  have hcast6 : (((6 * n - g : ℕ) : k)) = 6 * (n : k) - (g : k) := by
    rw [Nat.cast_sub hg6]
    push_cast
    rfl
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  simp only [firstSecondaryOne68]
  ring

set_option maxHeartbeats 2000000 in
/-- The complete load-free second one-form has the same deficit-two
coefficient as its core; every term in the remainder has deficit three. -/
theorem cubicHomogeneousRowOnePolynomial68_secondaryCoeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
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
  exact firstSecondaryCoreRowOnePolynomial68_coeff A B c D e n g
    hn hg hsmall hA hB hc hD he

/-- Contribution of the constant-load pieces to the second one-form row. -/
def cubicLoadRowOnePolynomial68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : k[X] :=
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  Ul * derivative D + (2 : k) • (Tl * derivative E) -
    (2 : k) • (C0 * derivative Vl) - D * derivative Ul

/-- Linearity of the second one-form row under the homogeneous/load split. -/
theorem cubicRowOnePolynomial68_split
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    lowerRowOnePolynomial68
      (cubicHomogeneousTPolynomial68 A B c e +
        cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D)
      (cubicHomogeneousUPolynomial68 A B c D +
        cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e)
      (cubicHomogeneousVPolynomial68 A B c D e +
        cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta A B c D e)
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
    cubicHomogeneousRowOnePolynomial68 A B c D e +
      cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c D e := by
  simp only [cubicHomogeneousRowOnePolynomial68,
    cubicLoadRowOnePolynomial68, lowerRowOnePolynomial68, derivative_add,
    Polynomial.smul_eq_C_mul]
  ring

set_option maxHeartbeats 2000000 in
/-- The constant-load pieces lie strictly below the deficit-two coefficient
of the second one-form. -/
theorem cubicLoadRowOnePolynomial68_degree_lt
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he
  have hTl : Tl.natDegree ≤ 5 * n - g := by
    simpa only [Tl] using hloads.2.1
  have hUl : Ul.natDegree ≤ 6 * n := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlD : (Ul * derivative D).natDegree <
      12 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hTlE : (Tl * derivative E).natDegree <
      12 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hC0Vl : (C0 * derivative Vl).natDegree <
      12 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hDUl : (D * derivative Ul).natDegree <
      12 * n - 2 * g - 1 := by
    compute_degree
    omega
  change (Ul * derivative D + (2 : k) • (Tl * derivative E) -
    (2 : k) • (C0 * derivative Vl) - D * derivative Ul).natDegree < _
  compute_degree
  omega

set_option maxHeartbeats 3000000 in
/-- The literal integrated second one-form supplies `F₁` at its first
secondary coefficient. -/
theorem integratedLowerRowOnePolynomial68_secondaryCoeff
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (12 * n - 2 * g - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hsmall hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowOnePolynomial68_secondaryCoeff A B c D e n g
    hn hg hsmall hA hB hc hD he

/-! ## Terminal one-form and `F₀` -/

/-- Exact load-free terminal one-form after the cubic translation. -/
def cubicHomogeneousRowZeroPolynomial68 (A B c D e : k[X]) : k[X] :=
  lowerRowZeroPolynomial68
    (cubicHomogeneousUPolynomial68 A B c D)
    (cubicHomogeneousVPolynomial68 A B c D e) D
    ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)

/-- Deficit-two part of the load-free terminal one-form. -/
def firstSecondaryCoreRowZeroPolynomial68 (A B c D e : k[X]) : k[X] :=
  (4 / 81 : k) •
    (A ^ 2 * B * c * derivative A -
      (3 : k) • (A * D * c * derivative A) -
      (9 : k) • (D * e * derivative A))

/-- Deficit-three remainder of the load-free terminal one-form. -/
def cubicRemainderRowZeroPolynomial68 (A B c D e : k[X]) : k[X] :=
  (4 / 81 : k) •
    ((6 : k) • (A * B * D * derivative B) +
      (3 : k) • (A * B * c * derivative c) +
      (3 : k) • (B ^ 2 * D * derivative A) +
      (3 : k) • (B * c ^ 2 * derivative A) -
      (9 : k) • (B * D * derivative D) +
      (9 : k) • (B * c * derivative e) -
      (9 : k) • (D ^ 2 * derivative B) -
      (9 : k) • (D * c * derivative c))

/-- Fully expanded load-free terminal row. -/
def cubicHomogeneousRowZeroExpandedPolynomial68
    (A B c D e : k[X]) : k[X] :=
  firstSecondaryCoreRowZeroPolynomial68 A B c D e +
    cubicRemainderRowZeroPolynomial68 A B c D e

set_option maxHeartbeats 4000000 in
theorem cubicHomogeneousRowZeroPolynomial68_eq_expanded
    (A B c D e : k[X]) :
    cubicHomogeneousRowZeroPolynomial68 A B c D e =
      cubicHomogeneousRowZeroExpandedPolynomial68 A B c D e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicHomogeneousRowZeroPolynomial68,
    cubicHomogeneousRowZeroExpandedPolynomial68,
    firstSecondaryCoreRowZeroPolynomial68,
    cubicRemainderRowZeroPolynomial68,
    cubicHomogeneousUPolynomial68, cubicHomogeneousVPolynomial68,
    lowerRowZeroPolynomial68, derivative_add, derivative_sub,
    derivative_smul, derivative_mul, derivative_pow, derivative_C,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 2000000 in
/-- The deficit-two core of the terminal one-form is
`(8/81) n a F₀`. -/
theorem firstSecondaryCoreRowZeroPolynomial68_coeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (firstSecondaryCoreRowZeroPolynomial68 A B c D e).coeff
        (13 * n - 2 * g - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 : (A ^ 2 * B * c * derivative A).coeff
      (13 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) *
          ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 (A ^ 2) B c A
      (4 * n) (3 * n - g) (4 * n - g) (2 * n) (by omega)
      hA2deg hB hc hA
    have hi : 4 * n + (3 * n - g) + (4 * n - g) + 2 * n - 1 =
        13 * n - 2 * g - 1 := by omega
    rw [hi, hA2] at h
    exact h
  have h2 : (A * D * c * derivative A).coeff
      (13 * n - 2 * g - 1) =
      A.coeff (2 * n) * D.coeff (5 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) *
          ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 A D c A
      (2 * n) (5 * n - g) (4 * n - g) (2 * n) (by omega)
      hA hD hc hA
    have hi : 2 * n + (5 * n - g) + (4 * n - g) + 2 * n - 1 =
        13 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h3 : (D * e * derivative A).coeff (13 * n - 2 * g - 1) =
      D.coeff (5 * n - g) * e.coeff (6 * n - g) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 D e A
      (5 * n - g) (6 * n - g) (2 * n) (by omega) hD he hA
    have hi : (5 * n - g) + (6 * n - g) + 2 * n - 1 =
        13 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  simp only [firstSecondaryCoreRowZeroPolynomial68, coeff_smul, coeff_sub,
    h1, h2, h3, smul_eq_mul]
  push_cast
  simp only [firstSecondaryZero68]
  ring

set_option maxHeartbeats 2000000 in
/-- The complete load-free terminal one-form has the same deficit-two
coefficient as its core. -/
theorem cubicHomogeneousRowZeroPolynomial68_secondaryCoeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowZeroPolynomial68 A B c D e).coeff
        (13 * n - 2 * g - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hrem : (cubicRemainderRowZeroPolynomial68 A B c D e).natDegree <
      13 * n - 2 * g - 1 := by
    simp only [cubicRemainderRowZeroPolynomial68]
    compute_degree
    omega
  rw [cubicHomogeneousRowZeroPolynomial68_eq_expanded,
    cubicHomogeneousRowZeroExpandedPolynomial68, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrem, add_zero]
  exact firstSecondaryCoreRowZeroPolynomial68_coeff A B c D e n g
    hn hg hsmall hA hB hc hD he

/-- Contribution of the constant-load pieces to the terminal one-form. -/
def cubicLoadRowZeroPolynomial68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : k[X] :=
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  Ul * derivative E - D * derivative Vl

/-- Linearity of the terminal one-form under the homogeneous/load split. -/
theorem cubicRowZeroPolynomial68_split
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    lowerRowZeroPolynomial68
      (cubicHomogeneousUPolynomial68 A B c D +
        cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e)
      (cubicHomogeneousVPolynomial68 A B c D e +
        cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta A B c D e)
      D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
    cubicHomogeneousRowZeroPolynomial68 A B c D e +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c D e := by
  simp only [cubicHomogeneousRowZeroPolynomial68,
    cubicLoadRowZeroPolynomial68, lowerRowZeroPolynomial68, derivative_add,
    Polynomial.smul_eq_C_mul]
  ring

set_option maxHeartbeats 2000000 in
/-- The constant-load pieces lie strictly below the deficit-two coefficient
of the terminal one-form. -/
theorem cubicLoadRowZeroPolynomial68_degree_lt
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 13 * n - 2 * g - 1 := by
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he
  have hUl : Ul.natDegree ≤ 6 * n := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlE : (Ul * derivative E).natDegree <
      13 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hDVl : (D * derivative Vl).natDegree <
      13 * n - 2 * g - 1 := by
    compute_degree
    omega
  change (Ul * derivative E - D * derivative Vl).natDegree < _
  compute_degree
  omega

set_option maxHeartbeats 3000000 in
/-- The literal integrated terminal one-form supplies `F₀` at its first
secondary coefficient. -/
theorem integratedLowerRowZeroPolynomial68_secondaryCoeff
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
        (13 * n - 2 * g - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroPolynomial68_degree_lt
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hsmall hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowZeroPolynomial68_secondaryCoeff A B c D e n g
    hn hg hsmall hA hB hc hD he

/-! ## Packaging the literal five-row face -/

set_option maxHeartbeats 3000000 in
/-- The three literal one-form rows supply `F₂`, `F₁`, and `F₀`.  The
terminal row is stated only at the target coefficient so this lemma applies
both before and after denominator-clearing expansion. -/
theorem integratedPolynomialLowerRows_secondaryEquations68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B
        ((1 / 3 : k) • A ^ 2 + c) D)
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      B ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = 0)
    (hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
        (13 * n - 2 * g - 1) = 0) :
    firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) = 0 ∧
      firstSecondaryZero68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) = 0 := by
  have htwo := congrArg
    (fun p : k[X] => p.coeff (11 * n - 2 * g - 1)) hrowTwo
  rw [integratedLowerRowTwoPolynomial68_secondaryCoeff
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he] at htwo
  simp only [coeff_zero] at htwo
  have htwo0 := (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) hrowOne
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he] at hone
  simp only [coeff_zero] at hone
  have hone0 := (mul_eq_zero.mp hone).resolve_left (by norm_num)
  rw [integratedLowerRowZeroPolynomial68_secondaryCoeff
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he] at hrowZero
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfactor : (8 / 81 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 := (mul_eq_zero.mp hrowZero).resolve_left hfactor
  exact ⟨htwo0, hone0, hzero0⟩

set_option maxHeartbeats 3000000 in
/-- The literal integrated polynomial lower system supplies all five
equations of the first secondary face in the chamber `2g<n`. -/
theorem integratedPolynomialLowerSystem_firstSecondaryFace68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    FirstSecondaryFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) := by
  obtain ⟨i4, hI4⟩ := hsys.firstFour
  obtain ⟨i3, hI3⟩ := hsys.firstThree
  have hinv := polynomialSecondaryInvariantEquations68
    l beta gamma delta epsilon zeta i4 i3 A B C0 c D E e n g
    hn hg hsmall hA hB hc hD he hC0 hE0 hI4 hI3
  have hrowTwo := hsys.rowTwo
  rw [hC0, hE0] at hrowTwo
  have htwo := congrArg
    (fun p : k[X] => p.coeff (11 * n - 2 * g - 1)) hrowTwo
  rw [integratedLowerRowTwoPolynomial68_secondaryCoeff
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he] at htwo
  simp only [coeff_zero] at htwo
  have htwo0 : firstSecondaryTwo68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hrowOne := hsys.rowOne
  rw [hC0, hE0] at hrowOne
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) hrowOne
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he] at hone
  simp only [coeff_zero] at hone
  have hone0 : firstSecondaryOne68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hone).resolve_left (by norm_num)
  have hrowZero := hsys.rowZero
  rw [hC0, hE0] at hrowZero
  have hzero := congrArg
    (fun p : k[X] => p.coeff (13 * n - 2 * g - 1)) hrowZero
  rw [integratedLowerRowZeroPolynomial68_secondaryCoeff
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he] at hzero
  have hindex : 13 * n - 2 * g - 1 ≠ 0 := by omega
  simp only [coeff_C, if_neg hindex] at hzero
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfactor : (8 / 81 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 : firstSecondaryZero68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hfactor
  exact ⟨hinv.1, hinv.2, htwo0, hone0, hzero0⟩

/-- Direct classified form of the literal first secondary face. -/
theorem integratedPolynomialLowerSystem_firstSecondaryClassified68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    e.coeff (6 * n - g) = 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) =
        3 * D.coeff (5 * n - g) := by
  exact firstSecondaryFace68_classify_of_two_mul_gap_lt_radius n g
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha hsmall
    (integratedPolynomialLowerSystem_firstSecondaryFace68
      l alpha beta gamma delta epsilon zeta eta terminal
      A B C0 c D E e n g hn hg hsmall hA hB hc hD he ha hC0 hE0 hsys)

end SecondaryOneForms68

#print axioms cubicHomogeneousRowOnePolynomial68_eq_expanded
#print axioms firstSecondaryCoreRowOnePolynomial68_coeff
#print axioms cubicHomogeneousRowOnePolynomial68_secondaryCoeff
#print axioms cubicRowOnePolynomial68_split
#print axioms cubicLoadRowOnePolynomial68_degree_lt
#print axioms integratedLowerRowOnePolynomial68_secondaryCoeff
#print axioms cubicHomogeneousRowZeroPolynomial68_eq_expanded
#print axioms firstSecondaryCoreRowZeroPolynomial68_coeff
#print axioms cubicHomogeneousRowZeroPolynomial68_secondaryCoeff
#print axioms cubicRowZeroPolynomial68_split
#print axioms cubicLoadRowZeroPolynomial68_degree_lt
#print axioms integratedLowerRowZeroPolynomial68_secondaryCoeff
#print axioms integratedPolynomialLowerRows_secondaryEquations68
#print axioms integratedPolynomialLowerSystem_firstSecondaryFace68
#print axioms integratedPolynomialLowerSystem_firstSecondaryClassified68

end Max11DegreeRoutes
