import Sol68FiveToSixUniformLoadFreeStrideScratch

/-! # Uniform resultant attack on the five-to-six all-nonzero cusp branch

At an arbitrary positive load-free offset `s < 7n-2g` the uniform edge
classification leaves the all-nonzero cusp `a*b^2+3*c^2 = 0`.  This file
attacks that branch uniformly, without enumerating fixed offsets and
without any transverse-degree bound or unbounded Taylor tower.

Three sources are consumed.  First, the top coefficients of all three
one-form rows at the offset (`11n-2g-s-1`, `12n-2g-s-1`, `13n-2g-s-1`)
are computed exactly: each is a scalar multiple of one of the two
first-integral faces, and every constant load lies strictly below as
long as `s < 7n-2g` — the `zeta` load reaches the row tops exactly at
the terminal wall, which is preserved, not crossed.  The rows are
therefore exact face shadows and contribute no new constraint.

Second, the two first integrals are extracted one full lattice stride
below their faces (`9n-2g-s-60` and `10n-2g-s-60`).  Alignment of the
residue phases (`60 ∣ n, g, s`, forced by the branch nonzeros through
the expansion lattice) collapses each convolution to the two aligned
decompositions; the only surviving load is the literal wall term
`zeta * A.coeff (9n-2g-s-60)`, kept explicitly.  The second-jet pair is
a linear system in the new edge pair `(d', e')` whose matrix has
determinant `-(a*b^2+3*c^2) = 0` on the cusp: the system is singular,
`(d', e')` stays one-parameter free along the kernel `b*e' = -c*d'`,
and the cokernel produces exactly one compatibility scalar.

The resulting closure is NOT exact.  The smallest residual is the
compatibility recurrence

  `(2*a*b*(b*c₂ - c*b₂) - a₂*b^2*c) * d_s
     + (3/8)*zeta*a*b^2*A.coeff (9n-2g-s-60)
     + (3/2)*b*c*(d^2).coeff (10n-2g-s-60) = 0`,

which in the interior chambers divides down to `2a(b*c₂ - c*b₂) = a₂*b*c`
(deep offsets) and `2a(b*c₂ - c*b₂) + (3/2)*c*d₆₀ = a₂*b*c` (first
stride), tying the second-level jets `a₂, b₂, c₂`.  The first genuinely
independent unused row is the third-jet first-integral pair at
`9n-2g-s-120` / `10n-2g-s-120`, beginning the `s/60`-deep ladder toward
the loaded rung at `13n-2g-2s-1`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixUniformCuspResultant68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Residue-phase-safe second jet of the `B`-coordinate.  At the closed
window boundary `2g = 6n` the coordinate is a constant and the jet is
zero by definition, avoiding truncated-subtraction artifacts. -/
def uniformCuspSecondJetB68 (B : k[X]) (n g : ℕ) : k :=
  if 60 ≤ 3 * n - g then B.coeff (3 * n - g - 60) else 0

theorem uniformCuspSecondJetB68_of_le (B : k[X]) (n g : ℕ)
    (h : 60 ≤ 3 * n - g) :
    uniformCuspSecondJetB68 B n g = B.coeff (3 * n - g - 60) := if_pos h

theorem uniformCuspSecondJetB68_of_boundary (B : k[X]) (n g : ℕ)
    (h : 3 * n - g < 60) :
    uniformCuspSecondJetB68 B n g = 0 := if_neg (by omega)

/-- Support of a product of `60`-lattice polynomials stays on the
lattice. -/
theorem coeff_mul_lattice_support68 (p q : k[X])
    (hp : ∀ i : ℕ, ¬ (60 ∣ i) → p.coeff i = 0)
    (hq : ∀ i : ℕ, ¬ (60 ∣ i) → q.coeff i = 0) :
    ∀ i : ℕ, ¬ (60 ∣ i) → (p * q).coeff i = 0 := by
  intro i hi
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hxmem : x.1 + x.2 = i := by simpa using hx
  by_cases h1 : 60 ∣ x.1
  · have h2 : ¬ 60 ∣ x.2 := by omega
    rw [hq x.2 h2, mul_zero]
  · rw [hp x.1 h1, zero_mul]

/-- One full lattice stride below a product of separate degree bounds:
when the left factor is supported on the `60`-lattice and its bound is
aligned, only the two aligned decompositions survive. -/
theorem coeff_mul_offset_sixty_left_lattice68 (p q : k[X]) (u v : ℕ)
    (hu : 60 ≤ u) (hv : 60 ≤ v) (hdvd : 60 ∣ u)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hsupp : ∀ i : ℕ, ¬ (60 ∣ i) → p.coeff i = 0) :
    (p * q).coeff (u + v - 60) =
      p.coeff (u - 60) * q.coeff v + p.coeff u * q.coeff (v - 60) := by
  have hmem1 : u - 60 ∈ Finset.range (u + v - 60 + 1) :=
    Finset.mem_range.mpr (by omega)
  have hmem2 : u ∈ (Finset.range (u + v - 60 + 1)).erase (u - 60) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have hzero : ∀ i ∈
      ((Finset.range (u + v - 60 + 1)).erase (u - 60)).erase u,
      p.coeff i * q.coeff (u + v - 60 - i) = 0 := by
    intro i hi
    have hi1 := Finset.mem_erase.mp hi
    have hi2 := Finset.mem_erase.mp hi1.2
    have hi3 := Finset.mem_range.mp hi2.2
    by_cases hgt : u < i
    · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt hgt), zero_mul]
    · by_cases hlt : i < u - 60
      · rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega)),
          mul_zero]
      · rw [hsupp i (by omega), zero_mul]
  have h4 : (p * q).coeff (u + v - 60) =
      ∑ i ∈ Finset.range (u + v - 60 + 1),
        p.coeff i * q.coeff (u + v - 60 - i) := by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have h1 := Finset.add_sum_erase (Finset.range (u + v - 60 + 1))
    (fun i => p.coeff i * q.coeff (u + v - 60 - i)) hmem1
  have h2 := Finset.add_sum_erase
    ((Finset.range (u + v - 60 + 1)).erase (u - 60))
    (fun i => p.coeff i * q.coeff (u + v - 60 - i)) hmem2
  have h3 : ∑ i ∈ ((Finset.range (u + v - 60 + 1)).erase (u - 60)).erase u,
      p.coeff i * q.coeff (u + v - 60 - i) = 0 :=
    Finset.sum_eq_zero hzero
  rw [h4, ← h1, ← h2, h3, add_zero]
  show p.coeff (u - 60) * q.coeff (u + v - 60 - (u - 60)) +
      p.coeff u * q.coeff (u + v - 60 - u) =
    p.coeff (u - 60) * q.coeff v + p.coeff u * q.coeff (v - 60)
  rw [show u + v - 60 - (u - 60) = v from by omega,
    show u + v - 60 - u = v - 60 from by omega]

/-- Weak three-factor derivative coefficient: the derivative factor may
be constant, in which case both sides vanish. -/
theorem coeff_mul_mul_derivative_at_bounds_weak68 (p q r : k[X])
    (u v w : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hr : r.natDegree ≤ w) :
    (p * q * derivative r).coeff (u + v + w - 1) =
      p.coeff u * q.coeff v * r.coeff w * (w : k) := by
  rcases Nat.eq_zero_or_pos w with hw0 | hw
  · have hd0 : derivative r = 0 := by
      rw [eq_C_of_natDegree_le_zero (show r.natDegree ≤ 0 by omega)]
      exact derivative_C
    rw [hd0, mul_zero, coeff_zero, hw0]
    simp
  · exact coeff_mul_mul_derivative_at_bounds68 p q r u v w hw hp hq hr

/-! ## Uniform one-form row tops: exact face shadows -/

/-- Homogeneous row-two top at an arbitrary load-free offset: an exact
multiple of the I4 face. -/
theorem secondaryResidualRowTwoPolynomial68_coeff_uniform_fiveToSix
    (A B c d e : k[X]) (n g s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * g - s - 1) =
      (8 / 9 : k) * ((8 * n - 2 * g - s : ℕ) : k) * A.coeff (2 * n) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - s) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - s)) := by
  have h1raw := coeff_mul_mul_derivative_at_bounds68 A B e
    (2 * n) (3 * n - g) (6 * n - g - s) (by omega) hA hB he
  rw [show 2 * n + (3 * n - g) + (6 * n - g - s) - 1 =
    11 * n - 2 * g - s - 1 from by omega] at h1raw
  have h2raw := coeff_mul_mul_derivative_at_bounds_weak68 A e B
    (2 * n) (6 * n - g - s) (3 * n - g) hA he hB
  rw [show 2 * n + (6 * n - g - s) + (3 * n - g) - 1 =
    11 * n - 2 * g - s - 1 from by omega] at h2raw
  have h2 : (A * derivative B * e).coeff (11 * n - 2 * g - s - 1) =
      A.coeff (2 * n) * e.coeff (6 * n - g - s) *
        B.coeff (3 * n - g) * ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2raw
  have h3raw := coeff_mul_mul_derivative_at_bounds68 A c d
    (2 * n) (4 * n - g) (5 * n - g - s) (by omega) hA hc hd
  rw [show 2 * n + (4 * n - g) + (5 * n - g - s) - 1 =
    11 * n - 2 * g - s - 1 from by omega] at h3raw
  have h4raw := coeff_mul_mul_derivative_at_bounds68 A d c
    (2 * n) (5 * n - g - s) (4 * n - g) (by omega) hA hd hc
  rw [show 2 * n + (5 * n - g - s) + (4 * n - g) - 1 =
    11 * n - 2 * g - s - 1 from by omega] at h4raw
  have h4 : (A * derivative c * d).coeff (11 * n - 2 * g - s - 1) =
      A.coeff (2 * n) * d.coeff (5 * n - g - s) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h4raw
  have h5raw := coeff_mul_mul_derivative_at_bounds68 B e A
    (3 * n - g) (6 * n - g - s) (2 * n) (by omega) hB he hA
  rw [show 3 * n - g + (6 * n - g - s) + 2 * n - 1 =
    11 * n - 2 * g - s - 1 from by omega] at h5raw
  have h5 : (derivative A * B * e).coeff (11 * n - 2 * g - s - 1) =
      B.coeff (3 * n - g) * e.coeff (6 * n - g - s) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5raw
  have h6raw := coeff_mul_mul_derivative_at_bounds68 c d A
    (4 * n - g) (5 * n - g - s) (2 * n) (by omega) hc hd hA
  rw [show 4 * n - g + (5 * n - g - s) + 2 * n - 1 =
    11 * n - 2 * g - s - 1 from by omega] at h6raw
  have h6 : (derivative A * c * d).coeff (11 * n - 2 * g - s - 1) =
      c.coeff (4 * n - g) * d.coeff (5 * n - g - s) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6raw
  have hlow1 : (derivative A * B ^ 3).natDegree <
      11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow2 : (B ^ 2 * derivative d).natDegree <
      11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow3 : (B * derivative B * d).natDegree <
      11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow4 : (B * c * derivative c).natDegree <
      11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow5 : (derivative B * c ^ 2).natDegree <
      11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow6 : (d * derivative e).natDegree <
      11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow7 : (derivative d * e).natDegree <
      11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hcastE : ((6 * n - g - s : ℕ) : k) + ((3 * n - g : ℕ) : k) =
      ((8 * n - 2 * g - s : ℕ) : k) + ((n : ℕ) : k) := by
    have h : (6 * n - g - s) + (3 * n - g) = (8 * n - 2 * g - s) + n := by
      omega
    calc ((6 * n - g - s : ℕ) : k) + ((3 * n - g : ℕ) : k)
        = (((6 * n - g - s) + (3 * n - g) : ℕ) : k) := by push_cast; ring
      _ = (((8 * n - 2 * g - s) + n : ℕ) : k) := by rw [h]
      _ = ((8 * n - 2 * g - s : ℕ) : k) + ((n : ℕ) : k) := by
          push_cast; ring
  have hcastD : ((5 * n - g - s : ℕ) : k) + ((4 * n - g : ℕ) : k) =
      ((8 * n - 2 * g - s : ℕ) : k) + ((n : ℕ) : k) := by
    have h : (5 * n - g - s) + (4 * n - g) = (8 * n - 2 * g - s) + n := by
      omega
    calc ((5 * n - g - s : ℕ) : k) + ((4 * n - g : ℕ) : k)
        = (((5 * n - g - s) + (4 * n - g) : ℕ) : k) := by push_cast; ring
      _ = (((8 * n - 2 * g - s) + n : ℕ) : k) := by rw [h]
      _ = ((8 * n - 2 * g - s : ℕ) : k) + ((n : ℕ) : k) := by
          push_cast; ring
  have hcastW : ((2 * n : ℕ) : k) = 2 * ((n : ℕ) : k) := by
    push_cast; ring
  simp only [secondaryResidualRowTwoPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1raw, h2, h3raw, h4, h5, h6,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7, smul_eq_mul]
  linear_combination
    ((8 / 9 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - g - s)) * hcastE +
      ((8 / 9 : k) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - g - s)) * hcastD -
      ((4 / 9 : k) * A.coeff (2 * n) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - s) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - s))) * hcastW

/-- Homogeneous row-one top at an arbitrary load-free offset: an exact
multiple of the I3 face. -/
theorem secondaryResidualRowOnePolynomial68_coeff_uniform_fiveToSix
    (A B c d e : k[X]) (n g s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 2 * g - s - 1) =
      (-8 / 27 : k) * ((10 * n - 2 * g - s : ℕ) : k) * A.coeff (2 * n) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) * d.coeff (5 * n - g - s) -
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - s)) := by
  have hA2 : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA2c : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) * A.coeff (2 * n) := by
    rw [pow_two]
    have h := coeff_mul_at_bounds68 A A (2 * n) (2 * n) hA hA
    rw [show 2 * n + 2 * n = 4 * n from by omega] at h
    exact h
  have h1raw := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B d
    (4 * n) (3 * n - g) (5 * n - g - s) (by omega) hA2 hB hd
  rw [show 4 * n + (3 * n - g) + (5 * n - g - s) - 1 =
    12 * n - 2 * g - s - 1 from by omega, hA2c] at h1raw
  have h2raw := coeff_mul_mul_derivative_at_bounds_weak68 (A ^ 2) d B
    (4 * n) (5 * n - g - s) (3 * n - g) hA2 hd hB
  rw [show 4 * n + (5 * n - g - s) + (3 * n - g) - 1 =
    12 * n - 2 * g - s - 1 from by omega, hA2c] at h2raw
  have h2 : (A ^ 2 * derivative B * d).coeff (12 * n - 2 * g - s - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * d.coeff (5 * n - g - s) *
        B.coeff (3 * n - g) * ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2raw
  have h3raw := coeff_mul_mul_mul_derivative_at_bounds68 A B d A
    (2 * n) (3 * n - g) (5 * n - g - s) (2 * n) (by omega) hA hB hd hA
  rw [show 2 * n + (3 * n - g) + (5 * n - g - s) + 2 * n - 1 =
    12 * n - 2 * g - s - 1 from by omega] at h3raw
  have h3 : (A * derivative A * B * d).coeff (12 * n - 2 * g - s - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) * d.coeff (5 * n - g - s) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h3raw
  have h4raw := coeff_mul_mul_derivative_at_bounds68 A c e
    (2 * n) (4 * n - g) (6 * n - g - s) (by omega) hA hc he
  rw [show 2 * n + (4 * n - g) + (6 * n - g - s) - 1 =
    12 * n - 2 * g - s - 1 from by omega] at h4raw
  have h5raw := coeff_mul_mul_derivative_at_bounds68 A e c
    (2 * n) (6 * n - g - s) (4 * n - g) (by omega) hA he hc
  rw [show 2 * n + (6 * n - g - s) + (4 * n - g) - 1 =
    12 * n - 2 * g - s - 1 from by omega] at h5raw
  have h5 : (A * derivative c * e).coeff (12 * n - 2 * g - s - 1) =
      A.coeff (2 * n) * e.coeff (6 * n - g - s) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5raw
  have hlow1 : (derivative A * B ^ 2 * c).natDegree <
      12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow2 : (derivative A * d ^ 2).natDegree <
      12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow3 : (B ^ 2 * derivative e).natDegree <
      12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow4 : (B * c * derivative d).natDegree <
      12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow5 : (B * derivative c * d).natDegree <
      12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow6 : (derivative B * c * d).natDegree <
      12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow7 : (c ^ 2 * derivative c).natDegree <
      12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow8 : (e * derivative e).natDegree <
      12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hcastX : ((5 * n - g - s : ℕ) : k) + ((3 * n - g : ℕ) : k) +
      ((2 * n : ℕ) : k) = ((10 * n - 2 * g - s : ℕ) : k) := by
    have h : (5 * n - g - s) + (3 * n - g) + 2 * n =
        10 * n - 2 * g - s := by omega
    calc ((5 * n - g - s : ℕ) : k) + ((3 * n - g : ℕ) : k) +
        ((2 * n : ℕ) : k)
        = (((5 * n - g - s) + (3 * n - g) + 2 * n : ℕ) : k) := by
          push_cast; ring
      _ = ((10 * n - 2 * g - s : ℕ) : k) := by rw [h]
  have hcastY : ((6 * n - g - s : ℕ) : k) + ((4 * n - g : ℕ) : k) =
      ((10 * n - 2 * g - s : ℕ) : k) := by
    have h : (6 * n - g - s) + (4 * n - g) = 10 * n - 2 * g - s := by
      omega
    calc ((6 * n - g - s : ℕ) : k) + ((4 * n - g : ℕ) : k)
        = (((6 * n - g - s) + (4 * n - g) : ℕ) : k) := by push_cast; ring
      _ = ((10 * n - 2 * g - s : ℕ) : k) := by rw [h]
  simp only [secondaryResidualRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1raw, h2, h3, h4raw, h5,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8, smul_eq_mul]
  linear_combination
    ((-8 / 27 : k) * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        d.coeff (5 * n - g - s)) * hcastX +
      ((8 / 9 : k) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - g - s)) * hcastY

/-- Homogeneous row-zero top at an arbitrary load-free offset: an exact
multiple of the I4 face.  This is the uniform version of the verified
offset-`120` extraction. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_uniform_fiveToSix
    (A B c d e : k[X]) (n g s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 2 * g - s - 1) =
      (-8 / 27 : k) * (n : k) * A.coeff (2 * n) ^ 2 *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - s) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - s)) := by
  have h1raw := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - g - s) (2 * n) (by omega)
    hA hB he hA
  rw [show 2 * n + (3 * n - g) + (6 * n - g - s) + 2 * n - 1 =
    13 * n - 2 * g - s - 1 from by omega] at h1raw
  have h1 : (A * derivative A * B * e).coeff (13 * n - 2 * g - s - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - g - s) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1raw
  have h2raw := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - g - s) (2 * n) (by omega)
    hA hc hd hA
  rw [show 2 * n + (4 * n - g) + (5 * n - g - s) + 2 * n - 1 =
    13 * n - 2 * g - s - 1 from by omega] at h2raw
  have h2 : (A * derivative A * c * d).coeff (13 * n - 2 * g - s - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - g - s) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2raw
  have hlow1 : (A * B ^ 2 * derivative d).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow2 : (A * B * derivative B * d).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow3 : (derivative A * B * c ^ 2).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow4 : (derivative A * d * e).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow5 : (B * c * derivative e).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow6 : (B * d * derivative d).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow7 : (derivative B * d ^ 2).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow8 : (c * derivative c * d).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8, smul_eq_mul]
  push_cast
  ring

/-! ## Uniform pinned loads and their strict sub-top degrees -/

/-- Exact row-two load with the five-to-six pins `l=beta=delta=0`; the
whole `alpha` load cancels and `eta` is inert. -/
theorem cubicLoadRowTwoPolynomial68_uniform_pinned_eq68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e =
      (4 / 3 * gamma : k) • (A * derivative d) -
        (4 / 3 * gamma : k) • (B * derivative c) -
        (4 / 3 * gamma : k) • (c * derivative B) -
        (2 / 3 * gamma : k) • (d * derivative A) -
        (1 / 3 * epsilon : k) • (derivative A * B) +
        (2 / 3 * epsilon : k) • (A * derivative B) +
        (2 * epsilon : k) • derivative d +
        (2 / 3 * zeta : k) • (A * derivative A) +
        zeta • derivative c := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-- Exact row-one load with the five-to-six pins. -/
theorem cubicLoadRowOnePolynomial68_uniform_pinned_eq68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) :
    cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e =
      (4 / 3 * gamma : k) • (A * derivative e) -
        (4 / 3 * gamma : k) • (c * derivative c) +
        (2 / 9 * gamma : k) • (derivative A * B ^ 2) +
        (2 / 3 * gamma : k) • (B * derivative d) -
        (2 / 3 * gamma : k) • (d * derivative B) +
        (2 / 3 * epsilon : k) • (A * derivative c) +
        (2 * epsilon : k) • derivative e +
        (1 / 3 * zeta : k) • (derivative A * B) +
        (1 / 3 * zeta : k) • (A * derivative B) +
        zeta • derivative d := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowOnePolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-- Exact row-zero load with the five-to-six pins, retaining the live
`zeta` block `zeta • E'`. -/
theorem cubicLoadRowZeroPolynomial68_uniform_pinned_eq68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) :
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e =
      (2 / 9 * gamma : k) • (B * derivative A * c) +
        (2 / 3 * gamma : k) • (B * derivative e) -
        (1 / 9 * epsilon : k) • (A * B * derivative A) -
        (2 / 9 * gamma : k) • (A * derivative A * d) -
        (2 / 3 * gamma : k) • (d * derivative c) -
        (1 / 3 * epsilon : k) • (d * derivative A) +
        (1 / 9 * zeta : k) • (A ^ 2 * derivative A) +
        (1 / 3 * zeta : k) • (derivative A * c) +
        (1 / 3 * zeta : k) • (A * derivative c) +
        zeta • derivative e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68,
    zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-- The row-two load stays strictly below the uniform row-two top on the
whole load-free interval; the `zeta` block would reach it exactly at
`s = 7n-2g`. -/
theorem cubicLoadRowTwoPolynomial68_coeff_uniform_top_fiveToSix
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) (n g s : ℕ)
    (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s) :
    (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (11 * n - 2 * g - s - 1) = 0 := by
  rw [cubicLoadRowTwoPolynomial68_uniform_pinned_eq68]
  have hlow1 : (A * derivative d).natDegree < 11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow2 : (B * derivative c).natDegree < 11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow3 : (c * derivative B).natDegree < 11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow4 : (d * derivative A).natDegree < 11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow5 : (derivative A * B).natDegree < 11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow6 : (A * derivative B).natDegree < 11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow7 : (derivative d).natDegree < 11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow8 : (A * derivative A).natDegree < 11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow9 : (derivative c).natDegree < 11 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9, mul_zero, add_zero, sub_zero,
    zero_add, neg_zero]

/-- The row-one load stays strictly below the uniform row-one top on the
whole load-free interval. -/
theorem cubicLoadRowOnePolynomial68_coeff_uniform_top_fiveToSix
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) (n g s : ℕ)
    (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (12 * n - 2 * g - s - 1) = 0 := by
  rw [cubicLoadRowOnePolynomial68_uniform_pinned_eq68]
  have hlow1 : (A * derivative e).natDegree < 12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow2 : (c * derivative c).natDegree < 12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow3 : (derivative A * B ^ 2).natDegree <
      12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow4 : (B * derivative d).natDegree < 12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow5 : (d * derivative B).natDegree < 12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow6 : (A * derivative c).natDegree < 12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow7 : (derivative e).natDegree < 12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow8 : (derivative A * B).natDegree < 12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow9 : (A * derivative B).natDegree < 12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow10 : (derivative d).natDegree < 12 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9,
    coeff_eq_zero_of_natDegree_lt hlow10, mul_zero, add_zero, sub_zero,
    zero_add, neg_zero]

/-- The row-zero load stays strictly below the uniform row-zero top on
the whole load-free interval; the `zeta` block `A^2*A'` reaches the top
exactly at the terminal wall `s = 7n-2g`. -/
theorem cubicLoadRowZeroPolynomial68_coeff_uniform_top_fiveToSix
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) (n g s : ℕ)
    (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (13 * n - 2 * g - s - 1) = 0 := by
  rw [cubicLoadRowZeroPolynomial68_uniform_pinned_eq68]
  have hlow1 : (B * derivative A * c).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow2 : (B * derivative e).natDegree < 13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow3 : (A * B * derivative A).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow4 : (A * derivative A * d).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow5 : (d * derivative c).natDegree < 13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow6 : (d * derivative A).natDegree < 13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow7 : (A ^ 2 * derivative A).natDegree <
      13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow8 : (derivative A * c).natDegree < 13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow9 : (A * derivative c).natDegree < 13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  have hlow10 : (derivative e).natDegree < 13 * n - 2 * g - s - 1 := by
    compute_degree
    omega
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9,
    coeff_eq_zero_of_natDegree_lt hlow10, mul_zero, add_zero, sub_zero,
    zero_add, neg_zero]

/-- All three one-form rows are exact face shadows at their uniform top
coefficients: on the two-face locus every residual-plus-load top
coefficient vanishes identically, so the rows carry no constraint beyond
the faces anywhere strictly inside the load-free interval. -/
theorem fiveToSix_uniformCusp_oneFormTops_shadow68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) (n g s : ℕ)
    (hn : 0 < n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload : s < 7 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s)
    (hface4 : B.coeff (3 * n - g) * e.coeff (6 * n - g - s) +
      c.coeff (4 * n - g) * d.coeff (5 * n - g - s) = 0)
    (hface3 : -A.coeff (2 * n) * B.coeff (3 * n - g) *
        d.coeff (5 * n - g - s) +
      3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - s) = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (11 * n - 2 * g - s - 1) = 0 ∧
      (secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (12 * n - 2 * g - s - 1) = 0 ∧
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (13 * n - 2 * g - s - 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [coeff_add,
      secondaryResidualRowTwoPolynomial68_coeff_uniform_fiveToSix
        A B c d e n g s hn hs hwindow hload hA hB hc hd he,
      cubicLoadRowTwoPolynomial68_coeff_uniform_top_fiveToSix
        alpha gamma epsilon zeta eta A B c d e n g s hn hs hwindow hload
        hA hB hc hd he]
    linear_combination ((8 / 9 : k) * ((8 * n - 2 * g - s : ℕ) : k) *
      A.coeff (2 * n)) * hface4
  · rw [coeff_add,
      secondaryResidualRowOnePolynomial68_coeff_uniform_fiveToSix
        A B c d e n g s hn hs hwindow hload hA hB hc hd he,
      cubicLoadRowOnePolynomial68_coeff_uniform_top_fiveToSix
        alpha gamma epsilon zeta eta A B c d e n g s hn hs hwindow hload
        hA hB hc hd he]
    linear_combination ((8 / 27 : k) * ((10 * n - 2 * g - s : ℕ) : k) *
      A.coeff (2 * n)) * hface3
  · rw [coeff_add,
      secondaryResidualRowZeroPolynomial68_coeff_uniform_fiveToSix
        A B c d e n g s hn hs hwindow hload hA hB hc hd he,
      cubicLoadRowZeroPolynomial68_coeff_uniform_top_fiveToSix
        alpha gamma epsilon zeta eta A B c d e n g s hn hs hwindow hload
        hA hB hc hd he]
    linear_combination ((-8 / 27 : k) * (n : k) *
      A.coeff (2 * n) ^ 2) * hface4

/-! ## Uniform second-jet extraction of the two first integrals -/

/-- Second jet of `B*e` one lattice stride below the I4 face, covering
the closed boundary `2g = 6n` through the phase-safe jet symbol. -/
theorem mul_coeff_secondJet_Be_uniformCusp68
    (B e : k[X]) (n g s : ℕ)
    (hn120 : 120 ≤ n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload2 : s + 60 ≤ 7 * n - 2 * g)
    (hdn : 60 ∣ n) (hdg : 60 ∣ g)
    (hB : B.natDegree ≤ 3 * n - g) (he : e.natDegree ≤ 6 * n - g - s)
    (hBsupp : ∀ i : ℕ, ¬ (60 ∣ i) → B.coeff i = 0) :
    (B * e).coeff (9 * n - 2 * g - s - 60) =
      uniformCuspSecondJetB68 B n g * e.coeff (6 * n - g - s) +
        B.coeff (3 * n - g) * e.coeff (6 * n - g - s - 60) := by
  by_cases hcase : 60 ≤ 3 * n - g
  · have h := coeff_mul_offset_sixty_left_lattice68 B e
      (3 * n - g) (6 * n - g - s) hcase (by omega) (by omega) hB he hBsupp
    rw [show 3 * n - g + (6 * n - g - s) - 60 =
      9 * n - 2 * g - s - 60 from by omega] at h
    rw [h, uniformCuspSecondJetB68_of_le B n g hcase]
  · have hzero : 3 * n - g = 0 := by omega
    have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero (by omega)
    have hb : (B * e).coeff (9 * n - 2 * g - s - 60) =
        B.coeff 0 * e.coeff (9 * n - 2 * g - s - 60) := by
      conv_lhs => rw [hBC]
      rw [coeff_C_mul]
    rw [hb, uniformCuspSecondJetB68_of_boundary B n g (by omega), hzero,
      show 9 * n - 2 * g - s - 60 = 6 * n - g - s - 60 from by omega]
    ring

/-- Second jet of `A*B` one lattice stride below its top, covering the
closed boundary through the phase-safe jet symbol. -/
theorem mul_coeff_secondJet_AB_uniformCusp68
    (A B : k[X]) (n g : ℕ)
    (hn120 : 120 ≤ n) (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hdn : 60 ∣ n) (hdg : 60 ∣ g)
    (hA : A.natDegree ≤ 2 * n) (hB : B.natDegree ≤ 3 * n - g)
    (hAsupp : ∀ i : ℕ, ¬ (60 ∣ i) → A.coeff i = 0) :
    (A * B).coeff (5 * n - g - 60) =
      A.coeff (2 * n) * uniformCuspSecondJetB68 B n g +
        A.coeff (2 * n - 60) * B.coeff (3 * n - g) := by
  by_cases hcase : 60 ≤ 3 * n - g
  · have h := coeff_mul_offset_sixty_left_lattice68 A B
      (2 * n) (3 * n - g) (by omega) hcase (by omega) hA hB hAsupp
    rw [show 2 * n + (3 * n - g) - 60 = 5 * n - g - 60 from by omega] at h
    rw [h, uniformCuspSecondJetB68_of_le B n g hcase]
    ring
  · have hzero : 3 * n - g = 0 := by omega
    have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero (by omega)
    have hb : (A * B).coeff (5 * n - g - 60) =
        A.coeff (5 * n - g - 60) * B.coeff 0 := by
      conv_lhs => rw [hBC]
      rw [coeff_mul_C]
    rw [hb, uniformCuspSecondJetB68_of_boundary B n g (by omega), hzero,
      show 5 * n - g - 60 = 2 * n - 60 from by omega]
    ring

/-- Homogeneous I4 one lattice stride below the uniform face: the
residue phases collapse the convolution to the aligned second-jet
pairs. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_uniform_secondJet_fiveToSix
    (B c d e : k[X]) (n g s : ℕ)
    (hn120 : 120 ≤ n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload2 : s + 60 ≤ 7 * n - 2 * g)
    (hdn : 60 ∣ n) (hdg : 60 ∣ g)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s)
    (hBsupp : ∀ i : ℕ, ¬ (60 ∣ i) → B.coeff i = 0)
    (hcsupp : ∀ i : ℕ, ¬ (60 ∣ i) → c.coeff i = 0) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 2 * g - s - 60) =
      (8 / 3 : k) *
        (uniformCuspSecondJetB68 B n g * e.coeff (6 * n - g - s) +
          B.coeff (3 * n - g) * e.coeff (6 * n - g - s - 60) +
          c.coeff (4 * n - g - 60) * d.coeff (5 * n - g - s) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - s - 60)) := by
  have hBe := mul_coeff_secondJet_Be_uniformCusp68 B e n g s
    hn120 hs hwindow hload2 hdn hdg hB he hBsupp
  have hcd := coeff_mul_offset_sixty_left_lattice68 c d
    (4 * n - g) (5 * n - g - s) (by omega) (by omega) (by omega)
    hc hd hcsupp
  rw [show 4 * n - g + (5 * n - g - s) - 60 =
    9 * n - 2 * g - s - 60 from by omega] at hcd
  have hB3 : (B ^ 3).natDegree < 9 * n - 2 * g - s - 60 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, hBe, hcd,
    coeff_eq_zero_of_natDegree_lt hB3]
  ring

/-- Homogeneous I3 one lattice stride below the uniform face.  The
`d^2` block is kept literal: it vanishes for deep offsets and returns
the edge square exactly at the first stride. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_uniform_secondJet_fiveToSix
    (A B c d e : k[X]) (n g s : ℕ)
    (hn120 : 120 ≤ n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload2 : s + 60 ≤ 7 * n - 2 * g)
    (hdn : 60 ∣ n) (hdg : 60 ∣ g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s)
    (hAsupp : ∀ i : ℕ, ¬ (60 ∣ i) → A.coeff i = 0)
    (hBsupp : ∀ i : ℕ, ¬ (60 ∣ i) → B.coeff i = 0)
    (hcsupp : ∀ i : ℕ, ¬ (60 ∣ i) → c.coeff i = 0) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 2 * g - s - 60) =
      (-8 / 9 : k) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - s - 60) +
          (A.coeff (2 * n) * uniformCuspSecondJetB68 B n g +
            A.coeff (2 * n - 60) * B.coeff (3 * n - g)) *
            d.coeff (5 * n - g - s)) +
      (8 / 3 : k) *
        (c.coeff (4 * n - g) * e.coeff (6 * n - g - s - 60) +
          c.coeff (4 * n - g - 60) * e.coeff (6 * n - g - s)) +
      (4 / 3 : k) * (d ^ 2).coeff (10 * n - 2 * g - s - 60) := by
  have hAB : (A * B).natDegree ≤ 5 * n - g :=
    le_trans natDegree_mul_le (by omega)
  have hABtop : (A * B).coeff (5 * n - g) =
      A.coeff (2 * n) * B.coeff (3 * n - g) := by
    have h := coeff_mul_at_bounds68 A B (2 * n) (3 * n - g) hA hB
    rw [show 2 * n + (3 * n - g) = 5 * n - g from by omega] at h
    exact h
  have hAB2 := mul_coeff_secondJet_AB_uniformCusp68 A B n g
    hn120 hwindow hdn hdg hA hB hAsupp
  have hABsupp := coeff_mul_lattice_support68 A B hAsupp hBsupp
  have hABd := coeff_mul_offset_sixty_left_lattice68 (A * B) d
    (5 * n - g) (5 * n - g - s) (by omega) (by omega) (by omega)
    hAB hd hABsupp
  rw [show 5 * n - g + (5 * n - g - s) - 60 =
    10 * n - 2 * g - s - 60 from by omega, hAB2, hABtop] at hABd
  have hce := coeff_mul_offset_sixty_left_lattice68 c e
    (4 * n - g) (6 * n - g - s) (by omega) (by omega) (by omega)
    hc he hcsupp
  rw [show 4 * n - g + (6 * n - g - s) - 60 =
    10 * n - 2 * g - s - 60 from by omega] at hce
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - 2 * g - s - 60 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hce,
    coeff_eq_zero_of_natDegree_lt hB2c]
  ring

/-- Deep offsets: the `d^2` block dies one stride below the face. -/
theorem sq_coeff_uniform_secondJet_deep_fiveToSix68
    (d : k[X]) (n g s : ℕ) (hs2 : 120 ≤ s)
    (hload2 : s + 60 ≤ 7 * n - 2 * g)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hd : d.natDegree ≤ 5 * n - g - s) :
    (d ^ 2).coeff (10 * n - 2 * g - s - 60) = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  compute_degree
  omega

/-- First stride: the `d^2` block returns the edge square. -/
theorem sq_coeff_uniform_secondJet_firstStride_fiveToSix68
    (d : k[X]) (n g : ℕ) (hn120 : 120 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hd : d.natDegree ≤ 5 * n - g - 60) :
    (d ^ 2).coeff (10 * n - 2 * g - 120) =
      d.coeff (5 * n - g - 60) ^ 2 := by
  rw [pow_two]
  have h := coeff_mul_at_bounds68 d d (5 * n - g - 60) (5 * n - g - 60)
    hd hd
  rw [show 5 * n - g - 60 + (5 * n - g - 60) =
    10 * n - 2 * g - 120 from by omega] at h
  rw [h]
  ring

/-- Literal I4 second jet: load-free except for the explicit terminal
`zeta` block, which is nonzero only when the jet touches the wall
`s + 60 = 7n - 2g`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_uniform_secondJet_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X]) (n g s : ℕ)
    (hn120 : 120 ≤ n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload2 : s + 60 ≤ 7 * n - 2 * g)
    (hdn : 60 ∣ n) (hdg : 60 ∣ g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s)
    (hBsupp : ∀ i : ℕ, ¬ (60 ∣ i) → B.coeff i = 0)
    (hcsupp : ∀ i : ℕ, ¬ (60 ∣ i) → c.coeff i = 0) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 2 * g - s - 60) =
      (8 / 3 : k) *
        (uniformCuspSecondJetB68 B n g * e.coeff (6 * n - g - s) +
          B.coeff (3 * n - g) * e.coeff (6 * n - g - s - 60) +
          c.coeff (4 * n - g - 60) * d.coeff (5 * n - g - s) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - s - 60)) +
      zeta * A.coeff (9 * n - 2 * g - s - 60) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_uniform_secondJet_fiveToSix
      B c d e n g s hn120 hs hwindow hload2 hdn hdg hB hc hd he
      hBsupp hcsupp]
  have hloadB : ((2 * epsilon : k) • B).natDegree <
      9 * n - 2 * g - s - 60 := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree <
      9 * n - 2 * g - s - 60 := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  simp only [coeff_smul, smul_eq_mul]
  ring

/-- Literal I3 second jet: completely load-free inside the second-jet
window. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_uniform_secondJet_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X]) (n g s : ℕ)
    (hn120 : 120 ≤ n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload2 : s + 60 ≤ 7 * n - 2 * g)
    (hdn : 60 ∣ n) (hdg : 60 ∣ g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s)
    (hAsupp : ∀ i : ℕ, ¬ (60 ∣ i) → A.coeff i = 0)
    (hBsupp : ∀ i : ℕ, ¬ (60 ∣ i) → B.coeff i = 0)
    (hcsupp : ∀ i : ℕ, ¬ (60 ∣ i) → c.coeff i = 0) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 2 * g - s - 60) =
      (-8 / 9 : k) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - s - 60) +
          (A.coeff (2 * n) * uniformCuspSecondJetB68 B n g +
            A.coeff (2 * n - 60) * B.coeff (3 * n - g)) *
            d.coeff (5 * n - g - s)) +
      (8 / 3 : k) *
        (c.coeff (4 * n - g) * e.coeff (6 * n - g - s - 60) +
          c.coeff (4 * n - g - 60) * e.coeff (6 * n - g - s)) +
      (4 / 3 : k) * (d ^ 2).coeff (10 * n - 2 * g - s - 60) := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_uniform_secondJet_fiveToSix
      A B c d e n g s hn120 hs hwindow hload2 hdn hdg hA hB hc hd he
      hAsupp hBsupp hcsupp]
  have hloadB : (zeta • B).natDegree < 10 * n - 2 * g - s - 60 := by
    compute_degree
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree <
      10 * n - 2 * g - s - 60 := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree <
      10 * n - 2 * g - s - 60 := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree <
      10 * n - 2 * g - s - 60 := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

/-! ## The singular second-jet resultant -/

/-- Cokernel elimination of the singular second-jet system.  The matrix
of the pair `(d', e')` has determinant `-(a*b^2+3*c^2) = 0` on the cusp,
so `(a*b, -c)` is a left null vector; applying it and reducing through
the two faces and the cusp eliminates the new edge pair entirely and
leaves one compatibility scalar in the second-level jets. -/
theorem fiveToSix_uniformCusp_singular_compatibility_scalar68
    (a b c ds es b2 c2 a2 dp ep zw q : k)
    (hcusp : a * b ^ 2 + 3 * c ^ 2 = 0)
    (hface4 : b * es + c * ds = 0)
    (hface3 : -a * b * ds + 3 * c * es = 0)
    (hR4 : b * ep + b2 * es + c * dp + c2 * ds + (3 / 8 : k) * zw = 0)
    (hR3 : a * b * dp + (a * b2 + a2 * b) * ds - 3 * c * ep -
      3 * c2 * es - (3 / 2 : k) * q = 0) :
    (2 * a * b * (b * c2 - c * b2) - a2 * b ^ 2 * c) * ds +
      (3 / 8 : k) * a * b ^ 2 * zw + (3 / 2 : k) * b * c * q = 0 := by
  linear_combination (a * b ^ 2) * hR4 - (b * c) * hR3 -
    (b * ep + b2 * es - c2 * ds) * hcusp - (3 * c * c2) * hface4 +
    (b2 * c) * hface3

/-- Residual-coordinate second-jet compatibility on the uniform cusp
branch: the packed recurrence with its explicit terminal `zeta` wall
term and literal first-stride `d^2` block. -/
theorem fiveToSix_uniformCusp_secondJet_compatibility68
    (gamma epsilon zeta i4 i3 : k) (A B c d e : k[X]) (n g s : ℕ)
    (hn120 : 120 ≤ n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload2 : s + 60 ≤ 7 * n - 2 * g)
    (hdn : 60 ∣ n) (hdg : 60 ∣ g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s)
    (hAsupp : ∀ i : ℕ, ¬ (60 ∣ i) → A.coeff i = 0)
    (hBsupp : ∀ i : ℕ, ¬ (60 ∣ i) → B.coeff i = 0)
    (hcsupp : ∀ i : ℕ, ¬ (60 ∣ i) → c.coeff i = 0)
    (hcusp : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      3 * c.coeff (4 * n - g) ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    (2 * A.coeff (2 * n) * B.coeff (3 * n - g) *
        (B.coeff (3 * n - g) * c.coeff (4 * n - g - 60) -
          c.coeff (4 * n - g) * uniformCuspSecondJetB68 B n g) -
      A.coeff (2 * n - 60) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g)) * d.coeff (5 * n - g - s) +
      (3 / 8 : k) * zeta * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        A.coeff (9 * n - 2 * g - s - 60) +
      (3 / 2 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) *
        (d ^ 2).coeff (10 * n - 2 * g - s - 60) = 0 := by
  have hface := polynomialSecondaryResidualUniformFace68_fiveToSix
    gamma epsilon zeta i4 i3 A B c d e n g s (by omega) hs hwindow
    (by omega) hA hB hc hd he hi4 hi3
  have hz4 := congrArg
    (fun p : k[X] => p.coeff (9 * n - 2 * g - s - 60)) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_uniform_secondJet_fiveToSix
    gamma epsilon zeta A B c d e n g s hn120 hs hwindow hload2 hdn hdg
    hA hB hc hd he hBsupp hcsupp] at hz4
  have hj4 : 9 * n - 2 * g - s - 60 ≠ 0 := by omega
  simp only [coeff_C, if_neg hj4] at hz4
  have hz3 := congrArg
    (fun p : k[X] => p.coeff (10 * n - 2 * g - s - 60)) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_uniform_secondJet_fiveToSix
    gamma epsilon zeta A B c d e n g s hn120 hs hwindow hload2 hdn hdg
    hA hB hc hd he hAsupp hBsupp hcsupp] at hz3
  have hj3 : 10 * n - 2 * g - s - 60 ≠ 0 := by omega
  simp only [coeff_C, if_neg hj3] at hz3
  have hR4 : B.coeff (3 * n - g) * e.coeff (6 * n - g - s - 60) +
      uniformCuspSecondJetB68 B n g * e.coeff (6 * n - g - s) +
      c.coeff (4 * n - g) * d.coeff (5 * n - g - s - 60) +
      c.coeff (4 * n - g - 60) * d.coeff (5 * n - g - s) +
      (3 / 8 : k) * (zeta * A.coeff (9 * n - 2 * g - s - 60)) = 0 := by
    linear_combination (3 / 8 : k) * hz4
  have hR3 : A.coeff (2 * n) * B.coeff (3 * n - g) *
      d.coeff (5 * n - g - s - 60) +
      (A.coeff (2 * n) * uniformCuspSecondJetB68 B n g +
        A.coeff (2 * n - 60) * B.coeff (3 * n - g)) *
        d.coeff (5 * n - g - s) -
      3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - s - 60) -
      3 * c.coeff (4 * n - g - 60) * e.coeff (6 * n - g - s) -
      (3 / 2 : k) * (d ^ 2).coeff (10 * n - 2 * g - s - 60) = 0 := by
    linear_combination (-9 / 8 : k) * hz3
  have hmain := fiveToSix_uniformCusp_singular_compatibility_scalar68
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - g - s)) (e.coeff (6 * n - g - s))
    (uniformCuspSecondJetB68 B n g) (c.coeff (4 * n - g - 60))
    (A.coeff (2 * n - 60)) (d.coeff (5 * n - g - s - 60))
    (e.coeff (6 * n - g - s - 60))
    (zeta * A.coeff (9 * n - 2 * g - s - 60))
    ((d ^ 2).coeff (10 * n - 2 * g - s - 60))
    hcusp hface.four hface.three
    (by linear_combination hR4) (by linear_combination hR3)
  linear_combination hmain

/-! ## Source-facing uniform cusp resultant packet -/

set_option maxHeartbeats 30000000 in
/-- Source-facing uniform attack on the all-nonzero cusp branch at an
arbitrary positive load-free offset.  The branch pins all residue
phases, re-emits the two faces, records the preserved terminal `zeta`
wall, and is NOT closed: the exact smallest residual is the singular
second-jet compatibility recurrence, which in the interior chambers
divides down to `2a(b*c₂ - c*b₂) = a₂*b*c` (deep) and
`2a(b*c₂ - c*b₂) + (3/2)*c*d_s = a₂*b*c` (first stride).  The one-form
row tops are exact face shadows (see
`fiveToSix_uniformCusp_oneFormTops_shadow68`); the first genuinely
independent unused row is the third-jet I4/I3 pair. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformCusp_resultant68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (s : ℕ) (hterminal : terminal ≠ 0)
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
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hs : 0 < s)
    (hload :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      s < 7 * n - 2 * g)
    (hdrop :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.natDegree ≤ 5 * n - g - s ∧
        ee.natDegree ≤ 6 * n - g - s)
    (hbranch :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      Be.coeff (3 * n - g) ≠ 0 ∧
        ce.coeff (4 * n - g) ≠ 0 ∧
        d.coeff (5 * n - g - s) ≠ 0 ∧
        ee.coeff (6 * n - g - s) ≠ 0 ∧
        Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
          3 * ce.coeff (4 * n - g) ^ 2 = 0) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    60 ∣ n ∧ 60 ∣ g ∧ 60 ∣ s ∧ 120 ≤ n ∧ s + 60 ≤ 7 * n - 2 * g ∧
      SecondaryResidualBetweenFace68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - g - s))
        (ee.coeff (6 * n - g - s)) ∧
      (s + 60 = 7 * n - 2 * g →
        Ae.coeff (9 * n - 2 * g - s - 60) = Ae.coeff (2 * n)) ∧
      ((2 * Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
          (Be.coeff (3 * n - g) * ce.coeff (4 * n - g - 60) -
            ce.coeff (4 * n - g) * uniformCuspSecondJetB68 Be n g) -
        Ae.coeff (2 * n - 60) * Be.coeff (3 * n - g) ^ 2 *
          ce.coeff (4 * n - g)) * d.coeff (5 * n - g - s) +
        (3 / 8 : k) * zeta * Ae.coeff (2 * n) *
          Be.coeff (3 * n - g) ^ 2 *
          Ae.coeff (9 * n - 2 * g - s - 60) +
        (3 / 2 : k) * Be.coeff (3 * n - g) * ce.coeff (4 * n - g) *
          (d ^ 2).coeff (10 * n - 2 * g - s - 60) = 0) ∧
      (s + 120 ≤ 7 * n - 2 * g → 120 ≤ s →
        2 * Ae.coeff (2 * n) *
            (Be.coeff (3 * n - g) * ce.coeff (4 * n - g - 60) -
              ce.coeff (4 * n - g) * uniformCuspSecondJetB68 Be n g) =
          Ae.coeff (2 * n - 60) * Be.coeff (3 * n - g) *
            ce.coeff (4 * n - g)) ∧
      (s = 60 → s + 120 ≤ 7 * n - 2 * g →
        2 * Ae.coeff (2 * n) *
            (Be.coeff (3 * n - g) * ce.coeff (4 * n - g - 60) -
              ce.coeff (4 * n - g) * uniformCuspSecondJetB68 Be n g) +
          (3 / 2 : k) * ce.coeff (4 * n - g) *
            d.coeff (5 * n - g - s) =
          Ae.coeff (2 * n - 60) * Be.coeff (3 * n - g) *
            ce.coeff (4 * n - g)) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change s < 7 * n - 2 * g at hload
  change d.natDegree ≤ 5 * n - g - s ∧
    ee.natDegree ≤ 6 * n - g - s at hdrop
  change Be.coeff (3 * n - g) ≠ 0 ∧
    ce.coeff (4 * n - g) ≠ 0 ∧
    d.coeff (5 * n - g - s) ≠ 0 ∧
    ee.coeff (6 * n - g - s) ≠ 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
      3 * ce.coeff (4 * n - g) ^ 2 = 0 at hbranch
  obtain ⟨hb, hcT, hdT, heT, hcusp⟩ := hbranch
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hn0 : 0 < n := data.hn
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
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
  obtain ⟨i3, hi3raw⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3raw
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta] at hi3e
  rw [hdelta] at hI4
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  rw [hDrec] at hI4 hi3e
  have hBdiv : 60 ∣ 3 * n - g := by
    have hbexp : (expand k 60 B).coeff (3 * n - g) ≠ 0 := by
      simpa only [Be] using hb
    exact coeff_expand_ne_zero_dvd68 60 (by norm_num) B (3 * n - g) hbexp
  have hcexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have hCdiv : 60 ∣ 4 * n - g := by
    have hcexp2 : (expand k 60 (cubicCDefectPolynomial68 A C0)).coeff
        (4 * n - g) ≠ 0 := by
      rw [← hcexpand]
      exact hcT
    exact coeff_expand_ne_zero_dvd68 60 (by norm_num) _ _ hcexp2
  have hnDiv : 60 ∣ n := by
    obtain ⟨u, hu⟩ := hBdiv
    obtain ⟨v, hv⟩ := hCdiv
    refine ⟨v - u, ?_⟩
    omega
  have hgDiv : 60 ∣ g := by
    obtain ⟨u, hu⟩ := hnDiv
    obtain ⟨v, hv⟩ := hBdiv
    refine ⟨3 * u - v, ?_⟩
    omega
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have hsDiv : 60 ∣ s := by
    have hdexp2 : (expand k 60
        (secondaryDDefectPolynomial68 A B D)).coeff (5 * n - g - s) ≠ 0 := by
      rw [← hdexpand]
      exact hdT
    have h5 : 60 ∣ 5 * n - g - s :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num) _ _ hdexp2
    obtain ⟨u, hu⟩ := hnDiv
    obtain ⟨v, hv⟩ := hgDiv
    obtain ⟨w, hw⟩ := h5
    refine ⟨5 * u - v - w, ?_⟩
    omega
  have hn120 : 120 ≤ n := by
    obtain ⟨u, hu⟩ := hnDiv
    obtain ⟨v, hv⟩ := hgDiv
    obtain ⟨w, hw⟩ := hsDiv
    omega
  have hload2 : s + 60 ≤ 7 * n - 2 * g := by
    obtain ⟨u, hu⟩ := hnDiv
    obtain ⟨v, hv⟩ := hgDiv
    obtain ⟨w, hw⟩ := hsDiv
    omega
  have hAsupp : ∀ i : ℕ, ¬ (60 ∣ i) → Ae.coeff i = 0 := by
    intro i hi
    show (expand k 60 A).coeff i = 0
    rw [coeff_expand (by norm_num)]
    exact if_neg hi
  have hBsupp : ∀ i : ℕ, ¬ (60 ∣ i) → Be.coeff i = 0 := by
    intro i hi
    show (expand k 60 B).coeff i = 0
    rw [coeff_expand (by norm_num)]
    exact if_neg hi
  have hcsupp : ∀ i : ℕ, ¬ (60 ∣ i) → ce.coeff i = 0 := by
    intro i hi
    rw [hcexpand, coeff_expand (by norm_num)]
    exact if_neg hi
  have hface := polynomialSecondaryResidualUniformFace68_fiveToSix
    gamma epsilon zeta i4 i3 Ae Be ce d ee n g s data.hn hs hwindow hload
    data.hA data.hB data.hc hdrop.1 hdrop.2 hI4 hi3e
  have hcompat := fiveToSix_uniformCusp_secondJet_compatibility68
    gamma epsilon zeta i4 i3 Ae Be ce d ee n g s hn120 hs hwindow hload2
    hnDiv hgDiv data.hA data.hB data.hc hdrop.1 hdrop.2
    hAsupp hBsupp hcsupp hcusp hI4 hi3e
  refine ⟨hnDiv, hgDiv, hsDiv, hn120, hload2, hface, ?_, hcompat, ?_, ?_⟩
  · show s + 60 = 7 * n - 2 * g →
      Ae.coeff (9 * n - 2 * g - s - 60) = Ae.coeff (2 * n)
    intro hwall
    rw [show 9 * n - 2 * g - s - 60 = 2 * n from by omega]
  · show s + 120 ≤ 7 * n - 2 * g → 120 ≤ s →
      2 * Ae.coeff (2 * n) *
          (Be.coeff (3 * n - g) * ce.coeff (4 * n - g - 60) -
            ce.coeff (4 * n - g) * uniformCuspSecondJetB68 Be n g) =
        Ae.coeff (2 * n - 60) * Be.coeff (3 * n - g) *
          ce.coeff (4 * n - g)
    intro hint hdeep
    have haw : Ae.coeff (9 * n - 2 * g - s - 60) = 0 :=
      coeff_eq_zero_of_natDegree_lt (data.hA.trans_lt (by omega))
    have hqz : (d ^ 2).coeff (10 * n - 2 * g - s - 60) = 0 :=
      sq_coeff_uniform_secondJet_deep_fiveToSix68 d n g s hdeep hload2
        hwindow hdrop.1
    have hXds : (2 * Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
        (Be.coeff (3 * n - g) * ce.coeff (4 * n - g - 60) -
          ce.coeff (4 * n - g) * uniformCuspSecondJetB68 Be n g) -
        Ae.coeff (2 * n - 60) * Be.coeff (3 * n - g) ^ 2 *
          ce.coeff (4 * n - g)) * d.coeff (5 * n - g - s) = 0 := by
      linear_combination hcompat -
        ((3 / 8 : k) * zeta * Ae.coeff (2 * n) *
          Be.coeff (3 * n - g) ^ 2) * haw -
        ((3 / 2 : k) * Be.coeff (3 * n - g) * ce.coeff (4 * n - g)) * hqz
    have hX := (mul_eq_zero.mp hXds).resolve_right hdT
    have hbX : Be.coeff (3 * n - g) *
        (2 * Ae.coeff (2 * n) *
          (Be.coeff (3 * n - g) * ce.coeff (4 * n - g - 60) -
            ce.coeff (4 * n - g) * uniformCuspSecondJetB68 Be n g) -
          Ae.coeff (2 * n - 60) * Be.coeff (3 * n - g) *
            ce.coeff (4 * n - g)) = 0 := by
      linear_combination hX
    have hY := (mul_eq_zero.mp hbX).resolve_left hb
    linear_combination hY
  · show s = 60 → s + 120 ≤ 7 * n - 2 * g →
      2 * Ae.coeff (2 * n) *
          (Be.coeff (3 * n - g) * ce.coeff (4 * n - g - 60) -
            ce.coeff (4 * n - g) * uniformCuspSecondJetB68 Be n g) +
        (3 / 2 : k) * ce.coeff (4 * n - g) *
          d.coeff (5 * n - g - s) =
        Ae.coeff (2 * n - 60) * Be.coeff (3 * n - g) *
          ce.coeff (4 * n - g)
    intro hs60 hint
    have haw : Ae.coeff (9 * n - 2 * g - s - 60) = 0 :=
      coeff_eq_zero_of_natDegree_lt (data.hA.trans_lt (by omega))
    have hq60 : (d ^ 2).coeff (10 * n - 2 * g - s - 60) =
        d.coeff (5 * n - g - s) ^ 2 := by
      rw [hs60, show 10 * n - 2 * g - 60 - 60 = 10 * n - 2 * g - 120
        from by omega]
      exact sq_coeff_uniform_secondJet_firstStride_fiveToSix68 d n g
        hn120 hwindow (by
          have := hdrop.1
          omega)
    have hfact : (Be.coeff (3 * n - g) *
        (2 * Ae.coeff (2 * n) *
          (Be.coeff (3 * n - g) * ce.coeff (4 * n - g - 60) -
            ce.coeff (4 * n - g) * uniformCuspSecondJetB68 Be n g) -
          Ae.coeff (2 * n - 60) * Be.coeff (3 * n - g) *
            ce.coeff (4 * n - g) +
          (3 / 2 : k) * ce.coeff (4 * n - g) *
            d.coeff (5 * n - g - s))) * d.coeff (5 * n - g - s) = 0 := by
      linear_combination hcompat -
        ((3 / 8 : k) * zeta * Ae.coeff (2 * n) *
          Be.coeff (3 * n - g) ^ 2) * haw -
        ((3 / 2 : k) * Be.coeff (3 * n - g) * ce.coeff (4 * n - g)) * hq60
    have hbY := (mul_eq_zero.mp hfact).resolve_right hdT
    have hY := (mul_eq_zero.mp hbY).resolve_left hb
    linear_combination hY

#print axioms uniformCuspSecondJetB68_of_le
#print axioms uniformCuspSecondJetB68_of_boundary
#print axioms coeff_mul_lattice_support68
#print axioms coeff_mul_offset_sixty_left_lattice68
#print axioms coeff_mul_mul_derivative_at_bounds_weak68
#print axioms secondaryResidualRowTwoPolynomial68_coeff_uniform_fiveToSix
#print axioms secondaryResidualRowOnePolynomial68_coeff_uniform_fiveToSix
#print axioms secondaryResidualRowZeroPolynomial68_coeff_uniform_fiveToSix
#print axioms cubicLoadRowTwoPolynomial68_uniform_pinned_eq68
#print axioms cubicLoadRowOnePolynomial68_uniform_pinned_eq68
#print axioms cubicLoadRowZeroPolynomial68_uniform_pinned_eq68
#print axioms cubicLoadRowTwoPolynomial68_coeff_uniform_top_fiveToSix
#print axioms cubicLoadRowOnePolynomial68_coeff_uniform_top_fiveToSix
#print axioms cubicLoadRowZeroPolynomial68_coeff_uniform_top_fiveToSix
#print axioms fiveToSix_uniformCusp_oneFormTops_shadow68
#print axioms mul_coeff_secondJet_Be_uniformCusp68
#print axioms mul_coeff_secondJet_AB_uniformCusp68
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_uniform_secondJet_fiveToSix
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_uniform_secondJet_fiveToSix
#print axioms sq_coeff_uniform_secondJet_deep_fiveToSix68
#print axioms sq_coeff_uniform_secondJet_firstStride_fiveToSix68
#print axioms cubicFirstIntegralFourPolynomial68_coeff_uniform_secondJet_fiveToSix
#print axioms cubicFirstIntegralThreePolynomial68_coeff_uniform_secondJet_fiveToSix
#print axioms fiveToSix_uniformCusp_singular_compatibility_scalar68
#print axioms fiveToSix_uniformCusp_secondJet_compatibility68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformCusp_resultant68

end FiveToSixUniformCuspResultant68

end Max11DegreeRoutes
