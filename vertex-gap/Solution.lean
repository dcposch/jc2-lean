/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic agents (proofs)
-/
import Mathlib

/-!
# Solution: proofs of the vertex-gap obstruction at `(2,2)`

Follows the proof of Theorem 3.4 (`thm:22`) of *A Vertex-Gap Obstruction for
Low-Degree Strip Pairs in the Plane Jacobian Conjecture* (campaign artifact,
Zenodo DOI 10.5281/zenodo.21894922).  Architecture:

* `JC72108.VertexGap.e i j` is the exponent vector of `xⁱyʲ`, with small
  evaluation/addition lemmas.
* `JC72108.VertexGap.coeff_bracket`: the coefficient of `x^{n₀}y^{n₁}` in the
  Jacobian bracket `[P,Q] = Pₓ·Q_y − P_y·Qₓ` as an explicit double sum over
  exponent pairs (the paper's key formula `E_m = ∑_{p+q=m} det(p,q)·a_p·b_q`,
  Section 1, with the two bracket products kept separate).
* Inside `VertexGap22`: the twelve relevant *keys* — the vertex equation at
  Minkowski point `(3,1)`, the two gap keys `(2,1)`, `(2,2)`, and the nine
  block keys `(3,2)…(3,5)`, `(4,3)…(4,7)` — are extracted by instantiating
  `coeff_bracket` and discharging all out-of-strip coefficients.
* `JC72108.VertexGap.cascade`: the scalar elimination cascade of the paper's
  proof (gap kill, unit pivots, the two cancellations C1/C2, the rigidity
  event `a₃ = 0` and the pinning surplus `a₂²a₆ = 0`), done by explicit
  `linear_combination` certificates.  The one non-ideal step (Remark 3.5:
  the conclusion is radical, not ideal, membership) is `(a₃b₃)² = 0 → a₃b₃ = 0`.
  The certificates keep the factor `5` on the `b₉`-pivot instead of dividing
  by it, so only the invertibility of `2` and `3` is consumed; the hypothesis
  `(5 : K) ≠ 0` of the printed statement is retained for fidelity but unused
  (cf. the paper's Remark 3.7, which observes — without claim — that the
  obstruction appears to persist mod `5`).
-/

namespace JC72108.VertexGap

open MvPolynomial Finsupp

/-! ### Exponent vectors -/

/-- The exponent vector of `xⁱyʲ` as an element of `Fin 2 →₀ ℕ`. -/
noncomputable def e (i j : ℕ) : Fin 2 →₀ ℕ := single 0 i + single 1 j

@[simp] private lemma e_apply_zero (i j : ℕ) : e i j 0 = i := by
  simp [e]

@[simp] private lemma e_apply_one (i j : ℕ) : e i j 1 = j := by
  simp [e]

private lemma e_eta (u : Fin 2 →₀ ℕ) : e (u 0) (u 1) = u := by
  ext x
  fin_cases x <;> simp

private lemma e_add_x (i j : ℕ) : e i j + single 0 1 = e (i + 1) j := by
  ext x
  fin_cases x <;> simp [e]

private lemma e_add_y (i j : ℕ) : e i j + single 1 1 = e i (j + 1) := by
  ext x
  fin_cases x <;> simp [e]

/-! ### The bracket coefficient as a double sum -/

/-- Reindex a sum over the `Finsupp` antidiagonal of `e n₀ n₁` as a double
sum over rectangular ranges. -/
private lemma sum_antidiagonal_e {M : Type*} [AddCommMonoid M] (n₀ n₁ : ℕ)
    (F : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) → M) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (e n₀ n₁), F x
      = ∑ i ∈ Finset.range (n₀ + 1), ∑ j ∈ Finset.range (n₁ + 1),
          F (e i j, e (n₀ - i) (n₁ - j)) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => (x.1 0, x.1 1))
    (fun ij => (e ij.1 ij.2, e (n₀ - ij.1) (n₁ - ij.2))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h0 : u 0 + v 0 = n₀ := by
      have := congrArg (fun f => f 0) hx
      simpa using this
    have h1 : u 1 + v 1 = n₁ := by
      have := congrArg (fun f => f 1) hx
      simpa using this
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_product, Finset.mem_range] at hij
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    have hi : i + (n₀ - i) = n₀ := by omega
    have hj : j + (n₁ - j) = n₁ := by omega
    ext x
    fin_cases x <;> simp [e] <;> omega
  · rintro ⟨u, v⟩ hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h0 : u 0 + v 0 = n₀ := by
      have := congrArg (fun f => f 0) hx
      simpa using this
    have h1 : u 1 + v 1 = n₁ := by
      have := congrArg (fun f => f 1) hx
      simpa using this
    have hv0 : n₀ - u 0 = v 0 := by omega
    have hv1 : n₁ - u 1 = v 1 := by omega
    simp only [hv0, hv1, e_eta]
  · rintro ⟨i, j⟩ hij
    simp
  · rintro ⟨u, v⟩ hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h0 : u 0 + v 0 = n₀ := by
      have := congrArg (fun f => f 0) hx
      simpa using this
    have h1 : u 1 + v 1 = n₁ := by
      have := congrArg (fun f => f 1) hx
      simpa using this
    have hv0 : n₀ - u 0 = v 0 := by omega
    have hv1 : n₁ - u 1 = v 1 := by omega
    simp only [hv0, hv1, e_eta]

variable {K : Type*} [CommRing K]

/-- **The key formula** (equation (1) of the paper, split into its two
products).  The coefficient of `x^{n₀}y^{n₁}` in the Jacobian bracket
`Pₓ·Q_y − P_y·Qₓ` as an explicit double sum over exponent pairs. -/
private lemma coeff_bracket (P Q : MvPolynomial (Fin 2) K) (n₀ n₁ : ℕ) :
    coeff (e n₀ n₁) (pderiv 0 P * pderiv 1 Q - pderiv 1 P * pderiv 0 Q)
      = (∑ i ∈ Finset.range (n₀ + 1), ∑ j ∈ Finset.range (n₁ + 1),
          coeff (e (i + 1) j) P * ((i : K) + 1)
            * (coeff (e (n₀ - i) (n₁ - j + 1)) Q * (((n₁ - j : ℕ) : K) + 1)))
      - (∑ i ∈ Finset.range (n₀ + 1), ∑ j ∈ Finset.range (n₁ + 1),
          coeff (e i (j + 1)) P * ((j : K) + 1)
            * (coeff (e (n₀ - i + 1) (n₁ - j)) Q * (((n₀ - i : ℕ) : K) + 1))) := by
  classical
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul,
    sum_antidiagonal_e n₀ n₁ (fun x => coeff x.1 (pderiv 0 P) * coeff x.2 (pderiv 1 Q)),
    sum_antidiagonal_e n₀ n₁ (fun x => coeff x.1 (pderiv 1 P) * coeff x.2 (pderiv 0 Q))]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv, e_add_x, e_add_y,
      e_apply_zero, e_apply_one]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv, e_add_x, e_add_y,
      e_apply_zero, e_apply_one]

/-- The coefficients of the right-hand side `x²`. -/
private lemma coeff_X0_sq (n₀ n₁ : ℕ) :
    coeff (e n₀ n₁) ((X 0 : MvPolynomial (Fin 2) K) ^ 2)
      = if n₀ = 2 ∧ n₁ = 0 then 1 else 0 := by
  classical
  rw [MvPolynomial.coeff_X_pow]
  by_cases h : n₀ = 2 ∧ n₁ = 0
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos, if_pos ⟨rfl, rfl⟩]
    ext x
    fin_cases x <;> simp [e]
  · rw [if_neg, if_neg h]
    intro he
    have h0 := congrArg (fun f => f 0) he
    have h1 := congrArg (fun f => f 1) he
    simp at h0 h1
    exact h ⟨h0.symm, h1.symm⟩

/-! ### The scalar elimination cascade -/

/-- **The elimination cascade** of the proof of Theorem 3.4 (`thm:22`),
over an abstract field: from the vertex equation `hV`, the two gap keys
`hG1`, `hG2`, and the nine block keys `hK1`–`hK9` (Minkowski points
`(3,2), (3,3), (3,4), (3,5), (4,3), (4,4), (4,5), (4,6), (4,7)`, in the
paper's elimination order), conclude the rigidity event `a₃ = 0` and the
pinning surplus `a₂²·a₆ = 0`.

The `linear_combination` certificates below implement: the gap kill
(`β₁ = β₂ = 0`), the unit-pivot solves for `b₄, b₅, b₆, b₈` and the pivot
relations for `b₉, b₁₀` (cancellations C1 at `(3,4)` and C2 at `(4,5)`
included), the radical step `(a₃b₃)² = 0 ⇒ a₃b₃ = 0` from key `(3,5)`
(Remark 3.5), and the surplus pinning at `(4,7)`.  `hK5` (point `(4,3)`,
the `b₇`-pivot) is retained for completeness of the block but is not
needed once `a₃ = 0` is in hand. -/
private lemma cascade {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {a1 a2 a3 a4 a5 a6 a7 a8 a9 b3 b4 b5 b6 b7 b8 b9 b10 β1 β2 : K}
    (hV : a1 * b3 = 1)
    (hG1 : a1 * β1 = 0)
    (hG2 : 2 * (a1 * β2) = 0)
    (hK1 : 2 * (a1 * b4) - a2 * b3 = 0)
    (hK2 : 3 * (a1 * b5) - 3 * (a3 * b3) = 0)
    (hK3 : 4 * (a1 * b6) + a2 * b5 - 2 * (a3 * b4) + 2 * (a4 * β2) - a5 * β1 = 0)
    (hK4 : 2 * (a2 * b6) - a3 * b5 + a5 * β2 - 2 * (a6 * β1) = 0)
    (_hK5 : 3 * (a1 * b7) - 2 * (a4 * b3) = 0)
    (hK6 : 4 * (a1 * b8) - 4 * (a5 * b3) = 0)
    (hK7 : 5 * (a1 * b9) + a2 * b8 - 3 * (a3 * b7) + 2 * (a4 * b5) - 2 * (a5 * b4)
        - 6 * (a6 * b3) - a7 * β1 = 0)
    (hK8 : 6 * (a1 * b10) + 2 * (a2 * b9) - 2 * (a3 * b8) + 4 * (a4 * b6) - 4 * (a6 * b4)
        + 2 * (a7 * β2) - 2 * (a8 * β1) = 0)
    (hK9 : 3 * (a2 * b10) - a3 * b9 + 2 * (a5 * b6) - 2 * (a6 * b5) + a8 * β2
        - 3 * (a9 * β1) = 0) :
    a3 = 0 ∧ a2 ^ 2 * a6 = 0 := by
  have c2 : ∀ x : K, (2 : K) * x = 0 → x = 0 := fun x h =>
    (mul_eq_zero.mp h).resolve_left h2
  have c3 : ∀ x : K, (3 : K) * x = 0 → x = 0 := fun x h =>
    (mul_eq_zero.mp h).resolve_left h3
  -- gap kill: the coefficients in the gap column `x = 1` of `Q` vanish
  have hβ1 : β1 = 0 := by linear_combination b3 * hG1 - β1 * hV
  have hβ2 : β2 = 0 := c2 _ (by linear_combination b3 * hG2 - 2 * β2 * hV)
  -- unit-pivot eliminations in the inner block column
  have hB4 : 2 * b4 = a2 * b3 ^ 2 := by linear_combination b3 * hK1 - 2 * b4 * hV
  have hB5 : b5 = a3 * b3 ^ 2 :=
    sub_eq_zero.mp (c3 _ (by linear_combination b3 * hK2 - 3 * b5 * hV))
  -- cancellation C1 at `(3,4)`: `b₆ = 0`
  have hb6 : b6 = 0 := by
    refine c2 _ (c2 _ ?_)
    linear_combination b3 * hK3 - a2 * b3 * hB5 + a3 * b3 * hB4 - 4 * b6 * hV
      + a5 * b3 * hβ1 - 2 * a4 * b3 * hβ2
  -- rigidity event at `(3,5)`: the radical step forcing `a₃ = 0`
  have ha3 : a3 = 0 := by
    have h1 : a3 * b5 = 0 := by
      linear_combination -hK4 + 2 * a2 * hb6 + a5 * hβ2 - 2 * a6 * hβ1
    have hsq : (a3 * b3) ^ 2 = 0 := by linear_combination h1 - a3 * hB5
    have hzz : a3 * b3 = 0 := sq_eq_zero_iff.mp hsq
    linear_combination a1 * hzz - a3 * hV
  refine ⟨ha3, ?_⟩
  have hb5 : b5 = 0 := by linear_combination hB5 + b3 ^ 2 * ha3
  -- outer-column eliminations
  have hB8 : b8 = a5 * b3 ^ 2 := by
    refine sub_eq_zero.mp (c2 _ (c2 _ ?_))
    linear_combination b3 * hK6 - 4 * b8 * hV
  -- cancellation C2 at `(4,5)`: `b₉` is pinned to `a₆` alone
  have hB9 : 5 * b9 = 6 * a6 * b3 ^ 2 := by
    linear_combination b3 * hK7 - 5 * b9 * hV - a2 * b3 * hB8 + 3 * b3 * b7 * ha3
      - 2 * a4 * b3 * hb5 + a5 * b3 * hB4 + a7 * b3 * hβ1
  have hB10 : 30 * b10 = -(2 * (a2 * a6 * b3 ^ 3)) := by
    linear_combination 5 * b3 * hK8 - 30 * b10 * hV - 2 * a2 * b3 * hB9
      + 10 * b3 * b8 * ha3 - 20 * a4 * b3 * hb6 + 10 * a6 * b3 * hB4
      - 10 * a7 * b3 * hβ2 + 10 * a8 * b3 * hβ1
  -- the surplus key `(4,7)` is of pinning type: `a₂²a₆ = 0`
  have h9 : a2 * b10 = 0 := by
    refine c3 _ ?_
    linear_combination hK9 + b9 * ha3 - 2 * a5 * hb6 + 2 * a6 * hb5 - a8 * hβ2
      + 3 * a9 * hβ1
  have hz : a2 ^ 2 * a6 * b3 ^ 3 = 0 := c2 _ (by linear_combination a2 * hB10 - 30 * h9)
  linear_combination a1 ^ 3 * hz - a2 ^ 2 * a6 * ((a1 * b3) ^ 2 + a1 * b3 + 1) * hV

end JC72108.VertexGap

open MvPolynomial Finsupp JC72108.VertexGap

/-- **Corner enumeration** (Lemma 2.2, `lem:enum`).  If the Minkowski vertex
`(k+1, 1)` decomposes as a sum `p₀ + q₀` of lattice points with
`det (p₀, q₀) = ±1`, then `{p₀, q₀} = {(1,0), (k,1)}`: the two bottom
corners of a vertex-normalized strip pair are `(1,0)` and `(k,1)`, in
either order. -/
theorem CornerEnumeration (k : ℕ) (p₀ q₀ : ℕ × ℕ)
    (hsum : p₀ + q₀ = (k + 1, 1))
    (hdet : (p₀.1 : ℤ) * q₀.2 - (p₀.2 : ℤ) * q₀.1 = 1 ∨
      (p₀.1 : ℤ) * q₀.2 - (p₀.2 : ℤ) * q₀.1 = -1) :
    (p₀ = (1, 0) ∧ q₀ = (k, 1)) ∨ (p₀ = (k, 1) ∧ q₀ = (1, 0)) := by
  obtain ⟨a, b⟩ := p₀
  obtain ⟨c, d⟩ := q₀
  rw [Prod.mk_add_mk, Prod.mk.injEq] at hsum
  obtain ⟨h1, h2⟩ := hsum
  simp only [Prod.mk.injEq]
  have hbd : b = 0 ∧ d = 1 ∨ b = 1 ∧ d = 0 := by omega
  rcases hbd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    have ha : a = 1 := by rcases hdet with h | h <;> push_cast at h <;> omega
    omega
  · right
    have hc : c = 1 := by rcases hdet with h | h <;> push_cast at h <;> omega
    omega

/-- **The gap condition, side-symmetrically** (hypothesis (ii), as corrected
by the erratum recorded in Section 8 of the paper).  Under the vertex
normalization, `k ≥ 2` is equivalent to `max ((p₀)ₓ, (q₀)ₓ) ≥ 2` — a
condition symmetric in the two bottom corners, hence independent of which
member of the pair carries which corner. -/
theorem GapConditionSideSymm (k : ℕ) (p₀ q₀ : ℕ × ℕ)
    (hsum : p₀ + q₀ = (k + 1, 1))
    (hdet : (p₀.1 : ℤ) * q₀.2 - (p₀.2 : ℤ) * q₀.1 = 1 ∨
      (p₀.1 : ℤ) * q₀.2 - (p₀.2 : ℤ) * q₀.1 = -1) :
    2 ≤ k ↔ 2 ≤ max p₀.1 q₀.1 := by
  rcases CornerEnumeration k p₀ q₀ hsum hdet with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;>
    subst hp <;> subst hq <;> simp

set_option linter.unusedVariables false in
set_option maxHeartbeats 1600000 in
/-- **Vertex-gap obstruction at `(k,d₂) = (2,2)`, normalized labels**
(Theorem 3.4, `thm:22`).  Let `K` be a field with `2, 3, 5 ≠ 0` and let
`P, Q ∈ K[x,y]` satisfy

* `P` supported in the closed weight strip `0 ≤ 2i − j ≤ 2` (type-`(2,2)`
  strip along `d = (1,2)` with top edge through the origin — this includes
  the absence of `y`-axis support (S3)),
* `Q` supported in the strip `0 ≤ 2i − j ≤ 3` and on or above the
  near-origin bottom edge through `(0,0)` and `q₀ = (2,1)` (`i ≤ 2j`),
* `[P,Q] = Pₓ·Q_y − P_y·Qₓ = x²`.

Then the block coefficients `a₃ = a_{(1,2)}` and `a₂²a₆ =
a_{(1,1)}²·a_{(2,4)}` of `P` vanish; in particular (`K` a field) every
strip pair lies in `{a₃ = 0} ∩ ({a₂ = 0} ∪ {a₆ = 0})`, and the generic
chart `a₂a₆ ≠ 0` is empty. -/
theorem VertexGap22 {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (P Q : MvPolynomial (Fin 2) K)
    (hP : ∀ p ∈ P.support, p 1 ≤ 2 * p 0 ∧ 2 * p 0 ≤ p 1 + 2)
    (hQ : ∀ q ∈ Q.support, q 1 ≤ 2 * q 0 ∧ 2 * q 0 ≤ q 1 + 3 ∧ q 0 ≤ 2 * q 1)
    (hJ : pderiv 0 P * pderiv 1 Q - pderiv 1 P * pderiv 0 Q = X 0 ^ 2) :
    coeff (single 0 1 + single 1 2) P = 0 ∧
      coeff (single 0 1 + single 1 1) P ^ 2 * coeff (single 0 2 + single 1 4) P = 0 := by
  classical
  -- support constraints, in coefficient form
  have hA0 : ∀ i j : ℕ, ¬(j ≤ 2 * i ∧ 2 * i ≤ j + 2) → coeff (e i j) P = 0 := by
    intro i j h
    by_contra hc
    have h' := hP (e i j) (MvPolynomial.mem_support_iff.mpr hc)
    simp only [e_apply_zero, e_apply_one] at h'
    exact h h'
  have hB0 : ∀ i j : ℕ, ¬(j ≤ 2 * i ∧ 2 * i ≤ j + 3 ∧ i ≤ 2 * j) → coeff (e i j) Q = 0 := by
    intro i j h
    by_contra hc
    have h' := hQ (e i j) (MvPolynomial.mem_support_iff.mpr hc)
    simp only [e_apply_zero, e_apply_one] at h'
    exact h h'
  -- the vertex equation `E_{(3,1)} = 1` (coefficient of `x²`)
  have hE31 : coeff (e 1 0) P * coeff (e 2 1) Q = 1 := by
    have h := coeff_bracket P Q 2 0
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  -- the gap keys `E_{(2,1)} = 0`, `E_{(2,2)} = 0`
  have hE21 : coeff (e 1 0) P * coeff (e 1 1) Q = 0 := by
    have h := coeff_bracket P Q 1 0
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  have hE22 : 2 * (coeff (e 1 0) P * coeff (e 1 2) Q) = 0 := by
    have h := coeff_bracket P Q 1 1
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  -- the nine block keys, Minkowski column `3` …
  have hE32 : 2 * (coeff (e 1 0) P * coeff (e 2 2) Q)
      - coeff (e 1 1) P * coeff (e 2 1) Q = 0 := by
    have h := coeff_bracket P Q 2 1
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  have hE33 : 3 * (coeff (e 1 0) P * coeff (e 2 3) Q)
      - 3 * (coeff (e 1 2) P * coeff (e 2 1) Q) = 0 := by
    have h := coeff_bracket P Q 2 2
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  have hE34 : 4 * (coeff (e 1 0) P * coeff (e 2 4) Q)
      + coeff (e 1 1) P * coeff (e 2 3) Q
      - 2 * (coeff (e 1 2) P * coeff (e 2 2) Q)
      + 2 * (coeff (e 2 2) P * coeff (e 1 2) Q)
      - coeff (e 2 3) P * coeff (e 1 1) Q = 0 := by
    have h := coeff_bracket P Q 2 3
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  have hE35 : 2 * (coeff (e 1 1) P * coeff (e 2 4) Q)
      - coeff (e 1 2) P * coeff (e 2 3) Q
      + coeff (e 2 3) P * coeff (e 1 2) Q
      - 2 * (coeff (e 2 4) P * coeff (e 1 1) Q) = 0 := by
    have h := coeff_bracket P Q 2 4
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  -- … and Minkowski column `4`
  have hE43 : 3 * (coeff (e 1 0) P * coeff (e 3 3) Q)
      - 2 * (coeff (e 2 2) P * coeff (e 2 1) Q) = 0 := by
    have h := coeff_bracket P Q 3 2
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  have hE44 : 4 * (coeff (e 1 0) P * coeff (e 3 4) Q)
      - 4 * (coeff (e 2 3) P * coeff (e 2 1) Q) = 0 := by
    have h := coeff_bracket P Q 3 3
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  have hE45 : 5 * (coeff (e 1 0) P * coeff (e 3 5) Q)
      + coeff (e 1 1) P * coeff (e 3 4) Q
      - 3 * (coeff (e 1 2) P * coeff (e 3 3) Q)
      + 2 * (coeff (e 2 2) P * coeff (e 2 3) Q)
      - 2 * (coeff (e 2 3) P * coeff (e 2 2) Q)
      - 6 * (coeff (e 2 4) P * coeff (e 2 1) Q)
      - coeff (e 3 4) P * coeff (e 1 1) Q = 0 := by
    have h := coeff_bracket P Q 3 4
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  have hE46 : 6 * (coeff (e 1 0) P * coeff (e 3 6) Q)
      + 2 * (coeff (e 1 1) P * coeff (e 3 5) Q)
      - 2 * (coeff (e 1 2) P * coeff (e 3 4) Q)
      + 4 * (coeff (e 2 2) P * coeff (e 2 4) Q)
      - 4 * (coeff (e 2 4) P * coeff (e 2 2) Q)
      + 2 * (coeff (e 3 4) P * coeff (e 1 2) Q)
      - 2 * (coeff (e 3 5) P * coeff (e 1 1) Q) = 0 := by
    have h := coeff_bracket P Q 3 5
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  have hE47 : 3 * (coeff (e 1 1) P * coeff (e 3 6) Q)
      - coeff (e 1 2) P * coeff (e 3 5) Q
      + 2 * (coeff (e 2 3) P * coeff (e 2 4) Q)
      - 2 * (coeff (e 2 4) P * coeff (e 2 3) Q)
      + coeff (e 3 5) P * coeff (e 1 2) Q
      - 3 * (coeff (e 3 6) P * coeff (e 1 1) Q) = 0 := by
    have h := coeff_bracket P Q 3 6
    rw [hJ, coeff_X0_sq] at h
    norm_num [Finset.sum_range_succ] at h
    simp (disch := decide) only [hA0, hB0] at h
    linear_combination -h
  -- run the cascade
  show coeff (e 1 2) P = 0 ∧ coeff (e 1 1) P ^ 2 * coeff (e 2 4) P = 0
  exact cascade h2 h3 hE31 hE21 hE22 hE32 hE33 hE34 hE35 hE43 hE44 hE45 hE46 hE47

/-- **Vertex-gap obstruction at `(2,2)`, swapped labels** (the
side-symmetric companion of `VertexGap22`, per the erratum: the corner
`(1,0)` may sit on either side of the pair).  Same bracket `[P,Q] = x²`,
but now `P` is the wide strip (`0 ≤ 2i − j ≤ 3`, bottom edge through
`(0,0)` and `(2,1)`) and `Q` the narrow one (`0 ≤ 2i − j ≤ 2`); the
obstruction lands on the block coefficients of `Q`.  The paper's label
normalization `(P,Q) ↦ (Q,−P)` (Section 2) is exactly the proof. -/
theorem VertexGap22_swapped {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (P Q : MvPolynomial (Fin 2) K)
    (hP : ∀ p ∈ P.support, p 1 ≤ 2 * p 0 ∧ 2 * p 0 ≤ p 1 + 3 ∧ p 0 ≤ 2 * p 1)
    (hQ : ∀ q ∈ Q.support, q 1 ≤ 2 * q 0 ∧ 2 * q 0 ≤ q 1 + 2)
    (hJ : pderiv 0 P * pderiv 1 Q - pderiv 1 P * pderiv 0 Q = X 0 ^ 2) :
    coeff (single 0 1 + single 1 2) Q = 0 ∧
      coeff (single 0 1 + single 1 1) Q ^ 2 * coeff (single 0 2 + single 1 4) Q = 0 := by
  refine VertexGap22 h2 h3 h5 Q (-P) hQ ?_ ?_
  · intro q hq
    rw [MvPolynomial.support_neg] at hq
    exact hP q hq
  · rw [map_neg, map_neg]
    linear_combination hJ
