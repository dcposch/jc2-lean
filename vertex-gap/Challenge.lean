/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic agents (drafting)
-/
import Mathlib

/-!
# Challenge: the vertex-gap obstruction at `(k,d₂) = (2,2)`

Statement module (Palomar registry).  The result is the main obstruction
theorem of *A Vertex-Gap Obstruction for Low-Degree Strip Pairs in the Plane
Jacobian Conjecture* (label `thm:22`, Theorem 3.4 in the current compilation;
archived with the campaign artifact, Zenodo DOI 10.5281/zenodo.21894922):

**Vertex-gap obstruction, `(k,d₂) = (2,2)`.**  Let `K` be a field of
characteristic not in `{2,3,5}` and let `P, Q ∈ K[x,y]` be a *strip pair* of
type `(2,2)` in normalized labels: writing `w(i,j) = 2i − j` for the weight
along the direction `d = (1,2)`,

* every exponent `(i,j)` of `P` satisfies `0 ≤ w(i,j) ≤ 2`,
* every exponent `(i,j)` of `Q` satisfies `0 ≤ w(i,j) ≤ 3` and lies on or
  above the line through `(0,0)` and the bottom corner `q₀ = (2,1)`
  (`i ≤ 2j`, the near-origin bottom edge of the Newton polygon `N(Q)`),
* the Jacobian bracket is `[P,Q] := Pₓ·Q_y − P_y·Qₓ = x²`.

Then, writing `a₂ = a_{(1,1)}`, `a₃ = a_{(1,2)}`, `a₆ = a_{(2,4)}` for the
block coefficients of `P`: every such pair satisfies `a₃ = 0` and
`a₂²·a₆ = 0`.  In particular the generic chart `a₂a₆ ≠ 0` of the strip
family is empty — the mechanism that discards the `(8,28)` subcase (2)
family of Guccione–Guccione–Horruitiner–Valqui (arXiv:2204.14178v1) at
Newton-degree pair `(72,108)` on its generic chart.

The paper carries the hypotheses in Newton-polygon language (Definition 2.1,
`def:strip`, plus the vertex normalization (i)); here they appear as the
equivalent explicit lattice-support inequalities.  The saturation of the
bottom corners (S2) is *not* assumed: the vertex equation
`a_{(1,0)}·b_{(2,1)} = 1` is forced by the bracket, so the formal statement
is (harmlessly) stronger than the printed one.  The condition
`char K ∉ {2,3,5}` is rendered as `(2 : K) ≠ 0`, `(3 : K) ≠ 0`,
`(5 : K) ≠ 0`, which is equivalent for fields.

Per the erratum incorporated in the paper (Section 8, "the gap condition
must be stated side-symmetrically"), the labels of a strip pair are
symmetric: either member may carry the corner `(1,0)`.  `VertexGap22` is
the normalized-label statement (the corner `(1,0)` on the `P` side);
`VertexGap22_swapped` is the mirrored statement (corner `(1,0)` on the `Q`
side), the paper's normalization `(P,Q) ↦ (Q,−P)` being exactly its proof.
`CornerEnumeration` is the arithmetic vertex-normalization lemma behind the
labels (Lemma 2.2, `lem:enum`): the two bottom corners of a normalized pair
can only be `(1,0)` and `(k,1)`, in either order.  `GapConditionSideSymm`
is the side-symmetric form of the gap condition (hypothesis (ii)):
`k ≥ 2 ↔ max((p₀)ₓ, (q₀)ₓ) ≥ 2`.

*Not* formalized here: the general-cell counting propositions (3.2, 3.3),
the `(2,3)`/`(2,4)`/`k ≥ 3` variants, the log-residue functional, the
radical-membership refinement (Remark 3.5), and the GGHV chart reduction;
see the README.

Reading conventions (all standard Mathlib):
* `MvPolynomial (Fin 2) K` is `K[x,y]` with `x = X 0`, `y = X 1`; an
  exponent vector is `Finsupp.single 0 i + Finsupp.single 1 j ↔ xⁱyʲ`,
  and `p 0`, `p 1` are its two components.
* `MvPolynomial.pderiv 0` and `pderiv 1` are `∂/∂x` and `∂/∂y`.
* `MvPolynomial.coeff m P` is the coefficient of the monomial `m` in `P`,
  and `P.support` is the (finite) set of exponents of nonzero coefficient.
-/

open MvPolynomial Finsupp

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
  sorry

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
  sorry

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
  sorry

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
  sorry
