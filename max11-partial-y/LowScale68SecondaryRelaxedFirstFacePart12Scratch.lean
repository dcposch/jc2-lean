import LowScale68SecondaryRelaxedFirstFacePart11Scratch

/-! # Relaxed first `(6,8)` secondary face after `l = 0`

The tracked extraction in `LowScale68SecondaryExtraction` and
`LowScale68SecondaryOneForms` uses the chamber `2g < n` because the Jacobian
load `l A^4` and the `l`-pieces of the integrated coefficients sit on or
above the first secondary face once `2g ≥ n`.  In the complementary
large-gap chamber the quartic invariant forces `l = 0`.  With that
hypothesis the same leading coefficients can be re-extracted under the
weaker old-weight cutoff `2g < 3n`, except the second one-form row, whose
`alpha A^2` load meets the face as soon as `g ≥ n`.

Exact chambers, remaining loads otherwise arbitrary:

* invariants `F₄`, `F₃` and one-forms `F₂`, `F₀`: `2g < 3n`
* one-form `F₁`: `g < n` (or `2g < 3n` after the extra vanishing `alpha = 0`)
* full five-face classification `e = 0 ∧ a*b = 3*d`: needs `F₁`
* four-equation classification without `F₁`, under `2g < 3n`:
  `(e = 0 ∧ a*b = 3*d) ∨ (e = 0 ∧ c = 0 ∧ a*b = d) ∨ (b = c = d = 0)`
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RelaxedSecondaryFace68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem leaf68_natDegree_mulDeriv_lt {p q : k[X]} {u v bound : ℕ}
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) (h : u + (v - 1) < bound) :
    (p * derivative q).natDegree < bound :=
  natDegree_mul_le.trans_lt
    (lt_of_le_of_lt
      (Nat.add_le_add hp ((natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1))) h)

private theorem leaf68_natDegree_smul_lt (r : k) {p : k[X]} {bound : ℕ}
    (h : p.natDegree < bound) : (r • p).natDegree < bound :=
  (natDegree_smul_le r p).trans_lt h

private theorem leaf68_natDegree_add_lt {p q : k[X]} {bound : ℕ}
    (hp : p.natDegree < bound) (hq : q.natDegree < bound) :
    (p + q).natDegree < bound :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem leaf68_natDegree_sub_lt {p q : k[X]} {bound : ℕ}
    (hp : p.natDegree < bound) (hq : q.natDegree < bound) :
    (p - q).natDegree < bound :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)


/-! ## Abstract classification under the relaxed radius gap -/

/-! ## Load degree cutoffs after `l = 0` -/

/-! ## Homogeneous invariant coefficients under `2g < 3n` -/

/-! ## One-form load cutoffs after `l = 0` -/

private theorem cubicE_degreeBound68 (A c e : k[X]) (n g : ℕ)
    (hA : A.natDegree ≤ 2 * n) (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e).natDegree ≤ 6 * n := by
  compute_degree
  omega

set_option maxHeartbeats 3000000 in
theorem cubicLoadRowZeroPolynomial68_degree_lt_of_loadL
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
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
  have hV : Vl.natDegree ≤ 6 * n :=
    cubicLoadVPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
      epsilon eta A B c D e n g hl hA hB hc hD he
  have hE : E.natDegree ≤ 6 * n := cubicE_degreeBound68 A c e n g hA hc he
  rcases le_total g n with hgle | hnge
  · have hU : Ul.natDegree ≤ 5 * n - g :=
      (cubicLoadUPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
        zeta A B c D e n g hl hA hB hc hD he).trans
        (by rw [max_eq_right (by omega)])
    have hUlE : (Ul * derivative E).natDegree < 13 * n - 2 * g - 1 :=
      leaf68_natDegree_mulDeriv_lt hU hE (by omega)
    have hDVl : (D * derivative Vl).natDegree < 13 * n - 2 * g - 1 :=
      leaf68_natDegree_mulDeriv_lt hD hV (by omega)
    change (Ul * derivative E - D * derivative Vl).natDegree < _
    exact leaf68_natDegree_sub_lt
          hUlE
          hDVl
  · have hU : Ul.natDegree ≤ 4 * n :=
      (cubicLoadUPolynomial68_degreeBound_of_loadL l alpha beta gamma delta
        zeta A B c D e n g hl hA hB hc hD he).trans
        (by rw [max_eq_left (by omega)])
    have hUlE : (Ul * derivative E).natDegree < 13 * n - 2 * g - 1 :=
      leaf68_natDegree_mulDeriv_lt hU hE (by omega)
    have hDVl : (D * derivative Vl).natDegree < 13 * n - 2 * g - 1 :=
      leaf68_natDegree_mulDeriv_lt hD hV (by omega)
    change (Ul * derivative E - D * derivative Vl).natDegree < _
    exact leaf68_natDegree_sub_lt
          hUlE
          hDVl

end RelaxedSecondaryFace68
end Max11DegreeRoutes
