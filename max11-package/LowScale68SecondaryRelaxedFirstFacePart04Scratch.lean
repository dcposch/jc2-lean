import LowScale68SecondaryRelaxedFirstFacePart03Scratch

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

/-! ## Abstract classification under the relaxed radius gap -/

/-! ## Load degree cutoffs after `l = 0` -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadUPolynomial68_degreeBound_of_loadL_alpha
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) (n g : ℕ)
    (hl : l = 0) (halpha : alpha = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e).natDegree ≤
      4 * n := by
  have heq : cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e =
      (5 / 24 * beta : k) • A ^ 2 + (5 / 6 * beta : k) • c +
        (2 / 3 * gamma : k) • B + (1 / 2 * delta : k) • A + C zeta := by
    simp [cubicLoadUPolynomial68, hl, halpha, mul_zero, zero_smul, add_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadVPolynomial68_degreeBound_of_loadL_alpha
    (l alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (n g : ℕ) (hl : l = 0) (halpha : alpha = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ max (4 * n) (5 * n - g) := by
  have heq : cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
        A B c D e =
      -(5 / 36 * beta : k) • (A * B) + (5 / 6 * beta : k) • D +
        (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
        (1 / 2 * delta : k) • B + (1 / 3 * epsilon : k) • A + C eta := by
    simp [cubicLoadVPolynomial68, hl, halpha, mul_zero, zero_smul, add_zero,
      sub_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- After `l = 0`, every remaining quartic-invariant load is at most the
old weight of `beta A^3`. -/
theorem secondaryLoadInvariantFourPolynomial68_degree_le_sixRadius_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68 l beta gamma delta epsilon zeta
      A B c D e).natDegree ≤ 6 * n := by
  have heq : secondaryLoadInvariantFourPolynomial68 l beta gamma delta
        epsilon zeta A B c D e =
      zeta • A + (2 * epsilon : k) • B +
        (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
        (4 * gamma : k) • D - (4 / 3 * gamma : k) • (A * B) +
        (5 * beta : k) • e + (5 / 6 * beta : k) • (A * c) -
        (5 / 12 * beta : k) • B ^ 2 + (5 / 72 * beta : k) • A ^ 3 := by
    simp [secondaryLoadInvariantFourPolynomial68, hl, mul_zero, zero_smul,
      add_zero, sub_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_firstFace_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68 l beta gamma delta epsilon zeta
      A B c D e).natDegree < 9 * n - 2 * g := by
  have hle := secondaryLoadInvariantFourPolynomial68_degree_le_sixRadius_of_loadL
    l beta gamma delta epsilon zeta A B c D e n g hl hA hB hc hD he
  exact hle.trans_lt (by omega)

end RelaxedSecondaryFace68
end Max11DegreeRoutes
