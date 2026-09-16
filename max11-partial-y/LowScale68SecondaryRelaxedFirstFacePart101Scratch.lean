import LowScale68SecondaryResidualExtraction

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

theorem firstSecondaryFace68_gap_ne_six_radius
    (n g : ℕ) (hn : 0 < n) (hrel : 2 * g < 3 * n) :
    (g : k) - 6 * (n : k) ≠ 0 := by
  intro hzero
  have heq : (g : k) = 6 * (n : k) := sub_eq_zero.mp hzero
  have hnat : g = 6 * n := by exact_mod_cast heq
  omega

theorem firstSecondaryFace68_classify_of_two_mul_gap_lt_three_mul_radius
    (n g : ℕ) (a b c d e : k) (ha : a ≠ 0)
    (hn : 0 < n) (hrel : 2 * g < 3 * n)
    (hface : FirstSecondaryFace68 (n : k) (g : k) a b c d e) :
    e = 0 ∧ a * b = 3 * d := by
  exact firstSecondaryFace68_classify (n : k) (g : k) a b c d e ha
    (firstSecondaryFace68_gap_ne_six_radius n g hn hrel) hface

end RelaxedSecondaryFace68
end Max11DegreeRoutes
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

/-- The two invariants and the terminal one-form, without `F₁`, leave three
algebraic families.  The middle family `e = 0`, `c = 0`, `a*b = d` is killed
only by `F₁`. -/
theorem firstSecondaryFourThreeZero68_classify
    (a b c d e : k) (ha : a ≠ 0)
    (hfour : firstSecondaryFour68 a b c d e = 0)
    (hthree : firstSecondaryThree68 a b c d e = 0)
    (hzero : firstSecondaryZero68 a b c d e = 0) :
    (e = 0 ∧ a * b = 3 * d) ∨
      (e = 0 ∧ c = 0 ∧ a * b = d) ∨
      (b = 0 ∧ c = 0 ∧ d = 0) := by
  have heFactor : e * (a * b - 3 * d) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-3 : k) ≠ 0)
    calc
      (-3 : k) * (e * (a * b - 3 * d)) =
          a * firstSecondaryFour68 a b c d e -
            firstSecondaryZero68 a b c d e := by
        simp only [firstSecondaryFour68, firstSecondaryZero68]
        ring
      _ = 0 := by rw [hfour, hzero]; ring
  rcases mul_eq_zero.mp heFactor with he0 | hab3
  · have hcFactor : c * (a * b - 3 * d) = 0 := by
      calc
        c * (a * b - 3 * d) = firstSecondaryFour68 a b c d e := by
          simp only [firstSecondaryFour68, he0, mul_zero, sub_zero]
          ring
        _ = 0 := hfour
    rcases mul_eq_zero.mp hcFactor with hc0 | hab3'
    · have hbd : (a * b - d) * (a * b - 3 * d) = 0 := by
        calc
          (a * b - d) * (a * b - 3 * d) =
              firstSecondaryThree68 a b c d e := by
            simp only [firstSecondaryThree68, he0, hc0, mul_zero, add_zero]
            ring
          _ = 0 := hthree
      rcases mul_eq_zero.mp hbd with habd | hab3''
      · exact Or.inr (Or.inl ⟨he0, hc0, sub_eq_zero.mp habd⟩)
      · exact Or.inl ⟨he0, sub_eq_zero.mp hab3''⟩
    · exact Or.inl ⟨he0, sub_eq_zero.mp hab3'⟩
  · have hab3' : a * b = 3 * d := sub_eq_zero.mp hab3
    by_cases he : e = 0
    · exact Or.inl ⟨he, hab3'⟩
    · have hce : c * e = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (6 : k) ≠ 0)
        calc
          (6 : k) * (c * e) = firstSecondaryThree68 a b c d e -
              (a * b - d) * (a * b - 3 * d) := by
            simp only [firstSecondaryThree68]
            ring
          _ = 0 := by rw [hthree, hab3']; ring
      have hc0 : c = 0 := (mul_eq_zero.mp hce).resolve_right he
      have hde : d * e = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (-9 : k) ≠ 0)
        calc
          (-9 : k) * (d * e) = firstSecondaryZero68 a b c d e := by
            simp [firstSecondaryZero68, hc0]
            ring
          _ = 0 := hzero
      have hd0 : d = 0 := (mul_eq_zero.mp hde).resolve_right he
      have hb0 : b = 0 := by
        have hab0 : a * b = 0 := by simpa [hd0] using hab3'
        exact (mul_eq_zero.mp hab0).resolve_left ha
      exact Or.inr (Or.inr ⟨hb0, hc0, hd0⟩)

end RelaxedSecondaryFace68
end Max11DegreeRoutes
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
theorem cubicLoadSPolynomial68_degreeBound_of_loadL
    (l alpha beta delta : k) (A B c : k[X]) (n g : ℕ)
    (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadSPolynomial68 l alpha beta delta A B c).natDegree ≤
      max (2 * n) (3 * n - g) := by
  have heq : cubicLoadSPolynomial68 l alpha beta delta A B c =
      alpha • B + (5 / 6 * beta : k) • A + C delta := by
    simp [cubicLoadSPolynomial68, hl, mul_zero, zero_smul, add_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadTPolynomial68_degreeBound_of_loadL
    (l alpha beta gamma epsilon : k) (A B c D : k[X]) (n g : ℕ)
    (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g) :
    (cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D).natDegree ≤
      4 * n := by
  have heq : cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D =
      (1 / 3 * alpha : k) • A ^ 2 + alpha • c +
        (5 / 6 * beta : k) • B + (2 / 3 * gamma : k) • A + C epsilon := by
    simp [cubicLoadTPolynomial68, hl, mul_zero, zero_smul, add_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadUPolynomial68_degreeBound_of_loadL
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) (n g : ℕ)
    (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e).natDegree ≤
      max (4 * n) (5 * n - g) := by
  have heq : cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e =
      alpha • D + (5 / 24 * beta : k) • A ^ 2 +
        (5 / 6 * beta : k) • c + (2 / 3 * gamma : k) • B +
        (1 / 2 * delta : k) • A + C zeta := by
    simp [cubicLoadUPolynomial68, hl, mul_zero, zero_smul, add_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadVPolynomial68_degreeBound_of_loadL
    (l alpha beta gamma delta epsilon eta : k) (A B c D e : k[X])
    (n g : ℕ) (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ 6 * n := by
  have heq : cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
        A B c D e =
      (1 / 27 * alpha : k) • A ^ 3 + (1 / 3 * alpha : k) • (A * c) +
        alpha • e - (5 / 36 * beta : k) • (A * B) +
        (5 / 6 * beta : k) • D + (1 / 9 * gamma : k) • A ^ 2 +
        (2 / 3 * gamma : k) • c + (1 / 2 * delta : k) • B +
        (1 / 3 * epsilon : k) • A + C eta := by
    simp [cubicLoadVPolynomial68, hl, mul_zero, zero_smul, add_zero, sub_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadTPolynomial68_degreeBound_of_loadL_alpha
    (l alpha beta gamma epsilon : k) (A B c D : k[X]) (n g : ℕ)
    (hl : l = 0) (halpha : alpha = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g) :
    (cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D).natDegree ≤
      max (2 * n) (3 * n - g) := by
  have heq : cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D =
      (5 / 6 * beta : k) • B + (2 / 3 * gamma : k) • A + C epsilon := by
    simp [cubicLoadTPolynomial68, hl, halpha, mul_zero, zero_smul, add_zero]
  rw [heq]
  compute_degree
  omega

end RelaxedSecondaryFace68
end Max11DegreeRoutes
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
/-- After `l = 0`, every remaining cubic-invariant load is at most the old
weight of `beta A² B`. -/
theorem secondaryLoadInvariantThreePolynomial68_degree_le_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hl : l = 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantThreePolynomial68 l beta gamma delta epsilon zeta
      A B c D e).natDegree ≤ 7 * n := by
  have heq : secondaryLoadInvariantThreePolynomial68 l beta gamma delta
        epsilon zeta A B c D e =
      zeta • B + (2 * epsilon : k) • c + (4 * gamma : k) • e -
        (2 / 3 * gamma : k) • B ^ 2 + (3 * delta : k) • D -
        (3 / 2 * delta : k) • (A * B) +
        (5 / 24 * beta : k) • (A ^ 2 * B) -
        (5 / 6 * beta : k) • (A * D) -
        (5 / 6 * beta : k) • (B * c) := by
    simp [secondaryLoadInvariantThreePolynomial68, hl, mul_zero, zero_smul,
      add_zero, sub_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_firstFace_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantThreePolynomial68 l beta gamma delta epsilon zeta
      A B c D e).natDegree < 10 * n - 2 * g := by
  have hle := secondaryLoadInvariantThreePolynomial68_degree_le_of_loadL
    l beta gamma delta epsilon zeta A B c D e n g hl hA hB hc hD he
  exact hle.trans_lt (by omega)

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousFirstIntegralFourPolynomial68_secondaryCoeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e).coeff
        (9 * n - 2 * g) =
      (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have lower (p : k[X]) (hp : p.natDegree < 9 * n - 2 * g) :
      p.coeff (9 * n - 2 * g) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hABC : (A * B * c).coeff (9 * n - 2 * g) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B c (2 * n)
      (3 * n - g) (4 * n - g) hA hB hc
    have hi : 2 * n + (3 * n - g) + (4 * n - g) =
        9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBe : (B * e).coeff (9 * n - 2 * g) =
      B.coeff (3 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - g) hB he
    have hi : (3 * n - g) + (6 * n - g) = 9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hDc : (D * c).coeff (9 * n - 2 * g) =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) := by
    have h := coeff_mul_at_bounds68 D c (5 * n - g) (4 * n - g) hD hc
    have hi : (5 * n - g) + (4 * n - g) = 9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hB3 : (B ^ 3).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralFourPolynomial68, zero_mul, zero_smul,
    add_zero, sub_zero, coeff_add, coeff_sub, coeff_smul, hABC, hBe, hDc,
    hB3, smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstSecondaryFour68]
  ring

end RelaxedSecondaryFace68
end Max11DegreeRoutes
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

/-! ## Homogeneous invariant coefficients under `2g < 3n` -/

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousFirstIntegralThreePolynomial68_secondaryCoeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e).coeff
        (10 * n - 2 * g) =
      (4 / 9 : k) * firstSecondaryThree68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have lower (p : k[X]) (hp : p.natDegree < 10 * n - 2 * g) :
      p.coeff (10 * n - 2 * g) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hA2coeff : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hB2coeff : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hA2B2 : (A ^ 2 * B ^ 2).coeff (10 * n - 2 * g) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_mul_at_bounds68 (A ^ 2) (B ^ 2) (4 * n)
      (6 * n - 2 * g) hA2deg hB2deg
    have hi : 4 * n + (6 * n - 2 * g) = 10 * n - 2 * g := by omega
    rw [hi, hA2coeff, hB2coeff] at h
    exact h
  have hABD : (A * B * D).coeff (10 * n - 2 * g) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        D.coeff (5 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B D (2 * n)
      (3 * n - g) (5 * n - g) hA hB hD
    have hi : 2 * n + (3 * n - g) + (5 * n - g) =
        10 * n - 2 * g := by omega
    simpa only [hi] using h
  have hD2 : (D ^ 2).coeff (10 * n - 2 * g) =
      D.coeff (5 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 D (5 * n - g) 2 hD
    have hi : 2 * (5 * n - g) = 10 * n - 2 * g := by omega
    simpa only [hi] using h
  have hce : (c * e).coeff (10 * n - 2 * g) =
      c.coeff (4 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - g) hc he
    have hi : (4 * n - g) + (6 * n - g) = 10 * n - 2 * g := by omega
    simpa only [hi] using h
  have hB2c : (B ^ 2 * c).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralThreePolynomial68, zero_mul, zero_smul,
    add_zero, sub_zero, coeff_add, coeff_sub, coeff_smul, hA2B2, hABD,
    hB2c, hD2, hce, smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstSecondaryThree68]
  ring

end RelaxedSecondaryFace68
end Max11DegreeRoutes
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

/-! ## Homogeneous invariant coefficients under `2g < 3n` -/

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_secondaryCoeff_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        A B c D e).coeff (9 * n - 2 * g) =
      (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (secondaryLoadInvariantFourPolynomial68_degree_lt_firstFace_of_loadL
        l beta gamma delta epsilon zeta A B c D e n g hl hrel
        hA hB hc hD he), add_zero]
  simpa [hl] using
    cubicHomogeneousFirstIntegralFourPolynomial68_secondaryCoeff A B c D e
      n g hn hg hrel hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_secondaryCoeff_of_loadL
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        A B c D e).coeff (10 * n - 2 * g) =
      (4 / 9 : k) * firstSecondaryThree68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (secondaryLoadInvariantThreePolynomial68_degree_lt_firstFace_of_loadL
        l beta gamma delta epsilon zeta A B c D e n g hn hl hrel
        hA hB hc hD he), add_zero]
  simpa [hl] using
    cubicHomogeneousFirstIntegralThreePolynomial68_secondaryCoeff A B c D e
      n g hn hg hrel hA hB hc hD he

end RelaxedSecondaryFace68
end Max11DegreeRoutes
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

/-! ## Homogeneous invariant coefficients under `2g < 3n` -/

set_option maxHeartbeats 2000000 in
theorem polynomialSecondaryInvariantEquations68_of_loadL
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3) :
    firstSecondaryFour68 (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) = 0 ∧
      firstSecondaryThree68 (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) = 0 := by
  have ht4 : 9 * n - 2 * g ≠ 0 := by omega
  have ht3 : 10 * n - 2 * g ≠ 0 := by omega
  have hfour := congrArg (fun p : k[X] => p.coeff (9 * n - 2 * g)) hI4
  rw [hC0, hE0, firstIntegralFourPolynomial68_cubicCoordinates,
    cubicFirstIntegralFourPolynomial68_secondaryCoeff_of_loadL
      l beta gamma delta epsilon zeta A B c D e n g hn hg hl hrel
      hA hB hc hD he] at hfour
  simp only [coeff_C, if_neg ht4] at hfour
  have hthree := congrArg (fun p : k[X] => p.coeff (10 * n - 2 * g)) hI3
  rw [hC0, hE0, firstIntegralThreePolynomial68_cubicCoordinates,
    cubicFirstIntegralThreePolynomial68_secondaryCoeff_of_loadL
      l beta gamma delta epsilon zeta A B c D e n g hn hg hl hrel
      hA hB hc hD he] at hthree
  simp only [coeff_C, if_neg ht3] at hthree
  constructor
  · exact (mul_eq_zero.mp hfour).resolve_left (by norm_num)
  · exact (mul_eq_zero.mp hthree).resolve_left (by norm_num)

private theorem cubicC0_degreeBound68 (A c : k[X]) (n g : ℕ)
    (hA : A.natDegree ≤ 2 * n) (hc : c.natDegree ≤ 4 * n - g) :
    ((1 / 3 : k) • A ^ 2 + c).natDegree ≤ 4 * n := by
  compute_degree
  omega

private theorem cubicE_degreeBound68 (A c e : k[X]) (n g : ℕ)
    (hA : A.natDegree ≤ 2 * n) (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e).natDegree ≤ 6 * n := by
  compute_degree
  omega

end RelaxedSecondaryFace68
end Max11DegreeRoutes
