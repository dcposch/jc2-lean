import LowScale68SecondaryRelaxedFirstFacePart22Scratch

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

/-! ## One-form load cutoffs after `l = 0` -/

end RelaxedSecondaryFace68

section RelaxedSecondaryOneForms68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Homogeneous one-form coefficients under `2g < 3n` -/

/-! ## Packaged face and classification -/

theorem integratedPolynomialLowerSystem_firstSecondaryClassified68_of_loadL_alpha
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (halpha : alpha = 0)
    (hrel : 2 * g < 3 * n)
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
  exact firstSecondaryFace68_classify_of_two_mul_gap_lt_three_mul_radius n g
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha hn hrel
    (integratedPolynomialLowerSystem_firstSecondaryFace68_of_loadL_alpha
      l alpha beta gamma delta epsilon zeta eta terminal
      A B C0 c D E e n g hn hg hl halpha hrel hA hB hc hD he ha hC0 hE0 hsys)

set_option maxHeartbeats 3000000 in
/-- Without `F₁`, the relaxed chamber `2g < 3n` after `l = 0` still
supplies `F₄`, `F₃`, `F₂`, and `F₀`, leaving three algebraic families. -/
theorem polynomialSecondaryFourThreeZeroEquations68_of_loadL
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
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
    (e.coeff (6 * n - g) = 0 ∧
        A.coeff (2 * n) * B.coeff (3 * n - g) =
          3 * D.coeff (5 * n - g)) ∨
      (e.coeff (6 * n - g) = 0 ∧
        c.coeff (4 * n - g) = 0 ∧
        A.coeff (2 * n) * B.coeff (3 * n - g) =
          D.coeff (5 * n - g)) ∨
      (B.coeff (3 * n - g) = 0 ∧
        c.coeff (4 * n - g) = 0 ∧
        D.coeff (5 * n - g) = 0) := by
  obtain ⟨i4, hI4⟩ := hsys.firstFour
  obtain ⟨i3, hI3⟩ := hsys.firstThree
  have hinv := polynomialSecondaryInvariantEquations68_of_loadL
    l beta gamma delta epsilon zeta i4 i3 A B C0 c D E e n g
    hn hg hl hrel hA hB hc hD he hC0 hE0 hI4 hI3
  have hrowZero := hsys.rowZero
  rw [hC0, hE0] at hrowZero
  have hzero := congrArg
    (fun p : k[X] => p.coeff (13 * n - 2 * g - 1)) hrowZero
  rw [integratedLowerRowZeroPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at hzero
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
  exact firstSecondaryFourThreeZero68_classify
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha hinv.1 hinv.2 hzero0

end RelaxedSecondaryOneForms68
end Max11DegreeRoutes
