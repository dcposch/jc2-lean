import LowScale68SecondaryRelaxedFirstFacePart07Scratch

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
