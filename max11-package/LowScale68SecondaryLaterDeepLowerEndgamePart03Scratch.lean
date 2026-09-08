import LowScale68SecondaryLaterDeepLowerEndgamePart02Scratch

/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## I3 at `10n-2g` -/

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_laterDeepLower
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hl : l = 0)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantThreePolynomial68 l beta gamma delta epsilon zeta
      A B c D e).natDegree < 10 * n - 2 * g := by
  have hg3 : g < 3 * n := laterDeepLower_gap_lt_three_radius n g hn hwindow
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
theorem cubicFirstIntegralThreePolynomial68_laterDeepLowerCoeff
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
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
      (secondaryLoadInvariantThreePolynomial68_degree_lt_laterDeepLower
        l beta gamma delta epsilon zeta A B c D e n g hn hl hwindow
        hA hB hc hD he), add_zero]
  simpa [hl] using
    cubicHomogeneousFirstIntegralThreePolynomial68_laterDeepLowerCoeff
      A B c D e n g hn hg hwindow hA hB hc hD he

theorem cubicFirstIntegralThreePolynomial68_laterDeepLower_forces_face
    (l beta gamma delta epsilon zeta i3 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hl : l = 0)
    (hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hI3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e = C i3) :
    firstSecondaryThree68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (10 * n - 2 * g)) hI3
  rw [cubicFirstIntegralThreePolynomial68_laterDeepLowerCoeff
    l beta gamma delta epsilon zeta A B c D e n g hn hg hl hwindow
    hA hB hc hD he] at hcoeff
  have hi : 10 * n - 2 * g ≠ 0 :=
    laterDeepLower_three_index_ne_zero n g hn hwindow
  simp only [coeff_C, if_neg hi] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (by norm_num)

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
