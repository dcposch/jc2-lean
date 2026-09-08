import LowScale68SecondaryLaterDeepFiveToSixRowOnePart03Scratch

/-! # The row-one face in the later-deep five-to-six chamber

This module closes the two spurious families left by the I4/I3/row-zero
classification.  The only surviving top packet is `e = 0`, `a*b = 3*d`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSixRowOne68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact `F1` extraction from the integrated row-one equation throughout
`5n < 2g ≤ 6n`. -/
theorem integratedLowerRowOnePolynomial68_fiveToSix_forces_firstSecondaryOne
    (alpha gamma epsilon zeta eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hrow : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = 0) :
    firstSecondaryOne68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon zeta eta A B c D e
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split] at hrow
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) hrow
  simp only [coeff_add, coeff_zero,
    cubicHomogeneousRowOnePolynomial68_secondaryCoeff_fiveToSix
      A B c D e n g hn hwindow hA hB hc hD he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_fiveToSix
        alpha gamma epsilon zeta eta A B c D e n g hn hwindow
        hA hB hc hD he), add_zero] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (by norm_num)

/-- Pure scalar elimination: `F1` absorbs the middle family into the main
family and contradicts the all-but-`e` family using secondary attainment. -/
theorem firstSecondaryOne68_e_c_zero_d_eq_ab_fiveToSix
    (N G a b : k) :
    firstSecondaryOne68 N G a b 0 (a * b) 0 =
      (4 : k) * a ^ 3 * b ^ 2 * (6 * N - G) := by
  simp only [firstSecondaryOne68]
  ring

theorem firstSecondaryOne68_b_c_d_zero_fiveToSix
    (N G a e : k) :
    firstSecondaryOne68 N G a 0 0 0 e =
      (27 : k) * e ^ 2 * (G - 6 * N) := by
  simp only [firstSecondaryOne68]
  ring

end LaterDeepFiveToSixRowOne68
end Max11DegreeRoutes
