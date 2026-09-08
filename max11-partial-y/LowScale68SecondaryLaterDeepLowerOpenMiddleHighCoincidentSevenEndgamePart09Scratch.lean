import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentSevenEndgamePart08Scratch

/-! # Closure for the coincident seven wall `2h=3g=7n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The quartic incidence defect on the coincident wall -/

/-! ## Row zero at `6n-1` -/

/-! ## Row one after the row-zero/row-two cancellation -/

set_option maxHeartbeats 16000000 in
theorem laterDeepLowerOpenMiddle_coincidentSeven_impossible68
    (alpha gamma epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow2 : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0)
    (hrow1 : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68
        0 alpha 0 gamma 0 epsilon zeta eta A B c
          ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow0 :
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * n - 1) = 0) :
    False := by
  have hsum : g + h < 7 * n := by omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zero_sum_lt_seven
      gamma epsilon zeta A B c d e n g h hn hopen hsum hA hB hd
  have face :=
    polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_delta_zero
      gamma epsilon zeta i4 i3 A B c d e n g h hn hg hgh hh hopen
      hload hA hB hc hd he hi4 hi3
  have hrow0rel := coincidentSeven_rowZero_relation68
    alpha gamma epsilon zeta eta i4 A B c d e n g h hn hg hgh hh
    hwallH hwallG ha hA hB hc hd he hdisc hi4 hrow0
  have hrow2rel := fiveRadiusReducedRowTwo_coincidentSevenWalls_relation68
    gamma epsilon zeta i4 A B c d e n g h hn hg hgh hopen hwallH hwallG
    hA hB hc hd he hdisc hrow2
  have hrel := coincidentSeven_balancedRelation_of_rowZero_rowTwo68
    zeta (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) n hn hdisc hrow0rel hrow2rel
  have hreduced := fiveRadiusReducedRowOnePolynomial68_eq_zero
    alpha gamma epsilon zeta eta i3 A B c d e hi3 hrow1
  have hne := fiveRadiusReducedRowOnePolynomial68_coeff_coincidentSeven_ne_zero
    gamma epsilon zeta A B c d e n g h hn hg hgh hh hwallH hwallG
    hA hB hc hd he hc0 hdisc face.four hrel
  have hz := congrArg (fun p : k[X] => p.coeff (5 * n - 1)) hreduced
  simp only [coeff_zero] at hz
  exact hne hz

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
