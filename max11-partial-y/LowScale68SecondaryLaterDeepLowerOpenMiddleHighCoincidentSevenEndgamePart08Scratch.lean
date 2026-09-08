import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentSevenEndgamePart07Scratch

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

set_option maxHeartbeats 7000000 in
theorem fiveRadiusReducedRowOnePolynomial68_coeff_coincidentSeven_ne_zero
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hddeg : d.natDegree ≤ 5 * n - h)
    (hedeg : e.natDegree ≤ 6 * n - h)
    (hc : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (fiveRadiusReducedRowOnePolynomial68 gamma epsilon zeta A B c d e).coeff
      (5 * n - 1) ≠ 0 := by
  have htail := fiveRadiusCoincidentSevenRowOneTail68_degree_lt
    gamma epsilon zeta A B c d e n g h hn hg hgh hh hwallH hwallG
    hA hB hcdeg hddeg hedeg
  have hcore := fiveRadiusBalancedRowOneCore68_coeff_of_coincidentSeven
    A B c d e n g h hn hg hwallH hwallG hA hB hcdeg hddeg hedeg
  rw [fiveRadiusReducedRowOnePolynomial68_coincidentSevenSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt htail, add_zero, hcore]
  have hbal : 2 * h = 3 * g := by omega
  have hbalK : (2 : k) * (h : k) = (3 : k) * (g : k) := by
    exact_mod_cast hbal
  have hng : (4 : k) * (n : k) - (g : k) ≠ 0 := by
    have hpos : 0 < 4 * n - g := by omega
    have hcast : (((4 * n - g : ℕ) : k)) =
        (4 : k) * (n : k) - (g : k) := by
      rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
      push_cast
      ring
    rw [← hcast]
    exact Nat.cast_ne_zero.mpr hpos.ne'
  have hscalar := residualRowOneScalar_ne_zero68
    (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) hc hng hbalK hdisc hinc hrel
  have heq := residualRowOneScalar68
    (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) hc hbalK hdisc hinc hrel
  intro hz
  apply hscalar
  rw [← heq]
  rw [Nat.cast_sub (by omega : g ≤ 4 * n),
    Nat.cast_sub (by omega : h ≤ 6 * n)] at hz
  push_cast at hz
  have hwallGK : (3 : k) * (g : k) = (7 : k) * (n : k) := by
    exact_mod_cast hwallG
  have hfiveK : (12 : k) * (n : k) - (3 : k) * (g : k) =
      (5 : k) * (n : k) := by
    linear_combination -hwallGK
  rw [hfiveK]
  exact hz

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
