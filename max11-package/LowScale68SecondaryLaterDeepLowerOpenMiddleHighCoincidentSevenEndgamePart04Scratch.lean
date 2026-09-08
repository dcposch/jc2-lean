import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentSevenEndgamePart03Scratch

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

set_option maxHeartbeats 5000000 in
theorem coincidentSeven_rowZero_relation68
    (alpha gamma epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (ha : A.coeff (2 * n) ≠ 0)
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
    (hrow0 :
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * n - 1) = 0) :
    (32 / 81 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (8 / 9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) +
      (1 / 3 : k) * zeta * A.coeff (2 * n) ^ 2 = 0 := by
  have hQ := residualIncidenceQ68_degree_le_twoRadius_of_coincidentSeven
    gamma epsilon zeta i4 A B c d e n g h hn hwallH hwallG hA hB hd hi4
  have hq := residualIncidenceQ68_coeff_twoRadius_of_coincidentSeven
    gamma epsilon zeta i4 A B c d e n g h hn hwallH hwallG hA hB hd hi4
  have hres := secondaryResidualRowZeroPolynomial68_coeff_coincidentSeven
    A B c d e n g h hn hg hgh hh hwallH hwallG hA hB hc hd he hQ
  have hload := coincidentSevenRowZeroLoad68_coeff
    gamma epsilon zeta A B c d e n g h hn hg hwallH hwallG hA hB hc hd he
  have hloadEq := cubicLoadRowZeroPolynomial68_coincidentSeven
    alpha gamma epsilon zeta eta A B c d e
  rw [coeff_add, hres, hloadEq, hload, hq] at hrow0
  push_cast at hrow0
  have hN : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hfac : (n : k) * A.coeff (2 * n) ≠ 0 := mul_ne_zero hN ha
  have hfactor : (n : k) * A.coeff (2 * n) *
      ((32 / 81 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
        (8 / 9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        (1 / 3 : k) * zeta * A.coeff (2 * n) ^ 2) = 0 := by
    linear_combination hrow0 +
      (8 / 243 : k) * (n : k) * A.coeff (2 * n) *
        B.coeff (3 * n - g) * hdisc
  exact (mul_eq_zero.mp hfactor).resolve_left hfac

theorem coincidentSeven_balancedRelation_of_rowZero_rowTwo68
    (zeta : k) (a b c d e : k) (n : ℕ) (hn : 0 < n)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hrow0 :
      (32 / 81 : k) * b * c ^ 2 - (8 / 9 : k) * d * e +
        (1 / 3 : k) * zeta * a ^ 2 = 0)
    (hrow2 :
      (32 / 81 : k) * (((4 * n : ℕ) : k)) * a * b ^ 3 +
        (8 / 3 : k) * (((4 * n : ℕ) : k)) * d * e +
        zeta * (n : k) * a ^ 2 = 0) :
    (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0 := by
  push_cast at hrow2
  have hN : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hR2fac : (n : k) *
      ((-128 / 27 : k) * b * c ^ 2 + (32 / 3 : k) * d * e +
        zeta * a ^ 2) = 0 := by
    linear_combination hrow2 -
      (128 / 81 : k) * (n : k) * b * hdisc
  have hR2 :
      (-128 / 27 : k) * b * c ^ 2 + (32 / 3 : k) * d * e +
        zeta * a ^ 2 = 0 :=
    (mul_eq_zero.mp hR2fac).resolve_left hN
  have hfac : (40 / 27 : k) ≠ 0 := by norm_num
  have hbalanced : (40 / 27 : k) *
      ((4 : k) * b * c ^ 2 - (9 : k) * d * e) = 0 := by
    linear_combination (3 : k) * hrow0 - hR2
  exact (mul_eq_zero.mp hbalanced).resolve_left hfac

def fiveRadiusCoincidentSevenRowOneTail68
    (gamma epsilon zeta : k) (A B c d e : k[X]) : k[X] :=
  fiveRadiusBalancedRowOneTail68 gamma epsilon A B c d e +
    zeta • ((1 / 3 : k) • (derivative A * B) + derivative d)

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
