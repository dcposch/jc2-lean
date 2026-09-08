import LowScale68SecondaryLaterDeepFiveRadiusTerminalResiduals

/-! # Algebra for the terminal leaves on `2g = 5n`

This file isolates the inexpensive coefficient algebra from the source-level
expanded-system assembly.  The strict terminal leaf has `d=0` and
`5n<h≤6n`; its `e` edge is strictly below the old `B^3` edge.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusTerminalLeafAlgebra68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- On the strict terminal leaf, after `zeta=0`, the old `B^3` face is
unmixed: `B*e` is strictly lower and `d=0`. -/
theorem fiveRadiusStrictTerminalI4_forces_B_top_zero68
    (gamma epsilon i4 : k) (A B c e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hstrict : 5 * n < h) (hh : h ≤ 6 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B)) e = C i4) :
    B.coeff (3 * n - g) = 0 := by
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hidx : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
  rw [hidx] at hB3
  have hBe : (B * e).natDegree < 9 * n - 3 * g := by
    compute_degree
    omega
  have hBlt : B.natDegree < 9 * n - 3 * g := hB.trans_lt (by omega)
  have hi : 9 * n - 3 * g ≠ 0 := by omega
  have hi4' : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + 0) e = C i4 := by
    simpa only [add_zero] using hi4
  have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4'
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
      at hz
  simp only [secondaryResidualInvariantFourPolynomial68, zero_smul,
    add_zero, coeff_add, coeff_smul, smul_eq_mul, hB3,
    coeff_eq_zero_of_natDegree_lt hBe,
    coeff_eq_zero_of_natDegree_lt hBlt, coeff_zero, mul_zero, zero_add,
    coeff_C, if_neg hi] at hz
  have hb3 : B.coeff (3 * n - g) ^ 3 = 0 := by
    have hfac : (-8 / 27 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hz).resolve_left hfac
  exact eq_zero_of_pow_eq_zero hb3

/-- Everything except the unique `c^2*c'` term on the strict terminal leaf. -/
def fiveRadiusStrictTerminalRowOneTail68
    (gamma epsilon : k) (A B c e : k[X]) : k[X] :=
  (-4 / 27 : k) •
      ((-2 : k) • derivative (A * B ^ 2 * c) +
        (-3 : k) • (B ^ 2 * derivative e) +
        (-18 : k) • (e * derivative e)) +
    gamma •
      ((2 / 3 : k) • (-(2 : k) • (c * derivative c)) +
        (2 / 9 : k) • (derivative A * B ^ 2) +
        (4 / 9 : k) • (A * B * derivative B)) +
    (2 * epsilon : k) • derivative e

theorem fiveRadiusReducedRowOnePolynomial68_strictTerminalSplit
    (gamma epsilon : k) (A B c e : k[X]) :
    fiveRadiusReducedRowOnePolynomial68 gamma epsilon 0 A B c 0 e =
      fiveRadiusZeroResidualRowOneCore68 c +
        fiveRadiusStrictTerminalRowOneTail68 gamma epsilon A B c e := by
  simp only [fiveRadiusReducedRowOnePolynomial68,
    fiveRadiusZeroResidualRowOneCore68,
    fiveRadiusStrictTerminalRowOneTail68, mul_zero, zero_mul, pow_two,
    derivative_zero, smul_zero, zero_smul, add_zero, zero_add, sub_zero]
  module

set_option maxHeartbeats 6000000 in
theorem fiveRadiusStrictTerminalRowOneTail68_degree_lt
    (gamma epsilon : k) (A B c e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hstrict : 5 * n < h) (hh : h ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree < 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusStrictTerminalRowOneTail68 gamma epsilon A B c e).natDegree <
      12 * n - 3 * g - 1 := by
  let idx := 12 * n - 3 * g - 1
  have hAB2cprod : (A * B ^ 2 * c).natDegree < 12 * n - 3 * g := by
    compute_degree
    omega
  have hAB2c : (derivative (A * B ^ 2 * c)).natDegree < idx := by
    have hle := natDegree_derivative_le (A * B ^ 2 * c)
    dsimp [idx]
    omega
  have hB2e : (B ^ 2 * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hee : (e * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hcc : (c * derivative c).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hApB2 : (derivative A * B ^ 2).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hABBp : (A * B * derivative B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hep : (derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  simp only [fiveRadiusStrictTerminalRowOneTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_smul_lt68 (-4 / 27 : k)
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_smul_lt68 (-2 : k) hAB2c)
            (deepGap_natDegree_smul_lt68 (-3 : k) hB2e))
          (deepGap_natDegree_smul_lt68 (-18 : k) hee)))
      (deepGap_natDegree_smul_lt68 gamma
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_smul_lt68 (2 / 3 : k)
              (deepGap_natDegree_smul_lt68 (-(2 : k)) hcc))
            (deepGap_natDegree_smul_lt68 (2 / 9 : k) hApB2))
          (deepGap_natDegree_smul_lt68 (4 / 9 : k) hABBp))))
    (deepGap_natDegree_smul_lt68 (2 * epsilon : k) hep)

set_option maxHeartbeats 8000000 in
/-- The strict selector leaf `5n<h≤6n`, `d=0` is impossible already from
I4 and the reduced second one-form. -/
theorem fiveRadius_strictTerminal_impossible68
    (gamma epsilon zeta i4 : k) (A B c e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hstrict : 5 * n < h) (hh : h ≤ 6 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - h)
    (hsupport : B.coeff (3 * n - g) ≠ 0 ∨
      c.coeff (4 * n - g) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B)) e = C i4)
    (hrow : fiveRadiusReducedRowOnePolynomial68
      gamma epsilon zeta A B c 0 e = 0) : False := by
  have hzeta := cubicFirstIntegralFourPolynomial68_forces_zeta_of_fiveRadiusWall_above
    gamma epsilon zeta i4 A B c 0 e n g h hn hwall (by omega)
      hA ha hB hc (by simp) he (by simpa only [add_zero] using hi4)
  have hi40 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B)) e = C i4 := by
    simpa only [hzeta] using hi4
  have hb := fiveRadiusStrictTerminalI4_forces_B_top_zero68
    gamma epsilon i4 A B c e n g h hn hwall hstrict hh hB he hi40
  have hindex : 0 < 3 * n - g := by omega
  have hBlt := natDegree_lt_of_le_of_coeff_eq_zero68
    B (3 * n - g) hindex hB hb
  have hcne : c.coeff (4 * n - g) ≠ 0 :=
    hsupport.resolve_left (not_ne_iff.mpr hb)
  have htail := fiveRadiusStrictTerminalRowOneTail68_degree_lt
    gamma epsilon A B c e n g h hn hwall hstrict hh hA hBlt hc he
  have hcore := fiveRadiusZeroResidualRowOneCore68_coeff
    c n g hn hwall hc
  have hrow0 : fiveRadiusReducedRowOnePolynomial68
      gamma epsilon 0 A B c 0 e = 0 := by
    simpa only [hzeta] using hrow
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrow0
  rw [fiveRadiusReducedRowOnePolynomial68_strictTerminalSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt htail, add_zero, hcore, coeff_zero] at hcoeff
  have hcast : (((4 * n - g : ℕ) : k)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hcast)
    (pow_ne_zero 3 hcne)) hcoeff

#print axioms fiveRadiusStrictTerminalI4_forces_B_top_zero68
#print axioms fiveRadiusStrictTerminalRowOneTail68_degree_lt
#print axioms fiveRadius_strictTerminal_impossible68

end LaterDeepFiveRadiusTerminalLeafAlgebra68

end Max11DegreeRoutes
