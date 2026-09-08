import LowScale68SecondaryLaterDeepFiveRadiusScalarFaces
import LowScale68SecondaryResidualRowOneFaces
import LowScale68SecondaryResidualRowOneSystem

/-! # Exact residual walls on `2g = 5n`

The reduced row-two selector leaves two walls below `h=5n`.  This file
rewrites the literal second one-form through the exact cubic invariant and
extracts the next coefficient on those two walls.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusExactWalls68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The second one-form after using the derivative of the exact cubic
invariant.  Unlike the raw residual row, this has no hidden `I3` term. -/
def fiveRadiusReducedRowOnePolynomial68
    (gamma epsilon zeta : k) (A B c d e : k[X]) : k[X] :=
  (-4 / 27 : k) •
      ((3 : k) • derivative (A * d ^ 2) +
        (-2 : k) • derivative (A * B ^ 2 * c) +
        (6 : k) • (c ^ 2 * derivative c) +
        (3 : k) • derivative (B * c * d) +
        (6 : k) • (derivative B * c * d) +
        (-3 : k) • (B ^ 2 * derivative e) +
        (-18 : k) • (e * derivative e)) +
    gamma •
      ((2 / 3 : k) •
          (B * derivative d - d * derivative B -
            (2 : k) • (c * derivative c)) +
        (2 / 9 : k) • (derivative A * B ^ 2) +
        (4 / 9 : k) • (A * B * derivative B)) +
    (2 * epsilon : k) • derivative e +
    zeta • ((1 / 3 : k) • (derivative A * B) + derivative d)

set_option maxHeartbeats 12000000 in
theorem polynomialFiveRadiusReducedRowOne68
    (alpha gamma epsilon zeta eta i3 : k) (A B c d e : k[X])
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68
          0 alpha 0 gamma 0 epsilon zeta eta A B c
            ((1 / 3 : k) • (A * B) + d) e =
      fiveRadiusReducedRowOnePolynomial68 gamma epsilon zeta A B c d e := by
  have hI3 := hi3
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c
        ((1 / 3 : k) • (A * B) + d) e =
          secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    secondaryLoadInvariantThreePolynomial68_residualCoordinates_of_l_beta_delta]
      at hI3
  have hder := congrArg derivative hI3
  rw [residualRowOne_eq_inner68]
  simp only [residualRowOneInner68, fiveRadiusReducedRowOnePolynomial68,
    cubicLoadRowOnePolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    zero_mul, zero_smul, add_zero, zero_add, sub_zero,
    derivative_add, derivative_sub, derivative_mul, derivative_smul,
    derivative_pow, derivative_C, one_mul, smul_zero, zero_mul] at hder ⊢
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hdermap := congrArg (algebraMap k[X] (RatFunc k)) hder
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat,
    map_natCast, map_one] at hdermap ⊢
  linear_combination (1 / 3 : RatFunc k) *
    (algebraMap k[X] (RatFunc k) A) * hdermap

theorem fiveRadiusReducedRowOnePolynomial68_eq_zero
    (alpha gamma epsilon zeta eta i3 : k) (A B c d e : k[X])
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68
          0 alpha 0 gamma 0 epsilon zeta eta A B c
            ((1 / 3 : k) • (A * B) + d) e = 0) :
    fiveRadiusReducedRowOnePolynomial68 gamma epsilon zeta A B c d e = 0 := by
  rw [polynomialFiveRadiusReducedRowOne68 alpha gamma epsilon zeta eta i3
    A B c d e hi3] at hrow
  exact hrow

/-! ## The `2h=7n` wall -/

def fiveRadiusSevenWallRowOneCore68 (A d e : k[X]) : k[X] :=
  (-4 / 27 : k) •
    ((3 : k) • derivative (A * d ^ 2) +
      (-18 : k) • (e * derivative e))

def fiveRadiusSevenWallRowOneTail68
    (gamma epsilon zeta : k) (A B c d e : k[X]) : k[X] :=
  (-4 / 27 : k) •
      ((-2 : k) • derivative (A * B ^ 2 * c) +
        (6 : k) • (c ^ 2 * derivative c) +
        (3 : k) • derivative (B * c * d) +
        (6 : k) • (derivative B * c * d) +
        (-3 : k) • (B ^ 2 * derivative e)) +
    gamma •
      ((2 / 3 : k) •
          (B * derivative d - d * derivative B -
            (2 : k) • (c * derivative c)) +
        (2 / 9 : k) • (derivative A * B ^ 2) +
        (4 / 9 : k) • (A * B * derivative B)) +
    (2 * epsilon : k) • derivative e +
    zeta • ((1 / 3 : k) • (derivative A * B) + derivative d)

theorem fiveRadiusReducedRowOnePolynomial68_sevenSplit
    (gamma epsilon zeta : k) (A B c d e : k[X]) :
    fiveRadiusReducedRowOnePolynomial68 gamma epsilon zeta A B c d e =
      fiveRadiusSevenWallRowOneCore68 A d e +
        fiveRadiusSevenWallRowOneTail68 gamma epsilon zeta A B c d e := by
  simp only [fiveRadiusReducedRowOnePolynomial68,
    fiveRadiusSevenWallRowOneCore68, fiveRadiusSevenWallRowOneTail68]
  module

set_option maxHeartbeats 6000000 in
theorem fiveRadiusSevenWallRowOneTail68_degree_lt
    (gamma epsilon zeta : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hseven : 2 * h = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusSevenWallRowOneTail68 gamma epsilon zeta A B c d e).natDegree <
      5 * n - 1 := by
  have hAB2c : (derivative (A * B ^ 2 * c)).natDegree < 5 * n - 1 := by
    have hp : (A * B ^ 2 * c).natDegree ≤ 12 * n - 3 * g := by
      compute_degree
      omega
    have hd' := natDegree_derivative_le (A * B ^ 2 * c)
    have hle : (derivative (A * B ^ 2 * c)).natDegree ≤
        12 * n - 3 * g - 1 :=
      hd'.trans (Nat.sub_le_sub_right hp 1)
    omega
  have hc3 : (c ^ 2 * derivative c).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hBcd : (derivative (B * c * d)).natDegree < 5 * n - 1 := by
    have hp : (B * c * d).natDegree ≤ 12 * n - 2 * g - h := by
      compute_degree
      omega
    have hd' := natDegree_derivative_le (B * c * d)
    have hle : (derivative (B * c * d)).natDegree ≤
        12 * n - 2 * g - h - 1 :=
      hd'.trans (Nat.sub_le_sub_right hp 1)
    omega
  have hBp : (derivative B * c * d).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hBe : (B ^ 2 * derivative e).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hBd : (B * derivative d).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hdB : (d * derivative B).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hcc : (c * derivative c).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hApB2 : (derivative A * B ^ 2).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hABBp : (A * B * derivative B).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hep : (derivative e).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hApB : (derivative A * B).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hdp : (derivative d).natDegree < 5 * n - 1 := by
    compute_degree
    omega
  have hs1 := deepGap_natDegree_smul_lt68 (-2 : k) hAB2c
  have hs2 := deepGap_natDegree_smul_lt68 (6 : k) hc3
  have hs3 := deepGap_natDegree_smul_lt68 (3 : k) hBcd
  have hs4 := deepGap_natDegree_smul_lt68 (6 : k) hBp
  have hs5 := deepGap_natDegree_smul_lt68 (-3 : k) hBe
  have hmain := deepGap_natDegree_smul_lt68 (-4 / 27 : k)
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt hs1 hs2) hs3) hs4) hs5)
  have hccs := deepGap_natDegree_smul_lt68 (2 : k) hcc
  have hginner := deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_smul_lt68 (2 / 3 : k)
        (deepGap_natDegree_sub_lt
          (deepGap_natDegree_sub_lt hBd hdB) hccs))
      (deepGap_natDegree_smul_lt68 (2 / 9 : k) hApB2))
    (deepGap_natDegree_smul_lt68 (4 / 9 : k) hABBp)
  have hgpart := deepGap_natDegree_smul_lt68 gamma hginner
  have hepart := deepGap_natDegree_smul_lt68 (2 * epsilon : k) hep
  have hzinner := deepGap_natDegree_add_lt
    (deepGap_natDegree_smul_lt68 (1 / 3 : k) hApB) hdp
  have hzpart := deepGap_natDegree_smul_lt68 zeta hzinner
  simp only [fiveRadiusSevenWallRowOneTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt hmain hgpart) hepart) hzpart

set_option maxHeartbeats 6000000 in
theorem fiveRadiusSevenWallRowOneCore68_coeff
    (A d e : k[X]) (n h : ℕ) (hn : 0 < n) (hseven : 2 * h = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusSevenWallRowOneCore68 A d e).coeff (5 * n - 1) =
      (-4 / 27 : k) *
        ((3 : k) * A.coeff (2 * n) * d.coeff (5 * n - h) ^ 2 *
            ((5 * n : ℕ) : k) -
          (18 : k) * e.coeff (6 * n - h) ^ 2 *
            ((6 * n - h : ℕ) : k)) := by
  have hd2deg : (d ^ 2).natDegree ≤ 2 * (5 * n - h) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hd
  have hd2 : (d ^ 2).coeff (2 * (5 * n - h)) =
      d.coeff (5 * n - h) ^ 2 :=
    coeff_pow_at_bound68 d (5 * n - h) 2 hd
  have hAd2 := coeff_mul_at_bounds68 A (d ^ 2)
    (2 * n) (2 * (5 * n - h)) hA hd2deg
  have hiAd2 : 2 * n + 2 * (5 * n - h) = 5 * n := by omega
  rw [hiAd2, hd2] at hAd2
  have hAd2' := coeff_derivative_at_bound68 (A * d ^ 2) (5 * n) (by omega)
  rw [hAd2] at hAd2'
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = 5 * n - 1 := by omega
  rw [hiee] at hee
  simp only [fiveRadiusSevenWallRowOneCore68, coeff_smul, coeff_add,
    smul_eq_mul, hAd2', hee]
  ring

theorem fiveRadiusSevenWallScalar_ne_zero68
    (a b c d e : k) (hc : c ≠ 0) (hd : d ≠ 0)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0) :
    a * d ^ 2 - (3 : k) * e ^ 2 ≠ 0 := by
  intro hz
  have hprod : c ^ 2 * d ^ 2 = 0 := by
    have hab : a * b ^ 2 = -(3 : k) * c ^ 2 := by
      linear_combination hdisc
    have hbe : b * e = -c * d := by
      linear_combination hinc
    have habd : a * b ^ 2 * d ^ 2 = -(3 : k) * c ^ 2 * d ^ 2 := by
      calc
        a * b ^ 2 * d ^ 2 = (a * b ^ 2) * d ^ 2 := by ring
        _ = (-(3 : k) * c ^ 2) * d ^ 2 := by rw [hab]
        _ = -(3 : k) * c ^ 2 * d ^ 2 := by ring
    have hbe2 : b ^ 2 * e ^ 2 = c ^ 2 * d ^ 2 := by
      calc
        b ^ 2 * e ^ 2 = (b * e) ^ 2 := by ring
        _ = (-c * d) ^ 2 := by rw [hbe]
        _ = c ^ 2 * d ^ 2 := by ring
    have hzero : (-6 : k) * c ^ 2 * d ^ 2 = 0 := by
      calc
        (-6 : k) * c ^ 2 * d ^ 2
            = b ^ 2 * (a * d ^ 2 - (3 : k) * e ^ 2) := by
                linear_combination -habd + (3 : k) * hbe2
        _ = 0 := by rw [hz, mul_zero]
    have hzero' : (-6 : k) * (c ^ 2 * d ^ 2) = 0 := by
      simpa only [mul_assoc] using hzero
    exact (mul_eq_zero.mp hzero').resolve_left (by norm_num)
  have hd2zero := (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hc)
  exact (pow_ne_zero 2 hd) hd2zero

set_option maxHeartbeats 8000000 in
theorem fiveRadiusReducedRowOnePolynomial68_coeff_seven_ne_zero
    (gamma epsilon zeta : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hseven : 2 * h = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hddeg : d.natDegree ≤ 5 * n - h)
    (hedeg : e.natDegree ≤ 6 * n - h)
    (hc : c.coeff (4 * n - g) ≠ 0)
    (hd : d.coeff (5 * n - h) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0) :
    (fiveRadiusReducedRowOnePolynomial68 gamma epsilon zeta A B c d e).coeff
      (5 * n - 1) ≠ 0 := by
  have htail := fiveRadiusSevenWallRowOneTail68_degree_lt
    gamma epsilon zeta A B c d e n g h hn hwall hseven
    hA hB hcdeg hddeg hedeg
  have hcore := fiveRadiusSevenWallRowOneCore68_coeff
    A d e n h hn hseven hA hddeg hedeg
  rw [fiveRadiusReducedRowOnePolynomial68_sevenSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt htail, add_zero, hcore]
  have hscalar := fiveRadiusSevenWallScalar_ne_zero68
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) hc hd hdisc hinc
  have hcast : (((6 * n - h : ℕ) : k)) = (5 / 2 : k) * (n : k) := by
    have hsevenK : (2 : k) * (h : k) = (7 : k) * (n : k) := by
      exact_mod_cast hseven
    have heq : (2 : k) * ((6 * n - h : ℕ) : k) = (5 : k) * (n : k) := by
      rw [Nat.cast_sub (by omega : h ≤ 6 * n)]
      push_cast
      linear_combination -hsevenK
    linear_combination (1 / 2 : k) * heq
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [hcast]
  intro hz
  push_cast at hz
  apply hscalar
  have hfactor : (-20 / 9 : k) * (n : k) ≠ 0 :=
    mul_ne_zero (by norm_num) hncast
  have hzero : (-20 / 9 : k) * (n : k) *
      (A.coeff (2 * n) * d.coeff (5 * n - h) ^ 2 -
        (3 : k) * e.coeff (6 * n - h) ^ 2) = 0 := by
    linear_combination hz
  exact (mul_eq_zero.mp hzero).resolve_left hfactor

/-! ## The `2h=3g` wall -/

def fiveRadiusBalancedRowOneCore68 (A B c d e : k[X]) : k[X] :=
  (-4 / 27 : k) •
    ((3 : k) • derivative (A * d ^ 2) +
      (-2 : k) • derivative (A * B ^ 2 * c) +
      (6 : k) • (c ^ 2 * derivative c) +
      (-18 : k) • (e * derivative e))

def fiveRadiusBalancedRowOneTail68
    (gamma epsilon : k) (A B c d e : k[X]) : k[X] :=
  (-4 / 27 : k) •
      ((3 : k) • derivative (B * c * d) +
        (6 : k) • (derivative B * c * d) +
        (-3 : k) • (B ^ 2 * derivative e)) +
    gamma •
      ((2 / 3 : k) •
          (B * derivative d - d * derivative B -
            (2 : k) • (c * derivative c)) +
        (2 / 9 : k) • (derivative A * B ^ 2) +
        (4 / 9 : k) • (A * B * derivative B)) +
    (2 * epsilon : k) • derivative e

theorem fiveRadiusReducedRowOnePolynomial68_balancedSplit
    (gamma epsilon : k) (A B c d e : k[X]) :
    fiveRadiusReducedRowOnePolynomial68 gamma epsilon 0 A B c d e =
      fiveRadiusBalancedRowOneCore68 A B c d e +
        fiveRadiusBalancedRowOneTail68 gamma epsilon A B c d e := by
  simp only [fiveRadiusReducedRowOnePolynomial68,
    fiveRadiusBalancedRowOneCore68, fiveRadiusBalancedRowOneTail68,
    zero_smul, add_zero]
  module

set_option maxHeartbeats 6000000 in
theorem fiveRadiusBalancedRowOneTail68_degree_lt
    (gamma epsilon : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hgh : g < h)
    (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusBalancedRowOneTail68 gamma epsilon A B c d e).natDegree <
      12 * n - 3 * g - 1 := by
  let idx := 12 * n - 3 * g - 1
  have hBcd : (derivative (B * c * d)).natDegree < idx := by
    have hp : (B * c * d).natDegree ≤ 12 * n - 2 * g - h := by
      compute_degree
      omega
    have hd' := natDegree_derivative_le (B * c * d)
    have hle : (derivative (B * c * d)).natDegree ≤
        12 * n - 2 * g - h - 1 :=
      hd'.trans (Nat.sub_le_sub_right hp 1)
    dsimp [idx]
    omega
  have hBp : (derivative B * c * d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hBe : (B ^ 2 * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hBd : (B * derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hdB : (d * derivative B).natDegree < idx := by
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
  have hs1 := deepGap_natDegree_smul_lt68 (3 : k) hBcd
  have hs2 := deepGap_natDegree_smul_lt68 (6 : k) hBp
  have hs3 := deepGap_natDegree_smul_lt68 (-3 : k) hBe
  have hmain := deepGap_natDegree_smul_lt68 (-4 / 27 : k)
    (deepGap_natDegree_add_lt (deepGap_natDegree_add_lt hs1 hs2) hs3)
  have hccs := deepGap_natDegree_smul_lt68 (2 : k) hcc
  have hginner := deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_smul_lt68 (2 / 3 : k)
        (deepGap_natDegree_sub_lt
          (deepGap_natDegree_sub_lt hBd hdB) hccs))
      (deepGap_natDegree_smul_lt68 (2 / 9 : k) hApB2))
    (deepGap_natDegree_smul_lt68 (4 / 9 : k) hABBp)
  have hgpart := deepGap_natDegree_smul_lt68 gamma hginner
  have hepart := deepGap_natDegree_smul_lt68 (2 * epsilon : k) hep
  simp only [fiveRadiusBalancedRowOneTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt hmain hgpart) hepart

set_option maxHeartbeats 10000000 in
theorem fiveRadiusBalancedRowOneCore68_coeff
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusBalancedRowOneCore68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-4 / 27 : k) *
        (A.coeff (2 * n) *
            ((3 : k) * d.coeff (5 * n - h) ^ 2 -
              (2 : k) * B.coeff (3 * n - g) ^ 2 *
                c.coeff (4 * n - g)) *
            ((12 * n - 3 * g : ℕ) : k) +
          (6 : k) * ((4 * n - g : ℕ) : k) *
            c.coeff (4 * n - g) ^ 3 -
          (18 : k) * ((6 * n - h : ℕ) : k) *
            e.coeff (6 * n - h) ^ 2) := by
  let idx := 12 * n - 3 * g - 1
  have hd2deg : (d ^ 2).natDegree ≤ 2 * (5 * n - h) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hd
  have hd2 : (d ^ 2).coeff (2 * (5 * n - h)) =
      d.coeff (5 * n - h) ^ 2 :=
    coeff_pow_at_bound68 d (5 * n - h) 2 hd
  have hAd2 := coeff_mul_at_bounds68 A (d ^ 2)
    (2 * n) (2 * (5 * n - h)) hA hd2deg
  have hiAd2 : 2 * n + 2 * (5 * n - h) = 12 * n - 3 * g := by omega
  rw [hiAd2, hd2] at hAd2
  have hAd2' := coeff_derivative_at_bound68 (A * d ^ 2)
    (12 * n - 3 * g) (by omega)
  rw [hAd2] at hAd2'
  have hB2deg : (B ^ 2).natDegree ≤ 2 * (3 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hB
  have hB2 : (B ^ 2).coeff (2 * (3 * n - g)) =
      B.coeff (3 * n - g) ^ 2 :=
    coeff_pow_at_bound68 B (3 * n - g) 2 hB
  have hAB2c := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (2 * (3 * n - g)) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + 2 * (3 * n - g) + (4 * n - g) =
      12 * n - 3 * g := by omega
  rw [hiAB2c, hB2] at hAB2c
  have hAB2c' := coeff_derivative_at_bound68 (A * B ^ 2 * c)
    (12 * n - 3 * g) (by omega)
  rw [hAB2c] at hAB2c'
  have hc2deg : (c ^ 2).natDegree ≤ 2 * (4 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hc
  have hc2 : (c ^ 2).coeff (2 * (4 * n - g)) =
      c.coeff (4 * n - g) ^ 2 :=
    coeff_pow_at_bound68 c (4 * n - g) 2 hc
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (2 * (4 * n - g)) (4 * n - g) (by omega) hc2deg hc
  have hic3 : 2 * (4 * n - g) + (4 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hic3, hc2] at hc3
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiee] at hee
  simp only [fiveRadiusBalancedRowOneCore68, coeff_smul, coeff_add,
    smul_eq_mul, hAd2', hAB2c', hc3, hee, idx]
  ring

set_option maxHeartbeats 8000000 in
theorem fiveRadiusReducedRowOnePolynomial68_coeff_balanced_ne_zero
    (gamma epsilon : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hgh : g < h)
    (hbalanced : 2 * h = 3 * g)
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
    (fiveRadiusReducedRowOnePolynomial68 gamma epsilon 0 A B c d e).coeff
      (12 * n - 3 * g - 1) ≠ 0 := by
  have htail := fiveRadiusBalancedRowOneTail68_degree_lt
    gamma epsilon A B c d e n g h hn hwall hgh hbalanced
    hA hB hcdeg hddeg hedeg
  have hcore := fiveRadiusBalancedRowOneCore68_coeff
    A B c d e n g h hn hwall hbalanced hA hB hcdeg hddeg hedeg
  rw [fiveRadiusReducedRowOnePolynomial68_balancedSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt htail, add_zero, hcore]
  have hbalK : (2 : k) * (h : k) = (3 : k) * (g : k) := by
    exact_mod_cast hbalanced
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
  have hg4 : g ≤ 4 * n := by omega
  have h3g12 : 3 * g ≤ 12 * n := by omega
  have hh6 : h ≤ 6 * n := by omega
  rw [Nat.cast_sub h3g12, Nat.cast_sub hg4, Nat.cast_sub hh6] at hz
  push_cast at hz
  exact hz

set_option maxHeartbeats 12000000 in
/-- The two scalar-selector walls are both killed by the next one-form row. -/
theorem fiveRadiusResidualEndgamePacket_exactWalls_impossible68
    (gamma epsilon zeta i4 j4 i3 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hgh : g < h)
    (hh : h < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (P : FiveRadiusResidualEndgamePacket68
      gamma epsilon zeta i4 A B c d e n g h)
    (S : FiveRadiusScalarSelector68 zeta A B c d e n g h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C j4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : fiveRadiusReducedRowOnePolynomial68
      gamma epsilon zeta A B c d e = 0) : False := by
  have hh' : h < 2 * g := by omega
  rcases S.cases with hseven | hbalanced
  · have hbelow : 2 * h < 9 * n := by omega
    have face := polynomialSecondaryResidualBetweenFace68_of_fiveRadiusWall_below
      gamma epsilon zeta j4 i3 A B c d e n g h hn hwall hgh hh' hbelow
      hA hB hc hd he hi4 hi3
    have hne := fiveRadiusReducedRowOnePolynomial68_coeff_seven_ne_zero
      gamma epsilon zeta A B c d e n g h hn hwall hseven.1
      hA hB hc hd he P.c_ne P.d_ne P.discriminant face.four
    have hz := congrArg (fun p : k[X] => p.coeff (5 * n - 1)) hrow
    simp only [coeff_zero] at hz
    exact hne hz
  · have hbelow : 2 * h < 9 * n := by omega
    have face := polynomialSecondaryResidualBetweenFace68_of_fiveRadiusWall_below
      gamma epsilon zeta j4 i3 A B c d e n g h hn hwall hgh hh' hbelow
      hA hB hc hd he hi4 hi3
    have hrow0 : fiveRadiusReducedRowOnePolynomial68
        gamma epsilon 0 A B c d e = 0 := by
      simpa only [hbalanced.2.1] using hrow
    have hne := fiveRadiusReducedRowOnePolynomial68_coeff_balanced_ne_zero
      gamma epsilon A B c d e n g h hn hwall hgh hbalanced.1
      hA hB hc hd he P.c_ne P.discriminant face.four hbalanced.2.2
    have hz := congrArg
      (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrow0
    simp only [coeff_zero] at hz
    exact hne hz

set_option maxHeartbeats 24000000 in
/-- Source-facing exact-wall elimination.  On the five-radius wall the entire
`h<5n` packet is impossible; only the zero residual pair and the genuinely
later `h≥5n` packet remain. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusExactWalls68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g = 5 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    let h := secondaryResidualGap68 n d ee
    l = 0 ∧ beta = 0 ∧ delta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      ((d = 0 ∧ ee = 0) ∨
        (5 * n ≤ h ∧
          (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0))) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let h := secondaryResidualGap68 n d ee
  have old :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusScalarFaces68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hwall
  change l = 0 ∧ beta = 0 ∧ delta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧ _ at old
  refine ⟨old.1, old.2.1, old.2.2.1, old.2.2.2.1,
    old.2.2.2.2.1, old.2.2.2.2.2.1, old.2.2.2.2.2.2.1, ?_⟩
  rcases old.2.2.2.2.2.2.2 with hzero | hlt | hge
  · exact Or.inl hzero
  · rcases hlt with ⟨hlt, i4, P, S⟩
    have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
      ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
      ee.natDegree ≤ 6 * n - g ∧ _ at secondary
    have hn : 0 < n := by simpa only [n] using core.1
    have hA : Ae.natDegree ≤ 2 * n := by
      have hAe : Ae.natDegree = 2 * n := by
        simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
      omega
    have hwall' : 2 * g = 5 * n := by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall
    have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
      simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
    have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
        (1 / 3 : k) • (Ae * ce) + ee := by
      simpa only [ce, ee] using
        cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
    have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
      simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
    obtain ⟨i3, hi3⟩ := hsys.firstThree
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    have hi3c := hi3e
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, old.1, old.2.1, old.2.2.1] at hi3c
    obtain ⟨i4', hi4⟩ := hsys.firstFour
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4' := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4' A B C0 D E hi4
    have hi4c := hi4e
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, old.1, old.2.1, old.2.2.1] at hi4c
    have h1e : lowerRowOnePolynomial68
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) Ce De Ee = 0 := by
      dsimp only [Ae, Be, Ce, De, Ee]
      rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
        ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
        hsys.rowOne, map_zero, zero_mul]
    rw [hCrec, hDrec, hErec] at h1e
    have hrow := polynomialSecondaryResidualRowOne68
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h1e
    rw [old.1, old.2.1, old.2.2.1] at hrow
    have hreduced := fiveRadiusReducedRowOnePolynomial68_eq_zero
      alpha gamma epsilon zeta eta i3 Ae Be ce d ee hi3c hrow
    exact (fiveRadiusResidualEndgamePacket_exactWalls_impossible68
      gamma epsilon zeta i4 i4' i3 Ae Be ce d ee n g h hn hwall'
      old.2.2.2.1 hlt hA secondary.2.1 secondary.2.2.1
      old.2.2.2.2.1 old.2.2.2.2.2.1 P S hi4c hi3c hreduced).elim
  · exact Or.inr hge

#print axioms polynomialFiveRadiusReducedRowOne68
#print axioms fiveRadiusReducedRowOnePolynomial68_coeff_seven_ne_zero
#print axioms fiveRadiusReducedRowOnePolynomial68_coeff_balanced_ne_zero
#print axioms fiveRadiusResidualEndgamePacket_exactWalls_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusExactWalls68

end LaterDeepFiveRadiusExactWalls68

end Max11DegreeRoutes
