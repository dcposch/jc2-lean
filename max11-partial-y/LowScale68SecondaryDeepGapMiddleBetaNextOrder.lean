import LowScale68SecondaryDeepGapMiddleBetaEndgame

/-! # Next-order first-deep middle after the I4 load at `6n`

The tracked middle-beta endgame leaves `h < 2g` and `3n ≤ 2h`.  This
module attacks the two remaining branches:

* Wall `2h = 3n`: residual row-one at `9n-1` is the `A d^2` / `e e'`
  face.  Its vanishing forces `a d^2 = 3 e^2`, which contradicts the
  residual discriminant and ordinary I4.
* Open `3n < 2h < 3g` after `beta = 0`: I4 load drops `Q` to degree
  `≤ 4n`, so the Q-feed sits at `≤ 6n-1`, strictly below the ordinary
  `d e` index.  The left residual face kills the chamber.

The remaining window is residual right/balanced `3g ≤ 2h < 4g`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section DeepGapMiddleBetaNextOrder68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## I3 load and residual degree on `n < g` -/

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_le_of_firstDeep
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantThreePolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree ≤ 7 * n - g := by
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_eq_I3load_of_l_eq_zero
    (beta gamma delta epsilon zeta i3 : k) (A B c d e : k[X])
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    secondaryResidualInvariantThreePolynomial68 A B c d e =
      C i3 -
        secondaryLoadInvariantThreePolynomial68
          0 beta gamma delta epsilon zeta A B c
            ((1 / 3 : k) • (A * B) + d) e := by
  have hsplit := hi3
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    cubicFirstIntegralThreePolynomial68_residualCoordinates] at hsplit
  exact eq_sub_of_add_eq hsplit

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_degree_le_of_firstDeep
    (beta gamma delta epsilon zeta i3 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      7 * n - g := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have heq := secondaryResidualInvariantThreePolynomial68_eq_I3load_of_l_eq_zero
    beta gamma delta epsilon zeta i3 A B c d e hi3
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_le_of_firstDeep
      beta gamma delta epsilon zeta A B c D e n g hn hgt hrel hA hB hc hD he
  rw [heq]
  compute_degree
  omega

/-! ## `Q` after `beta = 0` -/

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_le_fourRadius_of_beta
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree ≤ 4 * n := by
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_degree_le_fourRadius_of_beta
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hQeq := residualIncidenceQ68_eq_I4load_of_l_eq_zero
    0 gamma delta epsilon zeta i4 A B c d e hi4
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_le_fourRadius_of_beta
      gamma delta epsilon zeta A B c D e n g hn hgt hrel hA hB hc hD he
  rw [hQeq]
  compute_degree
  omega

/-! ## Wall `2h = 3n`: residual row-one at `9n-1` -/

theorem middleBetaWall_rowOne_disc_impossible68
    (a b c d e : k) (hd : d ≠ 0) (hc : c ≠ 0)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hinc : b * e + c * d = 0)
    (hrow1 : a * d ^ 2 - (3 : k) * e ^ 2 = 0) :
    False := by
  have hbe : b * e = -c * d := by linear_combination hinc
  have hprod : d ^ 2 * (a * b ^ 2 - (3 : k) * c ^ 2) = 0 := by
    calc
      d ^ 2 * (a * b ^ 2 - (3 : k) * c ^ 2)
          = (a * d ^ 2) * b ^ 2 - (3 : k) * c ^ 2 * d ^ 2 := by ring
      _ = ((3 : k) * e ^ 2) * b ^ 2 - (3 : k) * (c * d) ^ 2 := by
        have : a * d ^ 2 = (3 : k) * e ^ 2 := by linear_combination hrow1
        rw [this]
        ring
      _ = (3 : k) * (b * e) ^ 2 - (3 : k) * (c * d) ^ 2 := by ring
      _ = (3 : k) * (-c * d) ^ 2 - (3 : k) * (c * d) ^ 2 := by rw [hbe]
      _ = 0 := by ring
  have hdiff : a * b ^ 2 - (3 : k) * c ^ 2 = -((6 : k) * c ^ 2) := by
    linear_combination hdisc
  have : d ^ 2 * (-((6 : k) * c ^ 2)) = 0 := by
    rw [← hdiff]
    exact hprod
  have h6 : (6 : k) ≠ 0 := by norm_num
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
  exact (mul_ne_zero hd2 (mul_ne_zero h6 hc2)) (by simpa using this)

set_option maxHeartbeats 4000000 in
theorem residualRowOneInner_coeff_nineRadius_of_firstDeep_wall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hwall : 2 * h = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      7 * n - g) :
    (residualRowOneInner68 A B c d e).coeff (9 * n - 1) =
      (3 : k) * A.coeff (2 * n) * d.coeff (5 * n - h) ^ 2 *
          ((12 * n - 2 * h : ℕ) : k) +
        (-18 : k) * e.coeff (6 * n - h) ^ 2 *
          ((6 * n - h : ℕ) : k) := by
  let I3 := secondaryResidualInvariantThreePolynomial68 A B c d e
  set idx := 9 * n - 1
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have hidx9 : 12 * n - 2 * h - 1 = idx := by
    dsimp [idx]
    omega
  have hidx_cubic : 12 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    omega
  have hI3A : (A * derivative I3).natDegree < idx := by
    have h := middleBeta_natDegree_mul_derivative_le68 A I3 (2 * n) (7 * n - g)
      hA (by omega) hI3
    have hi : 2 * n + (7 * n - g) - 1 = 9 * n - g - 1 := by omega
    have hle : (A * derivative I3).natDegree ≤ 9 * n - g - 1 := by
      simpa only [hi] using h
    exact hle.trans_lt (by
      dsimp [idx]
      omega)
  have hd2deg : (d ^ 2).natDegree ≤ 10 * n - 2 * h := by
    compute_degree
    omega
  have hd2 := coeff_pow_at_bound68 d (5 * n - h) 2 hd
  have hid2 : 2 * (5 * n - h) = 10 * n - 2 * h := by omega
  rw [hid2] at hd2
  have hAd2coeff := coeff_mul_at_bounds68 A (d ^ 2) (2 * n) (10 * n - 2 * h)
    hA hd2deg
  have hiAd2 : 2 * n + (10 * n - 2 * h) = 12 * n - 2 * h := by omega
  rw [hiAd2, hd2] at hAd2coeff
  have hAd2der := coeff_derivative_at_bound68 (A * d ^ 2)
    (12 * n - 2 * h) (by omega)
  rw [hAd2coeff] at hAd2der
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hAB2c : (A * B ^ 2 * c).natDegree ≤ 12 * n - 3 * g := by
    have hAB2 := natDegree_mul_le_of_le hA hB2deg
    have hprod := natDegree_mul_le_of_le hAB2 hc
    have hsum : 2 * n + (6 * n - 2 * g) + (4 * n - g) = 12 * n - 3 * g := by
      omega
    rwa [hsum] at hprod
  have hAB2c' : (derivative (A * B ^ 2 * c)).natDegree < idx :=
    ((natDegree_derivative_le (A * B ^ 2 * c)).trans (by omega)).trans_lt
      hidx_cubic
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc3deg : (c ^ 2 * derivative c).natDegree ≤ 12 * n - 3 * g - 1 := by
    have hdc : (derivative c).natDegree ≤ 4 * n - g - 1 :=
      (natDegree_derivative_le c).trans (by omega)
    have hprod := natDegree_mul_le_of_le hc2deg hdc
    have hsum : (8 * n - 2 * g) + (4 * n - g - 1) = 12 * n - 3 * g - 1 := by
      omega
    rwa [hsum] at hprod
  have hc3' : (c ^ 2 * derivative c).natDegree < idx :=
    hc3deg.trans_lt hidx_cubic
  have hlowFace : 12 * n - 2 * g - h - 1 < idx := by
    dsimp [idx]
    omega
  have hlowBcd : (derivative (B * c * d)).natDegree < idx := by
    have hBc : (B * c).natDegree ≤ (3 * n - g) + (4 * n - g) :=
      natDegree_mul_le_of_le hB hc
    have hprod := natDegree_mul_le_of_le hBc hd
    have hsum : (3 * n - g) + (4 * n - g) + (5 * n - h) =
        12 * n - 2 * g - h := by omega
    rw [hsum] at hprod
    exact ((natDegree_derivative_le (B * c * d)).trans (by omega)).trans_lt
      hlowFace
  have hlowBp : (derivative B * c * d).natDegree < idx := by
    have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
      (natDegree_derivative_le B).trans (by omega)
    have hcd : (c * d).natDegree ≤ (4 * n - g) + (5 * n - h) :=
      natDegree_mul_le_of_le hc hd
    have hprod := natDegree_mul_le_of_le hdB hcd
    have hsum : (3 * n - g - 1) + ((4 * n - g) + (5 * n - h)) =
        12 * n - 2 * g - h - 1 := by omega
    have hle : (derivative B * (c * d)).natDegree ≤
        12 * n - 2 * g - h - 1 := by
      simpa only [hsum] using hprod
    have hassoc : derivative B * (c * d) = derivative B * c * d := by ring
    rw [hassoc] at hle
    exact hle.trans_lt hlowFace
  have hlowBe : (B ^ 2 * derivative e).natDegree < idx := by
    have hde : (derivative e).natDegree ≤ 6 * n - h - 1 :=
      (natDegree_derivative_le e).trans (by omega)
    have hprod := natDegree_mul_le_of_le hB2deg hde
    have hsum : (6 * n - 2 * g) + (6 * n - h - 1) =
        12 * n - 2 * g - h - 1 := by omega
    have hle : (B ^ 2 * derivative e).natDegree ≤
        12 * n - 2 * g - h - 1 := by
      simpa only [hsum] using hprod
    exact hle.trans_lt hlowFace
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = 12 * n - 2 * h - 1 := by omega
  rw [hiee] at hee
  have h0I3 : ((-9 / 4 : k) • (A * derivative I3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hI3A, mul_zero]
  have h0AB2c : ((-2 : k) • derivative (A * B ^ 2 * c)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAB2c', mul_zero]
  have h0c3 : ((6 : k) • (c ^ 2 * derivative c)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hc3', mul_zero]
  have h0Bcd : ((3 : k) • derivative (B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBcd, mul_zero]
  have h0Bp : ((6 : k) • (derivative B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBp, mul_zero]
  have h0Be : ((-3 : k) • (B ^ 2 * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBe, mul_zero]
  have hAd2sm : ((3 : k) • derivative (A * d ^ 2)).coeff idx =
      (3 : k) * (A.coeff (2 * n) * d.coeff (5 * n - h) ^ 2 *
        ((12 * n - 2 * h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    have hi : 12 * n - 2 * h - 1 = 9 * n - 1 := by omega
    rw [← hi, hAd2der]
  have heesm : ((-18 : k) • (e * derivative e)).coeff idx =
      (-18 : k) * (e.coeff (6 * n - h) ^ 2 * ((6 * n - h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    have hi : 12 * n - 2 * h - 1 = 9 * n - 1 := by omega
    rw [← hi, hee]
    ring
  dsimp [residualRowOneInner68]
  simp only [coeff_add]
  rw [h0I3, hAd2sm, h0AB2c, h0c3, h0Bcd, h0Bp, h0Be, heesm]
  simp only [add_zero, zero_add]
  ring

set_option maxHeartbeats 2000000 in
theorem residualRowOne_coeff_nineRadius_of_firstDeep_wall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hwall : 2 * h = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      7 * n - g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff (9 * n - 1) =
      (-8 / 9 : k) * ((6 * n - h : ℕ) : k) *
        (A.coeff (2 * n) * d.coeff (5 * n - h) ^ 2 -
          (3 : k) * e.coeff (6 * n - h) ^ 2) := by
  rw [residualRowOne_eq_inner68, coeff_smul, smul_eq_mul,
    residualRowOneInner_coeff_nineRadius_of_firstDeep_wall A B c d e n g h
      hn hg hgh hh hgt hrel hwall hA hB hc hd he hI3]
  have htw : ((12 * n - 2 * h : ℕ) : k) = (2 : k) * ((6 * n - h : ℕ) : k) := by
    have hN : 12 * n - 2 * h = 2 * (6 * n - h) := by omega
    exact_mod_cast hN
  rw [htw]
  ring

theorem residualRowOne_nineRadius_forces_ad2_of_firstDeep_wall
    (A B c d e load : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hwall : 2 * h = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      7 * n - g)
    (hload : load.natDegree < 9 * n - 1)
    (hsum : secondaryResidualRowOnePolynomial68 A B c d e + load = 0) :
    A.coeff (2 * n) * d.coeff (5 * n - h) ^ 2 -
      (3 : k) * e.coeff (6 * n - h) ^ 2 = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (9 * n - 1)) hsum
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload, add_zero,
    residualRowOne_coeff_nineRadius_of_firstDeep_wall A B c d e n g h
      hn hg hgh hh hgt hrel hwall hA hB hc hd he hI3] at hcoeff
  have hsc : (-8 / 9 : k) ≠ 0 := by norm_num
  have hN : ((6 * n - h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact (mul_eq_zero.mp hcoeff).resolve_left (mul_ne_zero hsc hN)

/-! ## Open `3n < 2h < 3g` after `beta = 0` -/

set_option maxHeartbeats 4000000 in
theorem residualRowTwo_coeff_leftChamber_of_firstDeep_highLeft
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hhigh : 3 * n < 2 * h) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) =
      (8 / 3 : k) * ((11 * n - 2 * h : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 2 * h - 1
  have hidxQ : 6 * n - 1 < idx := by
    dsimp [idx]
    omega
  have hidx_cubic : 11 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    omega
  have hAQ : (A * derivative Q).natDegree < idx := by
    have h := middleBeta_natDegree_mul_derivative_le68 A Q (2 * n) (4 * n)
      hA (by omega) hQ
    have hi : 2 * n + 4 * n - 1 = 6 * n - 1 := by omega
    have hle : (A * derivative Q).natDegree ≤ 6 * n - 1 := by
      simpa only [hi] using h
    exact hle.trans_lt hidxQ
  have hAQ' : (derivative A * Q).natDegree < idx := by
    have h := middleBeta_natDegree_derivative_mul_le68 A Q (2 * n) (4 * n)
      (by omega) hA hQ
    have hi : 2 * n + 4 * n - 1 = 6 * n - 1 := by omega
    have hle : (derivative A * Q).natDegree ≤ 6 * n - 1 := by
      simpa only [hi] using h
    exact hle.trans_lt hidxQ
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_firstDeep A B c n g
    hn hg hrel hA hB hc
  have hAB : (A * B ^ 2 * derivative B).natDegree < idx :=
    hcore.1.trans_lt hidx_cubic
  have hA3 : (derivative A * B ^ 3).natDegree < idx :=
    hcore.2.1.trans_lt hidx_cubic
  have hBc : (derivative (B * c ^ 2)).natDegree < idx :=
    hcore.2.2.trans_lt hidx_cubic
  have hBd := residualRowTwoInner_Bd_degree_le68_of_firstDeep B d n g h
    hg hgh hh hrel hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hdebound := natDegree_mul_le_of_le hd he
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hide] at hdebound
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0AB : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAB, mul_zero]
  have h0A3 : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hA3, mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0Bc : ((6 : k) • derivative (B * c ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBc, mul_zero]
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hde]
  have hinner : inner.coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0AB, h0A3, h0Bd, h0Bc, hde']
    ring
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  ring

theorem residualRowTwo_highLeft_ne_zero_of_firstDeep
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hhigh : 3 * n < 2 * h) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_leftChamber_of_firstDeep_highLeft A B c d e n g h
    hn hg hgh hh hgt hrel hhigh hleft hA hB hc hd he hQ]
  have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 2 * h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) hd0) he0

/-! ## Canonical next-order theorems -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleWall_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < g ∧ 2 * g < 3 * n)
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
      let d := secondaryDDefectPolynomial68 Ae Be De
      let h := secondaryResidualGap68 n d ee
      h < 2 * g ∧ 2 * h = 3 * n) :
    False := by
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
  change n < g ∧ 2 * g < 3 * n at hchamber
  change h < 2 * g ∧ 2 * h = 3 * n at hwall
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualSelect68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          And.intro (by omega : n < 2 * g) hchamber.2)
  have hl : l = 0 := hsel.1
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg0 : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hgh : g < h := hsel.2.2.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hd : d.natDegree ≤ 5 * n - h := hsel.2.2.2.2.2.1
  have hee : ee.natDegree ≤ 6 * n - h := hsel.2.2.2.2.2.2.1
  have he' : ee.natDegree ≤ 6 * n - g := (hsel.2.2.2.1).le
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hsumgh : g + h < 3 * n := by omega
  have hface : SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
      (d.coeff (5 * n - h)) (ee.coeff (6 * n - h)) :=
    ⟨hsel.2.2.2.2.2.2.2.four_middle_below hwall.1 hsumgh,
      hsel.2.2.2.2.2.2.2.three_middle hwall.1⟩
  have hnotboth : ¬ (d = 0 ∧ ee = 0) := by
    intro hz
    have hzgap : secondaryResidualGap68 n d ee = 6 * n + 1 := by
      simp [secondaryResidualGap68, polynomialGap68, hz.1, hz.2]
    have : h = 6 * n + 1 := by
      simpa only [h, d, ee, n] using hzgap
    omega
  have hattained :
      d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0 :=
    secondaryResidualGap68_boundary_attained n d ee
      (hd.trans_lt (by omega)) (hee.trans_lt (by omega)) hnotboth
  have hclass := secondaryResidualBetweenFace68_classify_of_support
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (ee.coeff (6 * n - h)) ha hsel.2.1 hattained hface
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, hl] at hi3c
  have hI3le :=
    secondaryResidualInvariantThreePolynomial68_degree_le_of_firstDeep
      beta gamma delta epsilon zeta i3 Ae Be ce d ee n g hn hchamber.1
      hchamber.2 hA hB hc (hd.trans (by omega)) he' hi3c
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hrowOne : secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
      cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    have h := h1e
    rw [hCrec, hDrec, hErec] at h
    exact polynomialSecondaryResidualRowOne68
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h
  rw [hl] at hrowOne
  have hD' : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g :=
    middleBeta_natDegree_translatedD_le68 Ae Be d n g h
      hn hgh hchamber.2 hA hB hd
  have hload :
      (cubicLoadRowOnePolynomial68 0 alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
          9 * n - 1 := by
    have hlt := cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_firstDeep
      0 alpha beta gamma delta epsilon zeta eta Ae Be ce
      ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hg0 rfl hchamber.2
      hA hB hc hD' he'
    exact hlt.trans (by omega)
  have hrow1 := residualRowOne_nineRadius_forces_ad2_of_firstDeep_wall
    Ae Be ce d ee
    (cubicLoadRowOnePolynomial68 0 alpha beta gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
    n g h hn hg0 hgh hwall.1 hchamber.1 hchamber.2 hwall.2
    hA hB hc hd hee hI3le hload hrowOne
  exact middleBetaWall_rowOne_disc_impossible68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (ee.coeff (6 * n - h))
    hclass.2.2.1 hclass.2.1 hclass.2.2.2.2 hface.four hrow1

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleHighLeft_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < g ∧ 2 * g < 3 * n)
    (hhigh :
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
      h < 2 * g ∧ 3 * n < 2 * h ∧ 2 * h < 3 * g) :
    False := by
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
  change n < g ∧ 2 * g < 3 * n at hchamber
  change h < 2 * g ∧ 3 * n < 2 * h ∧ 2 * h < 3 * g at hhigh
  have hbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleHigh_beta_eq_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
        And.intro hhigh.1 hhigh.2.1)
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualSelect68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          And.intro (by omega : n < 2 * g) hchamber.2)
  have hl : l = 0 := hsel.1
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg0 : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hgh : g < h := hsel.2.2.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hd : d.natDegree ≤ 5 * n - h := hsel.2.2.2.2.2.1
  have hee : ee.natDegree ≤ 6 * n - h := hsel.2.2.2.2.2.2.1
  have he' : ee.natDegree ≤ 6 * n - g := (hsel.2.2.2.1).le
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hinc : Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
      ce.coeff (4 * n - g) * d.coeff (5 * n - h) = 0 := by
    rcases lt_trichotomy (g + h) (3 * n) with hlt | heq | hgt'
    · exact hsel.2.2.2.2.2.2.2.four_middle_below hhigh.1 hlt
    · have hmix := hsel.2.2.2.2.2.2.2.four_middle_mixed hhigh.1 heq
      rw [hbeta] at hmix
      have h8 : (8 / 3 : k) ≠ 0 := by norm_num
      have : (8 / 3 : k) *
          (Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
            ce.coeff (4 * n - g) * d.coeff (5 * n - h)) = 0 := by
        simpa [mul_zero, add_zero] using hmix
      exact (mul_eq_zero.mp this).resolve_left h8
    · exact (hsel.2.2.2.2.2.2.2.four_middle_above hhigh.1 hgt').2
  have hface : SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
      (d.coeff (5 * n - h)) (ee.coeff (6 * n - h)) :=
    ⟨hinc, hsel.2.2.2.2.2.2.2.three_middle hhigh.1⟩
  have hnotboth : ¬ (d = 0 ∧ ee = 0) := by
    intro hz
    have hzgap : secondaryResidualGap68 n d ee = 6 * n + 1 := by
      simp [secondaryResidualGap68, polynomialGap68, hz.1, hz.2]
    have : h = 6 * n + 1 := by
      simpa only [h, d, ee, n] using hzgap
    omega
  have hattained :
      d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0 :=
    secondaryResidualGap68_boundary_attained n d ee
      (hd.trans_lt (by omega)) (hee.trans_lt (by omega)) hnotboth
  have hclass := secondaryResidualBetweenFace68_classify_of_support
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (ee.coeff (6 * n - h)) ha hsel.2.1 hattained hface
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl, hbeta] at hi4c
  have hQle := residualIncidenceQ68_degree_le_fourRadius_of_beta
    gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hchamber.1 hchamber.2
    hA hB hc (hd.trans (by omega)) he' hi4c
  have hrowTwoe : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
      ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
  have hrowTwo : secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    have h := hrowTwoe
    rw [hCrec, hDrec, hErec] at h
    exact polynomialSecondaryResidualRowTwo68
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h
  rw [hl, hbeta] at hrowTwo
  have hD' : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g :=
    middleBeta_natDegree_translatedD_le68 Ae Be d n g h
      hn hgh hchamber.2 hA hB hd
  have hload :
      (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
          11 * n - 2 * h - 1 := by
    have hlt := cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_firstDeep_beta
      alpha gamma delta epsilon zeta eta Ae Be ce
      ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hg0 hchamber.1 hchamber.2
      hA hB hc hD' he'
    exact hlt.trans (by omega)
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68
    Ae Be ce d ee
    (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
    (11 * n - 2 * h - 1) hload hrowTwo
  exact residualRowTwo_highLeft_ne_zero_of_firstDeep Ae Be ce d ee n g h
    hn hg0 hgh hhigh.1 hchamber.1 hchamber.2 hhigh.2.1 hhigh.2.2
    hA hB hc hd hee hQle hclass.2.2.1 hclass.2.2.2.1 hcoeff0

/-- Remaining first-deep middle after this file: `3g ≤ 2h < 4g` with
`beta = 0`.  The wall `2h = 3n` and the open left window `3n < 2h < 3g`
are impossible.  The next coefficient on the remaining chamber is the
residual row-two inner at the cubic / `d e` coincidence `11n-3g-1`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleNext_obstruction68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < g ∧ 2 * g < 3 * n) :
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
    h < 2 * g ∧ 3 * g ≤ 2 * h ∧ beta = 0 := by
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
  change n < g ∧ 2 * g < 3 * n at hchamber
  have hobs :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddle_obstruction68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
  have hh : h < 2 * g := hobs.1
  have hge : 3 * n ≤ 2 * h := hobs.2.1
  have hwall_closed : 2 * h ≠ 3 * n := by
    intro heq
    exact maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleWall_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
        And.intro hh heq)
  have hgt : 3 * n < 2 * h := lt_of_le_of_ne hge (Ne.symm hwall_closed)
  have hbeta : beta = 0 := hobs.2.2.1 hgt
  have hleft_closed : ¬ 2 * h < 3 * g := by
    intro hleft
    exact maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleHighLeft_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
        And.intro hh (And.intro hgt hleft))
  exact ⟨hh, not_lt.mp hleft_closed, hbeta⟩

end DeepGapMiddleBetaNextOrder68

end Max11DegreeRoutes
