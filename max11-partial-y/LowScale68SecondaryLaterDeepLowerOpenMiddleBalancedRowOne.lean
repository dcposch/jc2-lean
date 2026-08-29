import LowScale68SecondaryLaterDeepLowerOpenMiddleOrdinaryBalanced
import LowScale68SecondaryResidualRowOneFaces

/-! # Row-one closure for the balanced strict-lower ordinary packet -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleBalancedRowOne68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Load bounds valid throughout the below-delta balanced chamber -/

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_le_sixRadius_of_laterDeepLowerOpen
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantThreePolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree ≤ 6 * n - g := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_degree_le_sixRadius_of_laterDeepLowerOpen
    (gamma delta epsilon zeta i3 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n - g := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hsplit := hi3
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    cubicFirstIntegralThreePolynomial68_residualCoordinates] at hsplit
  have heq : secondaryResidualInvariantThreePolynomial68 A B c d e =
      C i3 - secondaryLoadInvariantThreePolynomial68
        0 0 gamma delta epsilon zeta A B c D e :=
    eq_sub_of_add_eq hsplit
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_le_sixRadius_of_laterDeepLowerOpen
      gamma delta epsilon zeta A B c D e n g hn hopen hA hB hc hD he
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadVAlphaLowPolynomial68_degree_le_fourRadius_of_laterDeepLowerOpen
    (gamma delta epsilon eta : k) (A B c D : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hdeltaBelow : 3 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadVAlphaLowPolynomial68 0 gamma delta epsilon eta
      A B c D).natDegree ≤ 4 * n - g := by
  simp only [cubicLoadVAlphaLowPolynomial68, zero_mul, mul_zero, zero_smul,
    smul_zero, add_zero, zero_add]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_laterDeepLowerOpen_balanced
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hdeltaBelow : 3 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 3 * g - 1 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest 0 alpha 0 gamma delta
      epsilon zeta eta A B c D e rfl,
    cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest']
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let Vlow := cubicLoadVAlphaLowPolynomial68 0 gamma delta epsilon eta
    A B c D
  let C0c := (1 / 3 : k) • A ^ 2
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hgt : n < g := by omega
  have hgle : g ≤ 2 * n := by omega
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB hc
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
      alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow hgle
      hA hB hc hD he
  have hVlow : Vlow.natDegree ≤ 4 * n - g :=
    cubicLoadVAlphaLowPolynomial68_degree_le_fourRadius_of_laterDeepLowerOpen
      gamma delta epsilon eta A B c D n g hn hopen hdeltaBelow hA hB hc
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have heps : (C epsilon : k[X]).natDegree ≤ 0 := by rw [natDegree_C]
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 12 * n - 3 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 3 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (12 * n - 3 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative D).natDegree < 12 * n - 3 * g - 1 :=
    hbound (2 * n) (5 * n - g) (by omega) (by omega) Ur D hUr hD
  have h2 : ((alpha • c) * derivative Er).natDegree <
      12 * n - 3 * g - 1 :=
    hbound (4 * n - g) (6 * n - g) (by omega) (by omega)
      (alpha • c) Er ((natDegree_smul_le alpha c).trans hc) hEr
  have h3 : (((2 / 3 * gamma : k) • A) * derivative Er).natDegree <
      12 * n - 3 * g - 1 :=
    hbound (2 * n) (6 * n - g) (by omega) (by omega)
      ((2 / 3 * gamma : k) • A) Er ((natDegree_smul_le _ A).trans hA) hEr
  have h4 : ((C epsilon : k[X]) * derivative E).natDegree <
      12 * n - 3 * g - 1 :=
    hbound 0 (6 * n) (by omega) (by omega) _ E heps hE
  have h5 : (C0c * derivative Vlow).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n) (4 * n - g) (by omega) (by omega)
      C0c Vlow hC0c hVlow
  have h6 : (c * derivative Vr).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n - g) (6 * n - g) (by omega) (by omega) c Vr hc hVr
  have h7 : (D * derivative Ur).natDegree < 12 * n - 3 * g - 1 :=
    hbound (5 * n - g) (2 * n) (by omega) (by omega) D Ur hD hUr
  simp only [cubicLoadRowOneDeepGapRestPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  change (Ur * derivative D +
      (2 : k) • ((alpha • c) * derivative Er) +
      (2 : k) • (((2 / 3 * gamma : k) • A) * derivative Er) +
      (2 : k) • ((C epsilon : k[X]) * derivative E) -
      (2 : k) • (C0c * derivative Vlow) -
      (2 : k) • (c * derivative Vr) -
      D * derivative Ur).natDegree < _
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt h1
              (deepGap_natDegree_smul_lt68 (2 : k) h2))
              (deepGap_natDegree_smul_lt68 (2 : k) h3))
            (deepGap_natDegree_smul_lt68 (2 : k) h4))
          (deepGap_natDegree_smul_lt68 (2 : k) h5))
        (deepGap_natDegree_smul_lt68 (2 : k) h6)) h7

/-! ## The balanced residual coefficient -/

set_option maxHeartbeats 8000000 in
theorem residualRowOne_coeff_balancedChamber_of_laterDeepLowerOpen
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hbalanced : 2 * h = 3 * g) (hdeltaBelow : 3 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n - g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-4 / 27 : k) *
        (A.coeff (2 * n) *
            ((3 : k) * d.coeff (5 * n - h) ^ 2 -
              (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
            ((12 * n - 3 * g : ℕ) : k) +
          (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
          (18 : k) * ((6 * n - h : ℕ) : k) *
            e.coeff (6 * n - h) ^ 2) := by
  let I3 := secondaryResidualInvariantThreePolynomial68 A B c d e
  set idx := 12 * n - 3 * g - 1
  have hI3low : (A * derivative I3).natDegree < idx := by
    have ht := middleBeta_natDegree_mul_derivative_le68 A I3
      (2 * n) (6 * n - g) hA (by omega) hI3
    have hi : 2 * n + (6 * n - g) - 1 = 8 * n - g - 1 := by omega
    have hle : (A * derivative I3).natDegree ≤ 8 * n - g - 1 := by
      simpa only [hi] using ht
    exact hle.trans_lt (by dsimp [idx]; omega)
  have hd2deg : (d ^ 2).natDegree ≤ 10 * n - 3 * g := by
    compute_degree
    omega
  have hd2 : (d ^ 2).coeff (10 * n - 3 * g) =
      d.coeff (5 * n - h) ^ 2 := by
    have hp := coeff_pow_at_bound68 d (5 * n - h) 2 hd
    have hi : 2 * (5 * n - h) = 10 * n - 3 * g := by omega
    simpa only [hi] using hp
  have hAd2coeff := coeff_mul_at_bounds68 A (d ^ 2)
    (2 * n) (10 * n - 3 * g) hA hd2deg
  have hiAd2 : 2 * n + (10 * n - 3 * g) = 12 * n - 3 * g := by omega
  rw [hiAd2, hd2] at hAd2coeff
  have hAd2der := coeff_derivative_at_bound68 (A * d ^ 2)
    (12 * n - 3 * g) (by omega)
  rw [hAd2coeff] at hAd2der
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have hp := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using hp
  have hAB2ccoeff := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (6 * n - 2 * g) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + (6 * n - 2 * g) + (4 * n - g) =
      12 * n - 3 * g := by omega
  rw [hiAB2c, hB2] at hAB2ccoeff
  have hAB2cder := coeff_derivative_at_bound68 (A * B ^ 2 * c)
    (12 * n - 3 * g) (by omega)
  rw [hAB2ccoeff] at hAB2cder
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have hp := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using hp
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (8 * n - 2 * g) (4 * n - g) (by omega) hc2deg hc
  have hic3 : (8 * n - 2 * g) + (4 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hic3, hc2] at hc3
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = 12 * n - 2 * h - 1 := by
    omega
  rw [hiee] at hee
  have hidx_ee : 12 * n - 2 * h - 1 = idx := by
    dsimp [idx]
    omega
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
  have h0I3 : ((-9 / 4 : k) • (A * derivative I3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hI3low, mul_zero]
  have h0Bcd : ((3 : k) • derivative (B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBcd, mul_zero]
  have h0Bp : ((6 : k) • (derivative B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBp, mul_zero]
  have h0Be : ((-3 : k) • (B ^ 2 * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBe, mul_zero]
  have hAd2sm : ((3 : k) • derivative (A * d ^ 2)).coeff idx =
      (3 : k) * (A.coeff (2 * n) * d.coeff (5 * n - h) ^ 2 *
        ((12 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hAd2der]
  have hAB2csm : ((-2 : k) • derivative (A * B ^ 2 * c)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g) * ((12 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hAB2cder]
  have hc3sm : ((6 : k) • (c ^ 2 * derivative c)).coeff idx =
      (6 : k) * (c.coeff (4 * n - g) ^ 2 * c.coeff (4 * n - g) *
        ((4 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hc3]
  have heesm : ((-18 : k) • (e * derivative e)).coeff idx =
      (-18 : k) * (e.coeff (6 * n - h) ^ 2 * ((6 * n - h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, ← hidx_ee, hee]
    ring
  have hinner : (residualRowOneInner68 A B c d e).coeff idx =
      A.coeff (2 * n) *
          ((3 : k) * d.coeff (5 * n - h) ^ 2 -
            (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
          ((12 * n - 3 * g : ℕ) : k) +
        (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
        (18 : k) * ((6 * n - h : ℕ) : k) * e.coeff (6 * n - h) ^ 2 := by
    dsimp [residualRowOneInner68]
    simp only [coeff_add]
    rw [h0I3, hAd2sm, hAB2csm, hc3sm, h0Bcd, h0Bp, h0Be, heesm]
    ring
  rw [residualRowOne_eq_inner68, coeff_smul, smul_eq_mul, hinner]

theorem residualRowOne_balanced_coeff_ne_zero_of_laterDeepLowerOpen
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hbalanced : 2 * h = 3 * g) (hdeltaBelow : 3 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n - g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hface2 : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) ≠ 0 := by
  rw [residualRowOne_coeff_balancedChamber_of_laterDeepLowerOpen
    A B c d e n g h hn hg hgh hh hopen hbalanced hdeltaBelow
    hA hB hcdeg hd he hI3]
  have hcast12 : (((12 * n - 3 * g : ℕ) : k)) =
      (12 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 12 * n)]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) =
      (4 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - h : ℕ) : k)) =
      (6 : k) * (n : k) - (h : k) := by
    rw [Nat.cast_sub (by omega : h ≤ 6 * n)]
    push_cast
    rfl
  have hbal : (2 : k) * (h : k) = (3 : k) * (g : k) := by
    have ht := congrArg (fun m : ℕ => (m : k)) hbalanced
    push_cast at ht
    exact ht
  rw [hcast12, hcast4, hcast6]
  rw [residualRowOneScalar68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hbal hdisc hinc hface2]
  have h4ne : (4 : k) * (n : k) - (g : k) ≠ 0 := by
    rw [← hcast4]
    exact Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) h4ne)
    (pow_ne_zero 3 hc0)

/-! ## Source-facing elimination -/

set_option maxHeartbeats 16000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleBalancedBelowDelta_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hmiddle :
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
      h < 2 * g)
    (hbalanced :
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
      2 * h = 3 * g ∧ 3 * g < 5 * n) : False := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change h < 2 * g at hmiddle
  change 2 * h = 3 * g ∧ 3 * g < 5 * n at hbalanced
  have packet :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleBalancedBelowDelta68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hbalanced)
  change Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        (3 : k) * ce.coeff (4 * n - g) ^ 2 = 0 ∧
      (4 : k) * Be.coeff (3 * n - g) * ce.coeff (4 * n - g) ^ 2 -
        (9 : k) * d.coeff (5 * n - h) * ee.coeff (6 * n - h) = 0 at packet
  have ordinary :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleOrdinary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧ _ at ordinary
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
  have hg : 0 < g := secondary.1
  have hgh : g < h := ordinary.2.2.1
  have hh : h < 2 * g := hmiddle
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := secondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := secondary.2.2.1
  have hd : d.natDegree ≤ 5 * n - h := ordinary.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - h := ordinary.2.2.2.2.1
  have he' : ee.natDegree ≤ 6 * n - g := he.trans (by omega)
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hD : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, ordinary.1, ordinary.2.1] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, ordinary.1, ordinary.2.1] at hi3c
  have hsum : g + h < 5 * n := by omega
  have face :=
    polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_sum_lt_five
      gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g h hn hg hgh hh
      hopen hsum hA hB hc hd he hi4c hi3c
  have hI3 :=
    secondaryResidualInvariantThreePolynomial68_degree_le_sixRadius_of_laterDeepLowerOpen
      gamma delta epsilon zeta i3 Ae Be ce d ee n g hn hopen hA hB hc
      (hd.trans (by omega)) he' hi3c
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
    have hr := h1e
    rw [hCrec, hDrec, hErec] at hr
    exact polynomialSecondaryResidualRowOne68
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hr
  rw [ordinary.1, ordinary.2.1] at hrowOne
  have hload :=
    cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_laterDeepLowerOpen_balanced
      alpha gamma delta epsilon zeta eta Ae Be ce
      ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hg hopen hbalanced.2
      hA hB hc hD he'
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload, add_zero]
    at hcoeff
  exact residualRowOne_balanced_coeff_ne_zero_of_laterDeepLowerOpen
    Ae Be ce d ee n g h hn hg hgh hh hopen hbalanced.1 hbalanced.2
    hA hB hc hd he hI3 packet.2.1 packet.2.2.2.2.1 face.four
    packet.2.2.2.2.2 hcoeff

#print axioms secondaryLoadInvariantThreePolynomial68_degree_le_sixRadius_of_laterDeepLowerOpen
#print axioms secondaryResidualInvariantThreePolynomial68_degree_le_sixRadius_of_laterDeepLowerOpen
#print axioms cubicLoadVAlphaLowPolynomial68_degree_le_fourRadius_of_laterDeepLowerOpen
#print axioms cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_laterDeepLowerOpen_balanced
#print axioms residualRowOne_coeff_balancedChamber_of_laterDeepLowerOpen
#print axioms residualRowOne_balanced_coeff_ne_zero_of_laterDeepLowerOpen
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleBalancedBelowDelta_impossible68

end LaterDeepLowerOpenMiddleBalancedRowOne68

end Max11DegreeRoutes
