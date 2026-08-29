import LowScale68SecondaryLaterDeepLowerEndgame
import LowScale68SecondaryDeepGapMiddleBetaEndgame

/-! # Residual packet after the later-deep lower split `3n ≤ 2g ≤ 5n`

The tracked split
`maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerSplit68`
leaves three chambers: the mixed-`beta` wall `2g=3n`, the open first-face
interval `3n<2g<5n` with `e_top=0` and `a*b=3d`, and the mixed-`delta`
wall `2g=5n`.

This module records the next exact coefficients.  On the open interval the
first-face drops produce a residual gap `h>g`; I3 stays the ordinary
residual face, while I4 meets `(1/4) delta A²` at `4n` and therefore
splits on `g+h ? 5n`.  At `2g=3n` the row-two load `(5/18) n beta a⁴`
sits on `8n-1`.  At `2g=5n` the same row sees the `delta` load at `6n-1`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerResidual68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Residual drops on the open first-face chamber -/

theorem laterDeepLowerOpen_e_degree_lt
    (e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (he : e.natDegree ≤ 6 * n - g)
    (hetop : e.coeff (6 * n - g) = 0) :
    e.natDegree < 6 * n - g := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  exact natDegree_lt_of_le_of_coeff_eq_zero68 e (6 * n - g)
    (laterDeepLower_index_pos_six n g hn hwindow) he hetop

theorem laterDeepLowerOpen_residualDrops
    (A B D e : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hface : A.coeff (2 * n) * B.coeff (3 * n - g) =
      3 * D.coeff (5 * n - g))
    (hetop : e.coeff (6 * n - g) = 0) :
    (secondaryDDefectPolynomial68 A B D).natDegree < 5 * n - g ∧
      e.natDegree < 6 * n - g := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n :=
    ⟨le_of_lt hopen.1, le_of_lt hopen.2⟩
  exact ⟨secondaryDDefectPolynomial68_degree_lt_of_laterDeepLower A B D n g
    hn hwindow hA hB hD hface,
    laterDeepLowerOpen_e_degree_lt e n g hn hopen he hetop⟩

theorem laterDeepLowerOpen_residualGap_gt
    (n g : ℕ) (d e : k[X])
    (hd : d.natDegree < 5 * n - g)
    (he : e.natDegree < 6 * n - g) :
    g < secondaryResidualGap68 n d e :=
  secondaryResidualGap68_gt_of_strictDrops n g d e hd he

/-! ## Homogeneous residual I4/I3 on `3n < 2g < 5n` -/

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantFourPolynomial68_coeff_middle_of_laterDeepLowerOpen
    (B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - g - h := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - h) hB he
  have hBei : (3 * n - g) + (6 * n - h) = 9 * n - g - h := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (5 * n - h) hc hd
  have hcdi : (4 * n - g) + (5 * n - h) = 9 * n - g - h := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_middle_of_laterDeepLowerOpen
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - h) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - h) =
      10 * n - g - h := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - h) hc he
  have hcei : (4 * n - g) + (6 * n - h) = 10 * n - g - h := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantFourPolynomial68_coeff_double_of_laterDeepLowerOpen
    (B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 3 * g) =
      (8 / 27 : k) *
        (-(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g)) := by
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hB3i : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
  rw [hB3i] at hB3
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - 2 * g) hB he
  have hBei : (3 * n - g) + (6 * n - 2 * g) =
      9 * n - 3 * g := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - 2 * g) hc hd
  have hcdi : (4 * n - g) + (5 * n - 2 * g) =
      9 * n - 3 * g := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, hB3, hBe, hcd]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_double_of_laterDeepLowerOpen
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 3 * g) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - 2 * g) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - 2 * g) =
      10 * n - 3 * g := by omega
  rw [hABdi] at hABd
  have hBBc := coeff_mul_mul_at_bounds68 B B c (3 * n - g)
    (3 * n - g) (4 * n - g) hB hB hc
  have hBBci : (3 * n - g) + (3 * n - g) + (4 * n - g) =
      10 * n - 3 * g := by omega
  rw [hBBci] at hBBc
  have hB2c : (B ^ 2 * c).coeff (10 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) := by
    simpa only [pow_two] using hBBc
  have hce := coeff_mul_at_bounds68 c e (4 * n - g)
    (6 * n - 2 * g) hc he
  have hcei : (4 * n - g) + (6 * n - 2 * g) =
      10 * n - 3 * g := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 3 * g := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

/-! ## I3 load-free; I4 meets `delta A²` at `4n` -/

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_laterDeepLowerOpen
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - g - h := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_laterDeepLowerOpen
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantThreePolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_laterDeepLowerOpen_sum_lt_five
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n) (hsum : g + h < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        9 * n - g - h := by
  have heq :
      secondaryLoadInvariantFourPolynomial68 0 0 gamma delta epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      zeta • A + (2 * epsilon : k) • B +
        (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
        (4 * gamma : k) • ((1 / 3 : k) • (A * B) + d) -
        (4 / 3 * gamma : k) • (A * B) := by
    simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
      zero_smul, smul_zero, add_zero, sub_zero]
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_coeff_fourRadius_of_laterDeepLowerOpen
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n) (hsum : 5 * n ≤ g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (4 * n) =
      (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 := by
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hi : 2 * (2 * n) = 4 * n := by omega
  rw [hi] at hA2
  have hrest :
      (zeta • A + (2 * epsilon : k) • B + (3 * delta : k) • c +
        (4 * gamma : k) • ((1 / 3 : k) • (A * B) + d) -
        (4 / 3 * gamma : k) • (A * B)).natDegree < 4 * n := by
    compute_degree
    omega
  have heq :
      secondaryLoadInvariantFourPolynomial68 0 0 gamma delta epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      (zeta • A + (2 * epsilon : k) • B + (3 * delta : k) • c +
        (4 * gamma : k) • ((1 / 3 : k) • (A * B) + d) -
        (4 / 3 * gamma : k) • (A * B)) +
        (1 / 4 * delta : k) • A ^ 2 := by
    simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
      zero_smul, smul_zero, add_zero, sub_zero]
    module
  rw [heq, coeff_add, coeff_eq_zero_of_natDegree_lt hrest, zero_add,
    coeff_smul, hA2, smul_eq_mul]

/-! ## Residual faces: I3 ordinary; I4 splits on `g+h ? 5n` -/

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_laterDeepLowerOpen
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_laterDeepLowerOpen
      gamma delta epsilon zeta A B c D e n g h hn hg hh hopen
      hA hB hc hD he
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only [D] using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_middle_of_laterDeepLowerOpen
      A B c d e n g h hn hg hgh hh hopen hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_laterDeepLowerOpen_sum_lt_five
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n) (hsum : g + h < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_laterDeepLowerOpen_sum_lt_five
      gamma delta epsilon zeta A B c d e n g h hn hg hgh hh hopen hsum
      hA hB hc hd he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c
        ((1 / 3 : k) • (A * B) + d) e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      exact cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_middle_of_laterDeepLowerOpen
      B c d e n g h hn hg hgh hh hopen hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

theorem polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_sum_lt_five
    (gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n) (hsum : g + h < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_laterDeepLowerOpen_sum_lt_five
      gamma delta epsilon zeta A B c d e n g h hn hg hgh hh hopen hsum
      hA hB hc hd he] at hz
    have hindex : 9 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_laterDeepLowerOpen
      gamma delta epsilon zeta A B c d e n g h hn hg hgh hh hopen
      hA hB hc hd he] at hz
    have hindex : 10 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

theorem cubicFirstIntegralThreePolynomial68_residualMiddle_forces_face_of_laterDeepLowerOpen
    (gamma delta epsilon zeta i3 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    -(A.coeff (2 * n) * B.coeff (3 * n - g) * d.coeff (5 * n - h)) +
      3 * c.coeff (4 * n - g) * e.coeff (6 * n - h) = 0 := by
  have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_laterDeepLowerOpen
    gamma delta epsilon zeta A B c d e n g h hn hg hgh hh hopen
    hA hB hc hd he] at hz
  have hindex : 10 * n - g - h ≠ 0 := by omega
  simp only [coeff_C, if_neg hindex] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem cubicFirstIntegralFourPolynomial68_forces_delta_of_sum_gt_five
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n) (hsum : 5 * n < g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    delta = 0 := by
  have hhom :
      (cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c
        ((1 / 3 : k) • (A * B) + d) e).natDegree < 4 * n := by
    rw [cubicFirstIntegralFourPolynomial68_residualCoordinates]
    have hB3bound : 3 * (3 * n - g) < 4 * n := by omega
    have hB3 : (B ^ 3).natDegree < 4 * n := by compute_degree; omega
    have hBe : (B * e).natDegree < 4 * n := by compute_degree; omega
    have hcd : (c * d).natDegree < 4 * n := by compute_degree; omega
    simp only [secondaryResidualInvariantFourPolynomial68]
    refine deepGap_natDegree_add_lt ?_ (deepGap_natDegree_smul_lt68 (8 / 3 : k) hcd)
    exact deepGap_natDegree_add_lt
      (deepGap_natDegree_smul_lt68 (-8 / 27 : k) hB3)
      (deepGap_natDegree_smul_lt68 (8 / 3 : k) hBe)
  have hcoeff := congrArg (fun p : k[X] => p.coeff (4 * n)) hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt hhom, zero_add,
    secondaryLoadInvariantFourPolynomial68_coeff_fourRadius_of_laterDeepLowerOpen
      (gamma := gamma) (delta := delta) (epsilon := epsilon) (zeta := zeta)
      (A := A) (B := B) (c := c) (d := d) (e := e) (n := n) (g := g) (h := h)
      (hn := hn) (hopen := hopen) (hsum := le_of_lt hsum)
      (hA := hA) (hB := hB) (hc := hc) (hd := hd) (he := he)] at hcoeff
  have hi : 4 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi] at hcoeff
  have hpow : A.coeff (2 * n) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hs : (1 / 4 * delta : k) = 0 :=
    (mul_eq_zero.mp hcoeff).resolve_right hpow
  exact (mul_eq_zero.mp hs).resolve_left (by norm_num)

theorem cubicFirstIntegralFourPolynomial68_fiveSumWall_relation
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n) (hwall : g + h = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) +
      (1 / 4 * delta : k) * A.coeff (2 * n) ^ 2 = 0 := by
  have hi : 9 * n - g - h = 4 * n := by omega
  have hcoeff := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c
        ((1 / 3 : k) • (A * B) + d) e =
        secondaryResidualInvariantFourPolynomial68 B c d e from
      cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    secondaryResidualInvariantFourPolynomial68_coeff_middle_of_laterDeepLowerOpen
      B c d e n g h hn hg hgh hh hopen hB hc hd he, hi,
    secondaryLoadInvariantFourPolynomial68_coeff_fourRadius_of_laterDeepLowerOpen
      (gamma := gamma) (delta := delta) (epsilon := epsilon) (zeta := zeta)
      (A := A) (B := B) (c := c) (d := d) (e := e) (n := n) (g := g) (h := h)
      (hn := hn) (hopen := hopen) (hsum := le_of_eq hwall.symm)
      (hA := hA) (hB := hB) (hc := hc) (hd := hd) (he := he)] at hcoeff
  have hnz : 4 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hnz] at hcoeff
  simpa using hcoeff

/-! ## Mixed row-two load at the wall `2g = 3n` -/

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoPolynomial68_coeff_eightRadius_of_laterDeepLowerThreeWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (8 * n - 1) =
      (5 / 18 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 0 alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 0 alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
    A B c D e
  have hgt : n < g := by omega
  have hSldeg : Sl.natDegree ≤ 2 * n := by
    have h := cubicLoadSPolynomial68_degreeBound_of_loadL 0 alpha beta delta
      A B c n g rfl hA hB hc
    have hmax : max (2 * n) (3 * n - g) = 2 * n := by omega
    rwa [hmax] at h
  have hTldeg : Tl.natDegree ≤ 4 * n :=
    cubicLoadTPolynomial68_degreeBound_of_loadL 0 alpha beta gamma epsilon
      A B c D n g rfl hA hB hc hD
  have hUldeg : Ul.natDegree ≤ 4 * n := by
    have h := cubicLoadUPolynomial68_degreeBound_of_loadL 0 alpha beta gamma
      delta zeta A B c D e n g rfl hA hB hc hD he
    have hmax : max (4 * n) (5 * n - g) = 4 * n := by omega
    rwa [hmax] at h
  have hVldeg : Vl.natDegree ≤ 6 * n :=
    cubicLoadVPolynomial68_degreeBound_of_loadL 0 alpha beta gamma delta
      epsilon eta A B c D e n g rfl hA hB hc hD he
  have hC0deg : C0.natDegree ≤ 4 * n := by
    simp only [C0]; compute_degree; omega
  have hEdeg : E.natDegree ≤ 6 * n := by
    simp only [E]; compute_degree; omega
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hA2i : 2 * (2 * n) = 4 * n := by omega
  rw [hA2i] at hA2
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hA3i : 3 * (2 * n) = 6 * n := by omega
  rw [hA3i] at hA3
  have hclt : c.natDegree < 4 * n := hc.trans_lt (by omega)
  have hC0 : C0.coeff (4 * n) = (1 / 3 : k) * A.coeff (2 * n) ^ 2 := by
    simp only [C0, coeff_add, coeff_smul, smul_eq_mul, hA2,
      coeff_eq_zero_of_natDegree_lt hclt, add_zero]
  have hAclt : (A * c).natDegree < 6 * n := by compute_degree; omega
  have helt : e.natDegree < 6 * n := he.trans_lt (by omega)
  have hE : E.coeff (6 * n) = (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt, coeff_eq_zero_of_natDegree_lt helt,
      mul_zero, add_zero]
  have hSl : Sl.coeff (2 * n) =
      (5 / 6 * beta : k) * A.coeff (2 * n) := by
    simpa only [Sl] using
      cubicLoadSPolynomial68_coeff_twoRadius_of_firstDeep alpha beta delta
        A B c n g hn hgt hA hB
  have hUl : Ul.coeff (4 * n) =
      (5 / 24 * beta : k) * A.coeff (2 * n) ^ 2 := by
    simpa only [Ul] using
      cubicLoadUPolynomial68_coeff_fourRadius_of_firstDeep alpha beta gamma
        delta zeta A B c D e n g hn hg hgt hA hB hc hD
  have h1 : (Ul * derivative C0).coeff (8 * n - 1) =
      Ul.coeff (4 * n) * C0.coeff (4 * n) * ((4 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Ul C0 (4 * n) (4 * n)
      (by omega) hUldeg hC0deg
    have hi : 4 * n + 4 * n - 1 = 8 * n - 1 := by omega
    rwa [hi] at h
  have h2deg : ((2 : k) • (Tl * derivative D)).natDegree < 8 * n - 1 := by
    have h := middleBeta_natDegree_mul_derivative_le68 Tl D (4 * n)
      (5 * n - g) hTldeg (by omega) hD
    have hi : 4 * n + (5 * n - g) - 1 = 9 * n - g - 1 := by omega
    have hTD : (Tl * derivative D).natDegree ≤ 9 * n - g - 1 := by
      rwa [hi] at h
    exact (natDegree_smul_le (2 : k) (Tl * derivative D)).trans_lt
      (hTD.trans_lt (by omega))
  have h2 : ((2 : k) • (Tl * derivative D)).coeff (8 * n - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt h2deg
  have h3 : ((3 : k) • (Sl * derivative E)).coeff (8 * n - 1) =
      (3 : k) * Sl.coeff (2 * n) * E.coeff (6 * n) *
        ((6 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 Sl E (2 * n) (6 * n)
      (by omega) hSldeg hEdeg
    have hi : 2 * n + 6 * n - 1 = 8 * n - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have h4deg : ((3 : k) • (B * derivative Vl)).natDegree < 8 * n - 1 := by
    have h := middleBeta_natDegree_mul_derivative_le68 B Vl (3 * n - g)
      (6 * n) hB (by omega) hVldeg
    have hi : 3 * n - g + 6 * n - 1 = 9 * n - g - 1 := by omega
    have hBV : (B * derivative Vl).natDegree ≤ 9 * n - g - 1 := by
      rwa [hi] at h
    exact (natDegree_smul_le (3 : k) (B * derivative Vl)).trans_lt
      (hBV.trans_lt (by omega))
  have h4 : ((3 : k) • (B * derivative Vl)).coeff (8 * n - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt h4deg
  have h5 : ((2 : k) • (C0 * derivative Ul)).coeff (8 * n - 1) =
      (2 : k) * C0.coeff (4 * n) * Ul.coeff (4 * n) *
        ((4 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 C0 Ul (4 * n) (4 * n)
      (by omega) hC0deg hUldeg
    have hi : 4 * n + 4 * n - 1 = 8 * n - 1 := by omega
    rw [hi] at h
    rw [coeff_smul, smul_eq_mul, h]
    ring
  have h6deg : (D * derivative Tl).natDegree < 8 * n - 1 := by
    have h := middleBeta_natDegree_mul_derivative_le68 D Tl (5 * n - g)
      (4 * n) hD (by omega) hTldeg
    have hi : 5 * n - g + 4 * n - 1 = 9 * n - g - 1 := by omega
    have hDT : (D * derivative Tl).natDegree ≤ 9 * n - g - 1 := by
      rwa [hi] at h
    exact hDT.trans_lt (by omega)
  have h6 : (D * derivative Tl).coeff (8 * n - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt h6deg
  have hcast4 : ((4 * n : ℕ) : k) = 4 * (n : k) := by push_cast; rfl
  have hcast6 : ((6 * n : ℕ) : k) = 6 * (n : k) := by push_cast; rfl
  change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
      (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
      (2 : k) • (C0 * derivative Ul) - D * derivative Tl).coeff
        (8 * n - 1) = _
  simp only [coeff_add, coeff_sub, h1, h2, h3, h4, h5, h6, add_zero,
    sub_zero, zero_add]
  rw [hUl, hC0, hSl, hE, hcast4, hcast6]
  ring

set_option maxHeartbeats 3000000 in
theorem integratedLowerRowTwoPolynomial68_eightRadius_of_laterDeepLowerThreeWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowTwoPolynomial68
      (integratedSPolynomial68 0 alpha beta delta A B
        ((1 / 3 : k) • A ^ 2 + c) D)
      (integratedTPolynomial68 0 alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 0 alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      B ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (8 * n - 1) =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) +
      (5 / 18 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 := by
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hidx : 11 * n - 2 * g - 1 = 8 * n - 1 := by omega
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.s_eq, hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowTwoPolynomial68_split, coeff_add]
  rw [← hidx,
    cubicHomogeneousRowTwoPolynomial68_secondaryCoeff_of_laterDeepLower
      A B c D e n g hn hg hwindow hA hB hc hD he, hidx]
  rw [cubicLoadRowTwoPolynomial68_coeff_eightRadius_of_laterDeepLowerThreeWall
      (alpha := alpha) (beta := beta) (gamma := gamma) (delta := delta)
      (epsilon := epsilon) (zeta := zeta) (eta := eta)
      (A := A) (B := B) (c := c) (D := D) (e := e) (n := n) (g := g)
      (hn := hn) (hg := hg) (hwall := hwall)
      (hA := hA) (hB := hB) (hc := hc) (hD := hD) (he := he)]

/-! ## Canonical residual packets -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
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
      3 * n < 2 * g ∧ 2 * g < 5 * n) :
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
    l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
      g < secondaryResidualGap68 n d ee := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hdrops := laterDeepLowerOpen_residualDrops Ae Be De ee n g
    data.hn data.hg hopen data.hA data.hB data.hD data.he
    hclass.2.2.2 hclass.2.2.1
  have hgap := laterDeepLowerOpen_residualGap_gt n g d ee hdrops.1 hdrops.2
  exact ⟨hclass.1, hclass.2.1, hclass.2.2.1, hclass.2.2.2,
    hdrops.1, hdrops.2, hgap⟩

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWall_F2mixed68
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
      2 * g = 3 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
          (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
          (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
          (ee.coeff (6 * n - g)) +
        (5 / 18 : k) * (n : k) * beta * Ae.coeff (2 * n) ^ 4 = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 2 * g = 3 * n at hwall
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hI3 :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_I3face68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  have hl : l = 0 := hI3.1
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hl, hCrec, hErec] at h2e
  have hcoeff := congrArg (fun p : k[X] => p.coeff (8 * n - 1)) h2e
  rw [integratedLowerRowTwoPolynomial68_eightRadius_of_laterDeepLowerThreeWall
      (alpha := alpha) (beta := beta) (gamma := gamma) (delta := delta)
      (epsilon := epsilon) (zeta := zeta) (eta := eta)
      (A := Ae) (B := Be) (c := ce) (D := De) (e := ee) (n := n) (g := g)
      (hn := data.hn) (hg := data.hg) (hwall := hwall)
      (hA := data.hA) (hB := data.hB) (hc := data.hc)
      (hD := data.hD) (he := data.he)] at hcoeff
  simp only [coeff_zero] at hcoeff
  exact ⟨hl, hcoeff⟩

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerResidualSplit68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
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
    l = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      ((2 * g = 3 * n ∧
          (-8 / 9 : k) * firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (5 / 72 * beta : k) * Ae.coeff (2 * n) ^ 3 = 0 ∧
          (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (5 / 18 : k) * (n : k) * beta * Ae.coeff (2 * n) ^ 4 = 0) ∨
        (3 * n < 2 * g ∧ 2 * g < 5 * n ∧ beta = 0 ∧
          ee.coeff (6 * n - g) = 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
            3 * De.coeff (5 * n - g) ∧
          d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
          g < secondaryResidualGap68 n d ee) ∨
        (2 * g = 5 * n ∧ beta = 0 ∧
          (-8 / 9 : k) * firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0)) := by
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
  change 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n at hwindow
  have hsplit :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  obtain ⟨hl, hthree, hone, hcases⟩ := hsplit
  refine ⟨hl, hthree, hone, ?_⟩
  rcases hcases with hwall3 | hopen | hwall5
  · refine Or.inl ⟨hwall3.1, hwall3.2, ?_⟩
    have hF2 :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWall_F2mixed68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall3.1)
    exact hF2.2
  · refine Or.inr (Or.inl ?_)
    have hdrops :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
            And.intro hopen.1 hopen.2.1)
    exact ⟨hopen.1, hopen.2.1, hdrops.2.1, hdrops.2.2.1, hdrops.2.2.2.1,
      hdrops.2.2.2.2.1, hdrops.2.2.2.2.2.1, hdrops.2.2.2.2.2.2⟩
  · exact Or.inr (Or.inr hwall5)

end LaterDeepLowerResidual68

#print axioms laterDeepLowerOpen_residualDrops
#print axioms polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_sum_lt_five
#print axioms cubicFirstIntegralFourPolynomial68_forces_delta_of_sum_gt_five
#print axioms cubicFirstIntegralFourPolynomial68_fiveSumWall_relation
#print axioms cubicLoadRowTwoPolynomial68_coeff_eightRadius_of_laterDeepLowerThreeWall
#print axioms integratedLowerRowTwoPolynomial68_eightRadius_of_laterDeepLowerThreeWall
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusWall_F2mixed68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerResidualSplit68

end Max11DegreeRoutes

