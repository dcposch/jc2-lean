import Fable68LaterDeepStrictHighSevenSplitScratch

/-! # Endgame for the double strict-high chamber above the seven wall

On the double child `2g ≤ h` of the strict-open window `3n < 2g < 5n`,
the strict-high face `5n < 3g` forces `delta = 0` and — above the seven
wall `7n < 3g` — also `zeta = 0`
(`Fable68LaterDeepStrictHighSevenSplitScratch`).  This file transfers
the tracked middle-child `ZetaZeroEndgame` machinery to the double
child, keeping only the hypotheses that survive `2g ≤ h`:

* the middle-child trichotomy on `2h` versus `3g` collapses — the double
  child always sits on the right of it (`3g < 4g ≤ 2h`), so the `d*e`
  face, the `A*d^2` face and the `e*e'` face all fall strictly below the
  fixed cubic faces;
* the ordinary-chamber discriminant and the four nonvanishing facts are
  middle-child only and are **not** used; the row-two extraction is the
  raw cubic face `b*(a*b^2 - 9*c4^2)` of the seven split, now isolated
  by `zeta = 0` instead of by `3g < 7n`;
* residual row one contributes a second exact face at `12n - 3g - 1`,
  `c4*(a*b^2*(12n-3g) - 3*(4n-g)*c4^2) = 0` after the load correction
  drops (the invariant-three bound is easier here: `n < g` from the
  open window pins the load below `5n - g`).

The two faces are combined without discarding any zero branch: if
`b ≠ 0` and `c4 ≠ 0` the pair forces `g = 4n`, impossible inside
`2g < 5n`; the surviving branches give `b = 0` and `c4 = 0` outright.
Together with the residual drops (`a*b = 3*d5` and the vanishing
`e`-face) all four secondary defect faces die, contradicting the
attained secondary radius.  The above-seven chamber of the double
strict-high face is therefore impossible.  No claim is made on the
below-seven branch or on the seven wall itself, which remain open with
their exact packets. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleStrictHighAboveSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Row two: the cubic face isolated by `zeta = 0`

With `zeta = 0` the `4n - 1` face carries nothing, so the fixed cubic
face at `11n - 3g - 1` is the top face of the reduced row on the whole
double chamber — no position of `3g` against `7n` is needed.  The
extraction is the raw face of the seven split; the exact balance
`b*(a*b^2 - 9*c4^2) = 0` keeps both zero branches. -/

set_option maxHeartbeats 5000000 in
theorem fiveRadiusReducedRowTwo_doubleCubicFace_relation_of_zeta_zero68
    (gamma epsilon i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon 0 i4 A B c d e = 0) :
    B.coeff (3 * n - g) *
      (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
        (9 : k) * c.coeff (4 * n - g) ^ 2) = 0 := by
  have hfixed := fiveRadiusRowTwoFixedCore68_coeff_cubicFace_of_laterDeepLowerOpen
    A B c n g hn hg hopen hA hB hc
  have hde : ((8 / 3 : k) • derivative (d * e)).natDegree <
      11 * n - 3 * g - 1 := by
    have hp : (d * e).natDegree ≤
        (5 * n - h) + (6 * n - h) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (d * e)
    apply (natDegree_smul_le _ _).trans_lt
    omega
  have htail : (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d).natDegree <
      11 * n - 3 * g - 1 := by
    have hBd : (derivative (B ^ 2 * d)).natDegree < 11 * n - 3 * g - 1 := by
      have hp : (B ^ 2 * d).natDegree ≤
          (6 * n - 2 * g) + (5 * n - h) := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (B ^ 2 * d)
      omega
    have hAd : (derivative A).natDegree < 11 * n - 3 * g - 1 := by
      compute_degree
      omega
    have hBc : (derivative (B * c)).natDegree < 11 * n - 3 * g - 1 := by
      have hp : (B * c).natDegree ≤
          (3 * n - g) + (4 * n - g) := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (B * c)
      omega
    have hdd : (derivative d).natDegree < 11 * n - 3 * g - 1 := by
      compute_degree
      omega
    have h1 := deepGap_natDegree_smul_lt68 (-8 / 9 : k) hBd
    have h2 := deepGap_natDegree_smul_lt68 (1 / 6 * i4 : k) hAd
    have h3 := deepGap_natDegree_smul_lt68 (4 / 3 * gamma : k) hBc
    have h4 := deepGap_natDegree_smul_lt68 (2 * epsilon : k) hdd
    simp only [fiveRadiusRowTwoTail68]
    exact deepGap_natDegree_add_lt
      (deepGap_natDegree_sub_lt (deepGap_natDegree_sub_lt h1 h2) h3) h4
  have hzrow := congrArg
    (fun p : k[X] => p.coeff (11 * n - 3 * g - 1)) hrow
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit,
    coeff_add, coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hde,
    coeff_eq_zero_of_natDegree_lt htail,
    coeff_zero, hfixed] at hzrow
  simp only [zero_smul, coeff_zero, add_zero] at hzrow
  have hkey : ((8 / 81 : k) * ((11 * n - 3 * g : ℕ) : k)) *
      (B.coeff (3 * n - g) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
          (9 : k) * c.coeff (4 * n - g) ^ 2)) = 0 := by
    linear_combination hzrow
  exact (mul_eq_zero.mp hkey).resolve_left
    (mul_ne_zero (by norm_num)
      (Nat.cast_ne_zero.mpr (by omega : 11 * n - 3 * g ≠ 0)))

/-! ## The invariant-three bound on the double chamber

The balanced middle-child bound used `2h = 3g`; on the double child the
open window alone gives `n < g`, so every surviving load term of the
cubic invariant sits at or below `5n - g` — no wall position enters. -/

set_option maxHeartbeats 3000000 in
theorem secondaryResidualInvariantThreePolynomial68_degree_le_five_sub_g_of_double_zeta_zero
    (gamma epsilon i3 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - h)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon 0 A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      5 * n - g := by
  let D := (1 / 3 : k) • (A * B) + d
  have hsplit := hi3
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    cubicFirstIntegralThreePolynomial68_residualCoordinates] at hsplit
  have heq : secondaryResidualInvariantThreePolynomial68 A B c d e =
      C i3 - secondaryLoadInvariantThreePolynomial68
        0 0 gamma 0 epsilon 0 A B c D e :=
    eq_sub_of_add_eq hsplit
  have hload : (secondaryLoadInvariantThreePolynomial68
      0 0 gamma 0 epsilon 0 A B c D e).natDegree ≤ 5 * n - g := by
    simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
      zero_smul, smul_zero, add_zero, sub_zero]
    compute_degree
    omega
  rw [heq]
  compute_degree
  omega

/-! ## Residual row one at the cubic face `12n - 3g - 1`

On the double child `3g < 2h`, so the `A*d^2` and `e*e'` faces of the
balanced middle-child packet fall strictly below `12n - 3g - 1` and only
the `A*B^2*c` and `c^3` terms survive on the face.  The invariant-three
term is controlled by the `5n - g` bound. -/

set_option maxHeartbeats 8000000 in
theorem residualRowOne_coeff_doubleChamber68
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      5 * n - g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-4 / 27 : k) *
        ((6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
          (2 : k) * ((12 * n - 3 * g : ℕ) : k) * A.coeff (2 * n) *
            B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) := by
  let I3 := secondaryResidualInvariantThreePolynomial68 A B c d e
  set idx := 12 * n - 3 * g - 1
  have hI3low : (A * derivative I3).natDegree < idx := by
    have ht := middleBeta_natDegree_mul_derivative_le68 A I3
      (2 * n) (5 * n - g) hA (by omega) hI3
    have hi : 2 * n + (5 * n - g) - 1 = 7 * n - g - 1 := by omega
    have hle : (A * derivative I3).natDegree ≤ 7 * n - g - 1 := by
      simpa only [hi] using ht
    exact hle.trans_lt (by dsimp [idx]; omega)
  have hAd2low : (derivative (A * d ^ 2)).natDegree < idx := by
    have hp : (A * d ^ 2).natDegree ≤
        2 * n + ((5 * n - h) + (5 * n - h)) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (A * d ^ 2)
    dsimp [idx]
    omega
  have heelow : (e * derivative e).natDegree < idx := by
    have hde : (derivative e).natDegree ≤ 6 * n - h - 1 :=
      (natDegree_derivative_le e).trans (by omega)
    have hprod := natDegree_mul_le_of_le he hde
    dsimp [idx]
    omega
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
  have hlowBcd : (derivative (B * c * d)).natDegree < idx := by
    have hBc : (B * c).natDegree ≤ (3 * n - g) + (4 * n - g) :=
      natDegree_mul_le_of_le hB hc
    have hprod := natDegree_mul_le_of_le hBc hd
    have hder := natDegree_derivative_le (B * c * d)
    dsimp [idx]
    omega
  have hlowBp : (derivative B * c * d).natDegree < idx := by
    have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
      (natDegree_derivative_le B).trans (by omega)
    have hcd : (c * d).natDegree ≤ (4 * n - g) + (5 * n - h) :=
      natDegree_mul_le_of_le hc hd
    have hprod := natDegree_mul_le_of_le hdB hcd
    have hassoc : derivative B * (c * d) = derivative B * c * d := by ring
    rw [hassoc] at hprod
    dsimp [idx]
    omega
  have hlowBe : (B ^ 2 * derivative e).natDegree < idx := by
    have hde : (derivative e).natDegree ≤ 6 * n - h - 1 :=
      (natDegree_derivative_le e).trans (by omega)
    have hprod := natDegree_mul_le_of_le hB2deg hde
    dsimp [idx]
    omega
  have h0I3 : ((-9 / 4 : k) • (A * derivative I3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hI3low, mul_zero]
  have h0Ad2 : ((3 : k) • derivative (A * d ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAd2low, mul_zero]
  have h0Bcd : ((3 : k) • derivative (B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBcd, mul_zero]
  have h0Bp : ((6 : k) • (derivative B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBp, mul_zero]
  have h0Be : ((-3 : k) • (B ^ 2 * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBe, mul_zero]
  have h0ee : ((-18 : k) • (e * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt heelow, mul_zero]
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
  have hinner : (residualRowOneInner68 A B c d e).coeff idx =
      (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
        (2 : k) * ((12 * n - 3 * g : ℕ) : k) * A.coeff (2 * n) *
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) := by
    dsimp [residualRowOneInner68]
    simp only [coeff_add]
    rw [h0I3, h0Ad2, hAB2csm, hc3sm, h0Bcd, h0Bp, h0Be, h0ee]
    ring
  rw [residualRowOne_eq_inner68, coeff_smul, smul_eq_mul, hinner]

/-! ## The load correction drops below the row-one cubic face -/

set_option maxHeartbeats 3000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_double_zeta_zero
    (alpha gamma epsilon eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        12 * n - 3 * g - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  change (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
    A B c D e).natDegree < 12 * n - 3 * g - 1
  rw [cubicLoadRowOnePolynomial68_zero_beta_delta_exact]
  compute_degree
  omega

/-! ## Scalar endgame: the two faces force both leading defects to die

No zero branch is discarded: `b = 0` and `c4 = 0` are the conclusions,
and the joint nonvanishing branch is refuted by the window (`g = 4n` is
incompatible with `2g < 5n`). -/

theorem doubleStrictHigh_rowFaces_force_leading_zero68
    (n g : ℕ) (a b c4 : k) (hn : 0 < n) (hwin : 2 * g < 5 * n)
    (ha : a ≠ 0)
    (hrow2 : b * (a * b ^ 2 - (9 : k) * c4 ^ 2) = 0)
    (hrow1 : (6 : k) * ((4 * n - g : ℕ) : k) * c4 ^ 3 -
      (2 : k) * ((12 * n - 3 * g : ℕ) : k) * a * b ^ 2 * c4 = 0) :
    b = 0 ∧ c4 = 0 := by
  have hN4 : (((4 * n - g : ℕ) : k)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  have hb : b = 0 := by
    by_contra hb
    have hab2 : a * b ^ 2 = (9 : k) * c4 ^ 2 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hrow2).resolve_left hb)
    by_cases hc4 : c4 = 0
    · have hzero : a * b ^ 2 = 0 := by
        rw [hab2, hc4]
        ring
      rcases mul_eq_zero.mp hzero with h | h
      · exact ha h
      · exact pow_ne_zero 2 hb h
    · have hkey : c4 ^ 3 *
          ((6 : k) * ((4 * n - g : ℕ) : k) -
            (18 : k) * ((12 * n - 3 * g : ℕ) : k)) = 0 := by
        linear_combination hrow1 +
          (2 : k) * ((12 * n - 3 * g : ℕ) : k) * c4 * hab2
      have hscal := (mul_eq_zero.mp hkey).resolve_left (pow_ne_zero 3 hc4)
      have hc4' : (((4 * n - g : ℕ) : k)) =
          (4 : k) * (n : k) - (g : k) := by
        rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
        push_cast
        rfl
      have hc12' : (((12 * n - 3 * g : ℕ) : k)) =
          (12 : k) * (n : k) - (3 : k) * (g : k) := by
        rw [Nat.cast_sub (by omega : 3 * g ≤ 12 * n)]
        push_cast
        rfl
      rw [hc4', hc12'] at hscal
      have hgn : ((g : ℕ) : k) = ((4 * n : ℕ) : k) := by
        push_cast
        linear_combination (1 / 48 : k) * hscal
      have hg4 : g = 4 * n := by exact_mod_cast hgn
      omega
  refine ⟨hb, ?_⟩
  by_contra hc4
  have hc3 : ((6 : k) * ((4 * n - g : ℕ) : k)) * c4 ^ 3 = 0 := by
    rw [hb] at hrow1
    linear_combination hrow1
  rcases mul_eq_zero.mp hc3 with h | h
  · exact (mul_ne_zero (by norm_num) hN4) h
  · exact pow_ne_zero 3 hc4 h

/-! ## Source-facing elimination of the above-seven chamber -/

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighAboveSeven_impossible68
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
    (hdouble :
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
      2 * g ≤ h)
    (habove :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      7 * n < 3 * g) : False := by
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
  change 2 * g ≤ h at hdouble
  change 7 * n < 3 * g at habove
  have hzd :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighAboveSeven_forces_zeta68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using habove)
  have hdelta : delta = 0 := hzd.1
  have hzeta : zeta = 0 := hzd.2
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h
    at drops
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
    ee.natDegree ≤ 6 * n - g ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 ∨
      De.coeff (5 * n - g) ≠ 0 ∨ ee.coeff (6 * n - g) ≠ 0) at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have hg : 0 < g := secondary.1
  have hgh : g < h := drops.2.2.2.2.2.2
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4c : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon 0 Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1, hdelta, hzeta] at hi4e
    exact hi4e
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon 0 Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1, hdelta, hzeta] at hi3e
    exact hi3e
  have hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at hrowTwo
  have hrow := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  rw [drops.1, drops.2.1, hdelta, hzeta] at hrow
  have hred : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon 0 i4 Ae Be ce d ee = 0 := by
    have ht := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
      alpha gamma 0 epsilon 0 eta i4 Ae Be ce d ee hi4c hrow
    simpa only [laterDeepFiveSumReducedRowTwoPolynomial68, zero_smul, add_zero]
      using ht
  have hrel2 := fiveRadiusReducedRowTwo_doubleCubicFace_relation_of_zeta_zero68
    gamma epsilon i4 Ae Be ce d ee n g h hn hg hgh hdouble hopen
    hA secondary.2.1 secondary.2.2.1 bounds.1 bounds.2 hred
  have hI3 :=
    secondaryResidualInvariantThreePolynomial68_degree_le_five_sub_g_of_double_zeta_zero
      gamma epsilon i3 Ae Be ce d ee n g h hn hg hgh hdouble hopen
      secondary.2.1 secondary.2.2.1 bounds.2 hi3c
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
  rw [drops.1, drops.2.1, hdelta, hzeta] at hrowOne
  have hload1 :=
    cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_double_zeta_zero
      alpha gamma epsilon eta Ae Be ce d ee n g h hn hg hgh hdouble hopen
      hA secondary.2.1 secondary.2.2.1 bounds.1 bounds.2
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload1, add_zero,
    residualRowOne_coeff_doubleChamber68 Ae Be ce d ee n g h
      hn hg hgh hdouble hopen hA secondary.2.1 secondary.2.2.1
      bounds.1 bounds.2 hI3] at hcoeff
  have hface1 : (6 : k) * ((4 * n - g : ℕ) : k) * ce.coeff (4 * n - g) ^ 3 -
      (2 : k) * ((12 * n - 3 * g : ℕ) : k) * Ae.coeff (2 * n) *
        Be.coeff (3 * n - g) ^ 2 * ce.coeff (4 * n - g) = 0 :=
    (mul_eq_zero.mp hcoeff).resolve_left (by norm_num)
  have hbc := doubleStrictHigh_rowFaces_force_leading_zero68 n g
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
    hn hopen.2 ha hrel2 hface1
  have hDface : De.coeff (5 * n - g) = 0 := by
    have hd5 := drops.2.2.2.1
    rw [hbc.1, mul_zero] at hd5
    exact ((mul_eq_zero.mp hd5.symm).resolve_left (by norm_num))
  rcases secondary.2.2.2.2.2 with hb' | hc4' | hD' | he'
  · exact hb' hbc.1
  · exact hc4' hbc.2
  · exact hD' hDface
  · exact he' drops.2.2.1

#print axioms fiveRadiusReducedRowTwo_doubleCubicFace_relation_of_zeta_zero68
#print axioms secondaryResidualInvariantThreePolynomial68_degree_le_five_sub_g_of_double_zeta_zero
#print axioms residualRowOne_coeff_doubleChamber68
#print axioms cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_double_zeta_zero
#print axioms doubleStrictHigh_rowFaces_force_leading_zero68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighAboveSeven_impossible68

end LaterDeepLowerOpenDoubleStrictHighAboveSevenEndgame68

end Max11DegreeRoutes
