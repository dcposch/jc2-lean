import Fable68LaterDeepStrictHighSevenSplitScratch

/-! # Consuming the below-seven face balance on the double strict-high chamber

On the double child `2g ≤ h` of the strict-open window `3n < 2g < 5n`,
the strict-high face `5n < 3g` forces `delta = 0`, and below seven
(`3g < 7n`) the reduced row two carries the exact cubic-face balance
`b * (a*b^2 - 9*c4^2) = 0` (`Fable68LaterDeepStrictHighSevenSplitScratch`).
This file splits that balance honestly into its two zero branches and
consumes the first independent row-one loading in each.

At the row-one cubic face `12n - 3g - 1` the double child keeps only two
primitives of the residual inner form: `A*B^2*c` and `c^2*c'`.  The
`A*d^2` and `e*e'` faces sit at `12n - 2h - 1`, strictly below because
`2h ≥ 4g > 3g`; the mixed `B*c*d`, `B'*c*d`, `B^2*e'` faces sit at
`12n - 2g - h - 1`, below by `g < h`; the `I3` shoulder is pinned under
`10n - 3g` by the constant cubic first integral through the tracked
double load bound; and the whole row-one load vanishes below the face by
the exact `l = beta = delta = 0` Wronskian form.  The surviving relation
is `-2*a*b^2*c4*(12n-3g) + 6*(4n-g)*c4^3 = 0` with `12n-3g = 3*(4n-g)`:

* on the degenerate branch `b = 0` it collapses to `6*(4n-g)*c4^3 = 0`,
  so `c4 = 0`;
* on the discriminant branch `a*b^2 = 9*c4^2` it collapses to
  `-48*(4n-g)*c4^3 = 0`, so `c4 = 0` and then `b = 0` from `a ≠ 0`.

Both branches therefore force `b = c4 = 0`.  The residual drops already
give `ee.coeff (6n-g) = 0` and `a*b = 3 * De.coeff (5n-g)`, so all four
defect coefficients at the secondary boundary vanish, contradicting the
attained gap in `secondaryRadius68`.  The below-seven face of the double
strict-high chamber is impossible, `7n ≤ 3g` is forced, and the seven
split collapses to the exact wall packet and the above-seven `zeta = 0`
branch, both preserved verbatim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleStrictHighBelowSevenBranches68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Scalar consumption of the two zero branches

The row-one cubic-face relation meets the row-two face balance in pure
scalars.  Both zero branches of the balance are consumed exactly: the
degenerate branch keeps `b = 0` and gains `c4 = 0`; the discriminant
branch loses its top coefficient entirely. -/

theorem doubleBelowSevenFace_rowOne_forces_bc_zero68
    (w4 a b c4 : k) (ha : a ≠ 0) (h4 : w4 ≠ 0)
    (hface : b * (a * b ^ 2 - (9 : k) * c4 ^ 2) = 0)
    (hrel : (-2 : k) * a * b ^ 2 * c4 * ((3 : k) * w4) +
      (6 : k) * w4 * c4 ^ 3 = 0) :
    b = 0 ∧ c4 = 0 := by
  rcases mul_eq_zero.mp hface with hb | hdisc
  · refine ⟨hb, ?_⟩
    have hc3 : ((6 : k) * w4) * c4 ^ 3 = 0 := by
      linear_combination hrel + (6 : k) * a * b * c4 * w4 * hb
    have h6w : (6 : k) * w4 ≠ 0 := mul_ne_zero (by norm_num) h4
    by_contra hc
    exact pow_ne_zero 3 hc ((mul_eq_zero.mp hc3).resolve_left h6w)
  · have hc3 : ((-48 : k) * w4) * c4 ^ 3 = 0 := by
      linear_combination hrel + (6 : k) * c4 * w4 * hdisc
    have h48 : (-48 : k) * w4 ≠ 0 := mul_ne_zero (by norm_num) h4
    have hc40 : c4 = 0 := by
      by_contra hc
      exact pow_ne_zero 3 hc ((mul_eq_zero.mp hc3).resolve_left h48)
    have hab2 : a * b ^ 2 = 0 := by
      linear_combination hdisc + (9 : k) * c4 * hc40
    have hb0 : b = 0 := by
      by_contra hbne
      exact pow_ne_zero 2 hbne ((mul_eq_zero.mp hab2).resolve_left ha)
    exact ⟨hb0, hc40⟩

/-! ## The `I3` shoulder on the double child

The middle-child bound `I3 ≤ 6n - h` needed `h < 2g` to keep the `B^2`
load term under `6n - h`; it does not transfer.  The double child
instead uses the tracked double load bound `< 10n - 3g`, which is all
the cubic face needs. -/

set_option maxHeartbeats 3000000 in
theorem secondaryResidualInvariantThreePolynomial68_degree_le_tenFace_of_double
    (gamma epsilon zeta i3 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      10 * n - 3 * g - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_lt_double_of_laterDeepLowerOpen
      gamma 0 epsilon zeta A B c D e n g hn hg hopen hA hB hc hD he
  have hsplit := hi3
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    cubicFirstIntegralThreePolynomial68_residualCoordinates] at hsplit
  have heq : secondaryResidualInvariantThreePolynomial68 A B c d e =
      C i3 - secondaryLoadInvariantThreePolynomial68
        0 0 gamma 0 epsilon zeta A B c D e :=
    eq_sub_of_add_eq hsplit
  rw [heq]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [natDegree_C]
    omega
  · omega

/-! ## The row-one load drops below the cubic face

The balanced-wall sharp bound needed `2h = 3g` only through `h < 2g`;
on the double child `2h ≥ 4g` pushes every load face at or below
`8n - 2g - 1 < 12n - 3g - 1`, so the exact Wronskian form closes the
bound outright. -/

set_option maxHeartbeats 3000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_double68
    (alpha gamma epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        12 * n - 3 * g - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  change (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
    A B c D e).natDegree < 12 * n - 3 * g - 1
  rw [cubicLoadRowOnePolynomial68_zero_beta_delta_exact]
  compute_degree
  omega

/-! ## The residual row-one cubic face on the double child

Unlike the balanced middle chamber, the `A*d^2` and `e*e'` faces drop
strictly below `12n - 3g - 1` because `2h ≥ 4g > 3g`, so only the
`A*B^2*c` and `c^2*c'` primitives survive. -/

set_option maxHeartbeats 8000000 in
theorem residualRowOne_coeff_doubleCubicFace68
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      10 * n - 3 * g - 1) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-4 / 27 : k) *
        ((-2 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
            c.coeff (4 * n - g) * ((12 * n - 3 * g : ℕ) : k) +
          (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3) := by
  let I3 := secondaryResidualInvariantThreePolynomial68 A B c d e
  set idx := 12 * n - 3 * g - 1
  have hI3low : (A * derivative I3).natDegree < idx := by
    have ht := middleBeta_natDegree_mul_derivative_le68 A I3
      (2 * n) (10 * n - 3 * g - 1) hA (by omega) hI3
    exact ht.trans_lt (by dsimp [idx]; omega)
  have hlowAd2 : (derivative (A * d ^ 2)).natDegree < idx := by
    have hp : (A * d ^ 2).natDegree ≤
        2 * n + ((5 * n - h) + (5 * n - h)) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (A * d ^ 2)
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
  have hlowee : (e * derivative e).natDegree < idx := by
    have hde : (derivative e).natDegree ≤ 6 * n - h - 1 :=
      (natDegree_derivative_le e).trans (by omega)
    have hprod := natDegree_mul_le_of_le he hde
    dsimp [idx]
    omega
  have h0I3 : ((-9 / 4 : k) • (A * derivative I3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hI3low, mul_zero]
  have h0Ad2 : ((3 : k) • derivative (A * d ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowAd2, mul_zero]
  have h0Bcd : ((3 : k) • derivative (B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBcd, mul_zero]
  have h0Bp : ((6 : k) • (derivative B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBp, mul_zero]
  have h0Be : ((-3 : k) • (B ^ 2 * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBe, mul_zero]
  have h0ee : ((-18 : k) • (e * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowee, mul_zero]
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
      (-2 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
          c.coeff (4 * n - g) * ((12 * n - 3 * g : ℕ) : k) +
        (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 := by
    dsimp [residualRowOneInner68]
    simp only [coeff_add]
    rw [h0I3, h0Ad2, hAB2csm, hc3sm, h0Bcd, h0Bp, h0Be, h0ee]
    ring
  rw [residualRowOne_eq_inner68, coeff_smul, smul_eq_mul, hinner]

/-! ## The exact row-one relation of the double chamber -/

set_option maxHeartbeats 4000000 in
theorem residualRowOne_doubleCubicFace_relation68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hdouble : 2 * g ≤ h)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      10 * n - 3 * g - 1)
    (hrowOne : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    (-2 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g) * ((12 * n - 3 * g : ℕ) : k) +
      (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 = 0 := by
  have hload :=
    cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_double68
      alpha gamma epsilon zeta eta A B c d e n g h hn hg hgh hdouble hopen
      hA hB hc hd he
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload, add_zero,
    residualRowOne_coeff_doubleCubicFace68 A B c d e n g h hn hg hgh hdouble
      hopen hA hB hc hd he hI3] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (by norm_num)

/-! ## Source-facing impossibility of the below-seven face

The row-two face balance splits into `b = 0` and `a*b^2 = 9*c4^2`; the
row-one relation kills `c4` in both, the discriminant then kills `b`,
the residual drops kill `De.coeff (5n-g)` and `ee.coeff (6n-g)`, and the
attained secondary gap refuses all four. -/

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighBelowSeven_impossible68
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
      5 * n < 3 * g)
    (hbelow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * g < 7 * n) : False := by
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
  change 5 * n < 3 * g at habove
  change 3 * g < 7 * n at hbelow
  have hdelta :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHigh_forces_delta68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using habove)
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have hee2g : ee.natDegree ≤ 6 * n - 2 * g :=
    bounds.2.trans (by omega)
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4c : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1, hdelta] at hi4e
    exact hi4e
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1, hdelta] at hi3e
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
  rw [drops.1, drops.2.1, hdelta] at hrow
  have hred : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 Ae Be ce d ee = 0 := by
    have ht := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
      alpha gamma 0 epsilon zeta eta i4 Ae Be ce d ee hi4c hrow
    simpa only [laterDeepFiveSumReducedRowTwoPolynomial68, zero_smul, add_zero]
      using ht
  have hface :=
    fiveRadiusReducedRowTwo_doubleBelowSeven_cubicFace_relation68
      gamma epsilon zeta i4 Ae Be ce d ee n g h hn hg
      drops.2.2.2.2.2.2 hdouble hopen hbelow hA secondary.2.1
      secondary.2.2.1 bounds.1 bounds.2 hred
  have hI3 :=
    secondaryResidualInvariantThreePolynomial68_degree_le_tenFace_of_double
      gamma epsilon zeta i3 Ae Be ce d ee n g hn hg hopen hA
      secondary.2.1 secondary.2.2.1 (le_of_lt drops.2.2.2.2.1) hee2g hi3c
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
  rw [drops.1, drops.2.1, hdelta] at hrowOne
  have hrel :=
    residualRowOne_doubleCubicFace_relation68
      alpha gamma epsilon zeta eta Ae Be ce d ee n g h hn hg
      drops.2.2.2.2.2.2 hdouble hopen hA secondary.2.1 secondary.2.2.1
      bounds.1 bounds.2 hI3 hrowOne
  have hcast12 : ((12 * n - 3 * g : ℕ) : k) =
      (3 : k) * ((4 * n - g : ℕ) : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 12 * n),
      Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    ring
  rw [hcast12] at hrel
  have h4ne : ((4 * n - g : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨hb0, hc40⟩ :=
    doubleBelowSevenFace_rowOne_forces_bc_zero68
      ((4 * n - g : ℕ) : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) ha h4ne hface hrel
  have hD50 : De.coeff (5 * n - g) = 0 := by
    have hprod := drops.2.2.2.1
    rw [hb0, mul_zero] at hprod
    exact ((mul_eq_zero.mp hprod.symm).resolve_left (by norm_num))
  rcases secondary.2.2.2.2.2 with hne | hne | hne | hne
  · exact hne hb0
  · exact hne hc40
  · exact hne hD50
  · exact hne drops.2.2.1

/-! ## The seven floor and the collapsed seven split

Below seven is gone, so the double strict-high chamber forces
`7n ≤ 3g`, and the honest split of the base file collapses to the exact
wall packet and the above-seven `zeta = 0` branch. -/

set_option maxHeartbeats 20000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHigh_forces_sevenFloor68
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
      5 * n < 3 * g) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    delta = 0 ∧ 7 * n ≤ 3 * g := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  have hdelta :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHigh_forces_delta68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hopen hdouble habove
  change delta = 0 ∧ 7 * n ≤ 3 * g
  refine ⟨hdelta, ?_⟩
  by_contra hnot
  have hbelow : 3 * g < 7 * n := by omega
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighBelowSeven_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hopen hdouble habove (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hbelow)

set_option maxHeartbeats 20000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighSevenCollapse68
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
      5 * n < 3 * g) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    delta = 0 ∧
      ((3 * g = 7 * n ∧
          (8 / 81 : k) * ((4 * n : ℕ) : k) * Be.coeff (3 * n - g) *
              (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
                (9 : k) * ce.coeff (4 * n - g) ^ 2) +
            zeta * (n : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
        (7 * n < 3 * g ∧ zeta = 0)) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighSevenSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hopen hdouble habove
  change delta = 0 ∧
      ((3 * g < 7 * n ∧
          Be.coeff (3 * n - g) *
            (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
              (9 : k) * ce.coeff (4 * n - g) ^ 2) = 0) ∨
        (3 * g = 7 * n ∧
          (8 / 81 : k) * ((4 * n : ℕ) : k) * Be.coeff (3 * n - g) *
              (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
                (9 : k) * ce.coeff (4 * n - g) ^ 2) +
            zeta * (n : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
        (7 * n < 3 * g ∧ zeta = 0)) at hsel
  change delta = 0 ∧
      ((3 * g = 7 * n ∧
          (8 / 81 : k) * ((4 * n : ℕ) : k) * Be.coeff (3 * n - g) *
              (Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 -
                (9 : k) * ce.coeff (4 * n - g) ^ 2) +
            zeta * (n : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
        (7 * n < 3 * g ∧ zeta = 0))
  refine ⟨hsel.1, ?_⟩
  rcases hsel.2 with ⟨hlt, _⟩ | hrest
  · exact
      (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighBelowSeven_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hopen hdouble habove (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlt)).elim
  · exact hrest

#print axioms doubleBelowSevenFace_rowOne_forces_bc_zero68
#print axioms secondaryResidualInvariantThreePolynomial68_degree_le_tenFace_of_double
#print axioms cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_double68
#print axioms residualRowOne_coeff_doubleCubicFace68
#print axioms residualRowOne_doubleCubicFace_relation68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighBelowSeven_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHigh_forces_sevenFloor68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleStrictHighSevenCollapse68

end LaterDeepLowerOpenDoubleStrictHighBelowSevenBranches68

end Max11DegreeRoutes
