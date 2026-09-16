import LowScale68SecondaryResidualLoadZeroEndgamePart103Scratch

/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

private theorem loadZero_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 1 < v) (hq : q.natDegree < v) :
    (p * derivative q).natDegree < u + v - 1 := by
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hd : (derivative q).natDegree ≤ v - 2 := by
    have h := natDegree_derivative_le q
    omega
  have hmul := natDegree_mul_le_of_le hu hd
  omega

set_option maxHeartbeats 6000000 in
/-- On `2h=3g`, residual row one has inner cubic-face coefficient
`a*(3*d_top^2-2*b^2*c_top)*(12n-3g)+6*(4n-g)*c_top^3-18*(6n-h)*e_top^2`. -/
theorem residualRowOne_coeff_balancedChamber68_of_twoGap
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g) :
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
    have hv : 1 < 10 * n - 3 * g := by omega
    have h := loadZero_natDegree_mul_derivative_lt68 A I3
      (2 * n) (10 * n - 3 * g) hA hv hI3
    have hi : 2 * n + (10 * n - 3 * g) - 1 = idx := by
      dsimp [idx]; omega
    simpa only [hi] using h
  have hd2deg : (d ^ 2).natDegree ≤ 10 * n - 3 * g := by
    compute_degree
    omega
  have hd2 : (d ^ 2).coeff (10 * n - 3 * g) =
      d.coeff (5 * n - h) ^ 2 := by
    have hd2pow := coeff_pow_at_bound68 d (5 * n - h) 2 hd
    have hi : 2 * (5 * n - h) = 10 * n - 3 * g := by omega
    simpa only [hi] using hd2pow
  have hAd2coeff := coeff_mul_at_bounds68 A (d ^ 2) (2 * n) (10 * n - 3 * g)
    hA hd2deg
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
    have hB2pow := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using hB2pow
  have hAB2ccoeff := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (6 * n - 2 * g) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + (6 * n - 2 * g) + (4 * n - g) = 12 * n - 3 * g :=
    by omega
  rw [hiAB2c, hB2] at hAB2ccoeff
  have hAB2cder := coeff_derivative_at_bound68 (A * B ^ 2 * c)
    (12 * n - 3 * g) (by omega)
  rw [hAB2ccoeff] at hAB2cder
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (8 * n - 2 * g) (4 * n - g) (by omega) hc2deg hc
  have hic3 : (8 * n - 2 * g) + (4 * n - g) - 1 = idx := by
    dsimp [idx]; omega
  rw [hic3, hc2] at hc3
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = 12 * n - 2 * h - 1 := by omega
  rw [hiee] at hee
  have hidx_ee : 12 * n - 2 * h - 1 = idx := by
    dsimp [idx]; omega
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
    have hder := natDegree_derivative_le (B * c * d)
    have hle : (derivative (B * c * d)).natDegree ≤
        12 * n - 2 * g - h - 1 := by omega
    exact hle.trans_lt hlowFace
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
    have hassoc : derivative B * (c * d) = derivative B * c * d := by
      ring
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

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

set_option maxHeartbeats 2000000 in
theorem residualRowOne_coeff_balancedChamber_eq68_of_twoGap
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-64 / 9 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 := by
  rw [residualRowOne_coeff_balancedChamber68_of_twoGap A B c d e n g h hg hgh hh hsmall
    hbalanced hA hB hcdeg hd he hI3]
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
    have := congrArg (fun m : ℕ => (m : k)) hbalanced
    push_cast at this
    exact this
  rw [hcast12, hcast4, hcast6]
  exact residualRowOneScalar68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hbal hdisc hinc hrel

/-- Residual row one cannot vanish at the balanced cubic face. -/
theorem residualRowOne_balanced_coeff_ne_zero68_of_twoGap
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) ≠ 0 := by
  rw [residualRowOne_coeff_balancedChamber_eq68_of_twoGap A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel]
  have hcast4 : (((4 * n - g : ℕ) : k)) =
      (4 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  rw [hcast4]
  have hNG : (4 : k) * (n : k) - (g : k) ≠ 0 := by
    rw [← hcast4]
    exact Nat.cast_ne_zero.mpr (by omega)
  exact residualRowOneScalar_ne_zero68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hNG
    (by
      have := congrArg (fun m : ℕ => (m : k)) hbalanced
      push_cast at this
      exact this)
    hdisc hinc hrel

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

theorem residualRowOne_add_load_eq_zero_imp_false68_of_twoGap
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0)
    (hload : load.natDegree < 12 * n - 3 * g - 1)
    (hsum : secondaryResidualRowOnePolynomial68 A B c d e + load = 0) :
    False := by
  have hcoeff :
      (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hsum
    rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload,
      add_zero] at h
    exact h
  exact residualRowOne_balanced_coeff_ne_zero68_of_twoGap A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel hcoeff

theorem residualRowOne_eq_zero_imp_false68_of_twoGap
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0)
    (hrow : secondaryResidualRowOnePolynomial68 A B c d e = 0) :
    False := by
  have hcoeff :
      (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) = 0 := by
    simp [hrow]
  exact residualRowOne_balanced_coeff_ne_zero68_of_twoGap A B c d e n g h hg hgh hh
    hsmall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel hcoeff

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_not_leftChamber68_of_twoGap
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    False := by
  have hidx : 11 * n - 3 * g - 1 < 11 * n - 2 * h - 1 := by omega
  have hload' : load.natDegree < 11 * n - 2 * h - 1 := hload.trans hidx
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68
    A B c d e load (11 * n - 2 * h - 1) hload' hsum
  exact residualRowTwo_leftChamber_ne_zero68_of_twoGap A B c d e n g h
    hg hgh hh hsmall hleft hA hB hc hd he hQ hd0 he0 hcoeff0

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

/-! ## Row-two trichotomy, balanced relation, and row-one endgame -/

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_not_rightChamber68_of_twoGap
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hb0 : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0) :
    False := by
  have ha0 := residualDisc_imp_leadingA_ne_zero68
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    hdisc hc0
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68
    A B c d e load (11 * n - 3 * g - 1) hload hsum
  exact residualRowTwo_rightChamber_ne_zero68_of_twoGap A B c d e n g h
    hg hgh hh hsmall hright hA hB hc hd he hQ hdisc ha0 hb0 hcoeff0

set_option maxHeartbeats 2000000 in
theorem residualSelectedGap_eq_balanced68_of_twoGap
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hb0 : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    2 * h = 3 * g := by
  rcases lt_trichotomy (2 * h) (3 * g) with hleft | heq | hright
  · exact (residualRowTwo_not_leftChamber68_of_twoGap A B c d e load n g h
      hg hgh hh hsmall hleft hA hB hc hd he hQ hload hsum hd0 he0).elim
  · exact heq
  · exact (residualRowTwo_not_rightChamber68_of_twoGap A B c d e load n g h
      hg hgh hh hsmall hright hA hB hc hd he hQ hload hsum hdisc hb0 hc0).elim

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

/-! ## Row-two trichotomy, balanced relation, and row-one endgame -/

set_option maxHeartbeats 2000000 in
theorem residualSelectedGap_eq_balanced68_of_rowTwoSystem_of_l_eq_zero
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hload :
      (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
          11 * n - 3 * g - 1)
    (hrowTwo :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 0 alpha beta delta A B C0 D0)
        (integratedTPolynomial68 0 alpha beta gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          A B C0 D0 E0) B C0 D0 E0 = 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hb0 : B.coeff (3 * n - g) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    2 * h = 3 * g := by
  have hsum := polynomialSecondaryResidualRowTwo68
    0 alpha beta gamma delta epsilon zeta eta A B c d e hrowTwo
  exact residualSelectedGap_eq_balanced68_of_twoGap A B c d e
    (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e)
    n g h hg hgh hh hsmall hA hB hc hd he hQ hload hsum hdisc hb0 hc0 hd0 he0

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

/-! ## Row-two trichotomy, balanced relation, and row-one endgame -/

set_option maxHeartbeats 6000000 in
theorem residualCanonicalSelectedGap_eq_balanced68_of_l_eq_zero
    (alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hsmall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < n) :
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
    2 * h = 3 * g := by
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
  change 2 * g < n at hsmall
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hcdeg : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt_of_strictDrops n g d ee
      hdrops.1 hdrops.2
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualSelect68_of_l_eq_zero
      alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  obtain ⟨h', hgh', hh', hb0, hc0, hd0', he0', hdisc'⟩ := hsel
  change g < h' at hgh'
  change h' < 2 * g at hh'
  change Be.coeff (3 * n - g) ≠ 0 at hb0
  change ce.coeff (4 * n - g) ≠ 0 at hc0
  change d.coeff (5 * n - h') ≠ 0 at hd0'
  change ee.coeff (6 * n - h') ≠ 0 at he0'
  change Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
    3 * ce.coeff (4 * n - g) ^ 2 = 0 at hdisc'
  have hdne : d ≠ 0 := fun hz => by
    rw [hz, coeff_zero] at hd0'
    exact hd0' rfl
  have hh : h < 2 * g := by
    have hgapd : polynomialGap68 n 5 d ≤ h' := by
      have hgap : polynomialGap68 n 5 d = 5 * n - d.natDegree := by
        simp [polynomialGap68, hdne]
      rw [hgap]
      have hle : 5 * n - h' ≤ d.natDegree := by
        by_contra hnot
        have hz : d.coeff (5 * n - h') = 0 :=
          coeff_eq_zero_of_natDegree_lt (by omega)
        exact hd0' hz
      omega
    exact (le_trans (Nat.min_le_left _ _) hgapd).trans_lt hh'
  have hnotboth : ¬ (d = 0 ∧ ee = 0) := fun hboth => hdne hboth.1
  have hattained : d.coeff (5 * n - h) ≠ 0 ∨
      ee.coeff (6 * n - h) ≠ 0 := by
    simpa only [h] using secondaryResidualGap68_boundary_attained n d ee
      hdbase hebase hnotboth
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    calc
      Ee = (1 / 3 : k) • (Ae * Ce) - (2 / 27 : k) • Ae ^ 3 + ee := by
        simpa only [ee] using cubicEDefectPolynomial68_reconstruct Ae Ce Ee
      _ = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
        rw [hCrec]
        apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
        simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
          map_pow, RatFunc.algebraMap_C]
        simp only [map_div₀, map_ofNat, map_one]
        ring
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have hx := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using hx
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have hface :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualMiddleFace68_of_l_eq_zero
      alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgh)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hh)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hbounds)
  change SecondaryResidualBetweenFace68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (ee.coeff (6 * n - h)) at hface
  have hclass := secondaryResidualBetweenFace68_classify_of_support
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (ee.coeff (6 * n - h)) (by simpa only [n, Ae] using
      (maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
        0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys).2.2.2.2.2) (Or.inl hb0) hattained hface
  have hQ :
      (residualIncidenceQ68 Be ce d ee).natDegree < 9 * n - 3 * g := by
    have hq :=
      secondaryResidualIncidenceDefectPolynomial68_degree_lt_cubicFace_of_l_eq_zero
        beta gamma delta epsilon zeta i4 Ae Be ce d ee n g h
        hg hgh hsmall hA hB hcdeg hbounds.1 hbounds.2 hi4c
    simpa [residualIncidenceQ68,
      secondaryResidualIncidenceDefectPolynomial68] using hq
  have hload :
      (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
          11 * n - 3 * g - 1 :=
    cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_l_eq_zero
      alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
      hg hgh hsmall hA hB hcdeg hbounds.1 hbounds.2
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 0 alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 0 alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
      ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
  have hrowTwo :
      let Crec := (1 / 3 : k) • Ae ^ 2 + ce
      let Drec := (1 / 3 : k) • (Ae * Be) + d
      let Erec := (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 0 alpha beta delta Ae Be Crec Drec)
        (integratedTPolynomial68 0 alpha beta gamma epsilon Ae Be Crec Drec
          Erec)
        (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Crec
          Drec Erec)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          Ae Be Crec Drec Erec) Be Crec Drec Erec = 0 := by
    simp only
    rw [← hCrec, ← hDrec, ← hErec]
    exact h2e
  exact residualSelectedGap_eq_balanced68_of_rowTwoSystem_of_l_eq_zero
    alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
    hg hgh hh hsmall hA hB hcdeg hbounds.1 hbounds.2 hQ hload hrowTwo
    hclass.2.2.2.2 hb0 hc0 hclass.2.2.1 hclass.2.2.2.1

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

/-! ## Row-two trichotomy, balanced relation, and row-one endgame -/

/-- Residual data on the balanced wall after `l=0`, with chamber `2g<n`. -/
structure LoadZeroBalancedResidualData68
    (A B c d e : k[X]) (n g h : ℕ) : Prop where
  hg : 0 < g
  hgh : g < h
  hh : h < 2 * g
  hsmall : 2 * g < n
  hbalanced : 2 * h = 3 * g
  hA : A.natDegree ≤ 2 * n
  hB : B.natDegree ≤ 3 * n - g
  hcdeg : c.natDegree ≤ 4 * n - g
  hd : d.natDegree ≤ 5 * n - h
  he : e.natDegree ≤ 6 * n - h
  ha0 : A.coeff (2 * n) ≠ 0
  hb0 : B.coeff (3 * n - g) ≠ 0
  hc0 : c.coeff (4 * n - g) ≠ 0
  hd0 : d.coeff (5 * n - h) ≠ 0
  he0 : e.coeff (6 * n - h) ≠ 0
  hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
    (3 : k) * c.coeff (4 * n - g) ^ 2 = 0
  hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
    c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0
  hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
    (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0
  hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
    10 * n - 3 * g

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

/-! ## Row-two trichotomy, balanced relation, and row-one endgame -/

set_option maxHeartbeats 8000000 in
theorem loadZeroBalancedResidualData68_of_system
    (alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hsmall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < n) :
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
    LoadZeroBalancedResidualData68 Ae Be ce d ee n g h := by
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
  change 2 * g < n at hsmall
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hcdeg : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt_of_strictDrops n g d ee
      hdrops.1 hdrops.2
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  have hbalanced : 2 * h = 3 * g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
      residualCanonicalSelectedGap_eq_balanced68_of_l_eq_zero
        alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  have hh : h < 2 * g := by omega
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have ha0 : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondarySmallGapBoundary68
      0 alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) at hboundary
  have hsupport := hboundary.2.2
  have hnotboth : ¬ (d = 0 ∧ ee = 0) := by
    rintro ⟨hd0, he0⟩
    have hh0 : h = 6 * n + 1 := by
      simp only [h, secondaryResidualGap68, polynomialGap68, hd0, he0,
        ↓reduceIte, min_self]
    omega
  have hattained : d.coeff (5 * n - h) ≠ 0 ∨
      ee.coeff (6 * n - h) ≠ 0 := by
    simpa only [h] using secondaryResidualGap68_boundary_attained n d ee
      hdbase hebase hnotboth
  have hface :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualMiddleFace68_of_l_eq_zero
      alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgh)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hh)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hbounds)
  change SecondaryResidualBetweenFace68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (ee.coeff (6 * n - h)) at hface
  have hclass := secondaryResidualBetweenFace68_classify_of_support
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (ee.coeff (6 * n - h)) ha0 hsupport hattained hface
  have hb0 : Be.coeff (3 * n - g) ≠ 0 := hclass.1
  have hc0 : ce.coeff (4 * n - g) ≠ 0 := hclass.2.1
  have hd0 : d.coeff (5 * n - h) ≠ 0 := hclass.2.2.1
  have he0 : ee.coeff (6 * n - h) ≠ 0 := hclass.2.2.2.1
  have hdisc : Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
      (3 : k) * ce.coeff (4 * n - g) ^ 2 = 0 := hclass.2.2.2.2
  have hinc : Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
      ce.coeff (4 * n - g) * d.coeff (5 * n - h) = 0 := hface.four
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    calc
      Ee = (1 / 3 : k) • (Ae * Ce) - (2 / 27 : k) • Ae ^ 3 + ee := by
        simpa only [ee] using cubicEDefectPolynomial68_reconstruct Ae Ce Ee
      _ = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
        rw [hCrec]
        apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
        simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
          map_pow, RatFunc.algebraMap_C]
        simp only [map_div₀, map_ofNat, map_one]
        ring
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have hx := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using hx
  have hi3e : firstIntegralThreePolynomial68 0 beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    have hx := congrArg (expand k 60) hi3
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralThreePolynomial68] using hx
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec] at hi3c
  have hQ :
      (residualBalancedIncidenceQ68 Be ce d ee).natDegree <
        9 * n - 3 * g := by
    have hq :=
      secondaryResidualIncidenceDefectPolynomial68_degree_lt_cubicFace_of_l_eq_zero
        beta gamma delta epsilon zeta i4 Ae Be ce d ee n g h
        hg hgh hsmall hA hB hcdeg hbounds.1 hbounds.2 hi4c
    simpa [residualBalancedIncidenceQ68,
      secondaryResidualIncidenceDefectPolynomial68] using hq
  have hload :
      (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
          11 * n - 3 * g - 1 :=
    cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_l_eq_zero
      alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
      hg hgh hsmall hA hB hcdeg hbounds.1 hbounds.2
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 0 alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 0 alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
      ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
  have hrowTwo :
      let Crec := (1 / 3 : k) • Ae ^ 2 + ce
      let Drec := (1 / 3 : k) • (Ae * Be) + d
      let Erec := (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 0 alpha beta delta Ae Be Crec Drec)
        (integratedTPolynomial68 0 alpha beta gamma epsilon Ae Be Crec Drec
          Erec)
        (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Crec
          Drec Erec)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          Ae Be Crec Drec Erec) Be Crec Drec Erec = 0 := by
    simp only
    rw [← hCrec, ← hDrec, ← hErec]
    exact h2e
  have hsum := polynomialSecondaryResidualRowTwo68
    0 alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  have hrel := residualRowTwo_add_load_eq_zero_imp_balancedRelation68_of_twoGap
    Ae Be ce d ee
    (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
    n g h hg hgh hh hsmall hbalanced hA hB hcdeg hbounds.1 hbounds.2
    hQ hdisc hload hsum
  have hD : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  have hload3 := secondaryLoadInvariantThreePolynomial68_degree_lt_cubicFace_of_twoGap
    0 beta gamma delta epsilon zeta Ae Be ce
    ((1 / 3 : k) • (Ae * Be) + d) ee n g h hg hgh hsmall
    hA hB hcdeg hD hbounds.2
  have hsplit := hi3c
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    cubicFirstIntegralThreePolynomial68_residualCoordinates] at hsplit
  have hI3eq :
      secondaryResidualInvariantThreePolynomial68 Ae Be ce d ee =
        C i3 - secondaryLoadInvariantThreePolynomial68
          0 beta gamma delta epsilon zeta Ae Be ce
            ((1 / 3 : k) • (Ae * Be) + d) ee :=
    eq_sub_iff_add_eq.mpr hsplit
  have hI3 :
      (secondaryResidualInvariantThreePolynomial68 Ae Be ce d ee).natDegree <
        10 * n - 3 * g := by
    rw [hI3eq]
    compute_degree
    omega
  exact ⟨hg, hgh, hh, hsmall, hbalanced, hA, hB, hcdeg, hbounds.1,
    hbounds.2, ha0, hb0, hc0, hd0, he0, hdisc, hinc, hrel, hI3⟩

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

/-! ## Row-two trichotomy, balanced relation, and row-one endgame -/

set_option maxHeartbeats 8000000 in
/-- After `l=0`, the residual chamber `2g<n` is impossible: the selected
gap is balanced and residual row one has a nonzero cubic-face coefficient. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl0 : l = 0)
    (hsmall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < n) :
    False := by
  subst hl0
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
  have hdata := loadZeroBalancedResidualData68_of_system
    alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys (by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change LoadZeroBalancedResidualData68 Ae Be ce d ee n g h at hdata
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    calc
      Ee = (1 / 3 : k) • (Ae * Ce) - (2 / 27 : k) • Ae ^ 3 + ee := by
        simpa only [ee] using cubicEDefectPolynomial68_reconstruct Ae Ce Ee
      _ = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
        rw [hCrec]
        apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
        simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
          map_pow, RatFunc.algebraMap_C]
        simp only [map_div₀, map_ofNat, map_one]
        ring
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hrowOne :
      let Crec := (1 / 3 : k) • Ae ^ 2 + ce
      let Drec := (1 / 3 : k) • (Ae * Be) + d
      let Erec := (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee
      lowerRowOnePolynomial68
        (integratedTPolynomial68 0 alpha beta gamma epsilon Ae Be Crec Drec
          Erec)
        (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Crec
          Drec Erec)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          Ae Be Crec Drec Erec) Crec Drec Erec = 0 := by
    simp only
    rw [← hCrec, ← hDrec, ← hErec]
    exact h1e
  have hsum := polynomialSecondaryResidualRowOne68
    0 alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowOne
  have hload := cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_twoGap
    0 alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
    hdata.hg hdata.hgh hdata.hsmall hdata.hA hdata.hB hdata.hcdeg
    hdata.hd hdata.he
  exact residualRowOne_add_load_eq_zero_imp_false68_of_twoGap
    Ae Be ce d ee
    (cubicLoadRowOnePolynomial68 0 alpha beta gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
    n g h hdata.hg hdata.hgh hdata.hh hdata.hsmall hdata.hbalanced
    hdata.hA hdata.hB hdata.hcdeg hdata.hd hdata.he hdata.hI3 hdata.hc0
    hdata.hdisc hdata.hinc hdata.hrel hload hsum

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
