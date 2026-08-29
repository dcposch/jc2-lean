import LowScale68SecondaryLargeGapLoadZeroFace
import LowScale68SecondaryResidualLoadZeroEndgame

/-! # Closure of the subcritical large-gap chamber

In the chamber `n < 2g`, `g < n`, and `3g < 2n`, the leading load is zero
and the selected residual gap is attained.  This module extracts its row-two
and row-one residual faces, forces the balanced chamber, excludes that chamber
by its nonzero row-one coefficient, and closes the residual double face.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LargeGapLoadZeroSubcritical68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Local degree helpers (the load-zero copies are file-private) -/

theorem largeGapSubcritical_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 1 < v) (hq : q.natDegree < v) :
    (p * derivative q).natDegree < u + v - 1 := by
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hd : (derivative q).natDegree ≤ v - 2 := by
    have h := natDegree_derivative_le q
    omega
  have hmul := natDegree_mul_le_of_le hu hd
  omega

theorem largeGapSubcritical_natDegree_derivative_mul_lt68
    (p q : k[X]) (u v : ℕ)
    (hu0 : 0 < u) (hu : p.natDegree ≤ u) (hq : q.natDegree < v) :
    (derivative p * q).natDegree < u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hmul := natDegree_mul_le_of_le hd hq'
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroPolynomial68_degree_lt_residualDouble_of_largeGapLoadZeroSubcritical
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowZeroPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 13 * n - 3 * g - 1 := by
  exact cubicLoadRowZeroPolynomial68_degree_lt_residualDouble_of_largeGapLoadZero
    alpha beta gamma delta epsilon zeta eta A B c D e n g hg
    hchamber.1 hchamber.2.1 hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_cubicFace_of_largeGapLoadZeroSubcritical
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - 3 * g := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_cubicFace_of_largeGapLoadZeroSubcritical
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_Q_degree_lt68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g : ℕ)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (A * derivative (residualIncidenceQ68 B c d e)).natDegree <
        11 * n - 3 * g - 1 ∧
      (derivative A * residualIncidenceQ68 B c d e).natDegree <
        11 * n - 3 * g - 1 := by
  have hpos : 0 < 9 * n - 3 * g :=
    lt_of_le_of_lt (Nat.zero_le _) hQ
  have hn : 0 < n := by omega
  have hv : 1 < 9 * n - 3 * g := by omega
  have h1 := largeGapSubcritical_natDegree_mul_derivative_lt68 A
    (residualIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g) hA hv hQ
  have h2 := largeGapSubcritical_natDegree_derivative_mul_lt68 A
    (residualIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g)
    (by omega) hA hQ
  have hi : 2 * n + (9 * n - 3 * g) - 1 = 11 * n - 3 * g - 1 := by omega
  exact ⟨by simpa only [hi] using h1, by simpa only [hi] using h2⟩

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_Bd_degree_le68_of_largeGapLoadZeroSubcritical
    (B d : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (derivative (B ^ 2 * d)).natDegree ≤ 11 * n - 2 * g - h - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hprod := natDegree_mul_le_of_le hB2 hd
  have hsum : 6 * n - 2 * g + (5 * n - h) = 11 * n - 2 * g - h := by omega
  rw [hsum] at hprod
  have hder := natDegree_derivative_le (B ^ 2 * d)
  omega

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_BcCore_degree_le68_of_largeGapLoadZeroSubcritical
    (A B c : k[X]) (n g : ℕ)
    (hg : 0 < g) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (A * B ^ 2 * derivative B).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative A * B ^ 3).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative (B * c ^ 2)).natDegree ≤ 11 * n - 3 * g - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
    (natDegree_derivative_le B).trans (by omega)
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have hAB2 := natDegree_mul_le_of_le hA hB2
  have hAB2d := natDegree_mul_le_of_le hAB2 hdB
  have hA3 := natDegree_mul_le_of_le hdA hB3
  have hBc2 := natDegree_mul_le_of_le hB hc2
  have hdBc2 := natDegree_derivative_le (B * c ^ 2)
  refine ⟨by omega, by omega, by omega⟩

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_de_degree_le68_of_largeGapLoadZeroSubcritical
    (d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (derivative (d * e)).natDegree ≤ 11 * n - 2 * h - 1 := by
  have hprod := natDegree_mul_le_of_le hd he
  have hsum : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hsum] at hprod
  have hder := natDegree_derivative_le (d * e)
  omega

set_option maxHeartbeats 4000000 in
theorem residualRowTwo_coeff_leftChamber68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) =
      (8 / 3 : k) * ((11 * n - 2 * h : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 2 * h - 1
  have hidx : 11 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    omega
  have hQdeg := residualRowTwoInner_Q_degree_lt68_of_largeGapLoadZeroSubcritical A B c d e n g hchamber hA hQ
  have hAQ : (A * derivative Q).natDegree < idx := hQdeg.1.trans hidx
  have hAQ' : (derivative A * Q).natDegree < idx := hQdeg.2.trans hidx
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_largeGapLoadZeroSubcritical A B c n g hg hchamber hA hB hc
  have hAB : (A * B ^ 2 * derivative B).natDegree < idx :=
    hcore.1.trans_lt hidx
  have hA3 : (derivative A * B ^ 3).natDegree < idx :=
    hcore.2.1.trans_lt hidx
  have hBc : (derivative (B * c ^ 2)).natDegree < idx :=
    hcore.2.2.trans_lt hidx
  have hBd := residualRowTwoInner_Bd_degree_le68_of_largeGapLoadZeroSubcritical B d n g h hg hgh hh hchamber hB hd
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

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_leftChamber_ne_zero68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_leftChamber68_of_largeGapLoadZeroSubcritical A B c d e n g h hg hgh hh hchamber hleft
    hA hB hc hd he hQ]
  have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 2 * h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) hd0) he0

set_option maxHeartbeats 4000000 in
theorem residualRowTwo_coeff_rightChamber68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) =
      (32 / 81 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 3 * g - 1
  have hQdeg := residualRowTwoInner_Q_degree_lt68_of_largeGapLoadZeroSubcritical A B c d e n g hchamber hA hQ
  have hAQ : (A * derivative Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.1
  have hAQ' : (derivative A * Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.2
  have hBd := residualRowTwoInner_Bd_degree_le68_of_largeGapLoadZeroSubcritical B d n g h hg hgh hh hchamber hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hde := residualRowTwoInner_de_degree_le68_of_largeGapLoadZeroSubcritical d e n g h hg hgh hh hchamber hd he
  have hde' : (derivative (d * e)).natDegree < idx := by
    dsimp [idx]
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 2) B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA hB2deg hB
  have hiAB : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB, hB2] at hAB
  have hABpow : (A * B ^ 2 * derivative B).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k) := by
    rw [hAB]
    ring
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hA3 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3 : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiA3, hB3] at hA3
  have hA3' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBcdeg : (B * c ^ 2).natDegree ≤ 11 * n - 3 * g := by
    have h := natDegree_mul_le_of_le hB hc2deg
    have hi : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
    rwa [hi] at h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hcast11 : (((11 * n - 3 * g : ℕ) : k)) =
      (11 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 11 * n)]
    push_cast
    rfl
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0de : ((-18 : k) • derivative (d * e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hde', mul_zero]
  have hABsm : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hABpow]
  have hA3sm : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx =
      (-2 / 3 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hA3']
  have hBcsm : ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (6 : k) * (B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hBc]
  have hinner : inner.coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0Bd, h0de, hABsm, hA3sm, hBcsm, hcast3, hcast2, hcast11]
    have hsc := residualRowTwoRightCoreScalar68_of_disc (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) hdisc
    convert hsc using 1
    ring
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  ring

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_rightChamber_ne_zero68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (ha0 : A.coeff (2 * n) ≠ 0)
    (hb0 : B.coeff (3 * n - g) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_rightChamber68_of_largeGapLoadZeroSubcritical A B c d e n g h hg hgh hh hchamber hright
    hA hB hc hd he hQ hdisc]
  have hscalar : (32 / 81 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 3 * g : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero hscalar hN) ha0) (pow_ne_zero 3 hb0)

set_option maxHeartbeats 2000000 in
theorem residualBalancedRowTwoInner_Q_degree_lt68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g : ℕ)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g) :
    (A * derivative (residualBalancedIncidenceQ68 B c d e)).natDegree <
        11 * n - 3 * g - 1 ∧
      (derivative A * residualBalancedIncidenceQ68 B c d e).natDegree <
        11 * n - 3 * g - 1 := by
  have hpos : 0 < 9 * n - 3 * g :=
    lt_of_le_of_lt (Nat.zero_le _) hQ
  have hn : 0 < n := by omega
  have hv : 1 < 9 * n - 3 * g := by omega
  have h1 := largeGapSubcritical_natDegree_mul_derivative_lt68 A
    (residualBalancedIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g) hA hv hQ
  have h2 := largeGapSubcritical_natDegree_derivative_mul_lt68 A
    (residualBalancedIncidenceQ68 B c d e) (2 * n) (9 * n - 3 * g)
    (by omega) hA hQ
  have hi : 2 * n + (9 * n - 3 * g) - 1 = 11 * n - 3 * g - 1 := by omega
  exact ⟨by simpa only [hi] using h1, by simpa only [hi] using h2⟩

set_option maxHeartbeats 2000000 in
theorem residualBalancedRowTwoInner_Bd_degree_le68_of_largeGapLoadZeroSubcritical
    (B d : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (derivative (B ^ 2 * d)).natDegree ≤ 11 * n - 2 * g - h - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hprod := natDegree_mul_le_of_le hB2 hd
  have hsum : 6 * n - 2 * g + (5 * n - h) = 11 * n - 2 * g - h := by omega
  rw [hsum] at hprod
  have hder := natDegree_derivative_le (B ^ 2 * d)
  omega

theorem residualRowTwo_coeff_balancedChamber68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) =
      (-8 / 27 : k) * ((11 * n - 3 * g : ℕ) : k) *
        ((4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
  let Q := residualBalancedIncidenceQ68 B c d e
  let inner := residualBalancedRowTwoInner68 A B c d e
  set idx := 11 * n - 3 * g - 1
  have hface : 11 * n - 2 * h = 11 * n - 3 * g := by omega
  have hQdeg := residualBalancedRowTwoInner_Q_degree_lt68_of_largeGapLoadZeroSubcritical A B c d e n g hchamber hA hQ
  have hAQ : (A * derivative Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.1
  have hAQ' : (derivative A * Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.2
  have hBd := residualBalancedRowTwoInner_Bd_degree_le68_of_largeGapLoadZeroSubcritical B d n g h hg hgh hh hchamber hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 2) B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA hB2deg hB
  have hiAB : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB, hB2] at hAB
  have hABpow : (A * B ^ 2 * derivative B).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k) := by
    rw [hAB]
    ring
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hA3 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3 : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiA3, hB3] at hA3
  have hA3' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBcdeg : (B * c ^ 2).natDegree ≤ 11 * n - 3 * g := by
    have h := natDegree_mul_le_of_le hB hc2deg
    have hi : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
    rwa [hi] at h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hcast11 : (((11 * n - 3 * g : ℕ) : k)) =
      (11 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 11 * n)]
    push_cast
    rfl
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have hABsm : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hABpow]
  have hA3sm : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx =
      (-2 / 3 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hA3']
  have hBcsm : ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (6 : k) * (B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hBc]
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    have hidx_de : 11 * n - 2 * h - 1 = idx := by
      dsimp [idx]
      omega
    rw [← hidx_de, hde, hface]
  have hcore :
      ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx +
        ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx +
        ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
    rw [hABsm, hA3sm, hBcsm, hcast3, hcast2, hcast11]
    have hsc := residualBalancedRightCoreScalar68_of_disc (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) hdisc
    convert hsc using 1
    ring
  have hinner : inner.coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 +
      (-18 : k) * ((11 * n - 3 * g : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
    dsimp [inner, residualBalancedRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0Bd, hde']
    linear_combination hcore
  rw [residualBalancedRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  exact residualBalancedRowTwoScalar68
    ((11 * n - 3 * g : ℕ) : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hdisc

theorem residualRowTwo_balanced_coeff_eq_zero_iff68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) = 0 ↔
      (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
        (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  rw [residualRowTwo_coeff_balancedChamber68_of_largeGapLoadZeroSubcritical A B c d e n g h hg hgh hh hchamber
    hbalanced hA hB hc hd he hQ hdisc]
  constructor
  · intro h
    have hsc : (-8 / 27 : k) * ((11 * n - 3 * g : ℕ) : k) ≠ 0 :=
      mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))
    exact (mul_eq_zero.mp h).resolve_left hsc
  · intro h
    rw [h, mul_zero]

theorem residualRowTwo_add_load_eq_zero_imp_balancedRelation68_of_largeGapLoadZeroSubcritical
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0) :
    (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  have hcoeff :
      (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff (11 * n - 3 * g - 1)) hsum
    rw [coeff_add, coeff_zero,
      coeff_eq_zero_of_natDegree_lt hload, add_zero] at h
    exact h
  exact (residualRowTwo_balanced_coeff_eq_zero_iff68_of_largeGapLoadZeroSubcritical A B c d e n g h hg hgh hh
    hchamber hbalanced hA hB hc hd he hQ hdisc).1 hcoeff

theorem residualRowTwo_eq_zero_imp_balancedRelation68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualBalancedIncidenceQ68 B c d e).natDegree < 9 * n - 3 * g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrow : secondaryResidualRowTwoPolynomial68 A B c d e = 0) :
    (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  have hcoeff :
      (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) = 0 := by
    simp [hrow]
  exact (residualRowTwo_balanced_coeff_eq_zero_iff68_of_largeGapLoadZeroSubcritical A B c d e n g h hg hgh hh
    hchamber hbalanced hA hB hc hd he hQ hdisc).1 hcoeff

theorem residualRowOne_coeff_balancedChamber68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hbalanced : 2 * h = 3 * g)
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
    have h := largeGapSubcritical_natDegree_mul_derivative_lt68 A I3
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

set_option maxHeartbeats 2000000 in
theorem residualRowOne_coeff_balancedChamber_eq68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hbalanced : 2 * h = 3 * g)
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
  rw [residualRowOne_coeff_balancedChamber68_of_largeGapLoadZeroSubcritical A B c d e n g h hg hgh hh hchamber
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

theorem residualRowOne_balanced_coeff_ne_zero68_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hbalanced : 2 * h = 3 * g)
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
  rw [residualRowOne_coeff_balancedChamber_eq68_of_largeGapLoadZeroSubcritical A B c d e n g h hg hgh hh
    hchamber hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel]
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

theorem residualRowOne_add_load_eq_zero_imp_false68_of_largeGapLoadZeroSubcritical
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hbalanced : 2 * h = 3 * g)
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
  exact residualRowOne_balanced_coeff_ne_zero68_of_largeGapLoadZeroSubcritical A B c d e n g h hg hgh hh
    hchamber hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel hcoeff

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_not_leftChamber68_of_largeGapLoadZeroSubcritical
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hleft : 2 * h < 3 * g)
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
  exact residualRowTwo_leftChamber_ne_zero68_of_largeGapLoadZeroSubcritical A B c d e n g h
    hg hgh hh hchamber hleft hA hB hc hd he hQ hd0 he0 hcoeff0

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_not_rightChamber68_of_largeGapLoadZeroSubcritical
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) (hright : 3 * g < 2 * h)
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
  exact residualRowTwo_rightChamber_ne_zero68_of_largeGapLoadZeroSubcritical A B c d e n g h
    hg hgh hh hchamber hright hA hB hc hd he hQ hdisc ha0 hb0 hcoeff0

set_option maxHeartbeats 2000000 in
theorem residualSelectedGap_eq_balanced68_of_largeGapLoadZeroSubcritical
    (A B c d e load : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
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
  · exact (residualRowTwo_not_leftChamber68_of_largeGapLoadZeroSubcritical A B c d e load n g h
      hg hgh hh hchamber hleft hA hB hc hd he hQ hload hsum hd0 he0).elim
  · exact heq
  · exact (residualRowTwo_not_rightChamber68_of_largeGapLoadZeroSubcritical A B c d e load n g h
      hg hgh hh hchamber hright hA hB hc hd he hQ hload hsum hdisc hb0 hc0).elim

set_option maxHeartbeats 3000000 in
theorem secondaryResidualRowOnePolynomial68_coeff_double_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (8 / 27 : k) *
        (3 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (g : k) *
            d.coeff (5 * n - 2 * g) -
          10 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (n : k) *
            d.coeff (5 * n - 2 * g) +
          2 * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 * (n : k) *
            c.coeff (4 * n - g) -
          9 * A.coeff (2 * n) * (g : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          30 * A.coeff (2 * n) * (n : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          3 * (g : k) * c.coeff (4 * n - g) ^ 3 -
          12 * (n : k) * c.coeff (4 * n - g) ^ 3) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have h1 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B d
    (4 * n) (3 * n - g) (5 * n - 2 * g) (by omega)
    hA2deg hB hd
  have hi1 : 4 * n + (3 * n - g) + (5 * n - 2 * g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi1, hA2] at h1
  have h2 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) d B
    (4 * n) (5 * n - 2 * g) (3 * n - g) (by omega)
    hA2deg hd hB
  have hi2 : 4 * n + (5 * n - 2 * g) + (3 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi2, hA2] at h2
  have h2' : (A ^ 2 * derivative B * d).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g) * ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 A B d A
    (2 * n) (3 * n - g) (5 * n - 2 * g) (2 * n) (by omega)
    hA hB hd hA
  have hi3 : 2 * n + (3 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (A * derivative A * B * d).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h3
  have h4 := coeff_mul_mul_derivative_at_bounds68 A c e
    (2 * n) (4 * n - g) (6 * n - 2 * g) (by omega) hA hc he
  have hi4 : 2 * n + (4 * n - g) + (6 * n - 2 * g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi4] at h4
  have h5 := coeff_mul_mul_derivative_at_bounds68 A e c
    (2 * n) (6 * n - 2 * g) (4 * n - g) (by omega) hA he hc
  have hi5 : 2 * n + (6 * n - 2 * g) + (4 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi5] at h5
  have h5' : (A * derivative c * e).coeff (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - 2 * g) * ((4 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5
  have h6 := coeff_mul_mul_derivative_at_bounds68 (B ^ 2) c A
    (6 * n - 2 * g) (4 * n - g) (2 * n) (by omega)
    hB2deg hc hA
  have hi6 : (6 * n - 2 * g) + (4 * n - g) + 2 * n - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi6, hB2] at h6
  have h6' : (derivative A * B ^ 2 * c).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6
  have h7 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (8 * n - 2 * g) (4 * n - g) (by omega) hc2deg hc
  have hi7 : (8 * n - 2 * g) + (4 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi7, hc2] at h7
  have hlowA : (derivative A * d ^ 2).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowB : (B ^ 2 * derivative e).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowC : (B * c * derivative d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowD : (B * derivative c * d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowE : (derivative B * c * d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowF : (e * derivative e).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) = 4 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast5 : (((5 * n - 2 * g : ℕ) : k)) =
      5 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 5 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - 2 * g : ℕ) : k)) =
      6 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 6 * n)]
    push_cast
    rfl
  simp only [secondaryResidualRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2', h3', h4, h5', h6', h7,
    coeff_eq_zero_of_natDegree_lt hlowA,
    coeff_eq_zero_of_natDegree_lt hlowB,
    coeff_eq_zero_of_natDegree_lt hlowC,
    coeff_eq_zero_of_natDegree_lt hlowD,
    coeff_eq_zero_of_natDegree_lt hlowE,
    coeff_eq_zero_of_natDegree_lt hlowF, smul_eq_mul]
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  ring

set_option maxHeartbeats 3000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_double_of_largeGapLoadZeroSubcritical
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 3 * g - 1) =
      (8 / 27 : k) * (n : k) * A.coeff (2 * n) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            e.coeff (6 * n - 2 * g)) -
          A.coeff (2 * n) * c.coeff (4 * n - g) *
            d.coeff (5 * n - 2 * g) +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) := by
  have h1 := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - 2 * g) (2 * n) (by omega)
    hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (6 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi1] at h1
  have h1' : (A * derivative A * B * e).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  have h2 := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - 2 * g) (2 * n) (by omega)
    hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi2] at h2
  have h2' : (A * derivative A * c * d).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3 * n - g) (4 * n - g) (4 * n - g) (2 * n) (by omega)
    hB hc hc hA
  have hi3 : (3 * n - g) + (4 * n - g) + (4 * n - g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (derivative A * B * c ^ 2).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h3
  have hlow1 : (A * B ^ 2 * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow3 : (derivative A * d * e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow4 : (B * c * derivative e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow5 : (B * d * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow6 : (derivative B * d ^ 2).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow7 : (c * derivative c * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1', h2', h3',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7, smul_eq_mul]
  push_cast
  ring

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

set_option maxHeartbeats 4000000 in
theorem secondaryResidualTiedDoubleFace68_impossible_of_largeGapLoadZeroSubcritical
    (n g : ℕ) (a b c d e : k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hn : 0 < n) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hface : SecondaryResidualTiedDoubleFace68
      (n : k) (g : k) a b c d e) : False := by
  have hcast := secondaryResidualTiedDoubleFace68_forces_gap_eq_four_radius
    (n : k) (g : k) a b c d e ha hb hc hface
  have hnat : g = 4 * n := by exact_mod_cast hcast
  omega

theorem secondaryResidualDoubleFace68_impossible_of_largeGapLoadZeroSubcritical
    (n g : ℕ) (a b c d e : k)
    (ha : a ≠ 0) (hsupport : b ≠ 0 ∨ c ≠ 0) (hn : 0 < n)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hface : SecondaryResidualTiedDoubleFace68
      (n : k) (g : k) a b c d e) : False := by
  have hb : b ≠ 0 := by
    rcases hsupport with hb | hc
    · exact hb
    · intro hb0
      have hd0 : d = 0 := by
        have h := hface.four
        rw [hb0] at h
        have hcd : c * d = 0 := by linear_combination (1 / 9 : k) * h
        exact (mul_eq_zero.mp hcd).resolve_left hc
      have he0 : e = 0 := by
        have h := hface.three
        rw [hb0] at h
        have hce : c * e = 0 := by linear_combination (1 / 3 : k) * h
        exact (mul_eq_zero.mp hce).resolve_left hc
      have hone := hface.one
      rw [hb0, hd0, he0] at hone
      have hcoeff : (3 * (g : k) - 12 * (n : k)) ≠ 0 := by
        intro hz
        have hcast : (3 * g : k) = (12 * n : ℕ) := by
          push_cast
          linear_combination hz
        have hnat : 3 * g = 12 * n := by exact_mod_cast hcast
        omega
      have hc3 : c ^ 3 = 0 := by
        have hprod : (3 * (g : k) - 12 * (n : k)) * c ^ 3 = 0 := by
          linear_combination hone
        exact (mul_eq_zero.mp hprod).resolve_left hcoeff
      exact (pow_ne_zero 3 hc) hc3
  have hc : c ≠ 0 := by
    rcases hsupport with hb' | hc
    · intro hc0
      have hd0 : d = 0 := by
        have h := hface.three
        rw [hc0] at h
        have hab : a * b ≠ 0 := mul_ne_zero ha hb'
        have habd : a * b * d = 0 := by linear_combination -h
        exact (mul_eq_zero.mp habd).resolve_left hab
      have he0 : e = 0 := by
        have h := hface.zero
        rw [hc0] at h
        have hab : a * b ≠ 0 := mul_ne_zero ha hb'
        have habe : a * b * e = 0 := by linear_combination -h
        exact (mul_eq_zero.mp habe).resolve_left hab
      have h := hface.four
      rw [hc0, hd0, he0] at h
      have hb3 : b ^ 3 = 0 := by linear_combination -h
      exact (pow_ne_zero 3 hb') hb3
    · exact hc
  by_cases hd : d = 0
  · exact secondaryResidualEAtDoubleFace68_impossible b c e hb hc
      (secondaryResidualEAtDoubleFace68_of_tied
        (n : k) (g : k) a b c d e hb hc hd hface)
  by_cases he : e = 0
  · exact secondaryResidualDAtDoubleFace68_impossible a b c d hb hc
      (secondaryResidualDAtDoubleFace68_of_tied
        (n : k) (g : k) a b c d e hb hc he hface)
  exact secondaryResidualTiedDoubleFace68_impossible_of_largeGapLoadZeroSubcritical
    n g a b c d e ha hb hc hn hchamber hface

set_option maxHeartbeats 4000000 in
theorem polynomialSecondaryResidualDoubleFace68_of_largeGapLoadZeroSubcritical
    (alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowOne :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowOnePolynomial68
        (integratedTPolynomial68 0 alpha beta gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          A B C0 D0 E0) C0 D0 E0 = 0)
    (hrowZero :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          A B C0 D0 E0) D0 E0).coeff (13 * n - 3 * g - 1) = 0) :
    SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (e.coeff (6 * n - 2 * g)) := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let D0 := (1 / 3 : k) • (A * B) + d
  let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  change lowerRowOnePolynomial68
    (integratedTPolynomial68 0 alpha beta gamma epsilon A B C0 D0 E0)
    (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
      A B C0 D0 E0) C0 D0 E0 = 0 at hrowOne
  change (lowerRowZeroPolynomial68
    (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
      A B C0 D0 E0) D0 E0).coeff (13 * n - 3 * g - 1) = 0 at hrowZero
  have hD : D0.natDegree ≤ 5 * n - g := by
    simp only [D0]
    compute_degree
    omega
  have hinv := polynomialSecondaryResidualDoubleInvariants68_of_largeGapLoadZero
    beta gamma delta epsilon zeta i4 i3 A B c d e n g hg
    hchamber.1 hchamber.2.1
    hA hB hc hd he hi4 hi3
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha beta gamma delta epsilon zeta eta A B c D0 e
  have hloadOne :
      (cubicLoadRowOnePolynomial68 0 alpha beta gamma delta epsilon zeta eta
        A B c D0 e).natDegree < 12 * n - 3 * g - 1 := by
    simpa only [D0] using
      cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_largeGapLoadZero
        alpha beta gamma delta epsilon zeta eta A B c d e n g (2 * g)
        hg (by omega) hchamber.1 hchamber.2.1 hchamber.2.2
        hA hB hc hd he
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    show cubicHomogeneousRowOnePolynomial68 A B c D0 e =
        secondaryResidualRowOnePolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowOnePolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowOnePolynomial68_coeff_double_of_largeGapLoadZeroSubcritical A B c d e n g
      hg hchamber hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      hloadOne, add_zero, coeff_zero] at hone
  have hone0 := (mul_eq_zero.mp hone).resolve_left (by norm_num)
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
    coeff_add,
    show cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
        secondaryResidualRowZeroPolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowZeroPolynomial68_coeff_double_of_largeGapLoadZeroSubcritical A B c d e n g
      hg hchamber hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroPolynomial68_degree_lt_residualDouble_of_largeGapLoadZeroSubcritical
        alpha beta gamma delta epsilon zeta eta A B c D0 e n g
        hg hchamber hA hB hc hD he), add_zero] at hrowZero
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfactor : (8 / 27 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 := (mul_eq_zero.mp hrowZero).resolve_left hfactor
  exact ⟨hinv.1, by linear_combination hinv.2,
    by linear_combination hzero0, by linear_combination hone0⟩

set_option maxHeartbeats 2000000 in
theorem residualSelectedGap_eq_balanced68_of_rowTwoSystem_of_largeGapLoadZeroSubcritical
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
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
  exact residualSelectedGap_eq_balanced68_of_largeGapLoadZeroSubcritical A B c d e
    (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e)
    n g h hg hgh hh hchamber hA hB hc hd he hQ hload hsum hdisc hb0 hc0 hd0 he0

set_option maxHeartbeats 3000000 in
theorem secondaryResidualIncidenceDefectPolynomial68_degree_lt_cubicFace_of_largeGapLoadZeroSubcritical
    (beta gamma delta epsilon zeta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualIncidenceDefectPolynomial68 B c d e).natDegree <
      9 * n - 3 * g := by
  let D := (1 / 3 : k) • (A * B) + d
  let q := secondaryResidualIncidenceDefectPolynomial68 B c d e
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_cubicFace_of_largeGapLoadZeroSubcritical
      beta gamma delta epsilon zeta A B c D e n g h hg hgh hchamber
      hA hB hc hD he
  have hsplit := hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    secondaryResidualInvariantFourPolynomial68_eq_incidenceDefect] at hsplit
  change (8 / 3 : k) • q +
    secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e = C i4 at hsplit
  have hcore : (8 / 3 : k) • q =
      C i4 - secondaryLoadInvariantFourPolynomial68
        0 beta gamma delta epsilon zeta A B c D e :=
    eq_sub_iff_add_eq.mpr hsplit
  have hq : q = (3 / 8 : k) •
      (C i4 - secondaryLoadInvariantFourPolynomial68
        0 beta gamma delta epsilon zeta A B c D e) := by
    calc
      q = (3 / 8 : k) • ((8 / 3 : k) • q) := by
        rw [smul_smul]
        norm_num
      _ = (3 / 8 : k) •
          (C i4 - secondaryLoadInvariantFourPolynomial68
            0 beta gamma delta epsilon zeta A B c D e) := by rw [hcore]
  change q.natDegree < 9 * n - 3 * g
  rw [hq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_degree_lt_cubicFace_of_largeGapLoadZeroSubcritical
    (beta gamma delta epsilon zeta i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hchamber : n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_lt_cubicFace_of_largeGapLoadZeroSubcritical
      beta gamma delta epsilon zeta A B c D e n g h hg hgh hchamber
      hA hB hc hD he
  have hsplit := hi3
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    cubicFirstIntegralThreePolynomial68_residualCoordinates] at hsplit
  have heq :
      secondaryResidualInvariantThreePolynomial68 A B c d e =
        C i3 - secondaryLoadInvariantThreePolynomial68
          0 beta gamma delta epsilon zeta A B c D e :=
    eq_sub_iff_add_eq.mpr hsplit
  rw [heq]
  compute_degree
  omega

set_option maxHeartbeats 5000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroSubcriticalResidualDoubleFace68
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
      n < 2 * g ∧ g < n ∧ 3 * g < 2 * n)
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
      d.natDegree ≤ 5 * n - 2 * g ∧ ee.natDegree ≤ 6 * n - 2 * g) :
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
      SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (ee.coeff (6 * n - 2 * g)) := by
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
  change n < 2 * g ∧ g < n ∧ 3 * g < 2 * n at hchamber
  change d.natDegree ≤ 5 * n - 2 * g ∧
    ee.natDegree ≤ 6 * n - 2 * g at hdouble
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.2.1)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hl : l = 0 := hclass.1
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
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
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
    hDrec, hl] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, hl] at hi3c
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnlarge : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E hn
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (13 * n - 3 * g - 1) = 0 := by
    rw [h0e]
    apply coeff_eq_zero_of_natDegree_lt
    have hdegree :
        (C terminal * (60 * (X ^ 59 : k[X]))).natDegree ≤ 59 := by
      compute_degree
    have hidx : 59 < 13 * n - 3 * g - 1 := by omega
    exact hdegree.trans_lt hidx
  have h1cubic := h1e
  rw [hCrec, hDrec, hErec, hl] at h1cubic
  have h0cubic := h0target
  rw [hCrec, hDrec, hErec, hl] at h0cubic
  exact ⟨hl,
    polynomialSecondaryResidualDoubleFace68_of_largeGapLoadZeroSubcritical
      alpha beta gamma delta epsilon zeta eta i4 i3 Ae Be ce d ee n g
      hg hchamber hA hB hc hdouble.1 hdouble.2 ha hi4c hi3c h1cubic h0cubic⟩

theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroSubcritical_impossible68
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
      n < 2 * g ∧ g < n ∧ 3 * g < 2 * n) :
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
  change n < 2 * g ∧ g < n ∧ 3 * g < 2 * n at hchamber
  have hgap :=
    maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.2.1)
  change l = 0 ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
    d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
    g < h ∧
    d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h at hgap
  have hl : l = 0 := hgap.1
  have hsupport := hgap.2.1
  have hgh : g < h := hgap.2.2.2.2.1
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := hgap.2.2.2.2.2
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  by_cases hh : h < 2 * g
  · have hface :=
      maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroResidualMiddleFace68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.2.1)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgh)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hh)
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hbounds)
    change l = 0 ∧ SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) at hface
    have hnotboth : ¬ (d = 0 ∧ ee = 0) := by
      rintro ⟨hd0, he0⟩
      have hsent : h = 6 * n + 1 := by
        simp [h, secondaryResidualGap68, polynomialGap68, hd0, he0]
      have : ¬ (6 * n + 1 < 2 * g) := by omega
      exact this (hsent ▸ hh)
    have hdbase : d.natDegree < 5 * n := by omega
    have hebase : ee.natDegree < 6 * n := by omega
    have hattained : d.coeff (5 * n - h) ≠ 0 ∨
        ee.coeff (6 * n - h) ≠ 0 := by
      simpa only [h] using secondaryResidualGap68_boundary_attained n d ee
        hdbase hebase hnotboth
    have hclass := secondaryResidualBetweenFace68_classify_of_support
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) ha hsupport hattained hface.2
    have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have hsecondary :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
    have hg0 : 0 < g := by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
    have hA : Ae.natDegree ≤ 2 * n := by
      have hAe : Ae.natDegree = 2 * n := by
        simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
      omega
    have hB : Be.natDegree ≤ 3 * n - g := by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
    have hcdeg : ce.natDegree ≤ 4 * n - g := by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
    have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
      simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
    have hErec :
        Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
      simpa only [ce, ee] using
        cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
    have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
      simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
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
      hDrec, hl] at hi4c
    have hi3c := hi3e
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, hl] at hi3c
    have hQ :
        (residualIncidenceQ68 Be ce d ee).natDegree < 9 * n - 3 * g := by
      have hq :=
        secondaryResidualIncidenceDefectPolynomial68_degree_lt_cubicFace_of_largeGapLoadZeroSubcritical
          beta gamma delta epsilon zeta i4 Ae Be ce d ee n g h
          hg0 hgh hchamber hA hB hcdeg hbounds.1 hbounds.2 hi4c
      simpa [residualIncidenceQ68,
        secondaryResidualIncidenceDefectPolynomial68] using hq
    have hload2 :
        (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
            11 * n - 3 * g - 1 :=
      cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_largeGapLoadZero
        alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
        hg0 hgh hchamber.1 hchamber.2.1 hA hB hcdeg hbounds.1 hbounds.2
    have h2e : lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) Be Ce De Ee = 0 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_lowerRowTwoPolynomial68_of_system
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
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
      rw [← hCrec, ← hDrec, ← hErec, ← hl]
      exact h2e
    have hbalanced :=
      residualSelectedGap_eq_balanced68_of_rowTwoSystem_of_largeGapLoadZeroSubcritical
        alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
        hg0 hgh hh hchamber hA hB hcdeg hbounds.1 hbounds.2 hQ hload2 hrowTwo
        hclass.2.2.2.2 hclass.1 hclass.2.1 hclass.2.2.1 hclass.2.2.2.1
    have hQb :
        (residualBalancedIncidenceQ68 Be ce d ee).natDegree <
          9 * n - 3 * g := by
      simpa [residualBalancedIncidenceQ68, residualIncidenceQ68] using hQ
    have hsum2 := polynomialSecondaryResidualRowTwo68
      0 alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
    have hrel :=
      residualRowTwo_add_load_eq_zero_imp_balancedRelation68_of_largeGapLoadZeroSubcritical
        Ae Be ce d ee
        (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
        n g h hg0 hgh hh hchamber hbalanced hA hB hcdeg hbounds.1 hbounds.2
        hQb hclass.2.2.2.2 hload2 hsum2
    have hI3deg :=
      secondaryResidualInvariantThreePolynomial68_degree_lt_cubicFace_of_largeGapLoadZeroSubcritical
        beta gamma delta epsilon zeta i3 Ae Be ce d ee n g h
        hg0 hgh hchamber hA hB hcdeg hbounds.1 hbounds.2 hi3c
    have h1e : lowerRowOnePolynomial68
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) Ce De Ee = 0 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_lowerRowOnePolynomial68_of_system
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
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
      rw [← hCrec, ← hDrec, ← hErec, ← hl]
      exact h1e
    have hsum1 := polynomialSecondaryResidualRowOne68
      0 alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowOne
    have hload1 :=
      cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_largeGapLoadZero
        alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
        hg0 hgh hchamber.1 hchamber.2.1 hchamber.2.2
        hA hB hcdeg hbounds.1 hbounds.2
    exact residualRowOne_add_load_eq_zero_imp_false68_of_largeGapLoadZeroSubcritical
      Ae Be ce d ee
      (cubicLoadRowOnePolynomial68 0 alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
      n g h hg0 hgh hh hchamber hbalanced hA hB hcdeg hbounds.1 hbounds.2
      hI3deg hclass.2.1 hclass.2.2.2.2 hface.2.four hrel hload1 hsum1
  · have hdouble : d.natDegree ≤ 5 * n - 2 * g ∧
        ee.natDegree ≤ 6 * n - 2 * g := by
      constructor <;> omega
    have hface :=
      maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroSubcriticalResidualDoubleFace68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdouble)
    change l = 0 ∧ SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) at hface
    have hn : 0 < n := by simpa only [n] using hcore.1
    exact secondaryResidualDoubleFace68_impossible_of_largeGapLoadZeroSubcritical n g
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) ha hsupport hn hchamber hface.2

end LargeGapLoadZeroSubcritical68

#print axioms largeGapSubcritical_natDegree_mul_derivative_lt68
#print axioms cubicLoadRowZeroPolynomial68_degree_lt_residualDouble_of_largeGapLoadZeroSubcritical
#print axioms polynomialSecondaryResidualDoubleFace68_of_largeGapLoadZeroSubcritical
#print axioms secondaryResidualDoubleFace68_impossible_of_largeGapLoadZeroSubcritical
#print axioms residualSelectedGap_eq_balanced68_of_largeGapLoadZeroSubcritical
#print axioms residualRowOne_add_load_eq_zero_imp_false68_of_largeGapLoadZeroSubcritical
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroSubcriticalResidualDoubleFace68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZeroSubcritical_impossible68

end Max11DegreeRoutes
