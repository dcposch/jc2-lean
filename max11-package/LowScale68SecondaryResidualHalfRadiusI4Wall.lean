import LowScale68SecondaryResidualHalfRadiusLoadWall
import LowScale68SecondaryResidualRowTwoLoadDominance

/-! # The residual half-radius wall with the I4-forced incidence term

Unlike the earlier cutoff wrapper, this calculation keeps
the degree-`8n` coefficient of the incidence defect `Q`.  I4 determines that
coefficient as `-35/4608 * l * a^4`; its feeds into row two and row zero alter
the two load coefficients but leave a nonsingular pair, hence still force
`l = 0` without any separate degree hypothesis on `Q`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Scalar elimination -/

theorem residualHalfRadiusI4_two_zero_force_l
    (N a d e l : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (htwo : (80 / 3 : k) * N * d * e +
      (35 / 576 : k) * N * l * a ^ 5 = 0)
    (hzero : (-8 / 9 : k) * N * a * d * e +
      (35 / 1728 : k) * N * l * a ^ 6 = 0) :
    l = 0 := by
  have hload : (385 / 576 : k) * N * l * a ^ 6 = 0 := by
    linear_combination a * htwo + (30 : k) * hzero
  have hc : (385 / 576 : k) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp hload with hprefix | ha6
  · rcases mul_eq_zero.mp hprefix with hprefix | hl
    · rcases mul_eq_zero.mp hprefix with hc0 | hN0
      · exact (hc hc0).elim
      · exact (hN hN0).elim
    · exact hl
  · exact (pow_ne_zero 6 ha ha6).elim

/-! ## Row two with the degree-`8n` incidence feed retained -/

set_option maxHeartbeats 8000000 in
theorem secondaryResidualRowTwoPolynomial68_coeff_halfRadiusI4
    (l beta gamma delta epsilon zeta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (10 * n - 1) =
      (80 / 3 : k) * (n : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        (-245 / 5184 : k) * (n : k) * l * A.coeff (2 * n) ^ 5 := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 10 * n - 1
  have hgh : g < h := residualHalfRadiusLoadWall_gap_lt n g h hsmall hwall
  have hh : h < 2 * g :=
    residualHalfRadiusLoadWall_lt_double n g h hg (Nat.le_of_lt hstrict) hwall
  have hd' : d.natDegree ≤ 5 * n - g := hd.trans (by omega)
  have he' : e.natDegree ≤ 6 * n - g := he.trans (by omega)
  have hQdeg : Q.natDegree ≤ 8 * n := by
    simpa only [Q] using
      residualIncidenceQ68_degree_le_eightRadius_of_I4
        l beta gamma delta epsilon zeta i4 A B c d e n g
        hg hsmall hA hB hc hd' he' hi4
  have hQ8 : Q.coeff (8 * n) =
      (-35 / 4608 : k) * l * A.coeff (2 * n) ^ 4 := by
    simpa only [Q] using
      residualIncidenceQ68_coeff_eightRadius_of_I4
        l beta gamma delta epsilon zeta i4 A B c d e n g
        hn hg hsmall hA hB hc hd' he' hi4
  have hAQ : (A * derivative Q).coeff idx =
      A.coeff (2 * n) * Q.coeff (8 * n) * ((8 * n : ℕ) : k) := by
    have hx := coeff_mul_derivative_at_bounds68 A Q (2 * n) (8 * n)
      (by omega) hA hQdeg
    have hi : 2 * n + 8 * n - 1 = idx := by dsimp [idx]; omega
    simpa only [hi] using hx
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have hQA : (derivative A * Q).coeff idx =
      A.coeff (2 * n) * Q.coeff (8 * n) * ((2 * n : ℕ) : k) := by
    have hx := coeff_mul_at_bounds68 (derivative A) Q (2 * n - 1) (8 * n)
      hdA hQdeg
    have hi : (2 * n - 1) + 8 * n = idx := by dsimp [idx]; omega
    have hA' := coeff_derivative_at_bound68 A (2 * n) (by omega)
    rw [hi, hA'] at hx
    simpa [mul_comm, mul_left_comm, mul_assoc] using hx
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_twoGap
    A B c n g hg hsmall hA hB hc
  have hcoreIdx : 11 * n - 3 * g - 1 < idx := by dsimp [idx]; omega
  have hAB : (A * B ^ 2 * derivative B).natDegree < idx :=
    hcore.1.trans_lt hcoreIdx
  have hA3 : (derivative A * B ^ 3).natDegree < idx :=
    hcore.2.1.trans_lt hcoreIdx
  have hBc : (derivative (B * c ^ 2)).natDegree < idx :=
    hcore.2.2.trans_lt hcoreIdx
  have hBd0 := residualRowTwoInner_Bd_degree_le68_of_twoGap
    B d n g h hg hgh hh hsmall hB hd
  have hBd : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hdebound := natDegree_mul_le_of_le hd he
  have hide : (5 * n - h) + (6 * n - h) = 10 * n := by omega
  rw [hide] at hdebound
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hde := coeff_derivative_at_bound68 (d * e) (10 * n) (by omega)
  rw [hdecoeff] at hde
  have h0AB : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAB, mul_zero]
  have h0A3 : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hA3, mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd, mul_zero]
  have h0Bc : ((6 : k) • derivative (B * c ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBc, mul_zero]
  have hQpart : ((-6 : k) • (A * derivative Q)).coeff idx +
      ((3 : k) • (derivative A * Q)).coeff idx =
      (-42 : k) * (n : k) * A.coeff (2 * n) * Q.coeff (8 * n) := by
    rw [coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul, hAQ, hQA]
    push_cast
    ring
  have hdepart : ((-18 : k) • derivative (d * e)).coeff idx =
      (-180 : k) * (n : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hde]
    push_cast
    ring
  have hinner : inner.coeff idx =
      (-42 : k) * (n : k) * A.coeff (2 * n) * Q.coeff (8 * n) +
        (-180 : k) * (n : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0AB, h0A3, h0Bd, h0Bc, hdepart]
    linear_combination hQpart
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner, hQ8]
  ring

set_option maxHeartbeats 4000000 in
theorem integratedLowerRowTwoPolynomial68_coeff_halfRadiusI4
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g) :
    (secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (10 * n - 1) =
      (80 / 3 : k) * (n : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        (35 / 576 : k) * (n : k) * l * A.coeff (2 * n) ^ 5 := by
  rw [coeff_add,
    secondaryResidualRowTwoPolynomial68_coeff_halfRadiusI4
      l beta gamma delta epsilon zeta i4 A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he hi4,
    cubicLoadRowTwoPolynomial68_coeff_halfRadius
      l alpha beta gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g h
      hn hg hsmall hwall hA hB hc hD he]
  ring

/-! ## Row zero with the same incidence feed retained -/

set_option maxHeartbeats 10000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_halfRadiusI4
    (l beta gamma delta epsilon zeta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (12 * n - 1) =
      (-8 / 9 : k) * (n : k) * A.coeff (2 * n) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        (35 / 15552 : k) * (n : k) * l * A.coeff (2 * n) ^ 6 := by
  let Q := residualIncidenceQ68 B c d e
  have hgh : g < h := residualHalfRadiusLoadWall_gap_lt n g h hsmall hwall
  have hd' : d.natDegree ≤ 5 * n - g := hd.trans (by omega)
  have he' : e.natDegree ≤ 6 * n - g := he.trans (by omega)
  have hQdeg : Q.natDegree ≤ 8 * n := by
    simpa only [Q] using
      residualIncidenceQ68_degree_le_eightRadius_of_I4
        l beta gamma delta epsilon zeta i4 A B c d e n g
        hg hsmall hA hB hc hd' he' hi4
  have hQ8 : Q.coeff (8 * n) =
      (-35 / 4608 : k) * l * A.coeff (2 * n) ^ 4 := by
    simpa only [Q] using
      residualIncidenceQ68_coeff_eightRadius_of_I4
        l beta gamma delta epsilon zeta i4 A B c d e n g
        hn hg hsmall hA hB hc hd' he' hi4
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have hAA : (A * derivative A).natDegree ≤ 4 * n - 1 :=
    natDegree_mul_le.trans (by omega)
  have hA' : (derivative A).coeff (2 * n - 1) =
      A.coeff (2 * n) * ((2 * n : ℕ) : k) :=
    coeff_derivative_at_bound68 A (2 * n) (by omega)
  have hAAcoeff : (A * derivative A).coeff (4 * n - 1) =
      A.coeff (2 * n) ^ 2 * ((2 * n : ℕ) : k) := by
    have hx := coeff_mul_at_bounds68 A (derivative A) (2 * n) (2 * n - 1)
      hA hdA
    have hi : 2 * n + (2 * n - 1) = 4 * n - 1 := by omega
    rw [hi, hA'] at hx
    simpa [pow_two, mul_assoc] using hx
  have hAAQ : (A * derivative A * Q).coeff (12 * n - 1) =
      A.coeff (2 * n) ^ 2 * ((2 * n : ℕ) : k) * Q.coeff (8 * n) := by
    have hx := coeff_mul_at_bounds68 (A * derivative A) Q
      (4 * n - 1) (8 * n) hAA hQdeg
    have hi : (4 * n - 1) + 8 * n = 12 * n - 1 := by omega
    rw [hi, hAAcoeff] at hx
    exact hx
  have hB3 : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hAAB3 : (A * derivative A * B ^ 3).natDegree < 12 * n - 1 := by
    have hx := natDegree_mul_le_of_le hAA hB3
    omega
  have hsplit := residualRowZero_Ae_split68 A B c d e
  have hAe :
      (A * derivative A * B * e).coeff (12 * n - 1) +
        (A * derivative A * c * d).coeff (12 * n - 1) =
          (A * derivative A * Q).coeff (12 * n - 1) := by
    have hx := congrArg (fun p : k[X] => p.coeff (12 * n - 1)) hsplit
    simp only [coeff_add, coeff_smul, smul_eq_mul,
      coeff_eq_zero_of_natDegree_lt hAAB3, mul_zero, add_zero] at hx
    simpa only [Q] using hx
  have hlow1 : (A * B ^ 2 * derivative d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow2 : (A * B * derivative B * d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow3 : (derivative A * B * c ^ 2).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow4 : (B * c * derivative e).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow5 : (B * d * derivative d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow6 : (derivative B * d ^ 2).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hlow7 : (c * derivative c * d).natDegree < 12 * n - 1 := by
    compute_degree
    omega
  have hprod : (derivative A * d * e).coeff (12 * n - 1) =
      A.coeff (2 * n) * ((2 * n : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
    have hAd := coeff_mul_at_bounds68 (derivative A) d
      (2 * n - 1) (5 * n - h) hdA hd
    have hmul2 := coeff_mul_at_bounds68 (derivative A * d) e
      ((2 * n - 1) + (5 * n - h)) (6 * n - h)
      (natDegree_mul_le.trans (Nat.add_le_add hdA hd)) he
    have hi : (2 * n - 1) + (5 * n - h) + (6 * n - h) = 12 * n - 1 := by
      omega
    rw [hi, hAd, hA'] at hmul2
    simpa [mul_assoc] using hmul2
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7]
  have hAe' :
      (-1 : k) * (A * derivative A * B * e).coeff (12 * n - 1) -
          (A * derivative A * c * d).coeff (12 * n - 1) =
        -(A * derivative A * Q).coeff (12 * n - 1) := by
    linear_combination -hAe
  rw [hAe', hAAQ, hQ8, hprod]
  push_cast
  ring

set_option maxHeartbeats 4000000 in
theorem integratedLowerRowZeroPolynomial68_coeff_halfRadiusI4
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (12 * n - 1) =
      (-8 / 9 : k) * (n : k) * A.coeff (2 * n) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        (35 / 1728 : k) * (n : k) * l * A.coeff (2 * n) ^ 6 := by
  rw [coeff_add,
    secondaryResidualRowZeroPolynomial68_coeff_halfRadiusI4
      l beta gamma delta epsilon zeta i4 A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he hi4,
    cubicLoadRowZeroPolynomial68_coeff_halfRadius
      l alpha beta gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g h
      hn hg hsmall hwall hA hB hc hD he]
  ring

set_option maxHeartbeats 6000000 in
theorem polynomialSecondaryResidualHalfRadiusI4_force_l
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hwall : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n) (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrowTwo : secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrowZero : secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    l = 0 := by
  have hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  have htwo := congrArg (fun p : k[X] => p.coeff (10 * n - 1)) hrowTwo
  have hzero := congrArg (fun p : k[X] => p.coeff (12 * n - 1)) hrowZero
  rw [coeff_zero,
    integratedLowerRowTwoPolynomial68_coeff_halfRadiusI4
      l alpha beta gamma delta epsilon zeta eta i4 A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he hi4 hD] at htwo
  rw [coeff_zero,
    integratedLowerRowZeroPolynomial68_coeff_halfRadiusI4
      l alpha beta gamma delta epsilon zeta eta i4 A B c d e n g h
      hn hg hsmall hstrict hwall hA hB hc hd he hi4 hD] at hzero
  exact residualHalfRadiusI4_two_zero_force_l (n : k) (A.coeff (2 * n))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) l
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) ha htwo hzero

/-! ## Canonical expanded wrapper -/

set_option maxHeartbeats 10000000 in
/-- The residual half-radius wall in `2g < n < 3g` is impossible without
any auxiliary degree premise on the incidence defect: I4 itself determines
the only incidence coefficient that can reach the two decisive rows. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualHalfRadiusI4Wall_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
      2 * g < n)
    (hstrict :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 3 * g)
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
      2 * h = n)
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
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h) :
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
  change 2 * g < n at hsmall
  change n < 3 * g at hstrict
  change 2 * h = n at hwall
  change d.natDegree ≤ 5 * n - h ∧
    ee.natDegree ≤ 6 * n - h at hmiddle
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
  have hDbound : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hrowTwo := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee (by
      rw [hCrec, hDrec, hErec] at h2e
      exact h2e)
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
        Ae Be Ce De Ee) De Ee).coeff (12 * n - 1) = 0 :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal _ _ _ _ _ h0e
      (residualHalfRadiusLoadWallRowZeroIndex68_gt_fiftyNine n h hnlarge hwall)
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta Ae Be ce De ee
  have hsum :
      lowerRowZeroPolynomial68
        (integratedUPolynomial68 l alpha beta gamma delta zeta
          Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) De Ee =
        secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
          cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon
            zeta eta Ae Be ce De ee := by
    rw [hCrec, hErec, hcoords.u_eq, hcoords.v_eq,
      cubicRowZeroPolynomial68_split,
      show cubicHomogeneousRowZeroPolynomial68 Ae Be ce De ee =
          secondaryResidualRowZeroPolynomial68 Ae Be ce d ee by
        simpa [hDrec] using
          cubicHomogeneousRowZeroPolynomial68_residualCoordinates
            Ae Be ce d ee]
  have hzeroCoeff : (secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).coeff (12 * n - 1) = 0 := by
    have hzEq := congrArg (fun p : k[X] => p.coeff (12 * n - 1)) hsum
    simpa [hDrec] using hzEq.symm.trans h0target
  have htwoCoeff := congrArg (fun p : k[X] => p.coeff (10 * n - 1)) hrowTwo
  have htwo :
      (80 / 3 : k) * (n : k) * d.coeff (5 * n - h) *
          ee.coeff (6 * n - h) +
        (35 / 576 : k) * (n : k) * l * Ae.coeff (2 * n) ^ 5 = 0 := by
    rw [← integratedLowerRowTwoPolynomial68_coeff_halfRadiusI4
      l alpha beta gamma delta epsilon zeta eta i4 Ae Be ce d ee n g h
      hn hg hsmall hstrict hwall hA hB hc hmiddle.1 hmiddle.2 hi4c hDbound]
    simpa using htwoCoeff
  have hzero :
      (-8 / 9 : k) * (n : k) * Ae.coeff (2 * n) *
          d.coeff (5 * n - h) * ee.coeff (6 * n - h) +
        (35 / 1728 : k) * (n : k) * l * Ae.coeff (2 * n) ^ 6 = 0 := by
    rw [← integratedLowerRowZeroPolynomial68_coeff_halfRadiusI4
      l alpha beta gamma delta epsilon zeta eta i4 Ae Be ce d ee n g h
      hn hg hsmall hstrict hwall hA hB hc hmiddle.1 hmiddle.2 hi4c hDbound]
    exact hzeroCoeff
  have hl0 := residualHalfRadiusI4_two_zero_force_l (n : k)
    (Ae.coeff (2 * n)) (d.coeff (5 * n - h))
    (ee.coeff (6 * n - h)) l
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) ha htwo hzero
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hl0 (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)

#print axioms residualHalfRadiusI4_two_zero_force_l
#print axioms secondaryResidualRowTwoPolynomial68_coeff_halfRadiusI4
#print axioms secondaryResidualRowZeroPolynomial68_coeff_halfRadiusI4
#print axioms polynomialSecondaryResidualHalfRadiusI4_force_l
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualHalfRadiusI4Wall_impossible68

end Max11DegreeRoutes
