import LowScale68SecondaryDeepGapResidualEndgame

/-! # First-deep middle endgame on the I4 load `(5/72) beta a^3` at `6n`

After the residual double window is closed, the remaining first-deep
chamber is middle `g < h < 2g` with `g + h ≤ 3n`.  I4 being constant
rewrites the incidence defect as `Q = (3/8)(C i4 - I4_load)`, so
`Q.coeff(6n) = -(5/192) beta a^3`.  Residual row-two then sees a pure
Q-feed `(25/32) n beta a^4` at `8n-1`, while the direct beta load is
`(5/18) n beta a^4`.  Combined residual-plus-load is
`(35/216) n beta a^4` once the homogeneous `d*e` face is off that index.

On `n < g` the cubic core is strictly below `8n-1`.  The comparison
`h ? 3n/2` therefore splits the remaining middle:

* `h < 3n/2`: left chamber, ordinary `d e`.
* `h > 3n/2`: `(35/216) n beta a^4 = 0` forces `beta = 0`.
* `h = 3n/2`: mixed scalar `(64/3) n d e + (35/216) n beta a^4`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section DeepGapMiddleBetaEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Degree helpers -/

theorem middleBeta_natDegree_mul_derivative_le68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 0 < v) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (by omega)
  have hmul := natDegree_mul_le_of_le hu hd
  omega

theorem middleBeta_natDegree_derivative_mul_le68
    (p q : k[X]) (u v : ℕ)
    (hu0 : 0 < u) (hu : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (derivative p * q).natDegree ≤ u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hmul := natDegree_mul_le_of_le hd hq
  omega

theorem middleBeta_natDegree_translatedD_le68
    (A B d : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hgh : g < h) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g := by
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have hAB : (A * B).natDegree ≤ 5 * n - g := by
    have hmul := natDegree_mul_le_of_le hA hB
    have hsum : 2 * n + (3 * n - g) = 5 * n - g := by omega
    rwa [hsum] at hmul
  have hABs := (natDegree_smul_le (1 / 3 : k) (A * B)).trans hAB
  have hd' : d.natDegree ≤ 5 * n - g := hd.trans (by omega)
  exact (natDegree_add_le _ _).trans (max_le hABs hd')

/-! ## I4 load and the incidence defect `Q` -/

theorem residualIncidenceQ68_eq_I4 (B c d e : k[X]) :
    secondaryResidualInvariantFourPolynomial68 B c d e =
      (8 / 3 : k) • residualIncidenceQ68 B c d e := by
  simp only [secondaryResidualInvariantFourPolynomial68, residualIncidenceQ68]
  module

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_eq_I4load_of_l_eq_zero
    (beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    residualIncidenceQ68 B c d e =
      (3 / 8 : k) •
        (C i4 -
          secondaryLoadInvariantFourPolynomial68
            0 beta gamma delta epsilon zeta A B c
              ((1 / 3 : k) • (A * B) + d) e) := by
  let D := (1 / 3 : k) • (A * B) + d
  let Q := residualIncidenceQ68 B c d e
  let load := secondaryLoadInvariantFourPolynomial68
    0 beta gamma delta epsilon zeta A B c D e
  have hsplit := hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    residualIncidenceQ68_eq_I4] at hsplit
  change (8 / 3 : k) • Q + load = C i4 at hsplit
  have hcore : (8 / 3 : k) • Q = C i4 - load :=
    eq_sub_of_add_eq hsplit
  calc
    Q = (3 / 8 : k) • ((8 / 3 : k) • Q) := by
      rw [smul_smul]
      norm_num
    _ = (3 / 8 : k) • (C i4 - load) := by rw [hcore]

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_le_sixRadius_of_firstDeep
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree ≤ 6 * n := by
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_degree_le_sixRadius_of_firstDeep
    (beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hQeq := residualIncidenceQ68_eq_I4load_of_l_eq_zero
    beta gamma delta epsilon zeta i4 A B c d e hi4
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_le_sixRadius_of_firstDeep
      beta gamma delta epsilon zeta A B c D e n g hn hrel hA hB hc hD he
  rw [hQeq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_coeff_sixRadius_of_firstDeep
    (beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hQeq := residualIncidenceQ68_eq_I4load_of_l_eq_zero
    beta gamma delta epsilon zeta i4 A B c d e hi4
  have hload :=
    secondaryLoadInvariantFourPolynomial68_coeff_sixRadius_of_l_eq_zero
      beta gamma delta epsilon zeta A B c D e n g hn hg hA hB hc hD he
  have hindex : 6 * n ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by decide : 0 < 6) hn)
  rw [hQeq, coeff_smul, coeff_sub, coeff_C, if_neg hindex, smul_eq_mul]
  rw [show D = (1 / 3 : k) • (A * B) + d from rfl] at hload
  rw [hload]
  ring

theorem middleBetaQInnerScalar68 (N a q0 : k) :
    (-6 : k) * (a * q0 * (6 * N)) + (3 : k) * (a * q0 * (2 * N)) =
      (-30 : k) * N * a * q0 := by
  ring

theorem middleBetaQInner_of_I4load68 (N a beta : k) :
    (-30 : k) * N * a * (-((5 / 192 : k) * beta * a ^ 3)) =
      (25 / 32 : k) * N * beta * a ^ 4 := by
  ring

/-! ## Homogeneous inner degrees on `n < g` -/

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_de_degree_le68_of_firstDeep
    (d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hrel : 2 * g < 3 * n)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (derivative (d * e)).natDegree ≤ 11 * n - 2 * h - 1 := by
  have hprod := natDegree_mul_le_of_le hd he
  have hsum : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hsum] at hprod
  have hder := natDegree_derivative_le (d * e)
  omega

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_Bd_degree_le68_of_firstDeep
    (B d : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hrel : 2 * g < 3 * n)
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
theorem residualRowTwoInner_BcCore_degree_le68_of_firstDeep
    (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (A * B ^ 2 * derivative B).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative A * B ^ 3).natDegree ≤ 11 * n - 3 * g - 1 ∧
      (derivative (B * c ^ 2)).natDegree ≤ 11 * n - 3 * g - 1 := by
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
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

/-! ## Residual row two at `8n-1` -/

set_option maxHeartbeats 4000000 in
theorem residualRowTwoInner_coeff_eightRadius_of_firstDeep_high
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hhigh : 3 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (beta : k)
    (hq0 : (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3)) :
    (residualRowTwoInner68 A B c d e).coeff (8 * n - 1) =
      (25 / 32 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 8 * n - 1
  have hAQ := coeff_mul_derivative_at_bounds68 A Q (2 * n) (6 * n)
    (by omega) hA hQ
  have hiAQ : 2 * n + 6 * n - 1 = idx := by dsimp [idx]; omega
  rw [hiAQ] at hAQ
  have hQA := coeff_mul_derivative_at_bounds68 Q A (6 * n) (2 * n)
    (by omega) hQ hA
  have hiQA : 6 * n + 2 * n - 1 = idx := by dsimp [idx]; omega
  rw [hiQA] at hQA
  have hA3' : (derivative A * Q).coeff idx =
      A.coeff (2 * n) * Q.coeff (6 * n) * ((2 * n : ℕ) : k) := by
    rw [show (derivative A * Q).coeff idx = (Q * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hQA
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_firstDeep A B c n g
    hn hg hrel hA hB hc
  have hidx_cubic : 11 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    omega
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
  have hde := residualRowTwoInner_de_degree_le68_of_firstDeep d e n g h
    hg hgh hh hrel hd he
  have hde' : (derivative (d * e)).natDegree < idx := by
    dsimp [idx]
    omega
  have hcast6 : (((6 * n : ℕ) : k)) = (6 : k) * (n : k) := by
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have h0AB : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAB, mul_zero]
  have h0A3 : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hA3, mul_zero]
  have h0Bc : ((6 : k) • derivative (B * c ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBc, mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0de : ((-18 : k) • derivative (d * e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hde', mul_zero]
  have hQsm : ((-6 : k) • (A * derivative Q)).coeff idx =
      (-6 : k) * (A.coeff (2 * n) * Q.coeff (6 * n) *
        ((6 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hAQ]
  have hQ'sm : ((3 : k) • (derivative A * Q)).coeff idx =
      (3 : k) * (A.coeff (2 * n) * Q.coeff (6 * n) *
        ((2 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hA3']
  dsimp [inner, residualRowTwoInner68]
  simp only [coeff_add]
  rw [h0AB, h0A3, h0Bc, h0Bd, h0de, hQsm, hQ'sm]
  simp only [add_zero, zero_add]
  rw [hcast6, hcast2, hq0]
  have hscal := middleBetaQInnerScalar68 (n : k) (A.coeff (2 * n))
    (-((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3))
  rw [hscal]
  exact middleBetaQInner_of_I4load68 (n : k) (A.coeff (2 * n)) beta

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_coeff_eightRadius_of_firstDeep_high
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hhigh : 3 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (beta : k)
    (hq0 : (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3)) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (8 * n - 1) =
      (-25 / 216 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 := by
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul,
    residualRowTwoInner_coeff_eightRadius_of_firstDeep_high A B c d e n g h
      hn hg hgh hh hgt hrel hhigh hA hB hc hd he hQ beta hq0]
  ring

/-! ## Direct beta row-two load at `8n-1` -/

theorem middleBetaLoadScalar68 (N a beta : k) :
    (5 / 24 * beta : k) * a ^ 2 * ((1 / 3 : k) * a ^ 2) * (4 * N) +
      (3 : k) * ((5 / 6 * beta : k) * a) * ((1 / 27 : k) * a ^ 3) *
        (6 * N) -
      (2 : k) * ((1 / 3 : k) * a ^ 2) * ((5 / 24 * beta : k) * a ^ 2) *
        (4 * N) =
      (5 / 18 : k) * N * beta * a ^ 4 := by
  ring

set_option maxHeartbeats 2000000 in
theorem cubicLoadSPolynomial68_coeff_twoRadius_of_firstDeep
    (alpha beta delta : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hgt : n < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g) :
    (cubicLoadSPolynomial68 0 alpha beta delta A B c).coeff (2 * n) =
      (5 / 6 * beta : k) * A.coeff (2 * n) := by
  have heq : cubicLoadSPolynomial68 0 alpha beta delta A B c =
      alpha • B + (5 / 6 * beta : k) • A + C delta := by
    simp [cubicLoadSPolynomial68, zero_mul, mul_zero, zero_smul, smul_zero,
      add_zero]
  have hBlt : B.natDegree < 2 * n := hB.trans_lt (by omega)
  have hC : (C delta).coeff (2 * n) = 0 := by
    have hnz : 2 * n ≠ 0 := by omega
    simp [coeff_C, hnz]
  rw [heq, coeff_add, coeff_add, coeff_smul, coeff_smul, smul_eq_mul,
    smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBlt, hC, mul_zero,
    add_zero, zero_add]

set_option maxHeartbeats 2000000 in
theorem cubicLoadUPolynomial68_coeff_fourRadius_of_firstDeep
    (alpha beta gamma delta zeta : k) (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g) :
    (cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e).coeff
        (4 * n) =
      (5 / 24 * beta : k) * A.coeff (2 * n) ^ 2 := by
  have heq : cubicLoadUPolynomial68 0 alpha beta gamma delta zeta
        A B c D e =
      alpha • D + (5 / 24 * beta : k) • A ^ 2 +
        (5 / 6 * beta : k) • c + (2 / 3 * gamma : k) • B +
        (1 / 2 * delta : k) • A + C zeta := by
    simp [cubicLoadUPolynomial68, zero_mul, mul_zero, zero_smul, smul_zero,
      add_zero]
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hi : 2 * (2 * n) = 4 * n := by omega
  rw [hi] at hA2
  have hDlt : D.natDegree < 4 * n := hD.trans_lt (by omega)
  have hclt : c.natDegree < 4 * n := hc.trans_lt (by omega)
  have hBlt : B.natDegree < 4 * n := hB.trans_lt (by omega)
  have hAlt : A.natDegree < 4 * n := hA.trans_lt (by omega)
  have hC : (C zeta).coeff (4 * n) = 0 := by
    have hnz : 4 * n ≠ 0 := by omega
    simp [coeff_C, hnz]
  rw [heq]
  simp only [coeff_add, coeff_smul, smul_eq_mul, hA2,
    coeff_eq_zero_of_natDegree_lt hDlt, coeff_eq_zero_of_natDegree_lt hclt,
    coeff_eq_zero_of_natDegree_lt hBlt, coeff_eq_zero_of_natDegree_lt hAlt,
    hC, mul_zero, add_zero, zero_add]

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowTwoPolynomial68_degree_le_eightRadius_of_firstDeep
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree ≤ 8 * n - 1 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 0 alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 0 alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
    A B c D e
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have hSl : Sl.natDegree ≤ 2 * n := by
    have h := cubicLoadSPolynomial68_degreeBound_of_loadL 0 alpha beta delta
      A B c n g rfl hA hB hc
    have hmax : max (2 * n) (3 * n - g) = 2 * n := by omega
    rwa [hmax] at h
  have hTl : Tl.natDegree ≤ 4 * n :=
    cubicLoadTPolynomial68_degreeBound_of_loadL 0 alpha beta gamma epsilon
      A B c D n g rfl hA hB hc hD
  have hUl : Ul.natDegree ≤ 4 * n := by
    have h := cubicLoadUPolynomial68_degreeBound_of_loadL 0 alpha beta gamma
      delta zeta A B c D e n g rfl hA hB hc hD he
    have hmax : max (4 * n) (5 * n - g) = 4 * n := by omega
    rwa [hmax] at h
  have hVl : Vl.natDegree ≤ 6 * n :=
    cubicLoadVPolynomial68_degreeBound_of_loadL 0 alpha beta gamma delta
      epsilon eta A B c D e n g rfl hA hB hc hD he
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]; compute_degree; omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]; compute_degree; omega
  have h1 : (Ul * derivative C0).natDegree ≤ 8 * n - 1 := by
    have h := middleBeta_natDegree_mul_derivative_le68 Ul C0 (4 * n) (4 * n)
      hUl (by omega) hC0
    have hi : 4 * n + 4 * n - 1 = 8 * n - 1 := by omega
    rwa [hi] at h
  have h2 : ((2 : k) • (Tl * derivative D)).natDegree ≤ 8 * n - 1 := by
    have h := middleBeta_natDegree_mul_derivative_le68 Tl D (4 * n)
      (5 * n - g) hTl (by omega) hD
    have hi : 4 * n + (5 * n - g) - 1 = 9 * n - g - 1 := by omega
    have hTD : (Tl * derivative D).natDegree ≤ 9 * n - g - 1 := by
      rwa [hi] at h
    exact (natDegree_smul_le (2 : k) (Tl * derivative D)).trans
      (hTD.trans (by omega))
  have h3 : ((3 : k) • (Sl * derivative E)).natDegree ≤ 8 * n - 1 := by
    have h := middleBeta_natDegree_mul_derivative_le68 Sl E (2 * n) (6 * n)
      hSl (by omega) hE
    have hi : 2 * n + 6 * n - 1 = 8 * n - 1 := by omega
    exact (natDegree_smul_le (3 : k) (Sl * derivative E)).trans
      (by rwa [hi] at h)
  have h4 : ((3 : k) • (B * derivative Vl)).natDegree ≤ 8 * n - 1 := by
    have h := middleBeta_natDegree_mul_derivative_le68 B Vl (3 * n - g)
      (6 * n) hB (by omega) hVl
    have hi : 3 * n - g + 6 * n - 1 = 9 * n - g - 1 := by omega
    have hBV : (B * derivative Vl).natDegree ≤ 9 * n - g - 1 := by
      rwa [hi] at h
    exact (natDegree_smul_le (3 : k) (B * derivative Vl)).trans
      (hBV.trans (by omega))
  have h5 : ((2 : k) • (C0 * derivative Ul)).natDegree ≤ 8 * n - 1 := by
    have h := middleBeta_natDegree_mul_derivative_le68 C0 Ul (4 * n) (4 * n)
      hC0 (by omega) hUl
    have hi : 4 * n + 4 * n - 1 = 8 * n - 1 := by omega
    exact (natDegree_smul_le (2 : k) (C0 * derivative Ul)).trans
      (by rwa [hi] at h)
  have h6 : (D * derivative Tl).natDegree ≤ 8 * n - 1 := by
    have h := middleBeta_natDegree_mul_derivative_le68 D Tl (5 * n - g)
      (4 * n) hD (by omega) hTl
    have hi : 5 * n - g + 4 * n - 1 = 9 * n - g - 1 := by omega
    have hDT : (D * derivative Tl).natDegree ≤ 9 * n - g - 1 := by
      rwa [hi] at h
    exact hDT.trans (by omega)
  change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
      (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
      (2 : k) • (C0 * derivative Ul) - D * derivative Tl).natDegree ≤ _
  refine (natDegree_sub_le _ _).trans (max_le ?_ h6)
  refine (natDegree_sub_le _ _).trans (max_le ?_ h5)
  refine (natDegree_sub_le _ _).trans (max_le ?_ h4)
  refine (natDegree_add_le _ _).trans (max_le ?_ h3)
  exact (natDegree_add_le _ _).trans (max_le h1 h2)

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoPolynomial68_coeff_eightRadius_of_firstDeep
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g) (hrel : 2 * g < 3 * n)
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
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
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

/-! ## Combined residual-plus-load at `8n-1` on `h > 3n/2` -/

theorem residualRowTwo_add_load_coeff_eightRadius_of_firstDeep_high
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hhigh : 3 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (he' : e.natDegree ≤ 6 * n - g)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (hq0 : (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3)) :
    (secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff (8 * n - 1) =
      (35 / 216 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 := by
  rw [coeff_add,
    residualRowTwo_coeff_eightRadius_of_firstDeep_high A B c d e n g h
      hn hg hgh hh hgt hrel hhigh hA hB hc hd he hQ beta hq0,
    cubicLoadRowTwoPolynomial68_coeff_eightRadius_of_firstDeep
      alpha beta gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g hn hg hgt hrel hA hB hc hD he']
  ring

theorem residualRowTwo_add_load_eightRadius_forces_beta_of_firstDeep_high
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hhigh : 3 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (he' : e.natDegree ≤ 6 * n - g)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (hq0 : (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3))
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    beta = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (8 * n - 1)) hsum
  rw [coeff_zero,
    residualRowTwo_add_load_coeff_eightRadius_of_firstDeep_high
      alpha beta gamma delta epsilon zeta eta A B c d e n g h
      hn hg hgh hh hgt hrel hhigh hA hB hc hd he he' hD hQ hq0] at hcoeff
  have hn0 : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsc : (35 / 216 : k) ≠ 0 := by norm_num
  have ha4 : A.coeff (2 * n) ^ 4 ≠ 0 := pow_ne_zero 4 ha
  have hassoc :
      (35 / 216 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 =
        ((35 / 216 : k) * (n : k) * A.coeff (2 * n) ^ 4) * beta := by
    ring
  rw [hassoc] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left
    (mul_ne_zero (mul_ne_zero hsc hn0) ha4)

/-! ## Left chamber `h < 3n/2` after the Q-rewrite -/

set_option maxHeartbeats 4000000 in
theorem residualRowTwo_coeff_leftChamber_of_firstDeep_low
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hlow : 2 * h < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) =
      (8 / 3 : k) * ((11 * n - 2 * h : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 2 * h - 1
  have hidx8 : 8 * n - 1 < idx := by
    dsimp [idx]
    omega
  have hidx_cubic : 11 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    omega
  have hAQ : (A * derivative Q).natDegree < idx := by
    have h := middleBeta_natDegree_mul_derivative_le68 A Q (2 * n) (6 * n)
      hA (by omega) hQ
    have hi : 2 * n + 6 * n - 1 = 8 * n - 1 := by omega
    have hle : (A * derivative Q).natDegree ≤ 8 * n - 1 := by
      simpa only [hi] using h
    exact hle.trans_lt hidx8
  have hAQ' : (derivative A * Q).natDegree < idx := by
    have h := middleBeta_natDegree_derivative_mul_le68 A Q (2 * n) (6 * n)
      (by omega) hA hQ
    have hi : 2 * n + 6 * n - 1 = 8 * n - 1 := by omega
    have hle : (derivative A * Q).natDegree ≤ 8 * n - 1 := by
      simpa only [hi] using h
    exact hle.trans_lt hidx8
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

theorem residualRowTwo_leftChamber_ne_zero_of_firstDeep_low
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hlow : 2 * h < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_leftChamber_of_firstDeep_low A B c d e n g h
    hn hg hgh hh hgt hrel hlow hA hB hc hd he hQ]
  have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 2 * h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) hd0) he0

theorem residualRowTwo_not_leftChamber_of_firstDeep_low
    (A B c d e load : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hlow : 2 * h < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (hload : load.natDegree < 11 * n - 2 * h - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    False := by
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68
    A B c d e load (11 * n - 2 * h - 1) hload hsum
  exact residualRowTwo_leftChamber_ne_zero_of_firstDeep_low A B c d e n g h
    hn hg hgh hh hgt hrel hlow hA hB hc hd he hQ hd0 he0 hcoeff0

/-! ## Mixed wall `2h = 3n`: ordinary `d e` plus the I4 Q-feed -/

theorem middleBetaMixedResidualScalar68 (N d e a beta : k) :
    (-4 / 27 : k) *
        ((25 / 32 : k) * N * beta * a ^ 4 +
          (-18 : k) * (d * e * (8 * N))) =
      (-25 / 216 : k) * N * beta * a ^ 4 +
        (64 / 3 : k) * N * d * e := by
  ring

theorem middleBetaMixedSumScalar68 (N d e a beta : k) :
    (-25 / 216 : k) * N * beta * a ^ 4 +
      (64 / 3 : k) * N * d * e +
      (5 / 18 : k) * N * beta * a ^ 4 =
      (64 / 3 : k) * N * d * e +
        (35 / 216 : k) * N * beta * a ^ 4 := by
  ring

set_option maxHeartbeats 4000000 in
theorem residualRowTwoInner_coeff_eightRadius_of_firstDeep_wall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hwall : 2 * h = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (beta : k)
    (hq0 : (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3)) :
    (residualRowTwoInner68 A B c d e).coeff (8 * n - 1) =
      (25 / 32 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 +
        (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
          ((8 * n : ℕ) : k)) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 8 * n - 1
  have hAQ := coeff_mul_derivative_at_bounds68 A Q (2 * n) (6 * n)
    (by omega) hA hQ
  have hiAQ : 2 * n + 6 * n - 1 = idx := by dsimp [idx]; omega
  rw [hiAQ] at hAQ
  have hQA := coeff_mul_derivative_at_bounds68 Q A (6 * n) (2 * n)
    (by omega) hQ hA
  have hiQA : 6 * n + 2 * n - 1 = idx := by dsimp [idx]; omega
  rw [hiQA] at hQA
  have hA3' : (derivative A * Q).coeff idx =
      A.coeff (2 * n) * Q.coeff (6 * n) * ((2 * n : ℕ) : k) := by
    rw [show (derivative A * Q).coeff idx = (Q * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hQA
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_firstDeep A B c n g
    hn hg hrel hA hB hc
  have hidx_cubic : 11 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    omega
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
  have hide : (5 * n - h) + (6 * n - h) = 8 * n := by omega
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 8 * n := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (8 * n) hder0
  rw [hdecoeff] at hde
  have hcast6 : (((6 * n : ℕ) : k)) = (6 : k) * (n : k) := by
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have h0AB : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAB, mul_zero]
  have h0A3 : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hA3, mul_zero]
  have h0Bc : ((6 : k) • derivative (B * c ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBc, mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((8 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hde]
  have hQsm : ((-6 : k) • (A * derivative Q)).coeff idx =
      (-6 : k) * (A.coeff (2 * n) * Q.coeff (6 * n) *
        ((6 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hAQ]
  have hQ'sm : ((3 : k) • (derivative A * Q)).coeff idx =
      (3 : k) * (A.coeff (2 * n) * Q.coeff (6 * n) *
        ((2 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hA3']
  have hQpart :
      (-6 : k) * (A.coeff (2 * n) * Q.coeff (6 * n) *
          ((6 * n : ℕ) : k)) +
        (3 : k) * (A.coeff (2 * n) * Q.coeff (6 * n) *
          ((2 * n : ℕ) : k)) =
        (25 / 32 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 := by
    rw [hcast6, hcast2, hq0]
    have hscal := middleBetaQInnerScalar68 (n : k) (A.coeff (2 * n))
      (-((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3))
    rw [hscal]
    exact middleBetaQInner_of_I4load68 (n : k) (A.coeff (2 * n)) beta
  dsimp [inner, residualRowTwoInner68]
  simp only [coeff_add]
  rw [h0AB, h0A3, h0Bc, h0Bd, hde', hQsm, hQ'sm]
  simp only [add_zero, zero_add]
  linear_combination hQpart

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_coeff_eightRadius_of_firstDeep_wall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hwall : 2 * h = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (beta : k)
    (hq0 : (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3)) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (8 * n - 1) =
      (-25 / 216 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 +
        (64 / 3 : k) * (n : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul,
    residualRowTwoInner_coeff_eightRadius_of_firstDeep_wall A B c d e n g h
      hn hg hgh hh hgt hrel hwall hA hB hc hd he hQ beta hq0]
  have hcast8 : ((8 * n : ℕ) : k) = 8 * (n : k) := by push_cast; rfl
  rw [hcast8]
  ring

theorem residualRowTwo_add_load_coeff_eightRadius_of_firstDeep_wall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hwall : 2 * h = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (he' : e.natDegree ≤ 6 * n - g)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (hq0 : (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3)) :
    (secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff (8 * n - 1) =
      (64 / 3 : k) * (n : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        (35 / 216 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 := by
  rw [coeff_add,
    residualRowTwo_coeff_eightRadius_of_firstDeep_wall A B c d e n g h
      hn hg hgh hh hgt hrel hwall hA hB hc hd he hQ beta hq0,
    cubicLoadRowTwoPolynomial68_coeff_eightRadius_of_firstDeep
      alpha beta gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g hn hg hgt hrel hA hB hc hD he']
  ring

/-! ## Canonical middle theorems -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleLow_impossible68
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
    (hlow :
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
      h < 2 * g ∧ 2 * h < 3 * n ∧ g + h < 3 * n) :
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
  change h < 2 * g ∧ 2 * h < 3 * n ∧ g + h < 3 * n at hlow
  have hobs :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirst_obstruction68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
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
  have hgh : g < h := hsel.2.2.2.2.1
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
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl] at hi4c
  have hD' : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g :=
    middleBeta_natDegree_translatedD_le68 Ae Be d n g h
      hn hgh hchamber.2 hA hB hd
  have hQle := residualIncidenceQ68_degree_le_sixRadius_of_firstDeep
    beta gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hchamber.2
    hA hB hc (hd.trans (by omega)) he' hi4c
  have hface : SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
      (d.coeff (5 * n - h)) (ee.coeff (6 * n - h)) :=
    ⟨hobs.2.1 hlow.2.2, hsel.2.2.2.2.2.2.2.three_middle hlow.1⟩
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
  rw [hl] at hrowTwo
  have hload :
      (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
          11 * n - 2 * h - 1 := by
    have hle :=
      cubicLoadRowTwoPolynomial68_degree_le_eightRadius_of_firstDeep
        alpha beta gamma delta epsilon zeta eta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hg0 hchamber.1 hchamber.2
        hA hB hc hD' he'
    have hlt : 8 * n - 1 < 11 * n - 2 * h - 1 := by omega
    exact hle.trans_lt hlt
  exact residualRowTwo_not_leftChamber_of_firstDeep_low Ae Be ce d ee
    (cubicLoadRowTwoPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
    n g h hn hg0 (hsel.2.2.2.2.1) hlow.1 hchamber.1 hchamber.2 hlow.2.1
    hA hB hc hd hee hQle hload hrowTwo hclass.2.2.1 hclass.2.2.2.1

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleHigh_beta_eq_zero68
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
      h < 2 * g ∧ 3 * n < 2 * h) :
    beta = 0 := by
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
  change h < 2 * g ∧ 3 * n < 2 * h at hhigh
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
  have hgh : g < h := hsel.2.2.2.2.1
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
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl] at hi4c
  have hD' : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g :=
    middleBeta_natDegree_translatedD_le68 Ae Be d n g h
      hn hgh hchamber.2 hA hB hd
  have hQle := residualIncidenceQ68_degree_le_sixRadius_of_firstDeep
    beta gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hchamber.2
    hA hB hc (hd.trans (by omega)) he' hi4c
  have hq0 := residualIncidenceQ68_coeff_sixRadius_of_firstDeep
    beta gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hg0
    hA hB hc hD' he' hi4c
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
  rw [hl] at hrowTwo
  exact residualRowTwo_add_load_eightRadius_forces_beta_of_firstDeep_high
    alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
    hn hg0 (hsel.2.2.2.2.1) hhigh.1 hchamber.1 hchamber.2 hhigh.2
    hA hB hc hd hee he' hD' ha hQle hq0 hrowTwo

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleWall_scalar68
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
    (64 / 3 : k) * (n : k) *
        d.coeff (5 * n - h) * ee.coeff (6 * n - h) +
      (35 / 216 : k) * (n : k) * beta * Ae.coeff (2 * n) ^ 4 = 0 := by
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
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hgh : g < h := hsel.2.2.2.2.1
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
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl] at hi4c
  have hD' : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g :=
    middleBeta_natDegree_translatedD_le68 Ae Be d n g h
      hn hgh hchamber.2 hA hB hd
  have hQle := residualIncidenceQ68_degree_le_sixRadius_of_firstDeep
    beta gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hchamber.2
    hA hB hc (hd.trans (by omega)) he' hi4c
  have hq0 := residualIncidenceQ68_coeff_sixRadius_of_firstDeep
    beta gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hg0
    hA hB hc hD' he' hi4c
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
  rw [hl] at hrowTwo
  have hcoeff := congrArg (fun p : k[X] => p.coeff (8 * n - 1)) hrowTwo
  rw [coeff_zero,
    residualRowTwo_add_load_coeff_eightRadius_of_firstDeep_wall
      alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
      hn hg0 (hsel.2.2.2.2.1) hwall.1 hchamber.1 hchamber.2 hwall.2
      hA hB hc hd hee he' hD' hQle hq0] at hcoeff
  exact hcoeff

/-- First-deep remaining middle after this file: `h < 2g` and `3n ≤ 2h`.
The open wall `2h = 3n` mixes ordinary `d e` with the I4 Q-feed, giving
the scalar `(64/3) n d e + (35/216) n beta a^4`.  On `3n < 2h`
(including the mixed I4 wall `h = 3n-g`) one already has `beta = 0`.
The next coefficient needed to close `2h = 3n` is residual row-one at
`9n-1`.  After `beta = 0` on `3n < 2h`, the next coefficient is the
residual inner at the `d e` / cubic faces under `Q.natDegree < 6n`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddle_obstruction68
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
    h < 2 * g ∧ 3 * n ≤ 2 * h ∧
      (3 * n < 2 * h → beta = 0) ∧
      (2 * h = 3 * n →
        (64 / 3 : k) * (n : k) *
            d.coeff (5 * n - h) * ee.coeff (6 * n - h) +
          (35 / 216 : k) * (n : k) * beta *
            Ae.coeff (2 * n) ^ 4 = 0) := by
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
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirst_obstruction68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
  have hh : h < 2 * g := hobs.1
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualSelect68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          And.intro (by omega : n < 2 * g) hchamber.2)
  have hgh : g < h := hsel.2.2.2.2.1
  have hge : 3 * n ≤ 2 * h := by
    by_contra hlt
    have h2 : 2 * h < 3 * n := Nat.lt_of_not_ge hlt
    have hsum : g + h < 3 * n := by omega
    exact maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleLow_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
        And.intro hh (And.intro h2 hsum))
  refine ⟨hh, hge, ?_, ?_⟩
  · intro hgt
    exact maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleHigh_beta_eq_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
        And.intro hh hgt)
  · intro hwall
    exact maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleWall_scalar68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
        And.intro hh hwall)

end DeepGapMiddleBetaEndgame68

end Max11DegreeRoutes
