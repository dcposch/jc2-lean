import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentFiveRowZeroEndgame

/-! # Row-zero closure of the strict right exact-five wall

On `3g = 5n < 2h`, the `d*e` face has dropped below degree `8n-1`.
The attained `Q(4n)` edge, the fixed `B,c` face, and the `delta` row-zero
load contradict the normalized right row-two packet.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighRightFiveRowZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The attained incidence edge -/

set_option maxHeartbeats 3000000 in
theorem residualIncidenceQ68_degree_le_fourRadius_of_rightFive
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hwallG : 3 * g = 5 * n) (haboveH : 5 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n := by
  have hQeq := residualIncidenceQ68_eq_I4load_of_alphaWall
    0 gamma delta epsilon zeta i4 A B c d e hi4
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta]
    at hQeq
  rw [hQeq]
  compute_degree
  omega

set_option maxHeartbeats 4000000 in
theorem residualIncidenceQ68_coeff_fourRadius_of_rightFive
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hwallG : 3 * g = 5 * n) (haboveH : 5 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).coeff (4 * n) =
      -(3 / 32 : k) * delta * A.coeff (2 * n) ^ 2 := by
  have hQeq := residualIncidenceQ68_eq_I4load_of_alphaWall
    0 gamma delta epsilon zeta i4 A B c d e hi4
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta]
    at hQeq
  have hA2 := coeff_pow_at_bound68 A (2 * n) 2 hA
  have hiA : 2 * (2 * n) = 4 * n := by omega
  rw [hiA] at hA2
  have hAlt : A.natDegree < 4 * n := hA.trans_lt (by omega)
  have hBlt : B.natDegree < 4 * n := hB.trans_lt (by omega)
  have hclt : c.natDegree < 4 * n := hc.trans_lt (by omega)
  have hdlt : d.natDegree < 4 * n := hd.trans_lt (by omega)
  have hindex : 4 * n ≠ 0 := by omega
  rw [hQeq, coeff_smul, coeff_sub, coeff_C, if_neg hindex,
    coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_smul, coeff_smul, coeff_smul, coeff_smul, coeff_smul,
    smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hAlt,
    coeff_eq_zero_of_natDegree_lt hBlt,
    hA2,
    coeff_eq_zero_of_natDegree_lt hclt,
    coeff_eq_zero_of_natDegree_lt hdlt]
  ring

/-! ## Right row-two scalar -/

theorem laterDeepFiveSumReducedRowTwo_rightFive_packet68
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwallG : 3 * g = 5 * n) (haboveH : 5 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrow : laterDeepFiveSumReducedRowTwoPolynomial68
      gamma delta epsilon zeta i4 A B c d e = 0) :
    (15 : k) * delta * A.coeff (2 * n) ^ 3 -
      (256 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 = 0 := by
  have hrel := laterDeepFiveSumReducedRowTwo_rightFive_relation68
    gamma delta epsilon zeta i4 A B c d e n g h hn hg hgh hh hopen
    hwallG haboveH hA hB hc hd he hdisc hrow
  have hNG : 11 * n - 3 * g = 6 * n := by omega
  rw [hNG] at hrel
  push_cast at hrel
  have hnK : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hfactor : (n : k) *
      ((15 : k) * delta * A.coeff (2 * n) ^ 3 -
        (256 : k) * B.coeff (3 * n - g) *
          c.coeff (4 * n - g) ^ 2) = 0 := by
    linear_combination (36 : k) * hrel -
      (256 / 3 : k) * (n : k) * B.coeff (3 * n - g) * hdisc
  exact (mul_eq_zero.mp hfactor).resolve_left hnK

/-! ## Exact residual row zero -/

set_option maxHeartbeats 14000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_rightFive
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwallG : 3 * g = 5 * n) (haboveH : 5 * n < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (8 * n - 1) =
      (4 / 27 : k) * ((2 : k) * (n : k) * A.coeff (2 * n) *
        (-(A.coeff (2 * n) *
            (residualIncidenceQ68 B c d e).coeff (4 * n)) -
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9 +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2)) := by
  let Q := residualIncidenceQ68 B c d e
  let idx := 8 * n - 1
  change (secondaryResidualRowZeroPolynomial68 A B c d e).coeff idx =
    (4 / 27 : k) * ((2 : k) * (n : k) * A.coeff (2 * n) *
      (-(A.coeff (2 * n) * Q.coeff (4 * n)) -
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9 +
        B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2))
  have hAQ := coeff_mul_mul_derivative_at_bounds68 A Q A
    (2 * n) (4 * n) (2 * n) (by omega) hA hQ hA
  have hiAQ : 2 * n + 4 * n + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAQ] at hAQ
  have hAQ' : (A * derivative A * Q).coeff idx =
      A.coeff (2 * n) ^ 2 * Q.coeff (4 * n) * ((2 * n : ℕ) : k) := by
    rw [show (A * derivative A * Q).coeff idx =
        (A * Q * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hAQ
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have ht := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using ht
  have hAB3 := coeff_mul_mul_derivative_at_bounds68 A (B ^ 3) A
    (2 * n) (9 * n - 3 * g) (2 * n) (by omega) hA hB3deg hA
  have hiAB3 : 2 * n + (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB3, hB3] at hAB3
  have hAB3' : (A * derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (A * derivative A * B ^ 3).coeff idx =
        (A * B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hAB3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have ht := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using ht
  have hBc2 := coeff_mul_mul_derivative_at_bounds68 B (c ^ 2) A
    (3 * n - g) (8 * n - 2 * g) (2 * n) (by omega) hB hc2deg hA
  have hiBc2 : (3 * n - g) + (8 * n - 2 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiBc2, hc2] at hBc2
  have hBc2' : (derivative A * B * c ^ 2).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B * c ^ 2).coeff idx =
        (B * c ^ 2 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hBc2
  have h0Ade : (derivative A * d * e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0d : (A * B ^ 2 * derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0Bd : (A * B * derivative B * d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0Be : (B * c * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0dd : (B * d * derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0Bd2 : (derivative B * d ^ 2).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0cc : (c * derivative c * d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hBe_cd := residualRowZero_Be_cd_eq_Q A B c d e
  have hBe :
      (A * derivative A * B * e + A * derivative A * c * d).coeff idx =
        (A * derivative A * Q).coeff idx +
          ((1 / 9 : k) • (A * derivative A * B ^ 3)).coeff idx := by
    have ht := congrArg (fun p : k[X] => p.coeff idx) hBe_cd
    simpa only [Q, coeff_add, coeff_smul] using ht
  have hcast2 : ((2 * n : ℕ) : k) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hinner :
      (-(1 : k) • (A * derivative A * B * e) -
          A * derivative A * c * d -
          A * B ^ 2 * derivative d -
          A * B * derivative B * d +
          derivative A * B * c ^ 2 -
          (3 : k) • (derivative A * d * e) +
          (3 : k) • (B * c * derivative e) -
          (3 : k) • (B * d * derivative d) -
          (3 : k) • (derivative B * d ^ 2) -
          (3 : k) • (c * derivative c * d)).coeff idx =
        (2 : k) * (n : k) * A.coeff (2 * n) *
          (-(A.coeff (2 * n) * Q.coeff (4 * n)) -
            A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9 +
            B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) := by
    simp only [coeff_smul, smul_eq_mul, coeff_add, coeff_sub,
      coeff_eq_zero_of_natDegree_lt h0Ade,
      coeff_eq_zero_of_natDegree_lt h0d,
      coeff_eq_zero_of_natDegree_lt h0Bd,
      coeff_eq_zero_of_natDegree_lt h0Be,
      coeff_eq_zero_of_natDegree_lt h0dd,
      coeff_eq_zero_of_natDegree_lt h0Bd2,
      coeff_eq_zero_of_natDegree_lt h0cc, mul_zero]
    have hsum :
        -1 * (A * derivative A * B * e).coeff idx -
            (A * derivative A * c * d).coeff idx =
          -((A * derivative A * B * e +
            A * derivative A * c * d).coeff idx) := by
      rw [coeff_add]
      ring
    rw [hsum, hBe, coeff_smul, smul_eq_mul, hAQ', hAB3', hBc2', hcast2]
    ring
  rw [secondaryResidualRowZeroPolynomial68, coeff_smul, smul_eq_mul, hinner]

/-! ## Scalar and polynomial contradiction -/

theorem rightFive_rowZero_scalar_inconsistent68
    (N a b c delta : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (hdelta : delta ≠ 0)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hpacket : (15 : k) * delta * a ^ 3 - (256 : k) * b * c ^ 2 = 0)
    (hzero : (8 / 27 : k) * N * a *
          ((3 / 32 : k) * delta * a ^ 3 - a * b ^ 3 / 9 + b * c ^ 2) +
        (1 / 9 : k) * N * delta * a ^ 4 = 0) : False := by
  have hNa : N * a ≠ 0 := mul_ne_zero hN ha
  have hinner :
      (8 / 27 : k) *
          ((3 / 32 : k) * delta * a ^ 3 - a * b ^ 3 / 9 + b * c ^ 2) +
        (1 / 9 : k) * delta * a ^ 3 = 0 := by
    have hfactor : N * a *
        ((8 / 27 : k) *
            ((3 / 32 : k) * delta * a ^ 3 - a * b ^ 3 / 9 + b * c ^ 2) +
          (1 / 9 : k) * delta * a ^ 3) = 0 := by
      linear_combination hzero
    exact (mul_eq_zero.mp hfactor).resolve_left hNa
  have hx : (35 : k) * (delta * a ^ 3) = 0 := by
    linear_combination (216 : k) * hinner +
      (64 / 9 : k) * b * hdisc + (1 / 3 : k) * hpacket
  have hda : delta * a ^ 3 = 0 :=
    (mul_eq_zero.mp hx).resolve_left (by norm_num)
  exact hdelta ((mul_eq_zero.mp hda).resolve_right (pow_ne_zero 3 ha))

set_option maxHeartbeats 12000000 in
theorem laterDeepLowerOpenMiddle_rightFive_rowZero_inconsistent68
    (alpha gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwallG : 3 * g = 5 * n) (haboveH : 5 * n < 2 * h)
    (ha : A.coeff (2 * n) ≠ 0) (hdelta : delta ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrow2 : laterDeepFiveSumReducedRowTwoPolynomial68
      gamma delta epsilon zeta i4 A B c d e = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow0 : (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (8 * n - 1) = 0) : False := by
  have hpacket := laterDeepFiveSumReducedRowTwo_rightFive_packet68
    gamma delta epsilon zeta i4 A B c d e n g h hn hg hgh hh hopen
    hwallG haboveH hA hB hc hd he hdisc hrow2
  have hQle := residualIncidenceQ68_degree_le_fourRadius_of_rightFive
    gamma delta epsilon zeta i4 A B c d e n g h hn hwallG haboveH
    hA hB hc hd hi4
  have hQcoeff := residualIncidenceQ68_coeff_fourRadius_of_rightFive
    gamma delta epsilon zeta i4 A B c d e n g h hn hwallG haboveH
    hA hB hc hd hi4
  have hres := secondaryResidualRowZeroPolynomial68_coeff_rightFive
    A B c d e n g h hn hg hgh hh hwallG haboveH hA hB hc hd he hQle
  have hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  have he' : e.natDegree ≤ 6 * n - g := he.trans (by omega)
  have hload := cubicLoadRowZeroPolynomial68_coeff_eightRadius_of_coincidentFive
    alpha gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g hn hwallG
      hA hB hc hD he'
  rw [coeff_add, hres, hload, hQcoeff] at hrow0
  exact rightFive_rowZero_scalar_inconsistent68
    (n : k) (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) delta (Nat.cast_ne_zero.mpr hn.ne') ha hdelta
    hdisc hpacket (by
      push_cast at hrow0
      linear_combination hrow0)

/-! ## Source closure -/

set_option maxHeartbeats 26000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighRightFive_impossible68
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
      3 * g = 5 * n ∧ 5 * n < 2 * h) : False := by
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
  change 3 * g = 5 * n ∧ 5 * n < 2 * h at hwall
  have hdelta :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighRightFive_forces_delta_ne_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hwall)
  have ordinary :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleOrdinary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧ _
    at ordinary
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
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
      0 0 gamma delta epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, ordinary.1, ordinary.2.1] at hi4e
    exact hi4e
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
  rw [ordinary.1, ordinary.2.1] at hrow
  have hred := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
    alpha gamma delta epsilon zeta eta i4 Ae Be ce d ee hi4c hrow
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h0e
  have hsplit0 := cubicRowZeroPolynomial68_residualSplit
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee
  have hsum0 :
      secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee =
        C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa using hsplit0.symm.trans h0e
  have hidx : 8 * n - 1 ≠ 59 := by omega
  have hterm :
      (C terminal * (60 * (X ^ 59 : k[X]))).coeff (8 * n - 1) = 0 := by
    simp [coeff_C_mul, coeff_X_pow, hidx]
  have hrow0 := congrArg (fun p : k[X] => p.coeff (8 * n - 1)) hsum0
  rw [ordinary.1, ordinary.2.1, coeff_add, hterm] at hrow0
  exact laterDeepLowerOpenMiddle_rightFive_rowZero_inconsistent68
    alpha gamma delta epsilon zeta eta i4 Ae Be ce d ee n g h hn hg
    ordinary.2.2.1 hmiddle hopen hwall.1 hwall.2 ha hdelta hA secondary.2.1
    secondary.2.2.1 ordinary.2.2.2.1 ordinary.2.2.2.2.1
    ordinary.2.2.2.2.2.2.2.2.2 hred hi4c hrow0

#print axioms residualIncidenceQ68_coeff_fourRadius_of_rightFive
#print axioms secondaryResidualRowZeroPolynomial68_coeff_rightFive
#print axioms rightFive_rowZero_scalar_inconsistent68
#print axioms laterDeepLowerOpenMiddle_rightFive_rowZero_inconsistent68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighRightFive_impossible68

end LaterDeepLowerOpenMiddleHighRightFiveRowZeroEndgame68

end Max11DegreeRoutes
