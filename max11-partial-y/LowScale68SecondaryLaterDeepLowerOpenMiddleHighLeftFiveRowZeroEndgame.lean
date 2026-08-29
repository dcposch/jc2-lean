import LowScale68SecondaryLaterDeepLowerOpenMiddleHighRightFiveRowZeroEndgame
import LowScale68SecondaryLaterDeepLowerOpenMiddleHighLeftFiveWall

/-! # Row-zero closure of the strict left exact-five wall

On `2h = 5n < 3g`, the fixed `B,c` face has dropped below degree `8n-1`.
The attained `Q(4n)` and `d*e` edges, together with the `delta` row-zero
load, contradict the normalized left row-two packet.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighLeftFiveRowZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Loaded row zero throughout the strict later-deep window -/

set_option maxHeartbeats 9000000 in
theorem cubicLoadRowZeroPolynomial68_coeff_eightRadius_of_laterDeepLowerOpen
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).coeff (8 * n - 1) =
      (1 / 9 : k) * (n : k) * delta * A.coeff (2 * n) ^ 4 := by
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Uc := cubicLoadUAlphaCorePolynomial68 alpha D
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  have hgt : n < g := by omega
  have hwindow : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n := by omega
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB hc
  have hUc : Uc.natDegree ≤ 5 * n - g := by
    simp only [Uc, cubicLoadUAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha D).trans hD
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E, Ec, Er]
    compute_degree
    omega
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hA3i : 3 * (2 * n) = 6 * n := by omega
  rw [hA3i] at hA3
  have hAclt : (A * c).natDegree < 6 * n := by
    compute_degree
    omega
  have helt : e.natDegree < 6 * n := he.trans_lt (by omega)
  have hEtop : E.coeff (6 * n) =
      (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E, Ec, Er, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt,
      coeff_eq_zero_of_natDegree_lt helt, mul_zero, add_zero]
  have hUrTop : Ur.coeff (2 * n) =
      (1 / 2 * delta : k) * A.coeff (2 * n) := by
    simp only [Ur, cubicLoadUAlphaRestPolynomial68, zero_mul, zero_smul,
      smul_zero, zero_add, coeff_add, coeff_smul, smul_eq_mul]
    have hBlt : B.natDegree < 2 * n := hB.trans_lt (by omega)
    have hconst : (C zeta : k[X]).coeff (2 * n) = 0 := by
      simp [coeff_C, show 2 * n ≠ 0 by omega]
    rw [coeff_eq_zero_of_natDegree_lt hBlt, hconst]
    ring
  have h1 : (Ur * derivative E).coeff (8 * n - 1) =
      Ur.coeff (2 * n) * E.coeff (6 * n) * ((6 * n : ℕ) : k) := by
    have ht := coeff_mul_derivative_at_bounds68 Ur E (2 * n) (6 * n)
      (by omega) hUr hE
    have hi : 2 * n + 6 * n - 1 = 8 * n - 1 := by omega
    rwa [hi] at ht
  have hEr : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]
    compute_degree
    omega
  have h2deg : (Uc * derivative Er).natDegree < 8 * n - 1 := by
    have ht := middleBeta_natDegree_mul_derivative_le68 Uc Er
      (5 * n - g) (6 * n - g) hUc (by omega) hEr
    omega
  have h3deg : (D * derivative Vr).natDegree < 8 * n - 1 := by
    by_cases hgle : g ≤ 2 * n
    · have hVr : Vr.natDegree ≤ 6 * n - g :=
        cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
          alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow hgle
          hA hB hc hD he
      compute_degree
      omega
    · have hgge : 2 * n ≤ g := by omega
      have hVr : Vr.natDegree ≤ 4 * n :=
        cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_ge_two
          alpha 0 gamma delta epsilon eta A B c D e n g hn hwindow hgge
          hA hB hc hD he
      compute_degree
      omega
  rw [cubicLoadRowZeroPolynomial68_eq_deepGapRest_of_beta']
  change (Ur * derivative E + Uc * derivative Er - D * derivative Vr).coeff
      (8 * n - 1) = _
  simp only [coeff_add, coeff_sub, h1,
    coeff_eq_zero_of_natDegree_lt h2deg,
    coeff_eq_zero_of_natDegree_lt h3deg, add_zero, sub_zero]
  rw [hUrTop, hEtop]
  push_cast
  ring

/-! ## The attained incidence edge -/

set_option maxHeartbeats 3000000 in
theorem residualIncidenceQ68_degree_le_fourRadius_of_leftFive
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hwallH : 2 * h = 5 * n) (haboveG : 5 * n < 3 * g)
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
theorem residualIncidenceQ68_coeff_fourRadius_of_leftFive
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hwallH : 2 * h = 5 * n) (haboveG : 5 * n < 3 * g)
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

/-! ## Left row-two scalar -/

theorem laterDeepFiveSumReducedRowTwo_leftFive_packet68
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwallH : 2 * h = 5 * n) (haboveG : 5 * n < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow : laterDeepFiveSumReducedRowTwoPolynomial68
      gamma delta epsilon zeta i4 A B c d e = 0) :
    (5 : k) * delta * A.coeff (2 * n) ^ 3 +
      (192 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  have hrel := laterDeepFiveSumReducedRowTwo_leftFive_relation68
    gamma delta epsilon zeta i4 A B c d e n g h hn hg hgh hh hopen
    hwallH haboveG hA hB hc hd he hrow
  have hNH : 11 * n - 2 * h = 6 * n := by omega
  rw [hNH] at hrel
  push_cast at hrel
  have hnK : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hfactor : (n : k) *
      ((5 : k) * delta * A.coeff (2 * n) ^ 3 +
        (192 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) = 0 := by
    linear_combination (12 : k) * hrel
  exact (mul_eq_zero.mp hfactor).resolve_left hnK

/-! ## Exact residual row zero -/

set_option maxHeartbeats 14000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_leftFive
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwallH : 2 * h = 5 * n) (haboveG : 5 * n < 3 * g)
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
          (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h))) := by
  let Q := residualIncidenceQ68 B c d e
  let idx := 8 * n - 1
  change (secondaryResidualRowZeroPolynomial68 A B c d e).coeff idx =
    (4 / 27 : k) * ((2 : k) * (n : k) * A.coeff (2 * n) *
      (-(A.coeff (2 * n) * Q.coeff (4 * n)) -
        (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)))
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
  have hAde := coeff_mul_mul_derivative_at_bounds68 d e A
    (5 * n - h) (6 * n - h) (2 * n) (by omega) hd he hA
  have hiAde : (5 * n - h) + (6 * n - h) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAde] at hAde
  have hAde' : (derivative A * d * e).coeff idx =
      A.coeff (2 * n) * d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * d * e).coeff idx =
        (d * e * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hAde
  have h0AB3 : (A * derivative A * B ^ 3).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0Bc2 : (derivative A * B * c ^ 2).natDegree < idx := by
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
        (A * derivative A * Q).coeff idx := by
    have ht := congrArg (fun p : k[X] => p.coeff idx) hBe_cd
    have hz : ((1 / 9 : k) • (A * derivative A * B ^ 3)).coeff idx = 0 := by
      rw [coeff_smul, coeff_eq_zero_of_natDegree_lt h0AB3, smul_eq_mul,
        mul_zero]
    simpa only [Q, coeff_add, coeff_smul, hz, add_zero] using ht
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
            (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
    simp only [coeff_smul, smul_eq_mul, coeff_add, coeff_sub,
      coeff_eq_zero_of_natDegree_lt h0d,
      coeff_eq_zero_of_natDegree_lt h0Bd,
      coeff_eq_zero_of_natDegree_lt h0Bc2,
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
    rw [hsum, hBe, hAQ', hAde', hcast2]
    ring
  rw [secondaryResidualRowZeroPolynomial68, coeff_smul, smul_eq_mul, hinner]

/-! ## Scalar and polynomial contradiction -/

theorem leftFive_rowZero_scalar_inconsistent68
    (N a d e delta : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (hdelta : delta ≠ 0)
    (hpacket : (5 : k) * delta * a ^ 3 + (192 : k) * d * e = 0)
    (hzero : (8 / 27 : k) * N * a *
          ((3 / 32 : k) * delta * a ^ 3 - (3 : k) * d * e) +
        (1 / 9 : k) * N * delta * a ^ 4 = 0) : False := by
  have hNa : N * a ≠ 0 := mul_ne_zero hN ha
  have hinner :
      (8 / 27 : k) *
          ((3 / 32 : k) * delta * a ^ 3 - (3 : k) * d * e) +
        (1 / 9 : k) * delta * a ^ 3 = 0 := by
    have hfactor : N * a *
        ((8 / 27 : k) *
            ((3 / 32 : k) * delta * a ^ 3 - (3 : k) * d * e) +
          (1 / 9 : k) * delta * a ^ 3) = 0 := by
      linear_combination hzero
    exact (mul_eq_zero.mp hfactor).resolve_left hNa
  have hx : (35 : k) * (delta * a ^ 3) = 0 := by
    linear_combination (216 : k) * hinner + hpacket
  have hda : delta * a ^ 3 = 0 :=
    (mul_eq_zero.mp hx).resolve_left (by norm_num)
  exact hdelta ((mul_eq_zero.mp hda).resolve_right (pow_ne_zero 3 ha))

set_option maxHeartbeats 12000000 in
theorem laterDeepLowerOpenMiddle_leftFive_rowZero_inconsistent68
    (alpha gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwallH : 2 * h = 5 * n) (haboveG : 5 * n < 3 * g)
    (ha : A.coeff (2 * n) ≠ 0) (hdelta : delta ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow2 : laterDeepFiveSumReducedRowTwoPolynomial68
      gamma delta epsilon zeta i4 A B c d e = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow0 : (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (8 * n - 1) = 0) : False := by
  have hpacket := laterDeepFiveSumReducedRowTwo_leftFive_packet68
    gamma delta epsilon zeta i4 A B c d e n g h hn hg hgh hh hopen
    hwallH haboveG hA hB hc hd he hrow2
  have hQle := residualIncidenceQ68_degree_le_fourRadius_of_leftFive
    gamma delta epsilon zeta i4 A B c d e n g h hn hwallH haboveG
    hA hB hc hd hi4
  have hQcoeff := residualIncidenceQ68_coeff_fourRadius_of_leftFive
    gamma delta epsilon zeta i4 A B c d e n g h hn hwallH haboveG
    hA hB hc hd hi4
  have hres := secondaryResidualRowZeroPolynomial68_coeff_leftFive
    A B c d e n g h hn hg hgh hh hwallH haboveG hA hB hc hd he hQle
  have hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  have he' : e.natDegree ≤ 6 * n - g := he.trans (by omega)
  have hload := cubicLoadRowZeroPolynomial68_coeff_eightRadius_of_laterDeepLowerOpen
    alpha gamma delta epsilon zeta eta A B c
      ((1 / 3 : k) • (A * B) + d) e n g hn hopen
      hA hB hc hD he'
  rw [coeff_add, hres, hload, hQcoeff] at hrow0
  exact leftFive_rowZero_scalar_inconsistent68
    (n : k) (A.coeff (2 * n)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) delta (Nat.cast_ne_zero.mpr hn.ne') ha hdelta
    hpacket (by
      push_cast at hrow0
      linear_combination hrow0)

/-! ## Source closure -/

set_option maxHeartbeats 26000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighLeftFive_impossible68
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
      2 * h = 5 * n ∧ 5 * n < 3 * g) : False := by
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
  change 2 * h = 5 * n ∧ 5 * n < 3 * g at hwall
  have hdelta :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighLeftFive_forces_delta_ne_zero68
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
  exact laterDeepLowerOpenMiddle_leftFive_rowZero_inconsistent68
    alpha gamma delta epsilon zeta eta i4 Ae Be ce d ee n g h hn hg
    ordinary.2.2.1 hmiddle hopen hwall.1 hwall.2 ha hdelta hA secondary.2.1
    secondary.2.2.1 ordinary.2.2.2.1 ordinary.2.2.2.2.1 hred hi4c hrow0

#print axioms cubicLoadRowZeroPolynomial68_coeff_eightRadius_of_laterDeepLowerOpen
#print axioms secondaryResidualRowZeroPolynomial68_coeff_leftFive
#print axioms leftFive_rowZero_scalar_inconsistent68
#print axioms laterDeepLowerOpenMiddle_leftFive_rowZero_inconsistent68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighLeftFive_impossible68

end LaterDeepLowerOpenMiddleHighLeftFiveRowZeroEndgame68

end Max11DegreeRoutes
