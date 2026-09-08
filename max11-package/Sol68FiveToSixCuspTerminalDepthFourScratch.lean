import Sol68FiveToSixCuspTerminalDepthThreeScratch

/-! # Terminal depth four

The literal I4 coefficient `2N-4` is
`[L=4] b^3/9 - [R=4] (3/2) gamma d₀`.  At row-zero coefficient
`6N-5`, the `L=4` contribution contradicts the cusp, while on `R=4`
the I4 gamma contribution cancels the pinned gamma load and leaves the
nonzero `A'de` edge.  Thus both terminal depths advance to five.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspTerminalDepthFour68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem coeff_mul_at_reflect_four68 (p q : k[X]) (u v : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hsum : 4 ≤ u + v) :
    (p * q).coeff (u + v - 4) =
      (p.reflect u).coeff 0 * (q.reflect v).coeff 4 +
        (p.reflect u).coeff 1 * (q.reflect v).coeff 3 +
        (p.reflect u).coeff 2 * (q.reflect v).coeff 2 +
        (p.reflect u).coeff 3 * (q.reflect v).coeff 1 +
        (p.reflect u).coeff 4 * (q.reflect v).coeff 0 := by
  have h := congrArg (fun r : k[X] => r.coeff 4)
    (reflect_mul p q hp hq)
  rw [coeff_reflect, revAt_le hsum, mul_coeff_four_twoForty68] at h
  exact h

def FiveToSixTerminalDirectLowerRowFour68
    (alpha gamma epsilon zeta eta : k)
    (A B c d e : k[X]) (N : ℕ) : Prop :=
  (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * N - 5) = 0

theorem fiveToSix_terminal_directLowerRowFour68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G)) :
    FiveToSixTerminalDirectLowerRowFour68
      alpha gamma epsilon zeta eta A B c d e N := by
  rcases hpacket with
    ⟨_hN, _hgt5, _hle6, _hA, _hB, _hc, _hd, _he, _ha, _hcusp,
      _i4, _i3, _hi4, _hi3, hrow0, _hrow1, _hrow2, _hpos, _hiff⟩
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * N - 5)) hrow0
  have hidx : 6 * N - 5 ≠ 0 := by omega
  simpa only [FiveToSixTerminalDirectLowerRowFour68, coeff_C, if_neg hidx]
    using hcoeff

theorem fiveToSix_terminal_i4_faceSum_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N)
    (hzeta : zeta = 0)
    (hR4 : 4 ≤ 7 * N - 2 * G) (hL4 : 4 ≤ 3 * G - 7 * N) :
    (B * e + c * d).coeff (2 * N - 4) =
      (if 3 * G - 7 * N = 4 then
        (1 / 9 : k) * B.coeff (3 * N - G) ^ 3 else 0) -
      (if 7 * N - 2 * G = 4 then
        (3 / 2 : k) * gamma * d.coeff (G - 2 * N) else 0) := by
  rcases hpacket with
    ⟨_hN, hgt5, hle6, _hA, hB, _hc, _hd, _he, _ha, _hcusp,
      i4, _i3, hi4, _hi3, _hrow0, _hrow1, _hrow2, _hpos, _hiff⟩
  have hidx : 0 < 2 * N - 4 := by omega
  have hBlow : B.natDegree < 2 * N - 4 := by omega
  have hcoeff := congrArg (fun p : k[X] => p.coeff (2 * N - 4)) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    hzeta] at hcoeff
  by_cases hLwall : 3 * G - 7 * N = 4
  · have hRne : 7 * N - 2 * G ≠ 4 := by omega
    have hdlow : d.natDegree < 2 * N - 4 := by omega
    have hB3 := coeff_pow_at_bound68 B (3 * N - G) 3 hB
    rw [show 3 * (3 * N - G) = 2 * N - 4 from by omega] at hB3
    rw [if_pos hLwall, if_neg hRne, sub_zero]
    simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
      coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt hidx, if_false,
      hB3, coeff_eq_zero_of_natDegree_lt hBlow,
      coeff_eq_zero_of_natDegree_lt hdlow, zero_mul, add_zero] at hcoeff
    rw [coeff_add]
    linear_combination (3 / 8 : k) * hcoeff
  · by_cases hRwall : 7 * N - 2 * G = 4
    · have hB3low : (B ^ 3).natDegree < 2 * N - 4 := by
        compute_degree; omega
      rw [if_neg hLwall, if_pos hRwall, zero_sub]
      simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
        coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt hidx, if_false,
        coeff_eq_zero_of_natDegree_lt hB3low,
        coeff_eq_zero_of_natDegree_lt hBlow, zero_mul, add_zero] at hcoeff
      rw [show 2 * N - 4 = G - 2 * N from by omega] at hcoeff ⊢
      rw [coeff_add]
      linear_combination (3 / 8 : k) * hcoeff
    · have hB3low : (B ^ 3).natDegree < 2 * N - 4 := by
        compute_degree; omega
      have hdlow : d.natDegree < 2 * N - 4 := by omega
      rw [if_neg hLwall, if_neg hRwall, sub_zero]
      simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
        coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt hidx, if_false,
        coeff_eq_zero_of_natDegree_lt hB3low,
        coeff_eq_zero_of_natDegree_lt hBlow,
        coeff_eq_zero_of_natDegree_lt hdlow, zero_mul, add_zero] at hcoeff
      rw [coeff_add]
      linear_combination (3 / 8 : k) * hcoeff

theorem fiveToSix_terminal_AAF_four68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N)
    (hzeta : zeta = 0)
    (hR4 : 4 ≤ 7 * N - 2 * G) (hL4 : 4 ≤ 3 * G - 7 * N) :
    (A * derivative A * (B * e + c * d)).coeff (6 * N - 5) =
      A.coeff (2 * N) ^ 2 * (((2 * N : ℕ) : k)) *
        ((if 3 * G - 7 * N = 4 then
            (1 / 9 : k) * B.coeff (3 * N - G) ^ 3 else 0) -
          (if 7 * N - 2 * G = 4 then
            (3 / 2 : k) * gamma * d.coeff (G - 2 * N) else 0)) := by
  let F := B * e + c * d
  have hface := fiveToSix_contractedCusp_terminalFace68
    alpha gamma epsilon zeta eta terminal A B c d e N G hpacket
    hdTerminal heTerminal hzeta
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
  have hFdeg : F.natDegree ≤ 2 * N := by
    dsimp only [F]; compute_degree; omega
  have hPdeg : (A * derivative A).natDegree ≤ 4 * N - 1 := by
    compute_degree; omega
  have hF0 : F.coeff (2 * N) = 0 := by
    have hBe := coeff_mul_at_bounds68 B e (3 * N - G) (G - N)
      hB heTerminal
    rw [show (3 * N - G) + (G - N) = 2 * N from by omega] at hBe
    have hcd := coeff_mul_at_bounds68 c d (4 * N - G) (G - 2 * N)
      hc hdTerminal
    rw [show (4 * N - G) + (G - 2 * N) = 2 * N from by omega] at hcd
    simp only [F, coeff_add, hBe, hcd]
    exact hface.four
  have hF1 : F.coeff (2 * N - 1) = 0 := by
    have h := fiveToSix_terminal_i4_faceSum_one68
      alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
        ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩ hdTerminal heTerminal hzeta
    rw [if_neg (by omega : 3 * G - 7 * N ≠ 1)] at h
    exact h
  have hF2 : F.coeff (2 * N - 2) = 0 := by
    simpa only [F] using fiveToSix_terminal_i4_faceSum_two_zero68
      alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
        ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩ hdTerminal heTerminal hzeta
  have hF3 : F.coeff (2 * N - 3) = 0 := by
    have h := fiveToSix_terminal_i4_faceSum_three68
      alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
        ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩ hdTerminal heTerminal hzeta
    rw [if_neg (by omega : 3 * G - 7 * N ≠ 3),
      if_neg (by omega : 7 * N - 2 * G ≠ 3), sub_zero] at h
    exact h
  have hF4 : F.coeff (2 * N - 4) =
      (if 3 * G - 7 * N = 4 then
        (1 / 9 : k) * B.coeff (3 * N - G) ^ 3 else 0) -
      (if 7 * N - 2 * G = 4 then
        (3 / 2 : k) * gamma * d.coeff (G - 2 * N) else 0) := by
    simpa only [F] using fiveToSix_terminal_i4_faceSum_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
        ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩ hdTerminal heTerminal hzeta
      hR4 hL4
  have hPtop := coeff_mul_derivative_at_bounds68 A A (2 * N) (2 * N)
    (by omega) hA hA
  rw [show 2 * N + 2 * N - 1 = 4 * N - 1 from by omega] at hPtop
  have hraw := coeff_mul_at_reflect_four68 (A * derivative A) F
    (4 * N - 1) (2 * N) hPdeg hFdeg (by omega)
  rw [show (4 * N - 1) + 2 * N - 4 = 6 * N - 5 from by omega] at hraw
  have hPr0 : ((A * derivative A).reflect (4 * N - 1)).coeff 0 =
      A.coeff (2 * N) ^ 2 * (((2 * N : ℕ) : k)) := by
    rw [coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero, hPtop]
    ring
  have hFr0 : (F.reflect (2 * N)).coeff 0 = 0 := by
    rw [coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero, hF0]
  have hFr1 : (F.reflect (2 * N)).coeff 1 = 0 := by
    rw [coeff_reflect, revAt_le (by omega : 1 ≤ 2 * N), hF1]
  have hFr2 : (F.reflect (2 * N)).coeff 2 = 0 := by
    rw [coeff_reflect, revAt_le (by omega : 2 ≤ 2 * N), hF2]
  have hFr3 : (F.reflect (2 * N)).coeff 3 = 0 := by
    rw [coeff_reflect, revAt_le (by omega : 3 ≤ 2 * N), hF3]
  have hFr4 : (F.reflect (2 * N)).coeff 4 =
      (if 3 * G - 7 * N = 4 then
        (1 / 9 : k) * B.coeff (3 * N - G) ^ 3 else 0) -
      (if 7 * N - 2 * G = 4 then
        (3 / 2 : k) * gamma * d.coeff (G - 2 * N) else 0) := by
    rw [coeff_reflect, revAt_le (by omega : 4 ≤ 2 * N), hF4]
  rw [hPr0, hFr0, hFr1, hFr2, hFr3, hFr4] at hraw
  simpa only [mul_zero, add_zero] using hraw

/- The two wall consumers use exactly the same scalar reductions as depth
three; only the coefficient indices and arithmetic wall values change. -/
theorem fiveToSix_terminal_L_four_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N) (hzeta : zeta = 0)
    (hR4 : 4 ≤ 7 * N - 2 * G) (hL4 : 3 * G - 7 * N = 4) : False := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
  have hRne : 7 * N - 2 * G ≠ 4 := by omega
  have hAAF := fiveToSix_terminal_AAF_four68
    alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
    ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩ hdTerminal heTerminal hzeta
    hR4 (by omega)
  rw [if_pos hL4, if_neg hRne, sub_zero] at hAAF
  have hmain := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3 * N - G) (4 * N - G) (4 * N - G) (2 * N) (by omega)
    hB hc hc hA
  rw [show (3 * N - G) + (4 * N - G) + (4 * N - G) + 2 * N - 1 =
    6 * N - 5 from by omega] at hmain
  have hmain' : (derivative A * B * c ^ 2).coeff (6 * N - 5) =
      A.coeff (2 * N) * B.coeff (3 * N - G) *
        c.coeff (4 * N - G) ^ 2 * (((2 * N : ℕ) : k)) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hmain
  have hrow := fiveToSix_terminal_directLowerRowFour68
    alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
    ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
  change (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * N - 5) = 0 at hrow
  have hlow1 : (A * B ^ 2 * derivative d).natDegree < 6 * N - 5 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree < 6 * N - 5 := by compute_degree; omega
  have hlow4 : (B * c * derivative e).natDegree < 6 * N - 5 := by compute_degree; omega
  have hlow5 : (B * d * derivative d).natDegree < 6 * N - 5 := by compute_degree; omega
  have hlow6 : (derivative B * d ^ 2).natDegree < 6 * N - 5 := by compute_degree; omega
  have hlow7 : (c * derivative c * d).natDegree < 6 * N - 5 := by compute_degree; omega
  have hdeLow : (derivative A * d * e).natDegree < 6 * N - 5 := by compute_degree; omega
  have hload1 : (B * derivative A * c).natDegree < 6 * N - 5 := by compute_degree; omega
  have hload2 : (B * derivative e).natDegree < 6 * N - 5 := by compute_degree; omega
  have hload3 : (A * B * derivative A).natDegree < 6 * N - 5 := by compute_degree; omega
  have hload4 : (A * derivative A * d).natDegree < 6 * N - 5 := by compute_degree; omega
  have hload5 : (d * derivative c).natDegree < 6 * N - 5 := by compute_degree; omega
  have hload6 : (d * derivative A).natDegree < 6 * N - 5 := by compute_degree; omega
  rw [coeff_add, cubicLoadRowZeroPolynomial68_uniform_pinned_eq68, hzeta] at hrow
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, coeff_neg, coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2, coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5, coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7, coeff_eq_zero_of_natDegree_lt hdeLow,
    coeff_eq_zero_of_natDegree_lt hload1, coeff_eq_zero_of_natDegree_lt hload2,
    coeff_eq_zero_of_natDegree_lt hload3, coeff_eq_zero_of_natDegree_lt hload4,
    coeff_eq_zero_of_natDegree_lt hload5, coeff_eq_zero_of_natDegree_lt hload6,
    coeff_smul, smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero] at hrow
  have hcombine :
      (A * derivative A * B * e).coeff (6 * N - 5) +
        (A * derivative A * c * d).coeff (6 * N - 5) =
        (A * derivative A * (B * e + c * d)).coeff (6 * N - 5) := by
    rw [mul_add, coeff_add]; ring
  have hcore : (-4 / 27 : k) *
      (A * derivative A * (B * e + c * d)).coeff (6 * N - 5) +
      (4 / 27 : k) * (derivative A * B * c ^ 2).coeff (6 * N - 5) = 0 := by
    linear_combination hrow + (4 / 27 : k) * hcombine
  rw [hAAF, hmain'] at hcore
  have hcast : (((2 * N : ℕ) : k)) ≠ 0 := by
    exact_mod_cast (show (2 * N : ℕ) ≠ 0 by omega)
  have hprod : (((2 * N : ℕ) : k)) * A.coeff (2 * N) ^ 2 *
      B.coeff (3 * N - G) ^ 3 = 0 := by
    linear_combination (-243 / 16 : k) * hcore +
      (3 / 4 : k) * (((2 * N : ℕ) : k)) * A.coeff (2 * N) *
        B.coeff (3 * N - G) * hcusp
  exact (mul_ne_zero (mul_ne_zero hcast (pow_ne_zero 2 ha))
    (pow_ne_zero 3 hb)) hprod

theorem fiveToSix_terminal_R_four_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N) (hzeta : zeta = 0)
    (hR4 : 7 * N - 2 * G = 4) (hL4 : 4 ≤ 3 * G - 7 * N) : False := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
  have hLne : 3 * G - 7 * N ≠ 4 := by omega
  have hN4 : N = 4 := by omega
  have hG12 : G = 12 := by omega
  have hAAF := fiveToSix_terminal_AAF_four68
    alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
    ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩ hdTerminal heTerminal hzeta
    (by omega) hL4
  rw [if_neg hLne, if_pos hR4, zero_sub] at hAAF
  have hde := coeff_mul_mul_derivative_at_bounds68 d e A
    (G - 2 * N) (G - N) (2 * N) (by omega) hdTerminal heTerminal hA
  rw [show (G - 2 * N) + (G - N) + 2 * N - 1 = 6 * N - 5 from by omega] at hde
  have hde' : (derivative A * d * e).coeff (6 * N - 5) =
      A.coeff (2 * N) * d.coeff (G - 2 * N) * e.coeff (G - N) *
        (((2 * N : ℕ) : k)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hde
  have hAAd := coeff_mul_mul_derivative_at_bounds68 A d A
    (2 * N) (G - 2 * N) (2 * N) (by omega) hA hdTerminal hA
  rw [show 2 * N + (G - 2 * N) + 2 * N - 1 = 6 * N - 5 from by omega] at hAAd
  have hAAd' : (A * derivative A * d).coeff (6 * N - 5) =
      A.coeff (2 * N) ^ 2 * d.coeff (G - 2 * N) *
        (((2 * N : ℕ) : k)) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hAAd
  have hrow := fiveToSix_terminal_directLowerRowFour68
    alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
    ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
  change (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * N - 5) = 0 at hrow
  have hlow1 : (A * B ^ 2 * derivative d).natDegree < 6 * N - 5 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree < 6 * N - 5 := by compute_degree; omega
  have hlow3 : (derivative A * B * c ^ 2).natDegree < 6 * N - 5 := by compute_degree; omega
  have hlow4 : (B * c * derivative e).natDegree < 6 * N - 5 := by compute_degree; omega
  have hlow5 : (B * d * derivative d).natDegree < 6 * N - 5 := by compute_degree; omega
  have hlow6 : (derivative B * d ^ 2).natDegree < 6 * N - 5 := by compute_degree; omega
  have hlow7 : (c * derivative c * d).natDegree < 6 * N - 5 := by compute_degree; omega
  have hload1 : (B * derivative A * c).natDegree < 6 * N - 5 := by compute_degree; omega
  have hload2 : (B * derivative e).natDegree < 6 * N - 5 := by compute_degree; omega
  have hload3 : (A * B * derivative A).natDegree < 6 * N - 5 := by compute_degree; omega
  have hload5 : (d * derivative c).natDegree < 6 * N - 5 := by compute_degree; omega
  have hload6 : (d * derivative A).natDegree < 6 * N - 5 := by compute_degree; omega
  rw [coeff_add, cubicLoadRowZeroPolynomial68_uniform_pinned_eq68, hzeta] at hrow
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, coeff_neg, coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2, coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4, coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6, coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hload1, coeff_eq_zero_of_natDegree_lt hload2,
    coeff_eq_zero_of_natDegree_lt hload3, coeff_eq_zero_of_natDegree_lt hload5,
    coeff_eq_zero_of_natDegree_lt hload6, coeff_smul, smul_eq_mul,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero] at hrow
  have hcombine :
      (A * derivative A * B * e).coeff (6 * N - 5) +
        (A * derivative A * c * d).coeff (6 * N - 5) =
        (A * derivative A * (B * e + c * d)).coeff (6 * N - 5) := by
    rw [mul_add, coeff_add]; ring
  have hcore : (-4 / 27 : k) *
      (A * derivative A * (B * e + c * d)).coeff (6 * N - 5) -
      (4 / 9 : k) * (derivative A * d * e).coeff (6 * N - 5) -
      (2 / 9 * gamma : k) * (A * derivative A * d).coeff (6 * N - 5) = 0 := by
    linear_combination hrow + (4 / 27 : k) * hcombine
  rw [hAAF, hde', hAAd'] at hcore
  have hcast : (((2 * N : ℕ) : k)) ≠ 0 := by
    exact_mod_cast (show (2 * N : ℕ) ≠ 0 by omega)
  have hprod : (((2 * N : ℕ) : k)) * A.coeff (2 * N) *
      d.coeff (G - 2 * N) * e.coeff (G - N) = 0 := by
    linear_combination (-9 / 4 : k) * hcore
  have hdsTerminal : d.coeff (G - 2 * N) ≠ 0 := by
    simpa only [show 5 * N - G - (7 * N - 2 * G) = G - 2 * N by omega] using hds
  have hesTerminal : e.coeff (G - N) ≠ 0 := by
    simpa only [show 6 * N - G - (7 * N - 2 * G) = G - N by omega] using hes
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hcast ha) hdsTerminal) hesTerminal) hprod

def FiveToSixTerminalCuspDepthFiveResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ) : Prop :=
  FiveToSixTerminalCuspDepthFourResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G ∧
    5 ≤ 7 * N - 2 * G ∧ 5 ≤ 3 * G - 7 * N ∧
    FiveToSixTerminalDirectLowerRowFour68
      alpha gamma epsilon zeta eta A B c d e N

theorem fiveToSix_terminal_cusp_depth_five_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hres : FiveToSixTerminalCuspDepthFourResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G) :
    FiveToSixTerminalCuspDepthFiveResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G := by
  have hres0 := hres
  rcases hres with ⟨hbase, hR4, hL4, hrowThree⟩
  rcases hbase with ⟨hthree, _hR3, _hL3, _hi4two, _hrowTwo⟩
  rcases hthree with
    ⟨hNbig, hdTerminal, heTerminal, hzeta, _r2, _l2, hpacket, _row0⟩
  have hR5 : 5 ≤ 7 * N - 2 * G := by
    by_contra hn
    have heq : 7 * N - 2 * G = 4 := by omega
    exact fiveToSix_terminal_R_four_false68
      alpha gamma epsilon zeta eta terminal A B c d e N G hNbig hpacket
      hdTerminal heTerminal hzeta heq hL4
  have hL5 : 5 ≤ 3 * G - 7 * N := by
    by_contra hn
    have heq : 3 * G - 7 * N = 4 := by omega
    exact fiveToSix_terminal_L_four_false68
      alpha gamma epsilon zeta eta terminal A B c d e N G hNbig hpacket
      hdTerminal heTerminal hzeta hR4 heq
  exact ⟨hres0, hR5, hL5, fiveToSix_terminal_directLowerRowFour68
    alpha gamma epsilon zeta eta terminal A B c d e N G hNbig hpacket⟩

#print axioms fiveToSix_terminal_i4_faceSum_four68
#print axioms fiveToSix_terminal_AAF_four68
#print axioms fiveToSix_terminal_L_four_false68
#print axioms fiveToSix_terminal_R_four_false68
#print axioms fiveToSix_terminal_cusp_depth_five_residual68

end FiveToSixCuspTerminalDepthFour68

end Max11DegreeRoutes
