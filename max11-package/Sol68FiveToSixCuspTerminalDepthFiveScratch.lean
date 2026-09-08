import Sol68FiveToSixCuspTerminalDepthFourScratch

/-! # Terminal depth five

Both literal indices remain positive for `2 < N`.  The possible epsilon
coincidence `G=N+5` forces the already excluded depth `L=3`, so the live
walls have exactly the familiar two loads.  The `L=5` row contradicts the
cusp, and on `R=5` (necessarily `(N,G)=(5,15)`) the I4 gamma contribution
cancels the pinned row gamma contribution, leaving nonzero `A'de`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspTerminalDepthFive68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem coeff_mul_at_reflect_five68 (p q : k[X]) (u v : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hsum : 5 ≤ u + v) :
    (p * q).coeff (u + v - 5) =
      (p.reflect u).coeff 0 * (q.reflect v).coeff 5 +
        (p.reflect u).coeff 1 * (q.reflect v).coeff 4 +
        (p.reflect u).coeff 2 * (q.reflect v).coeff 3 +
        (p.reflect u).coeff 3 * (q.reflect v).coeff 2 +
        (p.reflect u).coeff 4 * (q.reflect v).coeff 1 +
        (p.reflect u).coeff 5 * (q.reflect v).coeff 0 := by
  have h := congrArg (fun r : k[X] => r.coeff 5)
    (reflect_mul p q hp hq)
  rw [coeff_reflect, revAt_le hsum, mul_coeff_five_twoForty68] at h
  exact h

def FiveToSixTerminalDirectLowerRowFive68
    (alpha gamma epsilon zeta eta : k)
    (A B c d e : k[X]) (N : ℕ) : Prop :=
  (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * N - 6) = 0

theorem fiveToSix_terminal_directLowerRowFive68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G)) :
    FiveToSixTerminalDirectLowerRowFive68
      alpha gamma epsilon zeta eta A B c d e N := by
  rcases hpacket with
    ⟨_hN, _hgt5, _hle6, _hA, _hB, _hc, _hd, _he, _ha, _hcusp,
      _i4, _i3, _hi4, _hi3, hrow0, _hrow1, _hrow2, _hpos, _hiff⟩
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * N - 6)) hrow0
  have hidx : 6 * N - 6 ≠ 0 := by omega
  simpa only [FiveToSixTerminalDirectLowerRowFive68, coeff_C, if_neg hidx]
    using hcoeff

theorem fiveToSix_terminal_i4_faceSum_five68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N) (hzeta : zeta = 0)
    (hR5 : 5 ≤ 7 * N - 2 * G) (hL5 : 5 ≤ 3 * G - 7 * N) :
    (B * e + c * d).coeff (2 * N - 5) =
      (if 3 * G - 7 * N = 5 then
        (1 / 9 : k) * B.coeff (3 * N - G) ^ 3 else 0) -
      (if 4 * N - G = 5 then
        (3 / 2 : k) * gamma * d.coeff (G - 2 * N) else 0) := by
  rcases hpacket with
    ⟨_hN, hgt5, hle6, _hA, hB, _hc, _hd, _he, _ha, _hcusp,
      i4, _i3, hi4, _hi3, _hrow0, _hrow1, _hrow2, _hpos, _hiff⟩
  have hidx : 0 < 2 * N - 5 := by omega
  have hcoeff := congrArg (fun p : k[X] => p.coeff (2 * N - 5)) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    hzeta] at hcoeff
  by_cases hLwall : 3 * G - 7 * N = 5
  · by_cases hDwall : 4 * N - G = 5
    · have hBlow : B.natDegree < 2 * N - 5 := by omega
      have hB3 := coeff_pow_at_bound68 B (3 * N - G) 3 hB
      rw [show 3 * (3 * N - G) = 2 * N - 5 from by omega] at hB3
      rw [if_pos hLwall, if_pos hDwall]
      simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
        coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt hidx, if_false,
        hB3, coeff_eq_zero_of_natDegree_lt hBlow, zero_mul, add_zero]
        at hcoeff
      rw [show 2 * N - 5 = G - 2 * N from by omega] at hcoeff ⊢
      rw [coeff_add]
      linear_combination (3 / 8 : k) * hcoeff
    · have hdlow : d.natDegree < 2 * N - 5 := by omega
      have hBlow : B.natDegree < 2 * N - 5 := by omega
      have hB3 := coeff_pow_at_bound68 B (3 * N - G) 3 hB
      rw [show 3 * (3 * N - G) = 2 * N - 5 from by omega] at hB3
      rw [if_pos hLwall, if_neg hDwall, sub_zero]
      simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
        coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt hidx, if_false,
        hB3, coeff_eq_zero_of_natDegree_lt hBlow,
        coeff_eq_zero_of_natDegree_lt hdlow, zero_mul, add_zero] at hcoeff
      rw [coeff_add]
      linear_combination (3 / 8 : k) * hcoeff
  · by_cases hDwall : 4 * N - G = 5
    · have hB3low : (B ^ 3).natDegree < 2 * N - 5 := by compute_degree; omega
      have hBlow : B.natDegree < 2 * N - 5 := by omega
      rw [if_neg hLwall, if_pos hDwall, zero_sub]
      simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
        coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt hidx, if_false,
        coeff_eq_zero_of_natDegree_lt hB3low,
        coeff_eq_zero_of_natDegree_lt hBlow, zero_mul, add_zero] at hcoeff
      rw [show 2 * N - 5 = G - 2 * N from by omega] at hcoeff ⊢
      rw [coeff_add]
      linear_combination (3 / 8 : k) * hcoeff
    · have hB3low : (B ^ 3).natDegree < 2 * N - 5 := by compute_degree; omega
      have hBlow : B.natDegree < 2 * N - 5 := by omega
      have hdlow : d.natDegree < 2 * N - 5 := by omega
      rw [if_neg hLwall, if_neg hDwall, sub_zero]
      simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
        coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt hidx, if_false,
        coeff_eq_zero_of_natDegree_lt hB3low,
        coeff_eq_zero_of_natDegree_lt hBlow,
        coeff_eq_zero_of_natDegree_lt hdlow, zero_mul, add_zero] at hcoeff
      rw [coeff_add]
      linear_combination (3 / 8 : k) * hcoeff

theorem fiveToSix_terminal_AAF_five68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N) (hzeta : zeta = 0)
    (hR5 : 5 ≤ 7 * N - 2 * G) (hL5 : 5 ≤ 3 * G - 7 * N) :
    (A * derivative A * (B * e + c * d)).coeff (6 * N - 6) =
      A.coeff (2 * N) ^ 2 * (((2 * N : ℕ) : k)) *
        ((if 3 * G - 7 * N = 5 then
            (1 / 9 : k) * B.coeff (3 * N - G) ^ 3 else 0) -
          (if 4 * N - G = 5 then
            (3 / 2 : k) * gamma * d.coeff (G - 2 * N) else 0)) := by
  let F := B * e + c * d
  have hface := fiveToSix_contractedCusp_terminalFace68
    alpha gamma epsilon zeta eta terminal A B c d e N G hpacket
    hdTerminal heTerminal hzeta
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
  have hFdeg : F.natDegree ≤ 2 * N := by dsimp only [F]; compute_degree; omega
  have hPdeg : (A * derivative A).natDegree ≤ 4 * N - 1 := by compute_degree; omega
  have hF0 : F.coeff (2 * N) = 0 := by
    have hBe := coeff_mul_at_bounds68 B e (3 * N - G) (G - N) hB heTerminal
    rw [show (3 * N - G) + (G - N) = 2 * N from by omega] at hBe
    have hcd := coeff_mul_at_bounds68 c d (4 * N - G) (G - 2 * N) hc hdTerminal
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
  have hF4 : F.coeff (2 * N - 4) = 0 := by
    have h := fiveToSix_terminal_i4_faceSum_four68
      alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
        ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩ hdTerminal heTerminal hzeta
      (by omega) (by omega)
    rw [if_neg (by omega : 3 * G - 7 * N ≠ 4),
      if_neg (by omega : 7 * N - 2 * G ≠ 4), sub_zero] at h
    exact h
  have hF5 : F.coeff (2 * N - 5) =
      (if 3 * G - 7 * N = 5 then
        (1 / 9 : k) * B.coeff (3 * N - G) ^ 3 else 0) -
      (if 4 * N - G = 5 then
        (3 / 2 : k) * gamma * d.coeff (G - 2 * N) else 0) := by
    simpa only [F] using fiveToSix_terminal_i4_faceSum_five68
      alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
        ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩ hdTerminal heTerminal hzeta hR5 hL5
  have hPtop := coeff_mul_derivative_at_bounds68 A A (2 * N) (2 * N)
    (by omega) hA hA
  rw [show 2 * N + 2 * N - 1 = 4 * N - 1 from by omega] at hPtop
  have hraw := coeff_mul_at_reflect_five68 (A * derivative A) F
    (4 * N - 1) (2 * N) hPdeg hFdeg (by omega)
  rw [show (4 * N - 1) + 2 * N - 5 = 6 * N - 6 from by omega] at hraw
  have hPr0 : ((A * derivative A).reflect (4 * N - 1)).coeff 0 =
      A.coeff (2 * N) ^ 2 * (((2 * N : ℕ) : k)) := by
    rw [coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero, hPtop]
    ring
  have hFr0 : (F.reflect (2 * N)).coeff 0 = 0 := by rw [coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero, hF0]
  have hFr1 : (F.reflect (2 * N)).coeff 1 = 0 := by rw [coeff_reflect, revAt_le (by omega : 1 ≤ 2 * N), hF1]
  have hFr2 : (F.reflect (2 * N)).coeff 2 = 0 := by rw [coeff_reflect, revAt_le (by omega : 2 ≤ 2 * N), hF2]
  have hFr3 : (F.reflect (2 * N)).coeff 3 = 0 := by rw [coeff_reflect, revAt_le (by omega : 3 ≤ 2 * N), hF3]
  have hFr4 : (F.reflect (2 * N)).coeff 4 = 0 := by rw [coeff_reflect, revAt_le (by omega : 4 ≤ 2 * N), hF4]
  have hFr5 : (F.reflect (2 * N)).coeff 5 =
      (if 3 * G - 7 * N = 5 then (1 / 9 : k) * B.coeff (3 * N - G) ^ 3 else 0) -
      (if 4 * N - G = 5 then (3 / 2 : k) * gamma * d.coeff (G - 2 * N) else 0) := by
    rw [coeff_reflect, revAt_le (by omega : 5 ≤ 2 * N), hF5]
  rw [hPr0, hFr0, hFr1, hFr2, hFr3, hFr4, hFr5] at hraw
  simpa only [mul_zero, add_zero] using hraw

theorem fiveToSix_terminal_L_five_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ) (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal A B c d e N G (7*N-2*G))
    (hdTerminal : d.natDegree ≤ G-2*N) (heTerminal : e.natDegree ≤ G-N)
    (hzeta : zeta=0) (hR5 : 5 ≤ 7*N-2*G) (hL5 : 3*G-7*N=5) : False := by
  rcases hpacket with ⟨hN,hgt5,hle6,hA,hB,hc,_hd,_he,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩
  have hAAF := fiveToSix_terminal_AAF_five68 alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
    ⟨hN,hgt5,hle6,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩
    hdTerminal heTerminal hzeta hR5 (by omega)
  rw [if_pos hL5] at hAAF
  have hmain := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3*N-G) (4*N-G) (4*N-G) (2*N) (by omega) hB hc hc hA
  rw [show (3*N-G)+(4*N-G)+(4*N-G)+2*N-1=6*N-6 from by omega] at hmain
  have hmain' : (derivative A*B*c^2).coeff (6*N-6) =
      A.coeff (2*N)*B.coeff (3*N-G)*c.coeff (4*N-G)^2*(((2*N:ℕ):k)) := by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hmain
  have hrow := fiveToSix_terminal_directLowerRowFive68 alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
    ⟨hN,hgt5,hle6,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩
  change (secondaryResidualRowZeroPolynomial68 A B c d e + cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta A B c ((1/3:k)•(A*B)+d) e).coeff (6*N-6)=0 at hrow
  have h1 : (A*B^2*derivative d).natDegree < 6*N-6 := by compute_degree; omega
  have h2 : (A*B*derivative B*d).natDegree < 6*N-6 := by compute_degree; omega
  have h4 : (B*c*derivative e).natDegree < 6*N-6 := by compute_degree; omega
  have h5 : (B*d*derivative d).natDegree < 6*N-6 := by compute_degree; omega
  have h6 : (derivative B*d^2).natDegree < 6*N-6 := by compute_degree; omega
  have h7 : (c*derivative c*d).natDegree < 6*N-6 := by compute_degree; omega
  have hde : (derivative A*d*e).natDegree < 6*N-6 := by compute_degree; omega
  have hl1 : (B*derivative A*c).natDegree < 6*N-6 := by compute_degree; omega
  have hl2 : (B*derivative e).natDegree < 6*N-6 := by compute_degree; omega
  have hl3 : (A*B*derivative A).natDegree < 6*N-6 := by compute_degree; omega
  have haa : (A*derivative A*d).coeff (6*N-6) =
      if 4*N-G=5 then A.coeff (2*N)^2*d.coeff (G-2*N)*(((2*N:ℕ):k)) else 0 := by
    by_cases hw : 4*N-G=5
    · rw [if_pos hw]
      have ht := coeff_mul_mul_derivative_at_bounds68 A d A
        (2*N) (G-2*N) (2*N) (by omega) hA hdTerminal hA
      rw [show 2*N+(G-2*N)+2*N-1=6*N-6 from by omega] at ht
      simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using ht
    · rw [if_neg hw]
      exact coeff_eq_zero_of_natDegree_lt (by compute_degree; omega)
  have hl5 : (d*derivative c).natDegree < 6*N-6 := by compute_degree; omega
  have hl6 : (d*derivative A).natDegree < 6*N-6 := by compute_degree; omega
  rw [coeff_add,cubicLoadRowZeroPolynomial68_uniform_pinned_eq68,hzeta] at hrow
  simp only [secondaryResidualRowZeroPolynomial68,coeff_smul,coeff_add,coeff_sub,coeff_neg,
    coeff_eq_zero_of_natDegree_lt h1,coeff_eq_zero_of_natDegree_lt h2,
    coeff_eq_zero_of_natDegree_lt h4,coeff_eq_zero_of_natDegree_lt h5,
    coeff_eq_zero_of_natDegree_lt h6,coeff_eq_zero_of_natDegree_lt h7,
    coeff_eq_zero_of_natDegree_lt hde,coeff_eq_zero_of_natDegree_lt hl1,
    coeff_eq_zero_of_natDegree_lt hl2,coeff_eq_zero_of_natDegree_lt hl3,
    coeff_eq_zero_of_natDegree_lt hl5,
    coeff_eq_zero_of_natDegree_lt hl6,smul_eq_mul,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at hrow
  have hcombine : (A*derivative A*B*e).coeff (6*N-6)+(A*derivative A*c*d).coeff (6*N-6)=
      (A*derivative A*(B*e+c*d)).coeff (6*N-6) := by rw [mul_add,coeff_add]; ring
  have hcore : (-4/27:k)*(A*derivative A*(B*e+c*d)).coeff (6*N-6)+
      (4/27:k)*(derivative A*B*c^2).coeff (6*N-6)-
      (2/9*gamma:k)*(A*derivative A*d).coeff (6*N-6)=0 := by
    linear_combination hrow+(4/27:k)*hcombine
  rw [hAAF,hmain',haa] at hcore
  have hcast : (((2*N:ℕ):k)) ≠ 0 := by exact_mod_cast (show (2*N:ℕ)≠0 by omega)
  have hp : (((2*N:ℕ):k))*A.coeff (2*N)^2*B.coeff (3*N-G)^3=0 := by
    by_cases hw : 4*N-G=5
    · simp only [if_pos hw] at hcore
      linear_combination (-243/16:k)*hcore+
        (3/4:k)*(((2*N:ℕ):k))*A.coeff (2*N)*B.coeff (3*N-G)*hcusp
    · simp only [if_neg hw] at hcore
      linear_combination (-243/16:k)*hcore+
        (3/4:k)*(((2*N:ℕ):k))*A.coeff (2*N)*B.coeff (3*N-G)*hcusp
  exact (mul_ne_zero (mul_ne_zero hcast (pow_ne_zero 2 ha)) (pow_ne_zero 3 hb)) hp

theorem fiveToSix_terminal_R_five_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ) (hNbig : 2<N)
    (hpacket : FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal A B c d e N G (7*N-2*G))
    (hdTerminal : d.natDegree≤G-2*N) (heTerminal : e.natDegree≤G-N)
    (hzeta:zeta=0) (hR5:7*N-2*G=5) (hL5:5≤3*G-7*N) : False := by
  rcases hpacket with ⟨hN,hgt5,hle6,hA,hB,hc,_hd,_he,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩
  have hN5 : N=5 := by omega
  have hG15 : G=15 := by omega
  have hLne : 3*G-7*N≠5 := by omega
  have hD5 : 4*N-G=5 := by omega
  have hAAF := fiveToSix_terminal_AAF_five68 alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
    ⟨hN,hgt5,hle6,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩
    hdTerminal heTerminal hzeta (by omega) hL5
  rw [if_neg hLne,if_pos hD5,zero_sub] at hAAF
  have hde := coeff_mul_mul_derivative_at_bounds68 d e A (G-2*N) (G-N) (2*N) (by omega) hdTerminal heTerminal hA
  rw [show (G-2*N)+(G-N)+2*N-1=6*N-6 from by omega] at hde
  have hde' : (derivative A*d*e).coeff (6*N-6)=A.coeff (2*N)*d.coeff (G-2*N)*e.coeff (G-N)*(((2*N:ℕ):k)) := by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hde
  have haa := coeff_mul_mul_derivative_at_bounds68 A d A (2*N) (G-2*N) (2*N) (by omega) hA hdTerminal hA
  rw [show 2*N+(G-2*N)+2*N-1=6*N-6 from by omega] at haa
  have haa' : (A*derivative A*d).coeff (6*N-6)=A.coeff (2*N)^2*d.coeff (G-2*N)*(((2*N:ℕ):k)) := by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using haa
  have hrow := fiveToSix_terminal_directLowerRowFive68 alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
    ⟨hN,hgt5,hle6,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩
  change (secondaryResidualRowZeroPolynomial68 A B c d e+cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta A B c ((1/3:k)•(A*B)+d) e).coeff (6*N-6)=0 at hrow
  have h1 : (A*B^2*derivative d).natDegree<6*N-6 := by compute_degree;omega
  have h2 : (A*B*derivative B*d).natDegree<6*N-6 := by compute_degree;omega
  have h3 : (derivative A*B*c^2).natDegree<6*N-6 := by compute_degree;omega
  have h4 : (B*c*derivative e).natDegree<6*N-6 := by compute_degree;omega
  have h5 : (B*d*derivative d).natDegree<6*N-6 := by compute_degree;omega
  have h6 : (derivative B*d^2).natDegree<6*N-6 := by compute_degree;omega
  have h7 : (c*derivative c*d).natDegree<6*N-6 := by compute_degree;omega
  have hl1 : (B*derivative A*c).natDegree<6*N-6 := by compute_degree;omega
  have hl2 : (B*derivative e).natDegree<6*N-6 := by compute_degree;omega
  have hl3 : (A*B*derivative A).natDegree<6*N-6 := by compute_degree;omega
  have hl5 : (d*derivative c).natDegree<6*N-6 := by compute_degree;omega
  have hl6 : (d*derivative A).natDegree<6*N-6 := by compute_degree;omega
  rw [coeff_add,cubicLoadRowZeroPolynomial68_uniform_pinned_eq68,hzeta] at hrow
  simp only [secondaryResidualRowZeroPolynomial68,coeff_smul,coeff_add,coeff_sub,coeff_neg,
    coeff_eq_zero_of_natDegree_lt h1,coeff_eq_zero_of_natDegree_lt h2,
    coeff_eq_zero_of_natDegree_lt h3,coeff_eq_zero_of_natDegree_lt h4,
    coeff_eq_zero_of_natDegree_lt h5,coeff_eq_zero_of_natDegree_lt h6,
    coeff_eq_zero_of_natDegree_lt h7,coeff_eq_zero_of_natDegree_lt hl1,
    coeff_eq_zero_of_natDegree_lt hl2,coeff_eq_zero_of_natDegree_lt hl3,
    coeff_eq_zero_of_natDegree_lt hl5,coeff_eq_zero_of_natDegree_lt hl6,
    smul_eq_mul,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at hrow
  have hcmb : (A*derivative A*B*e).coeff (6*N-6)+(A*derivative A*c*d).coeff (6*N-6)=
      (A*derivative A*(B*e+c*d)).coeff (6*N-6) := by rw [mul_add,coeff_add];ring
  have hcore : (-4/27:k)*(A*derivative A*(B*e+c*d)).coeff (6*N-6)-
      (4/9:k)*(derivative A*d*e).coeff (6*N-6)-(2/9*gamma:k)*(A*derivative A*d).coeff (6*N-6)=0 := by
    linear_combination hrow+(4/27:k)*hcmb
  rw [hAAF,hde',haa'] at hcore
  have hcast : (((2*N:ℕ):k))≠0 := by exact_mod_cast (show (2*N:ℕ)≠0 by omega)
  have hp : (((2*N:ℕ):k))*A.coeff (2*N)*d.coeff (G-2*N)*e.coeff (G-N)=0 := by
    linear_combination (-9/4:k)*hcore
  have hd0 : d.coeff (G-2*N)≠0 := by simpa only [show 5*N-G-(7*N-2*G)=G-2*N by omega] using hds
  have he0 : e.coeff (G-N)≠0 := by simpa only [show 6*N-G-(7*N-2*G)=G-N by omega] using hes
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hcast ha) hd0) he0) hp

def FiveToSixTerminalCuspDepthSixResidual68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ) : Prop :=
  FiveToSixTerminalCuspDepthFiveResidual68 alpha gamma epsilon zeta eta terminal A B c d e N G ∧
    6≤7*N-2*G ∧ 6≤3*G-7*N ∧
    FiveToSixTerminalDirectLowerRowFive68 alpha gamma epsilon zeta eta A B c d e N

theorem fiveToSix_terminal_cusp_depth_six_residual68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ)
    (hres:FiveToSixTerminalCuspDepthFiveResidual68 alpha gamma epsilon zeta eta terminal A B c d e N G) :
    FiveToSixTerminalCuspDepthSixResidual68 alpha gamma epsilon zeta eta terminal A B c d e N G := by
  have hres0:=hres
  rcases hres with ⟨hbase,hR5,hL5,hrow4⟩
  rcases hbase with ⟨hfour,_r4,_l4,_row3⟩
  rcases hfour with ⟨hthree,_r3,_l3,_i4two,_row2⟩
  rcases hthree with ⟨hN,hd,he,hz,_r1,_l1,hpacket,_row0⟩
  have hR6 : 6≤7*N-2*G := by
    by_contra hn
    have hw : 7*N-2*G=5 := by omega
    exact fiveToSix_terminal_R_five_false68 alpha gamma epsilon zeta eta terminal A B c d e N G hN hpacket hd he hz hw hL5
  have hL6 : 6≤3*G-7*N := by
    by_contra hn
    have hw : 3*G-7*N=5 := by omega
    exact fiveToSix_terminal_L_five_false68 alpha gamma epsilon zeta eta terminal A B c d e N G hN hpacket hd he hz hR5 hw
  exact ⟨hres0,hR6,hL6,fiveToSix_terminal_directLowerRowFive68
    alpha gamma epsilon zeta eta terminal A B c d e N G hN hpacket⟩

#print axioms fiveToSix_terminal_i4_faceSum_five68
#print axioms fiveToSix_terminal_AAF_five68
#print axioms fiveToSix_terminal_L_five_false68
#print axioms fiveToSix_terminal_R_five_false68
#print axioms fiveToSix_terminal_cusp_depth_six_residual68

end FiveToSixCuspTerminalDepthFive68

end Max11DegreeRoutes
