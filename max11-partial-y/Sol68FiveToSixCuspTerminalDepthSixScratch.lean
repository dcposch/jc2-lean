import Sol68FiveToSixCuspTerminalDepthFiveScratch

/-! # Terminal depth six

The retained bounds `R,L ≥ 6` exclude the `N=3` constant I4 index and
the epsilon wall `G=N+6`.  At I4 coefficient `2N-6`, the only loads are
`[L=6]b^3/9` and `[4N-G=6](3/2)gamma*d₀`.  The gamma contribution
cancels its pinned row-zero companion at coefficient `6N-7`.  The `L=6`
cusp wall and `R=6` terminal edge therefore both close.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspTerminalDepthSix68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem coeff_mul_at_reflect_six68 (p q : k[X]) (u v : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hsum : 6 ≤ u + v) :
    (p * q).coeff (u + v - 6) =
      (p.reflect u).coeff 0 * (q.reflect v).coeff 6 +
        (p.reflect u).coeff 1 * (q.reflect v).coeff 5 +
        (p.reflect u).coeff 2 * (q.reflect v).coeff 4 +
        (p.reflect u).coeff 3 * (q.reflect v).coeff 3 +
        (p.reflect u).coeff 4 * (q.reflect v).coeff 2 +
        (p.reflect u).coeff 5 * (q.reflect v).coeff 1 +
        (p.reflect u).coeff 6 * (q.reflect v).coeff 0 := by
  have h := congrArg (fun r : k[X] => r.coeff 6)
    (reflect_mul p q hp hq)
  rw [coeff_reflect, revAt_le hsum,
    mul_coeff_six_oneTwentyOrdinaryNonzeroNext68] at h
  exact h

/-- The depth-six packet cannot meet either constant-index/epsilon
coincidence. -/
theorem fiveToSix_terminal_depth_six_index_audit68
    (N G : ℕ) (hNbig : 2 < N)
    (hR6 : 6 ≤ 7 * N - 2 * G) (hL6 : 6 ≤ 3 * G - 7 * N) :
    0 < 2 * N - 6 ∧ N ≠ 3 ∧ G ≠ N + 6 := by
  omega

def FiveToSixTerminalDirectLowerRowSix68
    (alpha gamma epsilon zeta eta : k)
    (A B c d e : k[X]) (N : ℕ) : Prop :=
  (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * N - 7) = 0

theorem fiveToSix_terminal_directLowerRowSix68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G)) :
    FiveToSixTerminalDirectLowerRowSix68
      alpha gamma epsilon zeta eta A B c d e N := by
  rcases hpacket with
    ⟨_hN, _hgt5, _hle6, _hA, _hB, _hc, _hd, _he, _ha, _hcusp,
      _i4, _i3, _hi4, _hi3, hrow0, _hrow1, _hrow2, _hpos, _hiff⟩
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * N - 7)) hrow0
  have hidx : 6 * N - 7 ≠ 0 := by omega
  simpa only [FiveToSixTerminalDirectLowerRowSix68, coeff_C, if_neg hidx]
    using hcoeff

theorem fiveToSix_terminal_i4_faceSum_six68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N) (hzeta : zeta = 0)
    (hR6 : 6 ≤ 7 * N - 2 * G) (hL6 : 6 ≤ 3 * G - 7 * N) :
    (B * e + c * d).coeff (2 * N - 6) =
      (if 3 * G - 7 * N = 6 then
        (1 / 9 : k) * B.coeff (3 * N - G) ^ 3 else 0) -
      (if 4 * N - G = 6 then
        (3 / 2 : k) * gamma * d.coeff (G - 2 * N) else 0) := by
  have haudit := fiveToSix_terminal_depth_six_index_audit68 N G hNbig hR6 hL6
  rcases hpacket with
    ⟨_hN, hgt5, hle6, _hA, hB, _hc, _hd, _he, _ha, _hcusp,
      i4, _i3, hi4, _hi3, _hrow0, _hrow1, _hrow2, _hpos, _hiff⟩
  have hBlow : B.natDegree < 2 * N - 6 := by omega
  have hcoeff := congrArg (fun p : k[X] => p.coeff (2 * N - 6)) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    hzeta] at hcoeff
  by_cases hLwall : 3 * G - 7 * N = 6
  · have hQne : 4 * N - G ≠ 6 := by omega
    have hdlow : d.natDegree < 2 * N - 6 := by omega
    have hB3 := coeff_pow_at_bound68 B (3 * N - G) 3 hB
    rw [show 3 * (3 * N - G) = 2 * N - 6 from by omega] at hB3
    rw [if_pos hLwall, if_neg hQne, sub_zero]
    simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
      coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt haudit.1, if_false,
      hB3, coeff_eq_zero_of_natDegree_lt hBlow,
      coeff_eq_zero_of_natDegree_lt hdlow, zero_mul, add_zero] at hcoeff
    rw [coeff_add]
    linear_combination (3 / 8 : k) * hcoeff
  · by_cases hQwall : 4 * N - G = 6
    · have hB3low : (B ^ 3).natDegree < 2 * N - 6 := by compute_degree; omega
      rw [if_neg hLwall, if_pos hQwall, zero_sub]
      simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
        coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt haudit.1, if_false,
        coeff_eq_zero_of_natDegree_lt hB3low,
        coeff_eq_zero_of_natDegree_lt hBlow, zero_mul, add_zero] at hcoeff
      rw [show 2 * N - 6 = G - 2 * N from by omega] at hcoeff ⊢
      rw [coeff_add]
      linear_combination (3 / 8 : k) * hcoeff
    · have hB3low : (B ^ 3).natDegree < 2 * N - 6 := by compute_degree; omega
      have hdlow : d.natDegree < 2 * N - 6 := by omega
      rw [if_neg hLwall, if_neg hQwall, sub_zero]
      simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
        coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt haudit.1, if_false,
        coeff_eq_zero_of_natDegree_lt hB3low,
        coeff_eq_zero_of_natDegree_lt hBlow,
        coeff_eq_zero_of_natDegree_lt hdlow, zero_mul, add_zero] at hcoeff
      rw [coeff_add]
      linear_combination (3 / 8 : k) * hcoeff

theorem fiveToSix_terminal_AAF_six68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ) (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G))
    (hdTerminal : d.natDegree≤G-2*N) (heTerminal : e.natDegree≤G-N)
    (hzeta:zeta=0) (hR6:6≤7*N-2*G) (hL6:6≤3*G-7*N) :
    (A*derivative A*(B*e+c*d)).coeff (6*N-7)=A.coeff (2*N)^2*(((2*N:ℕ):k))*
      ((if 3*G-7*N=6 then (1/9:k)*B.coeff (3*N-G)^3 else 0)-
       (if 4*N-G=6 then (3/2:k)*gamma*d.coeff (G-2*N) else 0)) := by
  let F:=B*e+c*d
  have hface:=fiveToSix_contractedCusp_terminalFace68 alpha gamma epsilon zeta eta terminal A B c d e N G hpacket hdTerminal heTerminal hzeta
  rcases hpacket with ⟨hN,hgt5,hle6,hA,hB,hc,_hd,_he,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩
  have hFdeg:F.natDegree≤2*N:=by dsimp only [F];compute_degree;omega
  have hPdeg:(A*derivative A).natDegree≤4*N-1:=by compute_degree;omega
  have hF0:F.coeff (2*N)=0:=by
    have x:=coeff_mul_at_bounds68 B e (3*N-G) (G-N) hB heTerminal
    rw [show (3*N-G)+(G-N)=2*N from by omega] at x
    have y:=coeff_mul_at_bounds68 c d (4*N-G) (G-2*N) hc hdTerminal
    rw [show (4*N-G)+(G-2*N)=2*N from by omega] at y
    simp only [F,coeff_add,x,y];exact hface.four
  have hF1:F.coeff (2*N-1)=0:=by
    have h:=fiveToSix_terminal_i4_faceSum_one68 alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN,hgt5,hle6,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩ hdTerminal heTerminal hzeta
    rw [if_neg (by omega:3*G-7*N≠1)] at h;exact h
  have hF2:F.coeff (2*N-2)=0:=by
    simpa only [F] using fiveToSix_terminal_i4_faceSum_two_zero68 alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN,hgt5,hle6,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩ hdTerminal heTerminal hzeta
  have hF3:F.coeff (2*N-3)=0:=by
    have h:=fiveToSix_terminal_i4_faceSum_three68 alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN,hgt5,hle6,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩ hdTerminal heTerminal hzeta
    rw [if_neg (by omega:3*G-7*N≠3),if_neg (by omega:7*N-2*G≠3),sub_zero] at h;exact h
  have hF4:F.coeff (2*N-4)=0:=by
    have h:=fiveToSix_terminal_i4_faceSum_four68 alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN,hgt5,hle6,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩ hdTerminal heTerminal hzeta (by omega) (by omega)
    rw [if_neg (by omega:3*G-7*N≠4),if_neg (by omega:7*N-2*G≠4),sub_zero] at h;exact h
  have hF5:F.coeff (2*N-5)=0:=by
    have h:=fiveToSix_terminal_i4_faceSum_five68 alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN,hgt5,hle6,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩ hdTerminal heTerminal hzeta (by omega) (by omega)
    rw [if_neg (by omega:3*G-7*N≠5),if_neg (by omega:4*N-G≠5),sub_zero] at h;exact h
  have hF6:F.coeff (2*N-6)=
      ((if 3*G-7*N=6 then (1/9:k)*B.coeff (3*N-G)^3 else 0)-
       (if 4*N-G=6 then (3/2:k)*gamma*d.coeff (G-2*N) else 0)):=by
    simpa only [F] using fiveToSix_terminal_i4_faceSum_six68 alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN,hgt5,hle6,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,hadapter⟩ hdTerminal heTerminal hzeta hR6 hL6
  have hpt:=coeff_mul_derivative_at_bounds68 A A (2*N) (2*N) (by omega) hA hA
  rw [show 2*N+2*N-1=4*N-1 from by omega] at hpt
  have hr:=coeff_mul_at_reflect_six68 (A*derivative A) F (4*N-1) (2*N) hPdeg hFdeg (by omega)
  rw [show (4*N-1)+2*N-6=6*N-7 from by omega] at hr
  have hp0:((A*derivative A).reflect (4*N-1)).coeff 0=A.coeff (2*N)^2*(((2*N:ℕ):k)):=by
    rw [coeff_reflect,revAt_le (Nat.zero_le _),Nat.sub_zero,hpt];ring
  have hf0:(F.reflect (2*N)).coeff 0=0:=by rw [coeff_reflect,revAt_le (Nat.zero_le _),Nat.sub_zero,hF0]
  have hf1:(F.reflect (2*N)).coeff 1=0:=by rw [coeff_reflect,revAt_le (by omega:1≤2*N),hF1]
  have hf2:(F.reflect (2*N)).coeff 2=0:=by rw [coeff_reflect,revAt_le (by omega:2≤2*N),hF2]
  have hf3:(F.reflect (2*N)).coeff 3=0:=by rw [coeff_reflect,revAt_le (by omega:3≤2*N),hF3]
  have hf4:(F.reflect (2*N)).coeff 4=0:=by rw [coeff_reflect,revAt_le (by omega:4≤2*N),hF4]
  have hf5:(F.reflect (2*N)).coeff 5=0:=by rw [coeff_reflect,revAt_le (by omega:5≤2*N),hF5]
  have hf6:(F.reflect (2*N)).coeff 6=
      ((if 3*G-7*N=6 then (1/9:k)*B.coeff (3*N-G)^3 else 0)-
       (if 4*N-G=6 then (3/2:k)*gamma*d.coeff (G-2*N) else 0)):=by
    rw [coeff_reflect,revAt_le (by omega : 6 ≤ 2*N),hF6]
  rw [hp0,hf0,hf1,hf2,hf3,hf4,hf5,hf6] at hr
  simpa only [mul_zero,add_zero] using hr

theorem fiveToSix_terminal_L_six_false68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ) (hN:2<N)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal A B c d e N G (7*N-2*G))
    (hd:d.natDegree≤G-2*N) (he:e.natDegree≤G-N) (hz:zeta=0)
    (hR:6≤7*N-2*G) (hL:3*G-7*N=6):False:=by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,_hd,_he,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  have hQ:4*N-G≠6:=by omega
  have hAA:=fiveToSix_terminal_AAF_six68 alpha gamma epsilon zeta eta terminal A B c d e N G hN
    ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz hR (by omega)
  rw [if_pos hL,if_neg hQ,sub_zero] at hAA
  have hm:=coeff_mul_mul_mul_derivative_at_bounds68 B c c A (3*N-G) (4*N-G) (4*N-G) (2*N) (by omega) hB hc hc hA
  rw [show (3*N-G)+(4*N-G)+(4*N-G)+2*N-1=6*N-7 from by omega] at hm
  have hm':(derivative A*B*c^2).coeff (6*N-7)=A.coeff (2*N)*B.coeff (3*N-G)*c.coeff (4*N-G)^2*(((2*N:ℕ):k)):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hm
  have hr:=fiveToSix_terminal_directLowerRowSix68 alpha gamma epsilon zeta eta terminal A B c d e N G hN
    ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  change (secondaryResidualRowZeroPolynomial68 A B c d e+cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta A B c ((1/3:k)•(A*B)+d) e).coeff (6*N-7)=0 at hr
  have h1:(A*B^2*derivative d).natDegree<6*N-7:=by compute_degree;omega
  have h2:(A*B*derivative B*d).natDegree<6*N-7:=by compute_degree;omega
  have h4:(B*c*derivative e).natDegree<6*N-7:=by compute_degree;omega
  have h5:(B*d*derivative d).natDegree<6*N-7:=by compute_degree;omega
  have h6:(derivative B*d^2).natDegree<6*N-7:=by compute_degree;omega
  have h7:(c*derivative c*d).natDegree<6*N-7:=by compute_degree;omega
  have hde:(derivative A*d*e).natDegree<6*N-7:=by compute_degree;omega
  have x1:(B*derivative A*c).natDegree<6*N-7:=by compute_degree;omega
  have x2:(B*derivative e).natDegree<6*N-7:=by compute_degree;omega
  have x3:(A*B*derivative A).natDegree<6*N-7:=by compute_degree;omega
  have x4:(A*derivative A*d).natDegree<6*N-7:=by compute_degree;omega
  have x5:(d*derivative c).natDegree<6*N-7:=by compute_degree;omega
  have x6:(d*derivative A).natDegree<6*N-7:=by compute_degree;omega
  rw [coeff_add,cubicLoadRowZeroPolynomial68_uniform_pinned_eq68,hz] at hr
  simp only [secondaryResidualRowZeroPolynomial68,coeff_smul,coeff_add,coeff_sub,coeff_neg,
    coeff_eq_zero_of_natDegree_lt h1,coeff_eq_zero_of_natDegree_lt h2,coeff_eq_zero_of_natDegree_lt h4,
    coeff_eq_zero_of_natDegree_lt h5,coeff_eq_zero_of_natDegree_lt h6,coeff_eq_zero_of_natDegree_lt h7,
    coeff_eq_zero_of_natDegree_lt hde,coeff_eq_zero_of_natDegree_lt x1,coeff_eq_zero_of_natDegree_lt x2,
    coeff_eq_zero_of_natDegree_lt x3,coeff_eq_zero_of_natDegree_lt x4,coeff_eq_zero_of_natDegree_lt x5,
    coeff_eq_zero_of_natDegree_lt x6,smul_eq_mul,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at hr
  have hcmb:(A*derivative A*B*e).coeff (6*N-7)+(A*derivative A*c*d).coeff (6*N-7)=
      (A*derivative A*(B*e+c*d)).coeff (6*N-7):=by rw [mul_add,coeff_add];ring
  have core:(-4/27:k)*(A*derivative A*(B*e+c*d)).coeff (6*N-7)+(4/27:k)*(derivative A*B*c^2).coeff (6*N-7)=0:=by
    linear_combination hr+(4/27:k)*hcmb
  rw [hAA,hm'] at core
  have cast:(((2*N:ℕ):k))≠0:=by exact_mod_cast (show (2*N:ℕ)≠0 by omega)
  have z:(((2*N:ℕ):k))*A.coeff (2*N)^2*B.coeff (3*N-G)^3=0:=by
    linear_combination (-243/16:k)*core+(3/4:k)*(((2*N:ℕ):k))*A.coeff (2*N)*B.coeff (3*N-G)*hcusp
  exact (mul_ne_zero (mul_ne_zero cast (pow_ne_zero 2 ha)) (pow_ne_zero 3 hb)) z

theorem fiveToSix_terminal_R_six_false68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ) (hN:2<N)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal A B c d e N G (7*N-2*G))
    (hd:d.natDegree≤G-2*N) (he:e.natDegree≤G-N) (hz:zeta=0)
    (hR:7*N-2*G=6) (hL:6≤3*G-7*N):False:=by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,_hd,_he,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  have n6:N=6:=by omega
  have g18:G=18:=by omega
  have hLn:3*G-7*N≠6:=by omega
  have hQ:4*N-G=6:=by omega
  have hAA:=fiveToSix_terminal_AAF_six68 alpha gamma epsilon zeta eta terminal A B c d e N G hN
    ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz (by omega) hL
  rw [if_neg hLn,if_pos hQ,zero_sub] at hAA
  have hde:=coeff_mul_mul_derivative_at_bounds68 d e A (G-2*N) (G-N) (2*N) (by omega) hd he hA
  rw [show (G-2*N)+(G-N)+2*N-1=6*N-7 from by omega] at hde
  have hde':(derivative A*d*e).coeff (6*N-7)=A.coeff (2*N)*d.coeff (G-2*N)*e.coeff (G-N)*(((2*N:ℕ):k)):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hde
  have haa:=coeff_mul_mul_derivative_at_bounds68 A d A (2*N) (G-2*N) (2*N) (by omega) hA hd hA
  rw [show 2*N+(G-2*N)+2*N-1=6*N-7 from by omega] at haa
  have haa':(A*derivative A*d).coeff (6*N-7)=A.coeff (2*N)^2*d.coeff (G-2*N)*(((2*N:ℕ):k)):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using haa
  have hr:=fiveToSix_terminal_directLowerRowSix68 alpha gamma epsilon zeta eta terminal A B c d e N G hN
    ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  change (secondaryResidualRowZeroPolynomial68 A B c d e+cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta A B c ((1/3:k)•(A*B)+d) e).coeff (6*N-7)=0 at hr
  have h1:(A*B^2*derivative d).natDegree<6*N-7:=by compute_degree;omega
  have h2:(A*B*derivative B*d).natDegree<6*N-7:=by compute_degree;omega
  have h3:(derivative A*B*c^2).natDegree<6*N-7:=by compute_degree;omega
  have h4:(B*c*derivative e).natDegree<6*N-7:=by compute_degree;omega
  have h5:(B*d*derivative d).natDegree<6*N-7:=by compute_degree;omega
  have h6:(derivative B*d^2).natDegree<6*N-7:=by compute_degree;omega
  have h7:(c*derivative c*d).natDegree<6*N-7:=by compute_degree;omega
  have x1:(B*derivative A*c).natDegree<6*N-7:=by compute_degree;omega
  have x2:(B*derivative e).natDegree<6*N-7:=by compute_degree;omega
  have x3:(A*B*derivative A).natDegree<6*N-7:=by compute_degree;omega
  have x5:(d*derivative c).natDegree<6*N-7:=by compute_degree;omega
  have x6:(d*derivative A).natDegree<6*N-7:=by compute_degree;omega
  rw [coeff_add,cubicLoadRowZeroPolynomial68_uniform_pinned_eq68,hz] at hr
  simp only [secondaryResidualRowZeroPolynomial68,coeff_smul,coeff_add,coeff_sub,coeff_neg,
    coeff_eq_zero_of_natDegree_lt h1,coeff_eq_zero_of_natDegree_lt h2,coeff_eq_zero_of_natDegree_lt h3,
    coeff_eq_zero_of_natDegree_lt h4,coeff_eq_zero_of_natDegree_lt h5,coeff_eq_zero_of_natDegree_lt h6,
    coeff_eq_zero_of_natDegree_lt h7,coeff_eq_zero_of_natDegree_lt x1,coeff_eq_zero_of_natDegree_lt x2,
    coeff_eq_zero_of_natDegree_lt x3,coeff_eq_zero_of_natDegree_lt x5,coeff_eq_zero_of_natDegree_lt x6,
    smul_eq_mul,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at hr
  have hcmb:(A*derivative A*B*e).coeff (6*N-7)+(A*derivative A*c*d).coeff (6*N-7)=
      (A*derivative A*(B*e+c*d)).coeff (6*N-7):=by rw [mul_add,coeff_add];ring
  have core:(-4/27:k)*(A*derivative A*(B*e+c*d)).coeff (6*N-7)-(4/9:k)*(derivative A*d*e).coeff (6*N-7)-
      (2/9*gamma:k)*(A*derivative A*d).coeff (6*N-7)=0:=by linear_combination hr+(4/27:k)*hcmb
  rw [hAA,hde',haa'] at core
  have cast:(((2*N:ℕ):k))≠0:=by exact_mod_cast (show (2*N:ℕ)≠0 by omega)
  have z:(((2*N:ℕ):k))*A.coeff (2*N)*d.coeff (G-2*N)*e.coeff (G-N)=0:=by linear_combination (-9/4:k)*core
  have dn:d.coeff (G-2*N)≠0:=by simpa only [show 5*N-G-(7*N-2*G)=G-2*N by omega] using hds
  have en:e.coeff (G-N)≠0:=by simpa only [show 6*N-G-(7*N-2*G)=G-N by omega] using hes
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero cast ha) dn) en) z

def FiveToSixTerminalCuspDepthSevenResidual68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ):Prop:=
  FiveToSixTerminalCuspDepthSixResidual68 alpha gamma epsilon zeta eta terminal A B c d e N G ∧
    7≤7*N-2*G ∧ 7≤3*G-7*N ∧
    FiveToSixTerminalDirectLowerRowSix68 alpha gamma epsilon zeta eta A B c d e N

theorem fiveToSix_terminal_cusp_depth_seven_residual68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ)
    (hres:FiveToSixTerminalCuspDepthSixResidual68 alpha gamma epsilon zeta eta terminal A B c d e N G):
    FiveToSixTerminalCuspDepthSevenResidual68 alpha gamma epsilon zeta eta terminal A B c d e N G:=by
  have h0:=hres
  rcases hres with ⟨h5,hR6,hL6,row5⟩
  rcases h5 with ⟨h4,_r5,_l5,_row4⟩
  rcases h4 with ⟨h3,_r4,_l4,_row3⟩
  rcases h3 with ⟨h2,_r3,_l3,_i4,_row2⟩
  rcases h2 with ⟨hn,hd,he,hz,_r2,_l2,hp,_row1⟩
  have r7:7≤7*N-2*G:=by
    by_contra h;have w:7*N-2*G=6:=by omega
    exact fiveToSix_terminal_R_six_false68 alpha gamma epsilon zeta eta terminal A B c d e N G hn hp hd he hz w hL6
  have l7:7≤3*G-7*N:=by
    by_contra h;have w:3*G-7*N=6:=by omega
    exact fiveToSix_terminal_L_six_false68 alpha gamma epsilon zeta eta terminal A B c d e N G hn hp hd he hz hR6 w
  exact ⟨h0,r7,l7,fiveToSix_terminal_directLowerRowSix68
    alpha gamma epsilon zeta eta terminal A B c d e N G hn hp⟩

#print axioms fiveToSix_terminal_depth_six_index_audit68
#print axioms fiveToSix_terminal_i4_faceSum_six68
#print axioms fiveToSix_terminal_AAF_six68
#print axioms fiveToSix_terminal_L_six_false68
#print axioms fiveToSix_terminal_R_six_false68
#print axioms fiveToSix_terminal_cusp_depth_seven_residual68

end FiveToSixCuspTerminalDepthSix68

end Max11DegreeRoutes
