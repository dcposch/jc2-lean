import Sol68FiveToSixCuspTerminalDepthSixScratch

/-! # Terminal cusp depth seven

At this depth the old gamma wall `4N-G=6` can coexist with the new two
faces: it is exactly the corner `(N,G)=(5,14)`, where `R=L=7`.  Keeping
`F + (3/2) gamma d` intact makes the cancellation with the pinned row-zero
gamma term literal.  The two non-simultaneous faces are impossible.  The
simultaneous corner remains as one exact scalar and is not overclaimed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspTerminalDepthSeven68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem mul_coeff_seven_terminalCusp68 (p q : k[X]) :
    (p * q).coeff 7 =
      p.coeff 0 * q.coeff 7 + p.coeff 1 * q.coeff 6 +
        p.coeff 2 * q.coeff 5 + p.coeff 3 * q.coeff 4 +
        p.coeff 4 * q.coeff 3 + p.coeff 5 * q.coeff 2 +
        p.coeff 6 * q.coeff 1 + p.coeff 7 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

theorem coeff_mul_at_reflect_seven68 (p q : k[X]) (u v : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hsum : 7 ≤ u + v) :
    (p * q).coeff (u + v - 7) =
      (p.reflect u).coeff 0 * (q.reflect v).coeff 7 +
        (p.reflect u).coeff 1 * (q.reflect v).coeff 6 +
        (p.reflect u).coeff 2 * (q.reflect v).coeff 5 +
        (p.reflect u).coeff 3 * (q.reflect v).coeff 4 +
        (p.reflect u).coeff 4 * (q.reflect v).coeff 3 +
        (p.reflect u).coeff 5 * (q.reflect v).coeff 2 +
        (p.reflect u).coeff 6 * (q.reflect v).coeff 1 +
        (p.reflect u).coeff 7 * (q.reflect v).coeff 0 := by
  have h := congrArg (fun r : k[X] => r.coeff 7)
    (reflect_mul p q hp hq)
  rw [coeff_reflect, revAt_le hsum, mul_coeff_seven_terminalCusp68] at h
  exact h

/-- Complete arithmetic audit before taking either depth-seven coefficient.
The I4 and row-zero indices are positive; the epsilon/B wall is absent;
`Q=6` is precisely the simultaneous corner, while `Q=7` has the two stated
small charts. -/
theorem fiveToSix_terminal_depth_seven_index_audit68
    (N G : ℕ) (hNbig : 2 < N)
    (hR7 : 7 ≤ 7*N-2*G) (hL7 : 7 ≤ 3*G-7*N)
    (hwindow : 5*N < 2*G ∧ 2*G ≤ 6*N) :
    0 < 2*N-7 ∧ 0 < 6*N-8 ∧ N ≠ 3 ∧ G ≠ N+7 ∧
      6 ≤ 4*N-G ∧
      (4*N-G=6 → N=5 ∧ G=14 ∧ 7*N-2*G=7 ∧ 3*G-7*N=7) ∧
      (4*N-G=7 → (N=6 ∧ G=17) ∨ (N=7 ∧ G=21)) := by
  omega

def FiveToSixTerminalDirectLowerRowSeven68
    (alpha gamma epsilon zeta eta : k)
    (A B c d e : k[X]) (N : ℕ) : Prop :=
  (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1/3:k) • (A*B)+d) e).coeff (6*N-8)=0

theorem fiveToSix_terminal_directLowerRowSeven68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ) (hNbig : 2 < N)
    (hp : FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G)) :
    FiveToSixTerminalDirectLowerRowSeven68 alpha gamma epsilon zeta eta A B c d e N := by
  rcases hp with
    ⟨_hn,_hgt,_hle,_hA,_hB,_hc,_hd,_he,_ha,_hcusp,
      _i4,_i3,_hi4,_hi3,hrow0,_hrow1,_hrow2,_hpos,_hiff⟩
  have h := congrArg (fun p:k[X] => p.coeff (6*N-8)) hrow0
  have hi : 6*N-8 ≠ 0 := by omega
  simpa only [FiveToSixTerminalDirectLowerRowSeven68,coeff_C,if_neg hi] using h

/-- Literal I4 depth-seven coefficient.  The epsilon/B coincidence has
already been excluded by the audit; the gamma coefficient is deliberately
retained before cancellation. -/
theorem fiveToSix_terminal_i4_faceSum_seven68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ) (hNbig : 2 < N)
    (hp : FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G))
    (hd : d.natDegree ≤ G-2*N) (he : e.natDegree ≤ G-N)
    (hz : zeta=0) (hR7 : 7 ≤ 7*N-2*G) (hL7 : 7 ≤ 3*G-7*N) :
    (B*e+c*d).coeff (2*N-7) =
      (if 3*G-7*N=7 then (1/9:k)*B.coeff (3*N-G)^3 else 0) -
        (3/2:k)*gamma*d.coeff (2*N-7) := by
  rcases hp with
    ⟨_hn,hgt,hle,_hA,hB,_hc,_hd,_he,_ha,_hcusp,
      _i4,_i3,hi4,_hi3,_hrow0,_hrow1,_hrow2,_hpos,_hiff⟩
  have haudit := fiveToSix_terminal_depth_seven_index_audit68 N G hNbig hR7 hL7 ⟨hgt,hle⟩
  have hBlow : B.natDegree < 2*N-7 := by omega
  have hcoeff := congrArg (fun p:k[X] => p.coeff (2*N-7)) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,hz] at hcoeff
  by_cases hL : 3*G-7*N=7
  · have hB3 := coeff_pow_at_bound68 B (3*N-G) 3 hB
    rw [show 3*(3*N-G)=2*N-7 from by omega] at hB3
    rw [if_pos hL]
    simp only [secondaryResidualInvariantFourPolynomial68,coeff_add,coeff_smul,
      smul_eq_mul,coeff_C,Nat.ne_of_gt haudit.1,if_false,hB3,
      coeff_eq_zero_of_natDegree_lt hBlow,zero_mul,add_zero] at hcoeff
    rw [coeff_add]
    linear_combination (3/8:k)*hcoeff
  · have hB3low : (B^3).natDegree < 2*N-7 := by compute_degree;omega
    rw [if_neg hL,zero_sub]
    simp only [secondaryResidualInvariantFourPolynomial68,coeff_add,coeff_smul,
      smul_eq_mul,coeff_C,Nat.ne_of_gt haudit.1,if_false,
      coeff_eq_zero_of_natDegree_lt hB3low,
      coeff_eq_zero_of_natDegree_lt hBlow,zero_mul,add_zero] at hcoeff
    rw [coeff_add]
    linear_combination (3/8:k)*hcoeff

/-- Multiplying the compensated I4 face by `A A'` absorbs both gamma walls
`Q=6` and `Q=7`; all earlier compensated jets vanish. -/
theorem fiveToSix_terminal_compensatedAAF_seven68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ) (hNbig : 2 < N)
    (hp : FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G))
    (hd : d.natDegree ≤ G-2*N) (he : e.natDegree ≤ G-N)
    (hz : zeta=0) (hR7 : 7 ≤ 7*N-2*G) (hL7 : 7 ≤ 3*G-7*N) :
    (A*derivative A*((B*e+c*d)+(3/2*gamma:k) • d)).coeff (6*N-8) =
      A.coeff (2*N)^2*(((2*N:ℕ):k))*
        (if 3*G-7*N=7 then (1/9:k)*B.coeff (3*N-G)^3 else 0) := by
  let F := B*e+c*d
  let K := F+(3/2*gamma:k) • d
  have hface := fiveToSix_contractedCusp_terminalFace68 alpha gamma epsilon zeta eta terminal
    A B c d e N G hp hd he hz
  rcases hp with
    ⟨hn,hgt,hle,hA,hB,hc,_hd,_he,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  have haudit := fiveToSix_terminal_depth_seven_index_audit68 N G hNbig hR7 hL7 ⟨hgt,hle⟩
  have hFdeg : F.natDegree ≤ 2*N := by dsimp only [F];compute_degree;omega
  have hKdeg : K.natDegree ≤ 2*N := by dsimp only [K];compute_degree;omega
  have hPdeg : (A*derivative A).natDegree ≤ 4*N-1 := by compute_degree;omega
  have hF0 : F.coeff (2*N)=0 := by
    have x:=coeff_mul_at_bounds68 B e (3*N-G) (G-N) hB he
    rw [show (3*N-G)+(G-N)=2*N from by omega] at x
    have y:=coeff_mul_at_bounds68 c d (4*N-G) (G-2*N) hc hd
    rw [show (4*N-G)+(G-2*N)=2*N from by omega] at y
    simp only [F,coeff_add,x,y];exact hface.four
  have hK0 : K.coeff (2*N)=0 := by
    have dl : d.natDegree < 2*N := by omega
    simp only [K,coeff_add,coeff_smul,smul_eq_mul,hF0,
      coeff_eq_zero_of_natDegree_lt dl,mul_zero,add_zero]
  have hK1 : K.coeff (2*N-1)=0 := by
    have f:=fiveToSix_terminal_i4_faceSum_one68 alpha gamma epsilon zeta eta terminal
      A B c d e N G hNbig ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
        ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz
    rw [if_neg (by omega:3*G-7*N≠1)] at f
    have dl:d.natDegree<2*N-1:=by omega
    simp only [K,F,coeff_add,coeff_smul,smul_eq_mul,f,
      coeff_eq_zero_of_natDegree_lt dl,mul_zero,add_zero]
  have hK2 : K.coeff (2*N-2)=0 := by
    have f:=fiveToSix_terminal_i4_faceSum_two_zero68 alpha gamma epsilon zeta eta terminal
      A B c d e N G hNbig ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
        ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz
    have dl:d.natDegree<2*N-2:=by omega
    simp only [K,F,coeff_add,coeff_smul,smul_eq_mul,f,
      coeff_eq_zero_of_natDegree_lt dl,mul_zero,add_zero]
  have hK3 : K.coeff (2*N-3)=0 := by
    have f:=fiveToSix_terminal_i4_faceSum_three68 alpha gamma epsilon zeta eta terminal
      A B c d e N G hNbig ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
        ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz
    rw [if_neg (by omega:3*G-7*N≠3),if_neg (by omega:7*N-2*G≠3),sub_zero] at f
    have dl:d.natDegree<2*N-3:=by omega
    simp only [K,F,coeff_add,coeff_smul,smul_eq_mul,f,
      coeff_eq_zero_of_natDegree_lt dl,mul_zero,add_zero]
  have hK4 : K.coeff (2*N-4)=0 := by
    have f:=fiveToSix_terminal_i4_faceSum_four68 alpha gamma epsilon zeta eta terminal
      A B c d e N G hNbig ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
        ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz (by omega) (by omega)
    rw [if_neg (by omega:3*G-7*N≠4),if_neg (by omega:7*N-2*G≠4),sub_zero] at f
    have dl:d.natDegree<2*N-4:=by omega
    simp only [K,F,coeff_add,coeff_smul,smul_eq_mul,f,
      coeff_eq_zero_of_natDegree_lt dl,mul_zero,add_zero]
  have hK5 : K.coeff (2*N-5)=0 := by
    have f:=fiveToSix_terminal_i4_faceSum_five68 alpha gamma epsilon zeta eta terminal
      A B c d e N G hNbig ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
        ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz (by omega) (by omega)
    rw [if_neg (by omega:3*G-7*N≠5),if_neg (by omega:4*N-G≠5),sub_zero] at f
    have dl:d.natDegree<2*N-5:=by omega
    simp only [K,F,coeff_add,coeff_smul,smul_eq_mul,f,
      coeff_eq_zero_of_natDegree_lt dl,mul_zero,add_zero]
  have hK6 : K.coeff (2*N-6)=0 := by
    have f:=fiveToSix_terminal_i4_faceSum_six68 alpha gamma epsilon zeta eta terminal
      A B c d e N G hNbig ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
        ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz (by omega) (by omega)
    rw [if_neg (by omega:3*G-7*N≠6),zero_sub] at f
    by_cases q:4*N-G=6
    · rw [if_pos q] at f
      have idx:2*N-6=G-2*N:=by omega
      change F.coeff (2*N-6)+(3/2*gamma:k)*d.coeff (2*N-6)=0
      rw [f,idx]
      ring
    · rw [if_neg q,neg_zero] at f
      have dl:d.natDegree<2*N-6:=by omega
      change F.coeff (2*N-6)+(3/2*gamma:k)*d.coeff (2*N-6)=0
      rw [f,coeff_eq_zero_of_natDegree_lt dl]
      ring
  have hK7 : K.coeff (2*N-7)=
      (if 3*G-7*N=7 then (1/9:k)*B.coeff (3*N-G)^3 else 0) := by
    have f:=fiveToSix_terminal_i4_faceSum_seven68 alpha gamma epsilon zeta eta terminal
      A B c d e N G hNbig ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
        ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz hR7 hL7
    simp only [K,F,coeff_add,coeff_smul,smul_eq_mul,f]
    ring
  have hpt:=coeff_mul_derivative_at_bounds68 A A (2*N) (2*N) (by omega) hA hA
  rw [show 2*N+2*N-1=4*N-1 from by omega] at hpt
  have hr:=coeff_mul_at_reflect_seven68 (A*derivative A) K (4*N-1) (2*N)
    hPdeg hKdeg (by omega)
  rw [show (4*N-1)+2*N-7=6*N-8 from by omega] at hr
  have hp0:((A*derivative A).reflect (4*N-1)).coeff 0=
      A.coeff (2*N)^2*(((2*N:ℕ):k)):=by
    rw [coeff_reflect,revAt_le (Nat.zero_le _),Nat.sub_zero,hpt];ring
  have hk0:(K.reflect (2*N)).coeff 0=0:=by rw [coeff_reflect,revAt_le (Nat.zero_le _),Nat.sub_zero,hK0]
  have hk1:(K.reflect (2*N)).coeff 1=0:=by rw [coeff_reflect,revAt_le (by omega:1≤2*N),hK1]
  have hk2:(K.reflect (2*N)).coeff 2=0:=by rw [coeff_reflect,revAt_le (by omega:2≤2*N),hK2]
  have hk3:(K.reflect (2*N)).coeff 3=0:=by rw [coeff_reflect,revAt_le (by omega:3≤2*N),hK3]
  have hk4:(K.reflect (2*N)).coeff 4=0:=by rw [coeff_reflect,revAt_le (by omega:4≤2*N),hK4]
  have hk5:(K.reflect (2*N)).coeff 5=0:=by rw [coeff_reflect,revAt_le (by omega:5≤2*N),hK5]
  have hk6:(K.reflect (2*N)).coeff 6=0:=by rw [coeff_reflect,revAt_le (by omega:6≤2*N),hK6]
  have hk7:(K.reflect (2*N)).coeff 7=
      (if 3*G-7*N=7 then (1/9:k)*B.coeff (3*N-G)^3 else 0):=by
    rw [coeff_reflect,revAt_le (by omega:7≤2*N),hK7]
  rw [hp0,hk0,hk1,hk2,hk3,hk4,hk5,hk6,hk7] at hr
  simpa only [mul_zero,add_zero] using hr

/-- Exact row-seven reduction after the compensated I4/gamma cancellation. -/
theorem fiveToSix_terminal_row_seven_reduced68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ) (hNbig : 2 < N)
    (hp : FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G))
    (hd : d.natDegree ≤ G-2*N) (he : e.natDegree ≤ G-N)
    (hz : zeta=0) (hR7 : 7 ≤ 7*N-2*G) (hL7 : 7 ≤ 3*G-7*N) :
    (-4/27:k)*(A*derivative A*((B*e+c*d)+(3/2*gamma:k) • d)).coeff (6*N-8)+
      (4/27:k)*(derivative A*B*c^2).coeff (6*N-8)-
      (4/9:k)*(derivative A*d*e).coeff (6*N-8)=0 := by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,_hd,_he,ha,
    ⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  have hr:=fiveToSix_terminal_directLowerRowSeven68 alpha gamma epsilon zeta eta terminal
    A B c d e N G hNbig ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
      ⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  change (secondaryResidualRowZeroPolynomial68 A B c d e+
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1/3:k)•(A*B)+d) e).coeff (6*N-8)=0 at hr
  have h1:(A*B^2*derivative d).natDegree<6*N-8:=by compute_degree;omega
  have h2:(A*B*derivative B*d).natDegree<6*N-8:=by compute_degree;omega
  have h4:(B*c*derivative e).natDegree<6*N-8:=by compute_degree;omega
  have h5:(B*d*derivative d).natDegree<6*N-8:=by compute_degree;omega
  have h6:(derivative B*d^2).natDegree<6*N-8:=by compute_degree;omega
  have h7:(c*derivative c*d).natDegree<6*N-8:=by compute_degree;omega
  have x1:(B*derivative A*c).natDegree<6*N-8:=by compute_degree;omega
  have x2:(B*derivative e).natDegree<6*N-8:=by compute_degree;omega
  have x3:(A*B*derivative A).natDegree<6*N-8:=by compute_degree;omega
  have x5:(d*derivative c).natDegree<6*N-8:=by compute_degree;omega
  have x6:(d*derivative A).natDegree<6*N-8:=by compute_degree;omega
  rw [coeff_add,cubicLoadRowZeroPolynomial68_uniform_pinned_eq68,hz] at hr
  simp only [secondaryResidualRowZeroPolynomial68,coeff_smul,coeff_add,coeff_sub,coeff_neg,
    coeff_eq_zero_of_natDegree_lt h1,coeff_eq_zero_of_natDegree_lt h2,
    coeff_eq_zero_of_natDegree_lt h4,coeff_eq_zero_of_natDegree_lt h5,
    coeff_eq_zero_of_natDegree_lt h6,coeff_eq_zero_of_natDegree_lt h7,
    coeff_eq_zero_of_natDegree_lt x1,coeff_eq_zero_of_natDegree_lt x2,
    coeff_eq_zero_of_natDegree_lt x3,coeff_eq_zero_of_natDegree_lt x5,
    coeff_eq_zero_of_natDegree_lt x6,smul_eq_mul,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at hr
  have hF:(A*derivative A*B*e).coeff (6*N-8)+
      (A*derivative A*c*d).coeff (6*N-8)=
      (A*derivative A*(B*e+c*d)).coeff (6*N-8):=by rw [mul_add,coeff_add];ring
  have hKpoly:A*derivative A*((B*e+c*d)+(3/2*gamma:k) • d)=
      A*derivative A*(B*e+c*d)+(3/2*gamma:k) • (A*derivative A*d):=by
    rw [mul_add]
    simp only [Polynomial.smul_eq_C_mul]
    ring
  have hK:(A*derivative A*((B*e+c*d)+(3/2*gamma:k) • d)).coeff (6*N-8)=
      (A*derivative A*(B*e+c*d)).coeff (6*N-8)+
        (3/2*gamma:k)*(A*derivative A*d).coeff (6*N-8):=by
    rw [hKpoly,coeff_add,coeff_smul]
    ring
  have raw:(-4/27:k)*(A*derivative A*(B*e+c*d)).coeff (6*N-8)+
      (4/27:k)*(derivative A*B*c^2).coeff (6*N-8)-
      (4/9:k)*(derivative A*d*e).coeff (6*N-8)-
      (2/9*gamma:k)*(A*derivative A*d).coeff (6*N-8)=0:=by
    linear_combination hr+(4/27:k)*hF
  rw [hK]
  linear_combination raw

theorem fiveToSix_terminal_L_seven_of_R_ne_false68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ)
    (hN:2<N)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal A B c d e N G (7*N-2*G))
    (hd:d.natDegree≤G-2*N) (he:e.natDegree≤G-N) (hz:zeta=0)
    (hR:7≤7*N-2*G) (hL:3*G-7*N=7) (hRne:7*N-2*G≠7):False:=by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,_hd,_he,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  have hK:=fiveToSix_terminal_compensatedAAF_seven68 alpha gamma epsilon zeta eta terminal
    A B c d e N G hN ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
      ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz hR (by omega)
  rw [if_pos hL] at hK
  have hm:=coeff_mul_mul_mul_derivative_at_bounds68 B c c A (3*N-G) (4*N-G)
    (4*N-G) (2*N) (by omega) hB hc hc hA
  rw [show (3*N-G)+(4*N-G)+(4*N-G)+2*N-1=6*N-8 from by omega] at hm
  have hm':(derivative A*B*c^2).coeff (6*N-8)=
      A.coeff (2*N)*B.coeff (3*N-G)*c.coeff (4*N-G)^2*(((2*N:ℕ):k)):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hm
  have de:(derivative A*d*e).natDegree<6*N-8:=by compute_degree;omega
  have row:=fiveToSix_terminal_row_seven_reduced68 alpha gamma epsilon zeta eta terminal
    A B c d e N G hN ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
      ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz hR (by omega)
  rw [hK,hm',coeff_eq_zero_of_natDegree_lt de] at row
  have cast:(((2*N:ℕ):k))≠0:=by exact_mod_cast (show (2*N:ℕ)≠0 by omega)
  have z:(((2*N:ℕ):k))*A.coeff (2*N)^2*B.coeff (3*N-G)^3=0:=by
    linear_combination (-243/16:k)*row+(3/4:k)*(((2*N:ℕ):k))*A.coeff (2*N)*B.coeff (3*N-G)*hcusp
  exact (mul_ne_zero (mul_ne_zero cast (pow_ne_zero 2 ha)) (pow_ne_zero 3 hb)) z

theorem fiveToSix_terminal_R_seven_of_L_ne_false68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ)
    (hN:2<N)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal A B c d e N G (7*N-2*G))
    (hd:d.natDegree≤G-2*N) (he:e.natDegree≤G-N) (hz:zeta=0)
    (hR:7*N-2*G=7) (hL:7≤3*G-7*N) (hLne:3*G-7*N≠7):False:=by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,_hd,_he,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  have hK:=fiveToSix_terminal_compensatedAAF_seven68 alpha gamma epsilon zeta eta terminal
    A B c d e N G hN ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
      ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz (by omega) hL
  rw [if_neg hLne] at hK
  have m:(derivative A*B*c^2).natDegree<6*N-8:=by compute_degree;omega
  have hde:=coeff_mul_mul_derivative_at_bounds68 d e A (G-2*N) (G-N) (2*N)
    (by omega) hd he hA
  rw [show (G-2*N)+(G-N)+2*N-1=6*N-8 from by omega] at hde
  have hde':(derivative A*d*e).coeff (6*N-8)=
      A.coeff (2*N)*d.coeff (G-2*N)*e.coeff (G-N)*(((2*N:ℕ):k)):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hde
  have row:=fiveToSix_terminal_row_seven_reduced68 alpha gamma epsilon zeta eta terminal
    A B c d e N G hN ⟨hn,hgt,hle,hA,hB,hc,by omega,by omega,ha,
      ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz (by omega) hL
  rw [hK,coeff_eq_zero_of_natDegree_lt m,hde'] at row
  have cast:(((2*N:ℕ):k))≠0:=by exact_mod_cast (show (2*N:ℕ)≠0 by omega)
  have dn:d.coeff (G-2*N)≠0:=by simpa only [show 5*N-G-(7*N-2*G)=G-2*N by omega] using hds
  have en:e.coeff (G-N)≠0:=by simpa only [show 6*N-G-(7*N-2*G)=G-N by omega] using hes
  have z:(((2*N:ℕ):k))*A.coeff (2*N)*d.coeff (G-2*N)*e.coeff (G-N)=0:=by
    linear_combination (-9/4:k)*row
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero cast ha) dn) en) z

/-- The honest simultaneous corner left by row seven. -/
def FiveToSixTerminalSevenCorner68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ):Prop:=
  FiveToSixTerminalCuspDepthSevenResidual68 alpha gamma epsilon zeta eta terminal A B c d e N G ∧
    N=5 ∧ G=14 ∧
    4*A.coeff (2*N)*B.coeff (3*N-G)^3+
      27*d.coeff (G-2*N)*e.coeff (G-N)=0 ∧
    FiveToSixTerminalDirectLowerRowSeven68 alpha gamma epsilon zeta eta A B c d e N

theorem fiveToSix_terminal_seven_corner68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ)
    (hres:FiveToSixTerminalCuspDepthSevenResidual68 alpha gamma epsilon zeta eta terminal A B c d e N G)
    (hR:7*N-2*G=7) (hL:3*G-7*N=7):
    FiveToSixTerminalSevenCorner68 alpha gamma epsilon zeta eta terminal A B c d e N G:=by
  have h0:=hres
  rcases hres with ⟨h6,hR7,hL7,row6⟩
  rcases h6 with ⟨h5,_r6,_l6,_row5⟩
  rcases h5 with ⟨h4,_r5,_l5,_row4⟩
  rcases h4 with ⟨h3,_r4,_l4,_row3⟩
  rcases h3 with ⟨h2,_r3,_l3,_i4,_row2⟩
  rcases h2 with ⟨hn,hd,he,hz,_r2,_l2,hp,_row1⟩
  rcases hp with ⟨hn0,hgt,hle,hA,hB,hc,_hd,_he,ha,⟨hb,hc0,hds,hes,hcusp⟩,had⟩
  have n5:N=5:=by omega
  have g14:G=14:=by omega
  have hK:=fiveToSix_terminal_compensatedAAF_seven68 alpha gamma epsilon zeta eta terminal
    A B c d e N G hn ⟨hn0,hgt,hle,hA,hB,hc,by omega,by omega,ha,
      ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz hR7 hL7
  rw [if_pos hL] at hK
  have hm:=coeff_mul_mul_mul_derivative_at_bounds68 B c c A (3*N-G) (4*N-G)
    (4*N-G) (2*N) (by omega) hB hc hc hA
  rw [show (3*N-G)+(4*N-G)+(4*N-G)+2*N-1=6*N-8 from by omega] at hm
  have hm':(derivative A*B*c^2).coeff (6*N-8)=
      A.coeff (2*N)*B.coeff (3*N-G)*c.coeff (4*N-G)^2*(((2*N:ℕ):k)):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hm
  have hde:=coeff_mul_mul_derivative_at_bounds68 d e A (G-2*N) (G-N) (2*N)
    (by omega) hd he hA
  rw [show (G-2*N)+(G-N)+2*N-1=6*N-8 from by omega] at hde
  have hde':(derivative A*d*e).coeff (6*N-8)=
      A.coeff (2*N)*d.coeff (G-2*N)*e.coeff (G-N)*(((2*N:ℕ):k)):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hde
  have row:=fiveToSix_terminal_row_seven_reduced68 alpha gamma epsilon zeta eta terminal
    A B c d e N G hn ⟨hn0,hgt,hle,hA,hB,hc,by omega,by omega,ha,
      ⟨hb,hc0,hds,hes,hcusp⟩,had⟩ hd he hz hR7 hL7
  rw [hK,hm',hde'] at row
  have cast:(((2*N:ℕ):k))≠0:=by exact_mod_cast (show (2*N:ℕ)≠0 by omega)
  have scalar:4*A.coeff (2*N)*B.coeff (3*N-G)^3+
      27*d.coeff (G-2*N)*e.coeff (G-N)=0:=by
    have fact:(((2*N:ℕ):k))*A.coeff (2*N)*
        (4*A.coeff (2*N)*B.coeff (3*N-G)^3+
          27*d.coeff (G-2*N)*e.coeff (G-N))=0:=by
      linear_combination (-243/4:k)*row+
        3*(((2*N:ℕ):k))*A.coeff (2*N)*B.coeff (3*N-G)*hcusp
    exact (mul_eq_zero.mp fact).resolve_left (mul_ne_zero cast ha)
  exact ⟨h0,n5,g14,scalar,
    fiveToSix_terminal_directLowerRowSeven68 alpha gamma epsilon zeta eta terminal
      A B c d e N G hn ⟨hn0,hgt,hle,hA,hB,hc,by omega,by omega,ha,
        ⟨hb,hc0,hds,hes,hcusp⟩,had⟩⟩

def FiveToSixTerminalCuspDepthEightResidual68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ):Prop:=
  FiveToSixTerminalCuspDepthSevenResidual68 alpha gamma epsilon zeta eta terminal A B c d e N G ∧
    8≤7*N-2*G ∧ 8≤3*G-7*N ∧
    FiveToSixTerminalDirectLowerRowSeven68 alpha gamma epsilon zeta eta A B c d e N

theorem fiveToSix_terminal_cusp_depth_eight_or_corner68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ)
    (hres:FiveToSixTerminalCuspDepthSevenResidual68 alpha gamma epsilon zeta eta terminal A B c d e N G):
    FiveToSixTerminalSevenCorner68 alpha gamma epsilon zeta eta terminal A B c d e N G ∨
      FiveToSixTerminalCuspDepthEightResidual68 alpha gamma epsilon zeta eta terminal A B c d e N G:=by
  have h0:=hres
  rcases hres with ⟨h6,hR7,hL7,row6⟩
  rcases h6 with ⟨h5,_r6,_l6,_row5⟩
  rcases h5 with ⟨h4,_r5,_l5,_row4⟩
  rcases h4 with ⟨h3,_r4,_l4,_row3⟩
  rcases h3 with ⟨h2,_r3,_l3,_i4,_row2⟩
  rcases h2 with ⟨hn,hd,he,hz,_r2,_l2,hp,_row1⟩
  by_cases corner:7*N-2*G=7 ∧ 3*G-7*N=7
  · exact Or.inl (fiveToSix_terminal_seven_corner68 alpha gamma epsilon zeta eta terminal
      A B c d e N G h0 corner.1 corner.2)
  · have r8:8≤7*N-2*G:=by
      by_contra h
      have rw:7*N-2*G=7:=by omega
      have ln:3*G-7*N≠7:=by intro lw;exact corner ⟨rw,lw⟩
      exact fiveToSix_terminal_R_seven_of_L_ne_false68 alpha gamma epsilon zeta eta terminal
        A B c d e N G hn hp hd he hz rw hL7 ln
    have l8:8≤3*G-7*N:=by
      by_contra h
      have lw:3*G-7*N=7:=by omega
      have rn:7*N-2*G≠7:=by intro rw;exact corner ⟨rw,lw⟩
      exact fiveToSix_terminal_L_seven_of_R_ne_false68 alpha gamma epsilon zeta eta terminal
        A B c d e N G hn hp hd he hz hR7 lw rn
    exact Or.inr ⟨h0,r8,l8,fiveToSix_terminal_directLowerRowSeven68
      alpha gamma epsilon zeta eta terminal A B c d e N G hn hp⟩

#print axioms fiveToSix_terminal_depth_seven_index_audit68
#print axioms fiveToSix_terminal_i4_faceSum_seven68
#print axioms fiveToSix_terminal_compensatedAAF_seven68
#print axioms fiveToSix_terminal_row_seven_reduced68
#print axioms fiveToSix_terminal_seven_corner68
#print axioms fiveToSix_terminal_cusp_depth_eight_or_corner68

end FiveToSixCuspTerminalDepthSeven68

end Max11DegreeRoutes
