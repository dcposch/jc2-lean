import Sol68FiveToSixCuspTerminalFiniteStoppingScratch

/-! # The next independent row on the terminal simultaneous wall

The arithmetic wall is `(N,G,q)=(5k,14k,7k)`.  The compensated cubic
first integral has top degree `8k`; row one at `18k-1` is its first
independent source consumer.  We use it only for `k>=2`, leaving the
verified `k=1` depth-seven corner literally intact.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspTerminalSimultaneousNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact integral normalization of the simultaneous wall. -/
theorem fiveToSix_terminal_simultaneous_normalize68
    (N G q:ℕ) (hR:7*N-2*G=q) (hL:3*G-7*N=q) :
    ∃ m:ℕ, N=5*m ∧ G=14*m ∧ q=7*m := by
  have hratio : 5 * q = 7 * N := by omega
  have h5N : 5 ∣ N := by
    apply (by decide : Nat.Coprime 5 7).dvd_of_dvd_mul_right
    refine ⟨q, ?_⟩
    omega
  rcases h5N with ⟨m, hm⟩
  refine ⟨m, ?_, ?_, ?_⟩ <;> omega

/-- Full compensated I3 identity, retaining its constant source RHS. -/
theorem fiveToSix_terminal_compensatedI3_polynomial68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (N G:ℕ)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7*N-2*G)) (hz:zeta=0) :
    ∃ i3:k,
      (-(A*B*d)+(3:k) • (c*e))+(9/4*epsilon:k) • c+
          (9/2*gamma:k) • e-(3/4*gamma:k) • B^2 =
        B^2*c-(3/2:k) • d^2+(9/8:k) • C i3 := by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd,he,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  refine ⟨i3,?_⟩
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,hz] at hi3
  simp only [secondaryResidualInvariantThreePolynomial68] at hi3
  rw [← hi3]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul,map_add,map_sub,map_mul,map_pow,map_neg,
    map_zero,RatFunc.algebraMap_C,map_div₀,map_ofNat,map_natCast,map_one]
  ring

/-- At the normalized wall the compensated I3 polynomial has degree at
most `8m` and the displayed literal edge coefficient. -/
theorem fiveToSix_terminal_compensatedI3_top68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (m : ℕ) (hm : 0 < m)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e (5*m) (14*m) (7*m))
    (hdT:d.natDegree≤4*m) (heT:e.natDegree≤9*m) (hz:zeta=0) :
    let J:=(-(A*B*d)+(3:k) • (c*e))+(9/4*epsilon:k) • c+
      (9/2*gamma:k) • e-(3/4*gamma:k) • B^2
    J.natDegree≤8*m ∧
      J.coeff (8*m)=B.coeff m^2*c.coeff (6*m)-(3/2:k)*d.coeff (4*m)^2 := by
  dsimp only
  have hpT:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e (5*m) (14*m) (7*(5*m)-2*(14*m)):=by
    simpa only [show 7*(5*m)-2*(14*m)=7*m by omega] using hp
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd,he,ha,hcusp,had⟩
  rcases fiveToSix_terminal_compensatedI3_polynomial68 alpha gamma epsilon zeta
    eta terminal A B c d e (5*m) (14*m) hpT hz with ⟨i3,hJ⟩
  have hsupport:((-(A*B*d)+(3:k) • (c*e))+(9/4*epsilon:k) • c+
      (9/2*gamma:k) • e-(3/4*gamma:k) • B^2).natDegree≤8*m:=by
    rw [hJ]
    compute_degree
    omega
  refine ⟨hsupport,?_⟩
  rw [hJ,coeff_add,coeff_sub,coeff_smul,coeff_smul]
  have hB2:=coeff_pow_at_bound68 B m 2 (by simpa only [show 3*(5*m)-14*m=m by omega] using hB)
  have hB2deg:(B^2).natDegree≤2*m:=by compute_degree;omega
  have hB2c:=coeff_mul_at_bounds68 (B^2) c (2*m) (6*m) hB2deg
    (by simpa only [show 4*(5*m)-14*m=6*m by omega] using hc)
  rw [show 2*m+6*m=8*m from by omega,hB2] at hB2c
  have hd2:=coeff_pow_at_bound68 d (4*m) 2
    hdT
  rw [show 2*(4*m)=8*m from by omega] at hd2
  have c0:(C i3).coeff (8*m)=0:=by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  rw [hB2c,hd2,c0]
  simp only [smul_eq_mul,mul_zero,add_zero]

/-- The first genuinely new terminal row, at index `18m-1`.  It uses the
compensated I3 top and is independent of the retained row-zero scalar. -/
theorem fiveToSix_terminal_simultaneous_next_row_scalar68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (m : ℕ) (hm : 0 < m)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e (5*m) (14*m) (7*m))
    (hdT:d.natDegree≤4*m) (heT:e.natDegree≤9*m) (hz:zeta=0) :
    8*c.coeff (6*m)^3+3*A.coeff (10*m)*d.coeff (4*m)^2-
      9*e.coeff (9*m)^2=0 := by
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd,he,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  let H:k[X]:=-(A*B*d)+(3:k) • (c*e)
  let J:k[X]:=H+(9/4*epsilon:k) • c+(9/2*gamma:k) • e-
    (3/4*gamma:k) • B^2
  let K:=18*m-1
  have htop:=fiveToSix_terminal_compensatedI3_top68 alpha gamma epsilon zeta
    eta terminal A B c d e m hm
    ⟨hn,hgt,hle,hA,hB,hc,hd,he,ha,hcusp,
      ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩⟩ hdT heT hz
  rcases hcusp with ⟨hb,hcn,hds,hes,hcusp0⟩
  have hcuspN:A.coeff (10*m)*B.coeff m^2+3*c.coeff (6*m)^2=0:=by
    simpa only [show 2*(5*m)=10*m by omega,
      show 3*(5*m)-14*m=m by omega,
      show 4*(5*m)-14*m=6*m by omega] using hcusp0
  change J.natDegree≤8*m ∧
      J.coeff (8*m)=B.coeff m^2*c.coeff (6*m)-
        (3/2:k)*d.coeff (4*m)^2 at htop
  have hAJ:=coeff_mul_derivative_at_bounds68 A J (10*m) (8*m)
    (by omega) (by simpa only [show 2*(5*m)=10*m by omega] using hA) htop.1
  rw [show 10*m+8*m-1=K from by dsimp only [K];omega,htop.2] at hAJ
  have hB2deg:(B^2).natDegree≤2*m:=by compute_degree;omega
  have hB2:=coeff_pow_at_bound68 B m 2
    (by simpa only [show 3*(5*m)-14*m=m by omega] using hB)
  have hX:=coeff_mul_mul_derivative_at_bounds68 (B^2) c A
    (2*m) (6*m) (10*m) (by omega) hB2deg
    (by simpa only [show 4*(5*m)-14*m=6*m by omega] using hc)
    (by simpa only [show 2*(5*m)=10*m by omega] using hA)
  rw [show 2*m+6*m+10*m-1=K from by dsimp only [K];omega,hB2] at hX
  have hX':(derivative A*B^2*c).coeff K=
      B.coeff m^2*c.coeff (6*m)*A.coeff (10*m)*(((10*m:ℕ):k)):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hX
  have hY:=coeff_mul_mul_derivative_at_bounds68 d d A
    (4*m) (4*m) (10*m) (by omega) hdT hdT
    (by simpa only [show 2*(5*m)=10*m by omega] using hA)
  rw [show 4*m+4*m+10*m-1=K from by dsimp only [K];omega] at hY
  have hY':(derivative A*d^2).coeff K=
      d.coeff (4*m)^2*A.coeff (10*m)*(((10*m:ℕ):k)):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hY
  have hZ:=coeff_mul_mul_derivative_at_bounds68 c c c
    (6*m) (6*m) (6*m) (by omega)
    (by simpa only [show 4*(5*m)-14*m=6*m by omega] using hc)
    (by simpa only [show 4*(5*m)-14*m=6*m by omega] using hc)
    (by simpa only [show 4*(5*m)-14*m=6*m by omega] using hc)
  rw [show 6*m+6*m+6*m-1=K from by dsimp only [K];omega] at hZ
  have hZ':(c^2*derivative c).coeff K=
      c.coeff (6*m)^3*(((6*m:ℕ):k)):=by
    simpa only [pow_two,pow_succ,pow_zero,mul_one,one_mul,mul_assoc,mul_comm,
      mul_left_comm] using hZ
  have hW:=coeff_mul_derivative_at_bounds68 e e (9*m) (9*m)
    (by omega) heT heT
  rw [show 9*m+9*m-1=K from by dsimp only [K];omega] at hW
  have hmainPoly:
      (2:k) • (A^2*B*derivative d)+(2:k) • (A^2*derivative B*d)+
        (2:k) • (A*derivative A*B*d)-(6:k) • (A*c*derivative e)-
        (6:k) • (A*derivative c*e)=(-2:k) • (A*derivative H):=by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    dsimp only [H]
    simp only [derivative_add,derivative_neg,derivative_mul,derivative_smul,
      derivative_C,derivative_ofNat,zero_mul,add_zero,neg_mul,mul_neg,pow_two,
      Polynomial.smul_eq_C_mul,map_add,map_sub,map_mul,map_neg,map_ofNat,map_zero]
    ring
  have hmain:=congrArg (fun p:k[X]=>p.coeff K) hmainPoly
  simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul] at hmain
  have hrelPoly:A*derivative H=A*derivative J-
      (9/4*epsilon:k) • (A*derivative c)-
      (9/2*gamma:k) • (A*derivative e)+
      (3/4*gamma:k) • (A*derivative (B^2)):=by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    dsimp only [H,J]
    simp only [derivative_add,derivative_sub,derivative_neg,derivative_mul,
      derivative_smul,derivative_C,derivative_ofNat,zero_mul,add_zero,
      neg_mul,mul_neg,pow_two,Polynomial.smul_eq_C_mul,map_add,map_sub,
      map_mul,map_neg,map_ofNat,map_zero]
    ring
  have hAc:(A*derivative c).natDegree<K:=by dsimp only [K];compute_degree;omega
  have hAB2:(A*derivative (B^2)).natDegree<K:=by dsimp only [K];compute_degree;omega
  have hrel:=congrArg (fun p:k[X]=>p.coeff K) hrelPoly
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hAc,coeff_eq_zero_of_natDegree_lt hAB2,
    mul_zero,sub_zero,add_zero] at hrel
  have hlow1:(B^2*derivative e).natDegree<K:=by dsimp only [K];compute_degree;omega
  have hlow2:(B*c*derivative d).natDegree<K:=by dsimp only [K];compute_degree;omega
  have hlow3:(B*derivative c*d).natDegree<K:=by dsimp only [K];compute_degree;omega
  have hlow4:(derivative B*c*d).natDegree<K:=by dsimp only [K];compute_degree;omega
  have hload:(cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1/3:k) • (A*B)+d) e).coeff K=
      (4/3*gamma:k)*(A*derivative e).coeff K:=by
    rw [cubicLoadRowOnePolynomial68_uniform_pinned_eq68,hz]
    have l2:(c*derivative c).natDegree<K:=by dsimp only [K];compute_degree;omega
    have l3:(derivative A*B^2).natDegree<K:=by dsimp only [K];compute_degree;omega
    have l4:(B*derivative d).natDegree<K:=by dsimp only [K];compute_degree;omega
    have l5:(d*derivative B).natDegree<K:=by dsimp only [K];compute_degree;omega
    have l6:(A*derivative c).natDegree<K:=hAc
    have l7:(derivative e).natDegree<K:=by dsimp only [K];compute_degree;omega
    simp only [zero_mul,zero_smul,add_zero,coeff_add,coeff_sub,coeff_smul,
      smul_eq_mul,coeff_eq_zero_of_natDegree_lt l2,
      coeff_eq_zero_of_natDegree_lt l3,coeff_eq_zero_of_natDegree_lt l4,
      coeff_eq_zero_of_natDegree_lt l5,coeff_eq_zero_of_natDegree_lt l6,
      coeff_eq_zero_of_natDegree_lt l7,mul_zero,sub_zero]
  have hrow:=congrArg (fun p:k[X]=>p.coeff K) hrow1
  simp only [coeff_zero,coeff_add,hload] at hrow
  have raw:(-4/27:k)*(-2*(A*derivative H).coeff K-
      2*(derivative A*B^2*c).coeff K+3*(derivative A*d^2).coeff K+
      6*(c^2*derivative c).coeff K-18*(e*derivative e).coeff K)+
      (4/3*gamma:k)*(A*derivative e).coeff K=0:=by
    simp only [secondaryResidualRowOnePolynomial68,coeff_smul,coeff_add,
      coeff_sub,smul_eq_mul,coeff_eq_zero_of_natDegree_lt hlow1,
      coeff_eq_zero_of_natDegree_lt hlow2,
      coeff_eq_zero_of_natDegree_lt hlow3,
      coeff_eq_zero_of_natDegree_lt hlow4,mul_zero,add_zero,sub_zero] at hrow
    linear_combination hrow-(-4/27:k)*hmain
  have core:(-4/27:k)*(-2*(A*derivative J).coeff K-
      2*(derivative A*B^2*c).coeff K+3*(derivative A*d^2).coeff K+
      6*(c^2*derivative c).coeff K-18*(e*derivative e).coeff K)=0:=by
    linear_combination raw+(-8/27:k)*hrel
  rw [hAJ,hX',hY',hZ',hW] at core
  push_cast at core
  have hmc:((m:ℕ):k)≠0:=by exact_mod_cast (show m≠0 by omega)
  have mtimes:((m:ℕ):k)*(8*c.coeff (6*m)^3+
      3*A.coeff (10*m)*d.coeff (4*m)^2-9*e.coeff (9*m)^2)=0:=by
    linear_combination (-3/8:k)*core+
      2*((m:ℕ):k)*c.coeff (6*m)*hcuspN
  exact (mul_eq_zero.mp mtimes).resolve_left hmc

/-- The new row, the terminal I4 face, and the retained row-zero scalar
have an empty common all-nonzero cusp locus. -/
theorem fiveToSix_terminal_simultaneous_false68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (m : ℕ) (hm : 0 < m)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e (5*m) (14*m) (7*m))
    (hdT:d.natDegree≤4*m) (heT:e.natDegree≤9*m) (hz:zeta=0)
    (hrow0:4*A.coeff (10*m)*B.coeff m^3+
      27*d.coeff (4*m)*e.coeff (9*m)=0) : False := by
  have hpT:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e (5*m) (14*m) (7*(5*m)-2*(14*m)):=by
    simpa only [show 7*(5*m)-2*(14*m)=7*m by omega] using hp
  have hdTN:d.natDegree≤14*m-2*(5*m):=by omega
  have heTN:e.natDegree≤14*m-5*m:=by omega
  have hface:=fiveToSix_contractedCusp_terminalFace68 alpha gamma epsilon zeta
    eta terminal A B c d e (5*m) (14*m) hpT hdTN heTN hz
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd,he,ha,⟨hb,hcn,hds,hes,hcusp⟩,had⟩
  have hbN:B.coeff m≠0:=by
    simpa only [show 3*(5*m)-14*m=m by omega] using hb
  have hcN:c.coeff (6*m)≠0:=by
    simpa only [show 4*(5*m)-14*m=6*m by omega] using hcn
  have hcuspN:A.coeff (10*m)*B.coeff m^2+3*c.coeff (6*m)^2=0:=by
    simpa only [show 2*(5*m)=10*m by omega,
      show 3*(5*m)-14*m=m by omega,
      show 4*(5*m)-14*m=6*m by omega] using hcusp
  have hfour:B.coeff m*e.coeff (9*m)+c.coeff (6*m)*d.coeff (4*m)=0:=by
    simpa only [show 2*(5*m)=10*m by omega,
      show 3*(5*m)-14*m=m by omega,
      show 4*(5*m)-14*m=6*m by omega,
      show 14*m-5*m=9*m by omega,
      show 14*m-10*m=4*m by omega] using hface.four
  have hrow1:=fiveToSix_terminal_simultaneous_next_row_scalar68 alpha gamma
    epsilon zeta eta terminal A B c d e m hm
    ⟨hn,hgt,hle,hA,hB,hc,hd,he,ha,⟨hb,hcn,hds,hes,hcusp⟩,had⟩
    hdT heT hz
  have hsq:B.coeff m^2*e.coeff (9*m)^2=
      c.coeff (6*m)^2*d.coeff (4*m)^2:=by
    linear_combination
      (B.coeff m*e.coeff (9*m)-c.coeff (6*m)*d.coeff (4*m))*hfour
  have hplus:4*B.coeff m^2*c.coeff (6*m)+9*d.coeff (4*m)^2=0:=by
    have hfact:(3:k)*c.coeff (6*m)*
        (4*B.coeff m^2*c.coeff (6*m)+9*d.coeff (4*m)^2)=0:=by
      linear_combination 4*B.coeff m^2*hcuspN-B.coeff m*hrow0+
        27*d.coeff (4*m)*hfour
    exact (mul_eq_zero.mp hfact).resolve_left
      (mul_ne_zero (by norm_num) hcN)
  have hminus:4*B.coeff m^2*c.coeff (6*m)-9*d.coeff (4*m)^2=0:=by
    have hfact:(2:k)*c.coeff (6*m)^2*
        (4*B.coeff m^2*c.coeff (6*m)-9*d.coeff (4*m)^2)=0:=by
      linear_combination B.coeff m^2*hrow1-3*d.coeff (4*m)^2*hcuspN+9*hsq
    exact (mul_eq_zero.mp hfact).resolve_left
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hcN))
  have hzprod:(8:k)*B.coeff m^2*c.coeff (6*m)=0:=by
    linear_combination hplus+hminus
  exact (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hbN)) hcN) hzprod

/-- The finite-stopping residual is empty.  This includes the normalized
`m=1` depth-seven corner; the separate zeta-first branch is not an input. -/
theorem fiveToSix_terminal_cusp_finite_stopping_false68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X]) (N G:ℕ)
    (hres:FiveToSixTerminalCuspDepthSevenResidual68 alpha gamma epsilon zeta
      eta terminal A B c d e N G) : False := by
  have hf:=fiveToSix_terminal_cusp_finite_stopping68 alpha gamma epsilon zeta
    eta terminal A B c d e N G hres
  rcases hf with ⟨h0,q,hq7,hqD,hR,hL,hident,hscalar⟩
  rcases fiveToSix_terminal_simultaneous_normalize68 N G q hR hL with
    ⟨m,hNm,hGm,hqm⟩
  subst N
  subst G
  subst q
  rcases h0 with ⟨h6,hR7,hL7,row6⟩
  rcases h6 with ⟨h5,hR6,hL6,row5⟩
  rcases h5 with ⟨h4,hR5,hL5,row4⟩
  rcases h4 with ⟨h3,hR4,hL4,row3⟩
  rcases h3 with ⟨h2,hR3,hL3,i4two,row2⟩
  rcases h2 with ⟨hn,hdT0,heT0,hz,hR2,hL2,hp0,row1⟩
  have hm : 0 < m := by omega
  have hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e (5*m) (14*m) (7*m):=by
    simpa only [show 7*(5*m)-2*(14*m)=7*m by omega] using hp0
  have hdT:d.natDegree≤4*m:=by omega
  have heT:e.natDegree≤9*m:=by omega
  have hs:4*A.coeff (10*m)*B.coeff m^3+
      27*d.coeff (4*m)*e.coeff (9*m)=0:=by
    simpa only [show 2*(5*m)=10*m by omega,
      show 3*(5*m)-14*m=m by omega,
      show 14*m-10*m=4*m by omega,
      show 14*m-5*m=9*m by omega] using hscalar
  exact fiveToSix_terminal_simultaneous_false68 alpha gamma epsilon zeta eta
    terminal A B c d e m hm hp hdT heT hz hs

#print axioms fiveToSix_terminal_simultaneous_normalize68
#print axioms fiveToSix_terminal_compensatedI3_polynomial68
#print axioms fiveToSix_terminal_compensatedI3_top68
#print axioms fiveToSix_terminal_simultaneous_next_row_scalar68
#print axioms fiveToSix_terminal_simultaneous_false68
#print axioms fiveToSix_terminal_cusp_finite_stopping_false68

end FiveToSixCuspTerminalSimultaneousNext68

end Max11DegreeRoutes
