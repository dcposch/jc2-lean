import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroHDegreeScratch

/-! # Exact leading coefficient after the zero-`Fce` discriminant descent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroDeltaTop68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The top coefficient of the alternate global row is nonzero.  It fixes the
first surviving discriminant coefficient exactly as `3*b_D*d_V`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_Delta_top68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0)
    (hf:(((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B).coeff 0=0):
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let M:=3*D+Cc
    let L:=M-V
    (fiveToSixCuspDiscriminantPolynomial68 A B c).coeff L=
        (3:k)*B.coeff D*d.coeff V ∧
      (fiveToSixCuspDiscriminantPolynomial68 A B c).natDegree=L:=by
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let M:=3*D+Cc
  let L:=M-V
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  change Delta.coeff L=(3:k)*B.coeff D*d.coeff V ∧ Delta.natDegree=L
  have hglobal:=fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_global68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  rcases hglobal with ⟨i3,hFzero,hRce,hK⟩
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp0:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS,hSR,hd,he,hpacket,hrestSource⟩
  rcases hpacket with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  rcases hcusp with ⟨hBtop,hctop,hdtop,hetop,hcuspEq⟩
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq:9*N=7*S:=hnxt.1.1
  have hB':B.natDegree≤D:=by dsimp only [D];omega
  have hc':c.natDegree≤Cc:=by dsimp only [Cc];omega
  have hd':d.natDegree≤V:=by dsimp only [V];omega
  have hbidx:D=3*N-G:=by dsimp only [D];omega
  have hdidx:V=5*N-G-S:=by dsimp only [V];omega
  have hbcoeff:B.coeff D≠0:=by rw [hbidx];exact hBtop
  have hdcoeff:d.coeff V≠0:=by rw [hdidx];exact hdtop
  have hDelta:Delta.natDegree≤L:=by
    exact fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_Delta_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  have hM:V≤M:=by dsimp only [D,Cc,V,M];omega
  have hVL:V+L=M:=by dsimp only [L];omega
  have hB3deg:(B^3).natDegree≤3*D:=by compute_degree;omega
  have hB3:(B^3).coeff (3*D)=B.coeff D^3:=by
    have h:=coeff_pow_at_bound68 B D 3 hB'
    simpa only [Nat.mul_comm] using h
  have hB3c:(B^3*c).coeff M=B.coeff D^3*c.coeff Cc:=by
    have h:=coeff_mul_at_bounds68 (B^3) c (3*D) Cc hB3deg hc'
    rw [show 3*D+Cc=M by rfl,hB3] at h
    exact h
  have hd2deg:(d^2).natDegree≤2*V:=by compute_degree;omega
  have hd2:(d^2).coeff (2*V)=d.coeff V^2:=by
    have h:=coeff_pow_at_bound68 d V 2 hd'
    simpa only [Nat.mul_comm] using h
  have hBd2:(B*d^2).coeff M=B.coeff D*d.coeff V^2:=by
    have h:=coeff_mul_at_bounds68 B (d^2) D (2*V) hB' hd2deg
    rw [show D+2*V=M by dsimp only [D,Cc,V,M];omega,hd2] at h
    exact h
  have hdDelta:(d*Delta).coeff M=d.coeff V*Delta.coeff L:=by
    have h:=coeff_mul_at_bounds68 d Delta V L hd' hDelta
    rw [hVL] at h
    exact h
  have hB3low:(B^3).natDegree<M:=by dsimp only [D,Cc,M] at *;omega
  have hBlow:B.natDegree<M:=by dsimp only [D,Cc,M] at *;omega
  have hcdlow:(c*d).natDegree<M:=by compute_degree;dsimp only [D,Cc,V,M] at *;omega
  have hdlow:d.natDegree<M:=by dsimp only [D,Cc,V,M] at *;omega
  have hcoeff:=congrArg (fun P:k[X]=>P.coeff M) hK
  dsimp only [Delta] at hdDelta
  dsimp only [FiveToSixQZeroFceZeroDeltaDescent68] at hcoeff
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,hdDelta,hB3c,hBd2,
    coeff_eq_zero_of_natDegree_lt hB3low,
    coeff_eq_zero_of_natDegree_lt hBlow,
    coeff_eq_zero_of_natDegree_lt hcdlow,
    coeff_eq_zero_of_natDegree_lt hdlow,mul_zero,add_zero,sub_zero,
    coeff_zero] at hcoeff
  have htop:=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).2
  have hrel:d.coeff V*(Delta.coeff L-
      (3:k)*B.coeff D*d.coeff V)=0:=by
    linear_combination (1/24:k)*hcoeff-(1/6:k)*B.coeff D*htop
  have hdelta:Delta.coeff L=(3:k)*B.coeff D*d.coeff V:=by
    have hz:Delta.coeff L-(3:k)*B.coeff D*d.coeff V=0:=
      (mul_eq_zero.mp hrel).resolve_left hdcoeff
    linear_combination hz
  refine ⟨hdelta,?_⟩
  apply natDegree_eq_of_le_of_coeff_ne_zero hDelta
  rw [hdelta]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hbcoeff) hdcoeff

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_Delta_top68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroDeltaTop68

end Max11DegreeRoutes
