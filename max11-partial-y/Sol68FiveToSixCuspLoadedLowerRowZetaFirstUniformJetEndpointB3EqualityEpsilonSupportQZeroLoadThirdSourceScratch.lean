import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadThirdAlgebraScratch

/-! # Exact third-jet load coefficients on `q=0` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadThirdSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact third-jet expansion of the row-two load. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_third68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let V:=5*N-3*S
    let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    L2.coeff (p-4)=(6:k)*((p-3:ℕ):k)*
      FiveToSixQZeroBBDJetThree68
        (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
        (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3)):=by
  let p:=2*N
  let D:=3*N-2*S
  let V:=5*N-3*S
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  change L2.coeff (p-4)=_
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp0:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS,hSR,hd,he,hpacket,hrest⟩
  rcases hpacket with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq:9*N=7*S:=hnxt.1.1
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hd':d.natDegree≤V:=by dsimp only [V];rw [hGS] at hd;omega
  have hD:3≤D:=by dsimp only [D];omega
  have hV:3≤V:=by dsimp only [V];omega
  have hpEq:p=2*D+V:=by dsimp only [p,D,V];omega
  have hprod0:=coeff_mul_mul_three_below_bounds68 B B d D D V
    hD hD hV hB' hB' hd'
  have hprod:(B^2*d).coeff (p-3)=
      FiveToSixQZeroBBDJetThree68
        (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
        (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3)):=by
    rw [hpEq,show 2*D+V-3=D+D+V-3 by omega,pow_two]
    rw [hprod0]
    dsimp only [FiveToSixQZeroBBDJetThree68]
    ring
  have hsq:derivative (B^2)=(2:k)•(B*derivative B):=by
    rw [show B^2=B*B by ring,derivative_mul]
    simp only [two_smul]
    ring
  have hder:derivative (B^2*d)=
      (2:k)•(B*derivative B*d)+B^2*derivative d:=by
    rw [derivative_mul,hsq]
    simp only [two_smul]
    ring
  have hL2poly:L2=(6:k)•derivative (B^2*d):=by
    dsimp only [L2,FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68]
    rw [hder]
    module
  have hidx:p-4+1=p-3:=by dsimp only [p];omega
  have hcast:(((p-4:ℕ):k)+1)=((p-3:ℕ):k):=by exact_mod_cast hidx
  rw [hL2poly,coeff_smul,coeff_derivative,hidx,hcast,hprod]
  ring

/-- Exact third-jet expansion of the row-zero load. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_rowZero_load_third68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
    L0.coeff (2*p-4)=FiveToSixQZeroRowZeroLoadJetThree68 ((p:ℕ):k)
      (A.coeff p) (A.coeff (p-1)) (A.coeff (p-2)) (A.coeff (p-3))
      (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
      (c.coeff Cc) (c.coeff (Cc-1)) (c.coeff (Cc-2)) (c.coeff (Cc-3))
      (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3))
      (e.coeff E) (e.coeff (E-1)) (e.coeff (E-2)) (e.coeff (E-3)):=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  change L0.coeff (2*p-4)=_
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp0:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS,hSR,hd,he,hpacket,hrest⟩
  rcases hpacket with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq:9*N=7*S:=hnxt.1.1
  have hA':A.natDegree≤p:=by simpa [p] using hA
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hc':c.natDegree≤Cc:=by simpa [Cc,hGS] using hc
  have hd':d.natDegree≤V:=by dsimp only [V];rw [hGS] at hd;omega
  have he':e.natDegree≤E:=by dsimp only [E];rw [hGS] at he;omega
  have hp:3≤p:=by dsimp only [p];omega
  have hD:3≤D:=by dsimp only [D];omega
  have hC:3≤Cc:=by dsimp only [Cc];omega
  have hV:4≤V:=by dsimp only [V];omega
  have hE:4≤E:=by dsimp only [E];omega
  have hpEq:p=2*D+V:=by dsimp only [p,D,V];omega
  have htwopEq:2*p=D+Cc+E:=by dsimp only [p,D,Cc,E];omega
  have htwopEq':2*p=2*Cc+V:=by dsimp only [p,Cc,V];omega
  have hVcast:((V:ℕ):k)=(4/7:k)*((p:ℕ):k):=by
    have hnat:7*V=4*p:=by dsimp only [p,V];omega
    have h:=congrArg (fun n:ℕ=>(n:k)) hnat
    push_cast at h
    linear_combination h/7
  have hEcast:((E:ℕ):k)=(15/14:k)*((p:ℕ):k):=by
    have hnat:14*E=15*p:=by dsimp only [p,E];omega
    have h:=congrArg (fun n:ℕ=>(n:k)) hnat
    push_cast at h
    linear_combination h/14
  have hCcast:((Cc:ℕ):k)=(5/7:k)*((p:ℕ):k):=by
    have hnat:7*Cc=5*p:=by dsimp only [p,Cc];omega
    have h:=congrArg (fun n:ℕ=>(n:k)) hnat
    push_cast at h
    linear_combination h/7
  let Q:=B^2*d
  let R:=B^2*derivative d
  let T:=B^2*derivative d+B*derivative B*d
  have hQdeg:Q.natDegree≤p:=by dsimp only [Q];compute_degree;omega
  have hRdeg:R.natDegree≤p-1:=by
    have hdd:=natDegree_derivative_le d
    dsimp only [R]
    compute_degree
    omega
  have hTdeg:T.natDegree≤p-1:=by
    have hdd:=natDegree_derivative_le d
    have hdB:=natDegree_derivative_le B
    dsimp only [T]
    compute_degree
    omega
  have hQ0:Q.coeff p=FiveToSixQZeroBBDJetZero68
      (B.coeff D) (d.coeff V):=by
    have h:=coeff_mul_mul_at_bounds68 B B d D D V hB' hB' hd'
    rw [show D+D+V=p by omega] at h
    dsimp only [Q,FiveToSixQZeroBBDJetZero68]
    simpa only [pow_two] using h
  have hQ1:Q.coeff (p-1)=FiveToSixQZeroBBDJetOne68
      (B.coeff D) (B.coeff (D-1)) (d.coeff V) (d.coeff (V-1)):=by
    have h:=coeff_mul_mul_one_below_bounds68 B B d D D V
      (by omega) (by omega) (by omega) hB' hB' hd'
    rw [show D+D+V-1=p-1 by omega] at h
    dsimp only [Q,FiveToSixQZeroBBDJetOne68]
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at h ⊢
    linear_combination h
  have hQ2:Q.coeff (p-2)=FiveToSixQZeroBBDJetTwo68
      (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2))
      (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)):=by
    have h:=coeff_mul_mul_two_below_bounds68 B B d D D V
      (by omega) (by omega) (by omega) hB' hB' hd'
    rw [show D+D+V-2=p-2 by omega] at h
    dsimp only [Q,FiveToSixQZeroBBDJetTwo68]
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at h ⊢
    linear_combination h
  have hQ3:Q.coeff (p-3)=FiveToSixQZeroBBDJetThree68
      (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
      (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3)):=by
    have h:=coeff_mul_mul_three_below_bounds68 B B d D D V
      hD hD (by omega) hB' hB' hd'
    rw [show D+D+V-3=p-3 by omega] at h
    dsimp only [Q,FiveToSixQZeroBBDJetThree68]
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at h ⊢
    linear_combination h
  have hdd:d.natDegree≤V:=hd'
  have hdd':(derivative d).natDegree≤V-1:=
    (natDegree_derivative_le d).trans (Nat.sub_le_sub_right hdd 1)
  have hdt:=coeff_derivative_at_bound68 d V (by omega)
  have hd1:=coeff_derivative_at_bound68 d (V-1) (by omega)
  have hd2:=coeff_derivative_at_bound68 d (V-2) (by omega)
  have hd3:=coeff_derivative_at_bound68 d (V-3) (by omega)
  have hd1':(derivative d).coeff (V-2)=
      d.coeff (V-1)*((V-1:ℕ):k):=by
    rw [←show V-1-1=V-2 by omega]
    exact hd1
  have hd2':(derivative d).coeff (V-3)=
      d.coeff (V-2)*((V-2:ℕ):k):=by
    rw [←show V-2-1=V-3 by omega]
    exact hd2
  have hd3':(derivative d).coeff (V-4)=
      d.coeff (V-3)*((V-3:ℕ):k):=by
    rw [←show V-3-1=V-4 by omega]
    exact hd3
  have hcastV1:(((V-1:ℕ):k))=((V:ℕ):k)-1:=by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hcastV2:(((V-2:ℕ):k))=((V:ℕ):k)-2:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have hcastV3:(((V-3:ℕ):k))=((V:ℕ):k)-3:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have hR0:R.coeff (p-1)=FiveToSixQZeroBBDerivativeJetZero68
      ((p:ℕ):k) (B.coeff D) (d.coeff V):=by
    have h:=coeff_mul_mul_at_bounds68 B B (derivative d)
      D D (V-1) hB' hB' hdd'
    rw [show D+D+(V-1)=p-1 by omega,hdt] at h
    dsimp only [R,FiveToSixQZeroBBDerivativeJetZero68]
    rw [←hVcast]
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at h ⊢
    linear_combination h
  have hR1:R.coeff (p-2)=FiveToSixQZeroBBDerivativeJetOne68
      ((p:ℕ):k) (B.coeff D) (B.coeff (D-1))
      (d.coeff V) (d.coeff (V-1)):=by
    have h:=coeff_mul_mul_one_below_bounds68 B B (derivative d)
      D D (V-1) (by omega) (by omega) (by omega) hB' hB' hdd'
    rw [show D+D+(V-1)-1=p-2 by omega,hdt,hd1,hcastV1] at h
    dsimp only [R,FiveToSixQZeroBBDerivativeJetOne68]
    rw [←hVcast]
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at h ⊢
    linear_combination h
  have hR2:R.coeff (p-3)=FiveToSixQZeroBBDerivativeJetTwo68
      ((p:ℕ):k) (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2))
      (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)):=by
    have h:=coeff_mul_mul_two_below_bounds68 B B (derivative d)
      D D (V-1) (by omega) (by omega) (by omega) hB' hB' hdd'
    rw [show D+D+(V-1)-2=p-3 by omega,
      show V-1-2=V-2-1 by omega,hdt,hd1,hd2,hcastV1,hcastV2] at h
    dsimp only [R,FiveToSixQZeroBBDerivativeJetTwo68]
    rw [←hVcast]
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at h ⊢
    linear_combination h
  have hR3:R.coeff (p-4)=FiveToSixQZeroBBDerivativeJetThree68
      ((p:ℕ):k) (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2))
      (B.coeff (D-3)) (d.coeff V) (d.coeff (V-1))
      (d.coeff (V-2)) (d.coeff (V-3)):=by
    have h:=coeff_mul_mul_three_below_bounds68 B B (derivative d)
      D D (V-1) hD hD (by omega) hB' hB' hdd'
    rw [show D+D+(V-1)-3=p-4 by omega,
      show V-1-2=V-2-1 by omega,show V-1-3=V-3-1 by omega,
      hdt,hd1,hd2,hd3,
      hcastV1,hcastV2,hcastV3] at h
    dsimp only [R,FiveToSixQZeroBBDerivativeJetThree68]
    rw [←hVcast]
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at h ⊢
    linear_combination h
  have hTpoly:T=(1/2:k)•(derivative Q+R):=by
    dsimp only [T,Q,R]
    have hder:derivative (B^2*d)=
        derivative (B^2)*d+B^2*derivative d:=by rw [derivative_mul]
    have hsq:derivative (B^2)=(2:k)•(B*derivative B):=by
      rw [show B^2=B*B by ring,derivative_mul]
      simp only [two_smul]
      ring
    rw [hder,hsq]
    rw [smul_mul_assoc,add_assoc]
    have htwice:B^2*derivative d+B^2*derivative d=
        (2:k)•(B^2*derivative d):=by simp only [two_smul]
    rw [htwice,←smul_add,smul_smul]
    norm_num
    ring
  have hT0:T.coeff (p-1)=(1/2:k)*(p*
      FiveToSixQZeroBBDJetZero68 (B.coeff D) (d.coeff V)+
      FiveToSixQZeroBBDerivativeJetZero68 ((p:ℕ):k)
        (B.coeff D) (d.coeff V)):=by
    rw [hTpoly,coeff_smul,coeff_add,coeff_derivative,
      show p-1+1=p by omega,hQ0,hR0]
    have hcast:(((p-1:ℕ):k)+1)=((p:ℕ):k):=by exact_mod_cast
      (show p-1+1=p by omega)
    rw [hcast]
    simp only [smul_eq_mul]
    ring
  have hT1:T.coeff (p-2)=(1/2:k)*(((p:ℕ):k)-1)*
      FiveToSixQZeroBBDJetOne68 (B.coeff D) (B.coeff (D-1))
        (d.coeff V) (d.coeff (V-1))+
      (1/2:k)*FiveToSixQZeroBBDerivativeJetOne68 ((p:ℕ):k)
        (B.coeff D) (B.coeff (D-1)) (d.coeff V) (d.coeff (V-1)):=by
    rw [hTpoly,coeff_smul,coeff_add,coeff_derivative,
      show p-2+1=p-1 by omega,hQ1,hR1]
    have hcast:(((p-2:ℕ):k)+1)=((p:ℕ):k)-1:=by
      calc
        ((p-2:ℕ):k)+1=((p-1:ℕ):k):=by
          exact_mod_cast (show p-2+1=p-1 by omega)
        _=((p:ℕ):k)-1:=by rw [Nat.cast_sub (by omega)];norm_num
    rw [hcast]
    ring
  have hT2:T.coeff (p-3)=(1/2:k)*(((p:ℕ):k)-2)*
      FiveToSixQZeroBBDJetTwo68 (B.coeff D) (B.coeff (D-1))
        (B.coeff (D-2)) (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2))+
      (1/2:k)*FiveToSixQZeroBBDerivativeJetTwo68 ((p:ℕ):k)
        (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2))
        (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)):=by
    rw [hTpoly,coeff_smul,coeff_add,coeff_derivative,
      show p-3+1=p-2 by omega,hQ2,hR2]
    have hcast:(((p-3:ℕ):k)+1)=((p:ℕ):k)-2:=by
      calc
        ((p-3:ℕ):k)+1=((p-2:ℕ):k):=by
          exact_mod_cast (show p-3+1=p-2 by omega)
        _=((p:ℕ):k)-2:=by rw [Nat.cast_sub (by omega)];norm_num
    rw [hcast]
    ring
  have hT3:T.coeff (p-4)=(1/2:k)*(((p:ℕ):k)-3)*
      FiveToSixQZeroBBDJetThree68
        (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
        (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3))+
      (1/2:k)*FiveToSixQZeroBBDerivativeJetThree68 ((p:ℕ):k)
        (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
        (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3)):=by
    rw [hTpoly,coeff_smul,coeff_add,coeff_derivative,
      show p-4+1=p-3 by omega,hQ3,hR3]
    have hcast:(((p-4:ℕ):k)+1)=((p:ℕ):k)-3:=by
      calc
        ((p-4:ℕ):k)+1=((p-3:ℕ):k):=by
          exact_mod_cast (show p-4+1=p-3 by omega)
        _=((p:ℕ):k)-3:=by rw [Nat.cast_sub (by omega)];norm_num
    rw [hcast]
    ring
  have hATraw:=coeff_mul_three_below_bounds68 A T p (p-1)
    hp (by omega) hA' hTdeg
  rw [show p+(p-1)-3=2*p-4 by omega,
    show p-1-1=p-2 by omega,show p-1-2=p-3 by omega,
    show p-1-3=p-4 by omega,hT0,hT1,hT2,hT3] at hATraw
  have hAT:(A*T).coeff (2*p-4)=
      (1/2:k)*A.coeff p*(((p:ℕ):k)-3)*
          FiveToSixQZeroBBDJetThree68
            (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
            (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3))+
      (1/2:k)*A.coeff p*FiveToSixQZeroBBDerivativeJetThree68 ((p:ℕ):k)
          (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
          (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3))+
      (1/2:k)*A.coeff (p-1)*(((p:ℕ):k)-2)*
          FiveToSixQZeroBBDJetTwo68
            (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2))
            (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2))+
      (1/2:k)*A.coeff (p-1)*FiveToSixQZeroBBDerivativeJetTwo68 ((p:ℕ):k)
          (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2))
          (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2))+
      (1/2:k)*A.coeff (p-2)*(((p:ℕ):k)-1)*
          FiveToSixQZeroBBDJetOne68
            (B.coeff D) (B.coeff (D-1)) (d.coeff V) (d.coeff (V-1))+
      (1/2:k)*A.coeff (p-2)*FiveToSixQZeroBBDerivativeJetOne68 ((p:ℕ):k)
          (B.coeff D) (B.coeff (D-1)) (d.coeff V) (d.coeff (V-1))+
      (1/2:k)*A.coeff (p-3)*((p:ℕ):k)*
          FiveToSixQZeroBBDJetZero68 (B.coeff D) (d.coeff V)+
      (1/2:k)*A.coeff (p-3)*FiveToSixQZeroBBDerivativeJetZero68 ((p:ℕ):k)
          (B.coeff D) (d.coeff V):=by
    linear_combination hATraw
  have hde':(derivative e).natDegree≤E-1:=
    (natDegree_derivative_le e).trans (Nat.sub_le_sub_right he' 1)
  have het:=coeff_derivative_at_bound68 e E (by omega)
  have he1:=coeff_derivative_at_bound68 e (E-1) (by omega)
  have he2:=coeff_derivative_at_bound68 e (E-2) (by omega)
  have he3:=coeff_derivative_at_bound68 e (E-3) (by omega)
  have he1':(derivative e).coeff (E-2)=
      e.coeff (E-1)*((E-1:ℕ):k):=by
    rw [←show E-1-1=E-2 by omega]
    exact he1
  have he2':(derivative e).coeff (E-3)=
      e.coeff (E-2)*((E-2:ℕ):k):=by
    rw [←show E-2-1=E-3 by omega]
    exact he2
  have he3':(derivative e).coeff (E-4)=
      e.coeff (E-3)*((E-3:ℕ):k):=by
    rw [←show E-3-1=E-4 by omega]
    exact he3
  have hcastE1:(((E-1:ℕ):k))=((E:ℕ):k)-1:=by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hcastE2:(((E-2:ℕ):k))=((E:ℕ):k)-2:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have hcastE3:(((E-3:ℕ):k))=((E:ℕ):k)-3:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have h3raw:=coeff_mul_mul_three_below_bounds68 B c (derivative e)
    D Cc (E-1) hD hC (by omega) hB' hc' hde'
  rw [show D+Cc+(E-1)-3=2*p-4 by omega,
    show E-1-1=E-2 by omega,show E-1-2=E-3 by omega,
    show E-1-3=E-4 by omega,het,he1',he2',he3',
    hcastE1,hcastE2,hcastE3] at h3raw
  have h3:(B*c*derivative e).coeff (2*p-4)=
      FiveToSixQZeroBCEDerivativeJetThree68 ((p:ℕ):k)
        (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
        (c.coeff Cc) (c.coeff (Cc-1)) (c.coeff (Cc-2)) (c.coeff (Cc-3))
        (e.coeff E) (e.coeff (E-1)) (e.coeff (E-2)) (e.coeff (E-3)):=by
    dsimp only [FiveToSixQZeroBCEDerivativeJetThree68]
    rw [hEcast] at h3raw
    linear_combination h3raw
  have hdc':(derivative c).natDegree≤Cc-1:=
    (natDegree_derivative_le c).trans (Nat.sub_le_sub_right hc' 1)
  have hct:=coeff_derivative_at_bound68 c Cc (by omega)
  have hc1:=coeff_derivative_at_bound68 c (Cc-1) (by omega)
  have hc2:=coeff_derivative_at_bound68 c (Cc-2) (by omega)
  have hc3:=coeff_derivative_at_bound68 c (Cc-3) (by omega)
  have hc1':(derivative c).coeff (Cc-2)=
      c.coeff (Cc-1)*((Cc-1:ℕ):k):=by
    rw [←show Cc-1-1=Cc-2 by omega]
    exact hc1
  have hc2':(derivative c).coeff (Cc-3)=
      c.coeff (Cc-2)*((Cc-2:ℕ):k):=by
    rw [←show Cc-2-1=Cc-3 by omega]
    exact hc2
  have hc3':(derivative c).coeff (Cc-4)=
      c.coeff (Cc-3)*((Cc-3:ℕ):k):=by
    rw [←show Cc-3-1=Cc-4 by omega]
    exact hc3
  have hcastC1:(((Cc-1:ℕ):k))=((Cc:ℕ):k)-1:=by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hcastC2:(((Cc-2:ℕ):k))=((Cc:ℕ):k)-2:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have hcastC3:(((Cc-3:ℕ):k))=((Cc:ℕ):k)-3:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have h4raw:=coeff_mul_mul_three_below_bounds68 c (derivative c) d
    Cc (Cc-1) V hC (by omega) (by omega) hc' hdc' hd'
  rw [show Cc+(Cc-1)+V-3=2*p-4 by omega,
    show Cc-1-1=Cc-2 by omega,show Cc-1-2=Cc-3 by omega,
    show Cc-1-3=Cc-4 by omega,hct,hc1',hc2',hc3',
    hcastC1,hcastC2,hcastC3] at h4raw
  have h4:(c*derivative c*d).coeff (2*p-4)=
      FiveToSixQZeroCCDerivativeDJetThree68 ((p:ℕ):k)
        (c.coeff Cc) (c.coeff (Cc-1)) (c.coeff (Cc-2)) (c.coeff (Cc-3))
        (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3)):=by
    dsimp only [FiveToSixQZeroCCDerivativeDJetThree68]
    rw [hCcast] at h4raw
    linear_combination h4raw
  have hloadpoly:L0=A*T-(3:k)•(B*c*derivative e)+
      (3:k)•(c*derivative c*d):=by
    dsimp only [L0,T,FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68]
    ring
  rw [hloadpoly]
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,hAT,h3,h4]
  dsimp only [FiveToSixQZeroRowZeroLoadJetThree68]
  ring

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_third68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_rowZero_load_third68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadThirdSource68

end Max11DegreeRoutes
