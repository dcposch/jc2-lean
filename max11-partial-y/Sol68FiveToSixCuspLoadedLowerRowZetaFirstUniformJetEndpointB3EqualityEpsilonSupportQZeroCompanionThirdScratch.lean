import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionNextReductionScratch

/-! # The third source companion on `q=0`

This file extracts the next row-zero/row-two elimination without expanding
loads or deleting literal remainders.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionThird68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Three coefficients below a product of two separate bounds. -/
theorem coeff_mul_three_below_bounds68 (f g:k[X]) (u v:ℕ)
    (hu:3≤u) (hv:3≤v) (hf:f.natDegree≤u) (hg:g.natDegree≤v):
    (f*g).coeff (u+v-3)=
      f.coeff (u-3)*g.coeff v+f.coeff (u-2)*g.coeff (v-1)+
      f.coeff (u-1)*g.coeff (v-2)+f.coeff u*g.coeff (v-3):=by
  have hmem0:u-3∈Finset.range (u+v-3+1):=
    Finset.mem_range.mpr (by omega)
  have hmem1:u-2∈(Finset.range (u+v-3+1)).erase (u-3):=
    Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by omega)⟩
  have hmem2:u-1∈((Finset.range (u+v-3+1)).erase (u-3)).erase (u-2):=
    Finset.mem_erase.mpr ⟨by omega,
      Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by omega)⟩⟩
  have hmem3:u∈(((Finset.range (u+v-3+1)).erase (u-3)).erase (u-2)).erase (u-1):=
    Finset.mem_erase.mpr ⟨by omega,Finset.mem_erase.mpr ⟨by omega,
      Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by omega)⟩⟩⟩
  have hzero:∀i∈((((Finset.range (u+v-3+1)).erase (u-3)).erase (u-2)).erase
      (u-1)).erase u,f.coeff i*g.coeff (u+v-3-i)=0:=by
    intro i hi
    have hi0:=Finset.mem_erase.mp hi
    have hi1:=Finset.mem_erase.mp hi0.2
    have hi2:=Finset.mem_erase.mp hi1.2
    have hi3:=Finset.mem_erase.mp hi2.2
    by_cases hgt : u < i
    · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt hgt),zero_mul]
    · have hlt : i < u-3 := by omega
      rw [coeff_eq_zero_of_natDegree_lt (hg.trans_lt (by omega)),mul_zero]
  have hsum:(f*g).coeff (u+v-3)=
      ∑i∈Finset.range (u+v-3+1),f.coeff i*g.coeff (u+v-3-i):=by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have h0:=Finset.add_sum_erase (Finset.range (u+v-3+1))
    (fun i=>f.coeff i*g.coeff (u+v-3-i)) hmem0
  have h1:=Finset.add_sum_erase ((Finset.range (u+v-3+1)).erase (u-3))
    (fun i=>f.coeff i*g.coeff (u+v-3-i)) hmem1
  have h2:=Finset.add_sum_erase
    (((Finset.range (u+v-3+1)).erase (u-3)).erase (u-2))
    (fun i=>f.coeff i*g.coeff (u+v-3-i)) hmem2
  have h3:=Finset.add_sum_erase
    ((((Finset.range (u+v-3+1)).erase (u-3)).erase (u-2)).erase (u-1))
    (fun i=>f.coeff i*g.coeff (u+v-3-i)) hmem3
  have h4:∑i∈((((Finset.range (u+v-3+1)).erase (u-3)).erase (u-2)).erase
      (u-1)).erase u,f.coeff i*g.coeff (u+v-3-i)=0:=
    Finset.sum_eq_zero hzero
  rw [hsum,←h0,←h1,←h2,←h3,h4,add_zero]
  rw [show u+v-3-(u-3)=v by omega,
    show u+v-3-(u-2)=v-1 by omega,
    show u+v-3-(u-1)=v-2 by omega,
    show u+v-3-u=v-3 by omega]
  ring

/-- Every high row-two coefficient gives the corresponding `J` jet. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S r:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0) (hr:r<2*N):
    let p:=2*N
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
    let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
      alpha gamma epsilon zeta eta A B c d e
    (((p-r:ℕ):k))*
        ((3:k)*A.coeff (p-r)*Fce.coeff 0+(6:k)*J.coeff (p-r))+
      L2.coeff (p-r-1)+W2.coeff (p-r-1)=0:=by
  let p:=2*N
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let i:=p-r-1
  change (((p-r:ℕ):k))*
      ((3:k)*A.coeff (p-r)*Fce.coeff 0+(6:k)*J.coeff (p-r))+
    L2.coeff i+W2.coeff i=0
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  rcases hnxt.2.1 with ⟨i4,i3,hFce,hRce,hRceDeg⟩
  have hFconst:Fce=C (Fce.coeff 0):=by
    apply eq_C_of_natDegree_le_zero
    have hFce':Fce=(3/8:k)•C i4:=by exact hFce
    rw [hFce']
    compute_degree
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
  rcases had with ⟨j4,j3,hj4,hj3,hrow0,hrow1,hrowTwo,hpos,hiff⟩
  have hfactor:=fiveToSix_zetaFirst_B3_equality_support_load_factor68
    (k:=k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  have hdecomp2:
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
          alpha gamma epsilon zeta eta A B c d e=
        (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
          (9*gamma:k)•(A*derivative d)+
          (9/2*gamma:k)•(d*derivative A)+
          (9/4*epsilon:k)•(derivative A*B)-
          (9/2*epsilon:k)•(A*derivative B)+L2)+W2:=by
    dsimp only [W2,L2,
      FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68]
    module
  have hfull2:
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
        alpha gamma epsilon zeta eta A B c d e=0:=hrowTwo
  have hc:
      ((-(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
        (6:k)•derivative J)+L2+W2).coeff i=0:=by
    have hc':=congrArg (fun Q:k[X]=>Q.coeff i) hfull2
    rw [hdecomp2,hfactor.2] at hc'
    simpa only [coeff_zero] using hc'
  have hFder:derivative Fce=0:=by rw [hFconst,derivative_C]
  have hA'F:derivative A*Fce=Fce.coeff 0•derivative A:=by
    calc
      derivative A*Fce=derivative A*C (Fce.coeff 0):=by
        conv_lhs => rw [hFconst]
      _=Fce.coeff 0•derivative A:=by
        simp only [smul_eq_C_mul]
        ring
  rw [hFder,mul_zero,hA'F] at hc
  simp only [coeff_add,coeff_smul,smul_eq_mul,coeff_derivative,
    zero_mul,coeff_zero] at hc
  have hisucc:i+1=p-r:=by dsimp only [i,p];omega
  rw [hisucc] at hc
  have hicast:((i:k)+1)=((p-r:ℕ):k):=by exact_mod_cast hisucc
  rw [hicast] at hc
  push_cast at hc ⊢
  linear_combination hc

def FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionThirdScalar68
    (alpha gamma epsilon zeta eta:k) (A B c d e:k[X])
    (N S:ℕ):Prop:=
  let p:=2*N
  let D:=3*N-2*S
  let V:=5*N-3*S
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  (9:k)*((p-3:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*
      ((2*p-3:ℕ):k)*Fce.coeff 0*
      (A.coeff p*A.coeff (p-3)+A.coeff (p-1)*A.coeff (p-2))+
    (6:k)*((p-3:ℕ):k)^2*((p-2:ℕ):k)*((p-1:ℕ):k)*
      A.coeff (p-3)*B.coeff D^2*d.coeff V+
    (6:k)*((p-3:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*
      (L0.coeff (2*p-4)+W0.coeff (2*p-4))+
    ((p:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*A.coeff p*
      (L2.coeff (p-4)+W2.coeff (p-4))+
    ((p-3:ℕ):k)*((p-1:ℕ):k)^2*A.coeff (p-1)*
      (L2.coeff (p-3)+W2.coeff (p-3))+
    ((p-3:ℕ):k)*((p-2:ℕ):k)^2*A.coeff (p-2)*
      (L2.coeff (p-2)+W2.coeff (p-2))=0

/-- Exact division-free elimination of `J_(p-3)` and all higher `J` jets. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_companion_third68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionThirdScalar68
      alpha gamma epsilon zeta eta A B c d e N S:=by
  let p:=2*N
  let D:=3*N-2*S
  let V:=5*N-3*S
  let i0:=2*p-4
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  rcases hnxt with ⟨harith,hexact,hrow2old,hp1cast⟩
  rcases hexact with ⟨i4,i3,hFce,hRce,hRceDeg⟩
  have hEq:9*N=7*S:=harith.1
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
  have hA':A.natDegree≤p:=by simpa [p] using hA
  have hdA:(derivative A).natDegree≤p-1:=by
    have h:=natDegree_derivative_le A
    dsimp only [p]
    omega
  have hJ:J.natDegree≤p:=by
    have hloaded':=hs.1
    rcases hloaded' with ⟨hsupport,hrows⟩
    rcases hsupport with ⟨hstop,hTD⟩
    rcases hstop with ⟨hcur,ht,hstate,hclass,hraw0,hraw2⟩
    let T:=S-2*D
    let t:=min D T
    have htT:t=T:=by dsimp only [t];exact Nat.min_eq_right hTD
    have hstate':=hstate
    dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68] at hstate'
    have hjidx:5*N-2*S-(t-1)-1=p:=by
      dsimp only [D,T] at htT
      dsimp only [p]
      omega
    rw [hjidx] at hstate'
    exact hstate'.2
  have hp3:3≤p:=by dsimp only [p];omega
  have hpm1:3≤p-1:=by dsimp only [p];omega
  have hAAraw:=coeff_mul_three_below_bounds68 A (derivative A) p (p-1)
    hp3 hpm1 hA' hdA
  rw [show p+(p-1)-3=i0 by dsimp only [i0];omega] at hAAraw
  have hdA0:(derivative A).coeff (p-1)=A.coeff p*((p:ℕ):k):=by
    rw [coeff_derivative,show p-1+1=p by omega]
    congr 1
    exact_mod_cast (show p-1+1=p by omega)
  have hdA1:(derivative A).coeff (p-2)=
      A.coeff (p-1)*((p-1:ℕ):k):=by
    rw [coeff_derivative,show p-2+1=p-1 by omega]
    congr 1
    exact_mod_cast (show p-2+1=p-1 by omega)
  have hdA2:(derivative A).coeff (p-3)=
      A.coeff (p-2)*((p-2:ℕ):k):=by
    rw [coeff_derivative,show p-3+1=p-2 by omega]
    congr 1
    exact_mod_cast (show p-3+1=p-2 by omega)
  have hdA3:(derivative A).coeff (p-4)=
      A.coeff (p-3)*((p-3:ℕ):k):=by
    rw [coeff_derivative,show p-4+1=p-3 by omega]
    congr 1
    exact_mod_cast (show p-4+1=p-3 by omega)
  rw [show p-1-1=p-2 by omega,show p-1-2=p-3 by omega,
    show p-1-3=p-4 by omega,hdA0,hdA1,hdA2,hdA3] at hAAraw
  have hAA:(A*derivative A).coeff i0=((2*p-3:ℕ):k)*
      (A.coeff p*A.coeff (p-3)+A.coeff (p-1)*A.coeff (p-2)):=by
    have hcast0:((p:ℕ):k)+((p-3:ℕ):k)=((2*p-3:ℕ):k):=by
      exact_mod_cast (show p+(p-3)=2*p-3 by omega)
    have hcast1:((p-1:ℕ):k)+((p-2:ℕ):k)=
        ((2*p-3:ℕ):k):=by
      exact_mod_cast (show (p-1)+(p-2)=2*p-3 by omega)
    linear_combination hAAraw+
      A.coeff p*A.coeff (p-3)*hcast0+
      A.coeff (p-1)*A.coeff (p-2)*hcast1
  have hAJraw:=coeff_mul_three_below_bounds68 (derivative A) J (p-1) p
    hpm1 hp3 hdA hJ
  rw [show (p-1)+p-3=i0 by dsimp only [i0];omega,
    show p-1-1=p-2 by omega,show p-1-2=p-3 by omega,
    show p-1-3=p-4 by omega,hdA0,hdA1,hdA2,hdA3] at hAJraw
  have hAJ:(derivative A*J).coeff i0=
      ((p:ℕ):k)*A.coeff p*J.coeff (p-3)+
      ((p-1:ℕ):k)*A.coeff (p-1)*J.coeff (p-2)+
      ((p-2:ℕ):k)*A.coeff (p-2)*J.coeff (p-1)+
      ((p-3:ℕ):k)*A.coeff (p-3)*J.coeff p:=by
    linear_combination hAJraw
  have hFconst:Fce=C (Fce.coeff 0):=by
    apply eq_C_of_natDegree_le_zero
    have hFce':Fce=(3/8:k)•C i4:=by exact hFce
    rw [hFce']
    compute_degree
  have hAAF:(A*derivative A*Fce).coeff i0=Fce.coeff 0*
      ((2*p-3:ℕ):k)*
        (A.coeff p*A.coeff (p-3)+A.coeff (p-1)*A.coeff (p-2)):=by
    have heq:A*derivative A*Fce=Fce.coeff 0•(A*derivative A):=by
      calc
        A*derivative A*Fce=(A*derivative A)*C (Fce.coeff 0):=by
          conv_lhs => rw [hFconst]
        _=Fce.coeff 0•(A*derivative A):=by
          simp only [smul_eq_C_mul]
          ring
    rw [heq,coeff_smul,hAA]
    ring
  rcases had with ⟨j4,j3,hj4,hj3,hrow0,hrow1,hrowTwo,hpos,hiff⟩
  have hfull0:=hpos i0 (by dsimp only [i0,p];omega)
  have hfactor:=fiveToSix_zetaFirst_B3_equality_support_load_factor68
    (k:=k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  have hdecomp0:
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
          alpha gamma epsilon zeta eta A B c d e=
        (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
          (3/2*gamma:k)•(A*derivative A*d)+
          (3/4*epsilon:k)•(A*B*derivative A)+L0)+W0:=by
    dsimp only [W0,L0,
      FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68]
    module
  change (FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
    alpha gamma epsilon zeta eta A B c d e).coeff i0=0 at hfull0
  rw [hdecomp0,hfactor.1] at hfull0
  change (A*derivative A*Fce-derivative A*J+L0+W0).coeff i0=0 at hfull0
  simp only [coeff_add,coeff_sub,hAAF,hAJ] at hfull0
  have hrow0main:Fce.coeff 0*((2*p-3:ℕ):k)*
        (A.coeff p*A.coeff (p-3)+A.coeff (p-1)*A.coeff (p-2))-
      (((p:ℕ):k)*A.coeff p*J.coeff (p-3)+
       ((p-1:ℕ):k)*A.coeff (p-1)*J.coeff (p-2)+
       ((p-2:ℕ):k)*A.coeff (p-2)*J.coeff (p-1)+
       ((p-3:ℕ):k)*A.coeff (p-3)*J.coeff p)+
      L0.coeff i0+W0.coeff i0=0:=by
    linear_combination hfull0
  have hr1:=fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S 1 hs hq
      (by dsimp only [p] at *;omega)
  have hr2:=fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S 2 hs hq
      (by dsimp only [p] at *;omega)
  have hr3:=fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S 3 hs hq
      (by dsimp only [p] at *;omega)
  dsimp only at hr1 hr2 hr3
  change ((p-1:ℕ):k)*
      ((3:k)*A.coeff (p-1)*Fce.coeff 0+(6:k)*J.coeff (p-1))+
    L2.coeff (p-2)+W2.coeff (p-2)=0 at hr1
  change ((p-2:ℕ):k)*
      ((3:k)*A.coeff (p-2)*Fce.coeff 0+(6:k)*J.coeff (p-2))+
    L2.coeff (p-3)+W2.coeff (p-3)=0 at hr2
  change ((p-3:ℕ):k)*
      ((3:k)*A.coeff (p-3)*Fce.coeff 0+(6:k)*J.coeff (p-3))+
    L2.coeff (p-4)+W2.coeff (p-4)=0 at hr3
  have hcontract:=fiveToSix_zetaFirst_B3_equality_supportLoaded_contracted68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68]
    at hcontract
  have htop:=hcontract.2.1
  have hpOld:11*N-7*S=p:=by dsimp only [p];omega
  rw [hq,hpOld] at htop
  simp only [Nat.cast_zero,sub_zero] at htop
  have hNk:((N:ℕ):k)≠0:=by exact_mod_cast (show N≠0 by omega)
  have hpcast:((p:ℕ):k)=(2:k)*((N:ℕ):k):=by
    dsimp only [p]
    push_cast
    rfl
  have htopReduced:A.coeff p*Fce.coeff 0+
      (2:k)*(J.coeff p+B.coeff D^2*d.coeff V)=0:=by
    have hprod:((N:ℕ):k)*(A.coeff p*Fce.coeff 0+
        (2:k)*(J.coeff p+B.coeff D^2*d.coeff V))=0:=by
      dsimp only [p,D,V,Fce,J] at htop ⊢
      rw [hpcast] at htop
      linear_combination htop
    exact (mul_eq_zero.mp hprod).resolve_left hNk
  have hresult:
      (9:k)*((p-3:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*
          ((2*p-3:ℕ):k)*Fce.coeff 0*
          (A.coeff p*A.coeff (p-3)+A.coeff (p-1)*A.coeff (p-2))+
        (6:k)*((p-3:ℕ):k)^2*((p-2:ℕ):k)*((p-1:ℕ):k)*
          A.coeff (p-3)*B.coeff D^2*d.coeff V+
        (6:k)*((p-3:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*
          (L0.coeff i0+W0.coeff i0)+
        ((p:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*A.coeff p*
          (L2.coeff (p-4)+W2.coeff (p-4))+
        ((p-3:ℕ):k)*((p-1:ℕ):k)^2*A.coeff (p-1)*
          (L2.coeff (p-3)+W2.coeff (p-3))+
        ((p-3:ℕ):k)*((p-2:ℕ):k)^2*A.coeff (p-2)*
          (L2.coeff (p-2)+W2.coeff (p-2))=0:=by
    have hp1cast':((p-1:ℕ):k)=((p:ℕ):k)-(1:k):=by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      norm_num
    have hp2cast':((p-2:ℕ):k)=((p:ℕ):k)-(2:k):=by
      rw [Nat.cast_sub (by omega : 2 ≤ p)]
      norm_num
    have hp3cast':((p-3:ℕ):k)=((p:ℕ):k)-(3:k):=by
      rw [Nat.cast_sub hp3]
      norm_num
    have h2p3cast':((2*p-3:ℕ):k)=(2:k)*((p:ℕ):k)-(3:k):=by
      rw [Nat.cast_sub (by omega : 3 ≤ 2*p)]
      push_cast
      ring
    rw [hp1cast',hp2cast',hp3cast',h2p3cast'] at hrow0main ⊢
    rw [hp1cast'] at hr1
    rw [hp2cast'] at hr2
    rw [hp3cast'] at hr3
    linear_combination
      (6:k)*(((p:ℕ):k)-3)*(((p:ℕ):k)-2)*(((p:ℕ):k)-1)*hrow0main+
      ((p:ℕ):k)*(((p:ℕ):k)-2)*(((p:ℕ):k)-1)*A.coeff p*hr3+
      (((p:ℕ):k)-3)*(((p:ℕ):k)-1)^2*A.coeff (p-1)*hr2+
      (((p:ℕ):k)-3)*(((p:ℕ):k)-2)^2*A.coeff (p-2)*hr1+
      (3:k)*(((p:ℕ):k)-3)^2*(((p:ℕ):k)-2)*(((p:ℕ):k)-1)*
        A.coeff (p-3)*htopReduced
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionThirdScalar68,
    p,D,V,Fce,L0,W0,L2,W2]
  simpa only [i0] using hresult

#print axioms coeff_mul_three_below_bounds68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_jet68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_companion_third68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionThird68

end Max11DegreeRoutes
