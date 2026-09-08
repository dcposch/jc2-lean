import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetTwoRankScratch

/-! # The second-jet source companion on `q=0`

One coefficient below the first companion, row zero at `2p-3` and row two
at `p-3` contain the same `J_(p-2)` jet.  Eliminating it, then using the
already verified row-two equation for `J_(p-1)` and the top contraction for
`J_p`, gives an exact second-jet companion.  All lower loads and literal
remainders are retained explicitly.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionNextScalar68
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
  (9:k)*((p-2:ℕ):k)*((p-1:ℕ):k)*Fce.coeff 0*
      ((2:k)*A.coeff p*A.coeff (p-2)+A.coeff (p-1)^2)+
    (6:k)*((p-2:ℕ):k)^2*A.coeff (p-2)*B.coeff D^2*d.coeff V+
    ((p-2:ℕ):k)*A.coeff (p-1)*
      (L2.coeff (p-2)+W2.coeff (p-2))+
    (6:k)*((p-2:ℕ):k)*(L0.coeff (2*p-3)+W0.coeff (2*p-3))+
    ((p:ℕ):k)*A.coeff p*(L2.coeff (p-3)+W2.coeff (p-3))=0

/-- Exact division-free elimination of the second lower `J` jet. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_companion_next68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionNextScalar68
      alpha gamma epsilon zeta eta A B c d e N S:=by
  let p:=2*N
  let D:=3*N-2*S
  let V:=5*N-3*S
  let i0:=2*p-3
  let i2:=p-3
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
  rcases hloaded with ⟨hsupport,hrows⟩
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
  have hJ:J.natDegree≤p:=by exact hstate'.2
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S
      ⟨⟨⟨hcur,ht,hstate,hclass,hraw0,hraw2⟩,hTD⟩,hrows⟩ with
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
  have hp3:3≤p:=by dsimp only [p];omega
  have hAAraw:=coeff_mul_two_below_bounds68 A (derivative A) p (p-1)
    (by omega) (by omega) hA' hdA
  rw [show p+(p-1)-2=i0 by dsimp only [i0];omega] at hAAraw
  have hdAtop:(derivative A).coeff (p-1)=A.coeff p*((p:ℕ):k):=by
    rw [coeff_derivative,show p-1+1=p by omega]
    congr 1
    exact_mod_cast (show p-1+1=p by omega)
  have hdAone:(derivative A).coeff (p-2)=
      A.coeff (p-1)*((p-1:ℕ):k):=by
    rw [coeff_derivative,show p-2+1=p-1 by omega]
    congr 1
    exact_mod_cast (show p-2+1=p-1 by omega)
  have hdAtwo:(derivative A).coeff (p-3)=
      A.coeff (p-2)*((p-2:ℕ):k):=by
    rw [coeff_derivative,show p-3+1=p-2 by omega]
    congr 1
    exact_mod_cast (show p-3+1=p-2 by omega)
  rw [show p-1-1=p-2 by omega,show p-1-2=p-3 by omega,
    hdAtop,hdAone,hdAtwo] at hAAraw
  have hAA:(A*derivative A).coeff i0=
      ((p-1:ℕ):k)*
        ((2:k)*A.coeff p*A.coeff (p-2)+A.coeff (p-1)^2):=by
    have hcast:((p:ℕ):k)+((p-2:ℕ):k)=
        (2:k)*((p-1:ℕ):k):=by
      exact_mod_cast (show p+(p-2)=2*(p-1) by omega)
    linear_combination hAAraw+A.coeff p*A.coeff (p-2)*hcast
  have hAJraw:=coeff_mul_two_below_bounds68 (derivative A) J (p-1) p
    (by omega) (by omega) hdA hJ
  rw [show (p-1)+p-2=i0 by dsimp only [i0];omega,
    show p-1-1=p-2 by omega,show p-1-2=p-3 by omega,
    hdAtop,hdAone,hdAtwo] at hAJraw
  have hAJ:(derivative A*J).coeff i0=
      ((p:ℕ):k)*A.coeff p*J.coeff (p-2)+
      ((p-1:ℕ):k)*A.coeff (p-1)*J.coeff (p-1)+
      ((p-2:ℕ):k)*A.coeff (p-2)*J.coeff p:=by
    linear_combination hAJraw
  have hFconst:Fce=C (Fce.coeff 0):=by
    apply eq_C_of_natDegree_le_zero
    have hFce':Fce=(3/8:k)•C i4:=by exact hFce
    rw [hFce']
    compute_degree
  have hAAF:(A*derivative A*Fce).coeff i0=Fce.coeff 0*
      ((p-1:ℕ):k)*
        ((2:k)*A.coeff p*A.coeff (p-2)+A.coeff (p-1)^2):=by
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
  have hrow0main:
      Fce.coeff 0*((p-1:ℕ):k)*
          ((2:k)*A.coeff p*A.coeff (p-2)+A.coeff (p-1)^2)-
        (((p:ℕ):k)*A.coeff p*J.coeff (p-2)+
          ((p-1:ℕ):k)*A.coeff (p-1)*J.coeff (p-1)+
          ((p-2:ℕ):k)*A.coeff (p-2)*J.coeff p)+
        L0.coeff i0+W0.coeff i0=0:=by
    linear_combination hfull0
  have hfull2:
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
        alpha gamma epsilon zeta eta A B c d e=0:=hrowTwo
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
  have hrow2coeff:
      ((-(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
        (6:k)•derivative J)+L2+W2).coeff i2=0:=by
    have hc:=congrArg (fun Q:k[X]=>Q.coeff i2) hfull2
    rw [hdecomp2,hfactor.2] at hc
    simpa only [coeff_zero] using hc
  have hFder:derivative Fce=0:=by rw [hFconst,derivative_C]
  have hA'F:derivative A*Fce=Fce.coeff 0•derivative A:=by
    calc
      derivative A*Fce=derivative A*C (Fce.coeff 0):=by
        conv_lhs => rw [hFconst]
      _=Fce.coeff 0•derivative A:=by
        simp only [smul_eq_C_mul]
        ring
  rw [hFder,mul_zero,hA'F] at hrow2coeff
  simp only [coeff_add,coeff_smul,smul_eq_mul,coeff_derivative,
    zero_mul,coeff_zero] at hrow2coeff
  have hi2succ:i2+1=p-2:=by dsimp only [i2];omega
  rw [hi2succ] at hrow2coeff
  have hi2cast:((i2:k)+1)=((p-2:ℕ):k):=by exact_mod_cast hi2succ
  rw [hi2cast] at hrow2coeff
  have hrow2main:((p-2:ℕ):k)*
      ((3:k)*A.coeff (p-2)*Fce.coeff 0+(6:k)*J.coeff (p-2))+
      L2.coeff i2+W2.coeff i2=0:=by
    push_cast at hrow2coeff ⊢
    linear_combination hrow2coeff
  have hpOld:11*N-7*S=p:=by dsimp only [p];omega
  rw [hpOld] at hrow2old
  change ((p-1:ℕ):k)*
      ((3:k)*A.coeff (p-1)*Fce.coeff 0+(6:k)*J.coeff (p-1))+
      L2.coeff (p-2)+W2.coeff (p-2)=0 at hrow2old
  have hcontract:=fiveToSix_zetaFirst_B3_equality_supportLoaded_contracted68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68]
    at hcontract
  have htop:=hcontract.2.1
  rw [hq,hpOld] at htop
  simp only [Nat.cast_zero,sub_zero] at htop
  have hNk:((N:ℕ):k)≠0:=by exact_mod_cast (show N≠0 by omega)
  have hpcast:((p:ℕ):k)=(2:k)*((N:ℕ):k):=by
    dsimp only [p]
    push_cast
    rfl
  have htopReduced:
      A.coeff p*Fce.coeff 0+
        (2:k)*(J.coeff p+B.coeff D^2*d.coeff V)=0:=by
    have hprod:((N:ℕ):k)*
        (A.coeff p*Fce.coeff 0+
          (2:k)*(J.coeff p+B.coeff D^2*d.coeff V))=0:=by
      dsimp only [p,D,V,Fce,J] at htop ⊢
      rw [hpcast] at htop
      linear_combination htop
    exact (mul_eq_zero.mp hprod).resolve_left hNk
  have hpcast2:(2:k)*((p-1:ℕ):k)=((p:ℕ):k)+((p-2:ℕ):k):=by
    exact_mod_cast (show 2*(p-1)=p+(p-2) by omega)
  have hresult:
      (9:k)*((p-2:ℕ):k)*((p-1:ℕ):k)*Fce.coeff 0*
          ((2:k)*A.coeff p*A.coeff (p-2)+A.coeff (p-1)^2)+
        (6:k)*((p-2:ℕ):k)^2*A.coeff (p-2)*B.coeff D^2*d.coeff V+
        ((p-2:ℕ):k)*A.coeff (p-1)*
          (L2.coeff (p-2)+W2.coeff (p-2))+
        (6:k)*((p-2:ℕ):k)*(L0.coeff i0+W0.coeff i0)+
        ((p:ℕ):k)*A.coeff p*(L2.coeff i2+W2.coeff i2)=0:=by
    linear_combination
      (6:k)*((p-2:ℕ):k)*hrow0main+
      ((p:ℕ):k)*A.coeff p*hrow2main+
      ((p-2:ℕ):k)*A.coeff (p-1)*hrow2old-
      (-3:k)*((p-2:ℕ):k)^2*A.coeff (p-2)*htopReduced-
      (-3:k)*((p-2:ℕ):k)*Fce.coeff 0*A.coeff p*A.coeff (p-2)*hpcast2
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionNextScalar68,
    p,D,V,Fce,L0,W0,L2,W2]
  simpa only [i0,i2] using hresult

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_companion_next68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionNext68

end Max11DegreeRoutes
