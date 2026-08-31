import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroDeltaDegreeScratch

/-! # The bounded Jacobian row on the global zero-`Fce` branch -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroH68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixQZeroFceZeroH68 (B c d:k[X]):k[X]:=
  (4:k)•(B^2*c)+(9:k)•d^2

/-- Multiplying the bounded Jacobian numerator by `B` exposes the new
factor `c*(4B²c+9d²)`; the only omitted term is a multiple of `Fce`. -/
theorem fiveToSix_qZero_Fce_J_Delta_H_algebra68
    (gamma epsilon:k) (A B c d e:k[X]):
    let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
    let H:=FiveToSixQZeroFceZeroH68 B c d
    B*J=-(1/9:k)•(B^2*Delta)+(1/3:k)•(c*H)-
      (1/3:k)•(B^3*d)+(9/2*gamma:k)•d^2+
      (9/4*epsilon:k)•(B*d)-(3:k)•(d*Fce):=by
  dsimp only [FiveToSixQZeroFceZeroH68,
    fiveToSixCuspDiscriminantPolynomial68]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul,map_add,map_sub,map_mul,map_pow,
    map_neg,map_zero,RatFunc.algebraMap_C]
  simp only [map_div₀,map_ofNat,map_one]
  ring

/-- The bounded Jacobian row and the first discriminant descent force
`4B²c+9d²` down to degree `D+p-Cc` (equal to `N` on `9N=7S`). -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_H_degree68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0)
    (hf:(((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B).coeff 0=0):
    let p:=2*N
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    (FiveToSixQZeroFceZeroH68 B c d).natDegree≤D+p-Cc:=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let H:=FiveToSixQZeroFceZeroH68 B c d
  let M:=D+p
  change H.natDegree≤M-Cc
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
  have hcidx:Cc=4*N-G:=by dsimp only [Cc];omega
  have hccoeff:c.coeff Cc≠0:=by rw [hcidx];exact hctop
  have hcne:c≠0:=by
    intro hcz
    subst c
    exact hccoeff rfl
  have hcdeg:c.natDegree=Cc:=
    natDegree_eq_of_le_of_coeff_ne_zero hc' hccoeff
  have hDelta:Delta.natDegree≤3*D+Cc-V:=by
    exact fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_Delta_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  have hJ:J.natDegree≤p:=by
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
    exact hstate'.2
  have halg:=fiveToSix_qZero_Fce_J_Delta_H_algebra68
    gamma epsilon A B c d e
  change B*J=-(1/9:k)•(B^2*Delta)+(1/3:k)•(c*H)-
      (1/3:k)•(B^3*d)+(9/2*gamma:k)•d^2+
      (9/4*epsilon:k)•(B*d)-(3:k)•(d*Fce) at halg
  change Fce=0 at hFzero
  rw [hFzero,mul_zero,smul_zero,sub_zero] at halg
  have hiso:(1/3:k)•(c*H)=B*J+(1/9:k)•(B^2*Delta)+
      (1/3:k)•(B^3*d)-(9/2*gamma:k)•d^2-
      (9/4*epsilon:k)•(B*d):=by
    rw [halg]
    module
  have hscaled:((1/3:k)•(c*H)).natDegree≤M:=by
    rw [hiso]
    dsimp only [M]
    compute_degree <;> omega
  rw [natDegree_smul _ (by norm_num:(1/3:k)≠0)] at hscaled
  by_cases hHz:H=0
  · rw [hHz,natDegree_zero]
    exact Nat.zero_le _
  · rw [natDegree_mul hcne hHz,hcdeg] at hscaled
    omega

#print axioms fiveToSix_qZero_Fce_J_Delta_H_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_H_degree68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroH68

end Max11DegreeRoutes
