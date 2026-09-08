import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderThirdScratch
import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroI4NextTwoScratch

/-! # Independent order-three source jets on `q=0` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetThirdSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Three coefficients below a product of three separate degree bounds. -/
theorem coeff_mul_mul_three_below_bounds68 (p q r:k[X]) (u v w:ℕ)
    (hu:3≤u) (hv:3≤v) (hw:3≤w)
    (hp:p.natDegree≤u) (hq:q.natDegree≤v) (hr:r.natDegree≤w):
    (p*q*r).coeff (u+v+w-3)=
      p.coeff (u-3)*q.coeff v*r.coeff w+
      p.coeff (u-2)*q.coeff (v-1)*r.coeff w+
      p.coeff (u-1)*q.coeff (v-2)*r.coeff w+
      p.coeff u*q.coeff (v-3)*r.coeff w+
      p.coeff (u-2)*q.coeff v*r.coeff (w-1)+
      p.coeff (u-1)*q.coeff (v-1)*r.coeff (w-1)+
      p.coeff u*q.coeff (v-2)*r.coeff (w-1)+
      p.coeff (u-1)*q.coeff v*r.coeff (w-2)+
      p.coeff u*q.coeff (v-1)*r.coeff (w-2)+
      p.coeff u*q.coeff v*r.coeff (w-3):=by
  have hpq:(p*q).natDegree≤u+v:=by compute_degree;omega
  rw [coeff_mul_three_below_bounds68 (p*q) r (u+v) w
      (by omega) hw hpq hr,
    coeff_mul_three_below_bounds68 p q u v hu hv hp hq,
    coeff_mul_two_below_bounds68 p q u v (by omega) (by omega) hp hq,
    coeff_mul_one_below_bounds68 p q u v (by omega) (by omega) hp hq,
    coeff_mul_at_bounds68 p q u v hp hq]
  ring

/-- The exact third reflected-discriminant jet. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_third68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    A.coeff (p-3)*B.coeff D^2+
      (2:k)*A.coeff (p-2)*B.coeff D*B.coeff (D-1)+
      A.coeff (p-1)*((2:k)*B.coeff D*B.coeff (D-2)+
        B.coeff (D-1)^2)+
      A.coeff p*((2:k)*B.coeff D*B.coeff (D-3)+
        (2:k)*B.coeff (D-1)*B.coeff (D-2))+
      (6:k)*(c.coeff Cc*c.coeff (Cc-3)+
        c.coeff (Cc-1)*c.coeff (Cc-2))=0:=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let U:=8*N-2*G
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  change A.coeff (p-3)*B.coeff D^2+
      (2:k)*A.coeff (p-2)*B.coeff D*B.coeff (D-1)+
      A.coeff (p-1)*((2:k)*B.coeff D*B.coeff (D-2)+
        B.coeff (D-1)^2)+
      A.coeff p*((2:k)*B.coeff D*B.coeff (D-3)+
        (2:k)*B.coeff (D-1)*B.coeff (D-2))+
      (6:k)*(c.coeff Cc*c.coeff (Cc-3)+
        c.coeff (Cc-1)*c.coeff (Cc-2))=0
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
  rcases hrest with ⟨hless,hmu,hzeta,hzero,hDeltaDeg⟩
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq:9*N=7*S:=hnxt.1.1
  have hA':A.natDegree≤p:=by simpa [p] using hA
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hc':c.natDegree≤Cc:=by simpa [Cc,hGS] using hc
  have hp:3≤p:=by dsimp only [p];omega
  have hD:3≤D:=by dsimp only [D];omega
  have hC:3≤Cc:=by dsimp only [Cc];omega
  have hThree : 3 ≤ min S (7*N-2*G-S) := by omega
  have href:(Delta.reflect U).coeff 3=0:=by
    dsimp only [Delta,U]
    exact hzero 3 hThree
  have hDelta:Delta.coeff (U-3)=0:=by
    rw [coeff_reflect,revAt_le (by dsimp only [U];omega)] at href
    exact href
  have hABB0:=coeff_mul_mul_three_below_bounds68 A B B p D D
    hp hD hD hA' hB' hB'
  have hABB:(A*B^2).coeff (U-3)=
      A.coeff (p-3)*B.coeff D^2+
      (2:k)*A.coeff (p-2)*B.coeff D*B.coeff (D-1)+
      A.coeff (p-1)*((2:k)*B.coeff D*B.coeff (D-2)+
        B.coeff (D-1)^2)+
      A.coeff p*((2:k)*B.coeff D*B.coeff (D-3)+
        (2:k)*B.coeff (D-1)*B.coeff (D-2)):=by
    rw [show p+D+D=U by dsimp only [p,D,U];rw [hGS];omega] at hABB0
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at hABB0 ⊢
    linear_combination hABB0
  have hcc0:=coeff_mul_three_below_bounds68 c c Cc Cc hC hC hc' hc'
  have hcc:(c^2).coeff (U-3)=
      (2:k)*(c.coeff Cc*c.coeff (Cc-3)+
        c.coeff (Cc-1)*c.coeff (Cc-2)):=by
    rw [show Cc+Cc=U by dsimp only [Cc,U];rw [hGS];omega] at hcc0
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at hcc0 ⊢
    linear_combination hcc0
  dsimp only [Delta,fiveToSixCuspDiscriminantPolynomial68] at hDelta
  simp only [coeff_add,coeff_smul,smul_eq_mul,hABB,hcc] at hDelta
  linear_combination hDelta

/-- The exact third coefficient of the compensated `I4` product. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_I4_third68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    B.coeff (D-3)*e.coeff E+B.coeff (D-2)*e.coeff (E-1)+
      B.coeff (D-1)*e.coeff (E-2)+B.coeff D*e.coeff (E-3)+
      c.coeff (Cc-3)*d.coeff V+c.coeff (Cc-2)*d.coeff (V-1)+
      c.coeff (Cc-1)*d.coeff (V-2)+c.coeff Cc*d.coeff (V-3)=0:=by
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let K:=D+E
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  rcases hnxt.2.1 with ⟨i4,i3,hFce,hRce,hRceDeg⟩
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hpacket,hrest⟩
  rcases hpacket with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hc':c.natDegree≤Cc:=by simpa [Cc,hGS] using hc
  have hd':d.natDegree≤V:=by dsimp only [V];rw [hGS] at hd;omega
  have he':e.natDegree≤E:=by dsimp only [E];rw [hGS] at he;omega
  have hEq:9*N=7*S:=hnxt.1.1
  have hD:3≤D:=by dsimp only [D];omega
  have hC:3≤Cc:=by dsimp only [Cc];omega
  have hV:3≤V:=by dsimp only [V];omega
  have hE:3≤E:=by dsimp only [E];omega
  have hB3deg:(B^3).natDegree≤3*D:=by compute_degree;omega
  have hB3low:(B^3).natDegree<K-3:=by dsimp only [D,E,K] at *;omega
  have hdLow:d.natDegree<K-3:=by dsimp only [D,E,K,V] at *;omega
  have hBLow:B.natDegree<K-3:=by dsimp only [D,E,K] at *;omega
  have hBe0:=coeff_mul_three_below_bounds68 B e D E hD hE hB' he'
  have hBe:(B*e).coeff (K-3)=
      B.coeff (D-3)*e.coeff E+B.coeff (D-2)*e.coeff (E-1)+
      B.coeff (D-1)*e.coeff (E-2)+B.coeff D*e.coeff (E-3):=by
    simpa only [K] using hBe0
  have hcd0:=coeff_mul_three_below_bounds68 c d Cc V hC hV hc' hd'
  have hcd:(c*d).coeff (K-3)=
      c.coeff (Cc-3)*d.coeff V+c.coeff (Cc-2)*d.coeff (V-1)+
      c.coeff (Cc-1)*d.coeff (V-2)+c.coeff Cc*d.coeff (V-3):=by
    rw [show Cc+V=K by dsimp only [D,Cc,V,E,K];omega] at hcd0
    exact hcd0
  have hFK:Fce.coeff (K-3)=0:=by
    dsimp only [Fce]
    rw [hFce,coeff_smul,coeff_C]
    split_ifs with h
    · omega
    · simp only [smul_zero]
  dsimp only [Fce] at hFK
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,hBe,hcd,
    coeff_eq_zero_of_natDegree_lt hB3low,
    coeff_eq_zero_of_natDegree_lt hdLow,
    coeff_eq_zero_of_natDegree_lt hBLow,mul_zero,sub_zero,add_zero] at hFK
  linear_combination hFK

#print axioms coeff_mul_mul_three_below_bounds68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_third68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_I4_third68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetThirdSource68

end Max11DegreeRoutes
