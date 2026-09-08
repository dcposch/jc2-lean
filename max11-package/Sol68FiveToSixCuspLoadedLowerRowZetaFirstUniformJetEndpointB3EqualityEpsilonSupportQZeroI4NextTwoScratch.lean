import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroDiscriminantNextTwoScratch

/-! # The second compensated-I4 jet on `q=0`

Since the compensated `I4` polynomial is constant, its second coefficient
below the genuine top gives the second-order product incidence equation.
All secondary summands are uniformly too short, including in the minimal
chart.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroI4NextTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The exact second-jet equation of the compensated `I4` product. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_I4_next_two68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    B.coeff (D-2)*e.coeff E+B.coeff (D-1)*e.coeff (E-1)+
      B.coeff D*e.coeff (E-2)+
      c.coeff (Cc-2)*d.coeff V+c.coeff (Cc-1)*d.coeff (V-1)+
      c.coeff Cc*d.coeff (V-2)=0:=by
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
  have hD:2≤D:=by dsimp only [D];omega
  have hC:2≤Cc:=by dsimp only [Cc];omega
  have hV:2≤V:=by dsimp only [V];omega
  have hE:2≤E:=by dsimp only [E];omega
  have hB3deg:(B^3).natDegree≤3*D:=by compute_degree;omega
  have hB3low:(B^3).natDegree<K-2:=by dsimp only [D,E,K] at *;omega
  have hdLow:d.natDegree<K-2:=by dsimp only [D,E,K,V] at *;omega
  have hBLow:B.natDegree<K-2:=by dsimp only [D,E,K] at *;omega
  have hBe0:=coeff_mul_two_below_bounds68 B e D E hD hE hB' he'
  have hBe:(B*e).coeff (K-2)=
      B.coeff (D-2)*e.coeff E+B.coeff (D-1)*e.coeff (E-1)+
      B.coeff D*e.coeff (E-2):=by
    simpa only [K] using hBe0
  have hcd0:=coeff_mul_two_below_bounds68 c d Cc V hC hV hc' hd'
  have hcd:(c*d).coeff (K-2)=
      c.coeff (Cc-2)*d.coeff V+c.coeff (Cc-1)*d.coeff (V-1)+
      c.coeff Cc*d.coeff (V-2):=by
    rw [show Cc+V=K by dsimp only [D,Cc,V,E,K];omega] at hcd0
    exact hcd0
  have hFK:Fce.coeff (K-2)=0:=by
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

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_I4_next_two68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroI4NextTwo68

end Max11DegreeRoutes
