import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetReductionScratch

/-! # The independent first discriminant jet on `q=0`

The frozen source packet already kills an initial interval of reflected
discriminant coefficients.  On the exact `q=0` wall that interval contains
index one, so the first coefficient below the cusp top supplies its tangent
equation.  This relation is independent of the compensated-I4 first jet.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroDiscriminantNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The first tangent equation of the cusp discriminant on the exact
`q=0` wall. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    A.coeff (p-1)*B.coeff D^2+
      (2:k)*A.coeff p*B.coeff D*B.coeff (D-1)+
      (6:k)*c.coeff Cc*c.coeff (Cc-1)=0:=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let U:=8*N-2*G
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  change A.coeff (p-1)*B.coeff D^2+
    (2:k)*A.coeff p*B.coeff D*B.coeff (D-1)+
    (6:k)*c.coeff Cc*c.coeff (Cc-1)=0
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
  have hp:0<p:=by dsimp only [p];omega
  have hD:0<D:=by dsimp only [D];omega
  have hC:0<Cc:=by dsimp only [Cc];omega
  have hOne : 1 ≤ min S (7*N-2*G-S) := by omega
  have href: (Delta.reflect U).coeff 1=0:=by
    dsimp only [Delta,U]
    exact hzero 1 hOne
  have hDelta:Delta.coeff (U-1)=0:=by
    rw [coeff_reflect,revAt_le (by dsimp only [U];omega)] at href
    exact href
  have hABB0:=coeff_mul_mul_one_below_bounds68 A B B p D D
    hp hD hD hA' hB' hB'
  have hABB:(A*B^2).coeff (U-1)=
      A.coeff (p-1)*B.coeff D^2+
      (2:k)*A.coeff p*B.coeff D*B.coeff (D-1):=by
    rw [show p+D+D=U by dsimp only [p,D,U];rw [hGS];omega] at hABB0
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at hABB0 ⊢
    linear_combination hABB0
  have hcc0:=coeff_mul_one_below_bounds68 c c Cc Cc hC hC hc' hc'
  have hcc:(c^2).coeff (U-1)=
      (2:k)*c.coeff Cc*c.coeff (Cc-1):=by
    rw [show Cc+Cc=U by dsimp only [Cc,U];rw [hGS];omega] at hcc0
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at hcc0 ⊢
    linear_combination hcc0
  dsimp only [Delta,fiveToSixCuspDiscriminantPolynomial68] at hDelta
  simp only [coeff_add,coeff_smul,smul_eq_mul,hABB,hcc] at hDelta
  linear_combination hDelta

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroDiscriminantNext68

end Max11DegreeRoutes
