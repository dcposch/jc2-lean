import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetRankScratch

/-! # The second discriminant jet on `q=0`

The first-jet system is positive-dimensional.  The lowest unused independent
source coefficient is therefore reflected discriminant coefficient two.  It
supplies the exact quadratic second-jet cusp equation, uniformly including
the minimal `(N,S)=(7,9)` chart.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroDiscriminantNextTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Two coefficients below the product of two separate degree bounds. -/
theorem coeff_mul_two_below_bounds68 (p q:k[X]) (u v:ℕ)
    (hu:2≤u) (hv:2≤v)
    (hp:p.natDegree≤u) (hq:q.natDegree≤v):
    (p*q).coeff (u+v-2)=
      p.coeff (u-2)*q.coeff v+
      p.coeff (u-1)*q.coeff (v-1)+
      p.coeff u*q.coeff (v-2):=by
  have hmem1:u-2∈Finset.range (u+v-2+1):=
    Finset.mem_range.mpr (by omega)
  have hmem2:u-1∈(Finset.range (u+v-2+1)).erase (u-2):=
    Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by omega)⟩
  have hmem3:u∈((Finset.range (u+v-2+1)).erase (u-2)).erase (u-1):=
    Finset.mem_erase.mpr ⟨by omega,
      Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by omega)⟩⟩
  have hzero:∀i∈(((Finset.range (u+v-2+1)).erase (u-2)).erase (u-1)).erase u,
      p.coeff i*q.coeff (u+v-2-i)=0:=by
    intro i hi
    have hi1:=Finset.mem_erase.mp hi
    have hi2:=Finset.mem_erase.mp hi1.2
    have hi3:=Finset.mem_erase.mp hi2.2
    by_cases hgt : u < i
    · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt hgt),zero_mul]
    · have hlt : i < u-2 := by omega
      rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega)),mul_zero]
  have hsum:(p*q).coeff (u+v-2)=
      ∑i∈Finset.range (u+v-2+1),p.coeff i*q.coeff (u+v-2-i):=by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have h1:=Finset.add_sum_erase (Finset.range (u+v-2+1))
    (fun i=>p.coeff i*q.coeff (u+v-2-i)) hmem1
  have h2:=Finset.add_sum_erase ((Finset.range (u+v-2+1)).erase (u-2))
    (fun i=>p.coeff i*q.coeff (u+v-2-i)) hmem2
  have h3:=Finset.add_sum_erase
    (((Finset.range (u+v-2+1)).erase (u-2)).erase (u-1))
    (fun i=>p.coeff i*q.coeff (u+v-2-i)) hmem3
  have h4:∑i∈(((Finset.range (u+v-2+1)).erase (u-2)).erase (u-1)).erase u,
      p.coeff i*q.coeff (u+v-2-i)=0:=Finset.sum_eq_zero hzero
  rw [hsum,←h1,←h2,←h3,h4,add_zero]
  rw [show u+v-2-(u-2)=v by omega,
    show u+v-2-(u-1)=v-1 by omega,
    show u+v-2-u=v-2 by omega]
  ring

/-- Two coefficients below a product of three separate degree bounds. -/
theorem coeff_mul_mul_two_below_bounds68 (p q r:k[X]) (u v w:ℕ)
    (hu:2≤u) (hv:2≤v) (hw:2≤w)
    (hp:p.natDegree≤u) (hq:q.natDegree≤v) (hr:r.natDegree≤w):
    (p*q*r).coeff (u+v+w-2)=
      p.coeff (u-2)*q.coeff v*r.coeff w+
      p.coeff (u-1)*q.coeff (v-1)*r.coeff w+
      p.coeff u*q.coeff (v-2)*r.coeff w+
      p.coeff (u-1)*q.coeff v*r.coeff (w-1)+
      p.coeff u*q.coeff (v-1)*r.coeff (w-1)+
      p.coeff u*q.coeff v*r.coeff (w-2):=by
  have hpq:(p*q).natDegree≤u+v:=by compute_degree;omega
  rw [coeff_mul_two_below_bounds68 (p*q) r (u+v) w (by omega) hw hpq hr,
    coeff_mul_two_below_bounds68 p q u v hu hv hp hq,
    coeff_mul_one_below_bounds68 p q u v (by omega) (by omega) hp hq,
    coeff_mul_at_bounds68 p q u v hp hq]
  ring

/-- The exact second-jet cusp equation from reflected discriminant
coefficient two. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next_two68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    A.coeff (p-2)*B.coeff D^2+
      (2:k)*A.coeff (p-1)*B.coeff D*B.coeff (D-1)+
      A.coeff p*((2:k)*B.coeff D*B.coeff (D-2)+B.coeff (D-1)^2)+
      (3:k)*((2:k)*c.coeff Cc*c.coeff (Cc-2)+c.coeff (Cc-1)^2)=0:=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let U:=8*N-2*G
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  change A.coeff (p-2)*B.coeff D^2+
      (2:k)*A.coeff (p-1)*B.coeff D*B.coeff (D-1)+
      A.coeff p*((2:k)*B.coeff D*B.coeff (D-2)+B.coeff (D-1)^2)+
      (3:k)*((2:k)*c.coeff Cc*c.coeff (Cc-2)+c.coeff (Cc-1)^2)=0
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
  have hp:2≤p:=by dsimp only [p];omega
  have hD:2≤D:=by dsimp only [D];omega
  have hC:2≤Cc:=by dsimp only [Cc];omega
  have hTwo : 2 ≤ min S (7*N-2*G-S) := by omega
  have href:(Delta.reflect U).coeff 2=0:=by
    dsimp only [Delta,U]
    exact hzero 2 hTwo
  have hDelta:Delta.coeff (U-2)=0:=by
    rw [coeff_reflect,revAt_le (by dsimp only [U];omega)] at href
    exact href
  have hABB0:=coeff_mul_mul_two_below_bounds68 A B B p D D
    hp hD hD hA' hB' hB'
  have hABB:(A*B^2).coeff (U-2)=
      A.coeff (p-2)*B.coeff D^2+
      (2:k)*A.coeff (p-1)*B.coeff D*B.coeff (D-1)+
      A.coeff p*((2:k)*B.coeff D*B.coeff (D-2)+B.coeff (D-1)^2):=by
    rw [show p+D+D=U by dsimp only [p,D,U];rw [hGS];omega] at hABB0
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at hABB0 ⊢
    linear_combination hABB0
  have hcc0:=coeff_mul_two_below_bounds68 c c Cc Cc hC hC hc' hc'
  have hcc:(c^2).coeff (U-2)=
      (2:k)*c.coeff Cc*c.coeff (Cc-2)+c.coeff (Cc-1)^2:=by
    rw [show Cc+Cc=U by dsimp only [Cc,U];rw [hGS];omega] at hcc0
    simp only [pow_two,mul_assoc,mul_comm,mul_left_comm] at hcc0 ⊢
    linear_combination hcc0
  dsimp only [Delta,fiveToSixCuspDiscriminantPolynomial68] at hDelta
  simp only [coeff_add,coeff_smul,smul_eq_mul,hABB,hcc] at hDelta
  linear_combination hDelta

#print axioms coeff_mul_two_below_bounds68
#print axioms coeff_mul_mul_two_below_bounds68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next_two68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroDiscriminantNextTwo68

end Max11DegreeRoutes
