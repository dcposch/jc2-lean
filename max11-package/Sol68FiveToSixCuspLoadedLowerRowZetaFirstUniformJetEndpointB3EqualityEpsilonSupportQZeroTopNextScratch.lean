import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroTopResultantScratch

/-! # The first coefficient below the top compensated-I4 product on `q=0`

The compensated `I4` polynomial is constant on the exact `q=0` wall.  One
coefficient below its genuine top product therefore gives the four-term
first-jet relation among `B,e,c,d`.  This identity is uniform: the terms of
lower secondary degree are already too short even in the exceptional
`(N,S)=(7,9)` chart.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroTopNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- One coefficient below the sum of two positive separate degree bounds. -/
theorem coeff_mul_one_below_bounds68 (p q : k[X]) (u v : ℕ)
    (hu : 0 < u) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (p * q).coeff (u + v - 1) =
      p.coeff (u - 1) * q.coeff v + p.coeff u * q.coeff (v - 1) := by
  have hmem1 : u - 1 ∈ Finset.range (u + v - 1 + 1) :=
    Finset.mem_range.mpr (by omega)
  have hmem2 : u ∈ (Finset.range (u + v - 1 + 1)).erase (u - 1) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have hzero : ∀ i ∈
      ((Finset.range (u + v - 1 + 1)).erase (u - 1)).erase u,
      p.coeff i * q.coeff (u + v - 1 - i) = 0 := by
    intro i hi
    have hi1 := Finset.mem_erase.mp hi
    have hi2 := Finset.mem_erase.mp hi1.2
    by_cases hgt : u < i
    · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt hgt), zero_mul]
    · have hlt : i < u - 1 := by omega
      rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega)), mul_zero]
  have hsum : (p * q).coeff (u + v - 1) =
      ∑ i ∈ Finset.range (u + v - 1 + 1),
        p.coeff i * q.coeff (u + v - 1 - i) := by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have h1 := Finset.add_sum_erase (Finset.range (u + v - 1 + 1))
    (fun i => p.coeff i * q.coeff (u + v - 1 - i)) hmem1
  have h2 := Finset.add_sum_erase
    ((Finset.range (u + v - 1 + 1)).erase (u - 1))
    (fun i => p.coeff i * q.coeff (u + v - 1 - i)) hmem2
  have h3 : ∑ i ∈ ((Finset.range (u + v - 1 + 1)).erase (u - 1)).erase u,
      p.coeff i * q.coeff (u + v - 1 - i) = 0 :=
    Finset.sum_eq_zero hzero
  rw [hsum, ← h1, ← h2, h3, add_zero]
  rw [show u + v - 1 - (u - 1) = v by omega,
    show u + v - 1 - u = v - 1 by omega]

/-- The first-jet product relation forced by the constant compensated `I4`
identity on the exact `q=0` wall. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_top_next68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    B.coeff (D-1)*e.coeff E+B.coeff D*e.coeff (E-1)+
      c.coeff (Cc-1)*d.coeff V+c.coeff Cc*d.coeff (V-1)=0:=by
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
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hc':c.natDegree≤Cc:=by simpa [Cc,hGS] using hc
  have hd':d.natDegree≤V:=by dsimp only [V];rw [hGS] at hd;omega
  have he':e.natDegree≤E:=by dsimp only [E];rw [hGS] at he;omega
  have hEq:9*N=7*S:=hnxt.1.1
  have hD:0<D:=by dsimp only [D];omega
  have hC:0<Cc:=by dsimp only [Cc];omega
  have hV:0<V:=by dsimp only [V];omega
  have hE:0<E:=by dsimp only [E];omega
  have hK1:0<K-1:=by dsimp only [D,E,K];omega
  have hB3deg:(B^3).natDegree≤3*D:=by compute_degree;omega
  have hB3low:(B^3).natDegree<K-1:=by dsimp only [D,E,K] at *;omega
  have hdLow:d.natDegree<K-1:=by dsimp only [D,E,K,V] at *;omega
  have hBLow:B.natDegree<K-1:=by dsimp only [D,E,K] at *;omega
  have hBe0:=coeff_mul_one_below_bounds68 B e D E hD hE hB' he'
  have hBe:(B*e).coeff (K-1)=
      B.coeff (D-1)*e.coeff E+B.coeff D*e.coeff (E-1):=by
    simpa only [K] using hBe0
  have hcd0:=coeff_mul_one_below_bounds68 c d Cc V hC hV hc' hd'
  have hcd:(c*d).coeff (K-1)=
      c.coeff (Cc-1)*d.coeff V+c.coeff Cc*d.coeff (V-1):=by
    rw [show Cc+V=K by dsimp only [D,Cc,V,E,K];omega] at hcd0
    exact hcd0
  have hFK:Fce.coeff (K-1)=0:=by
    dsimp only [Fce]
    rw [hFce,coeff_smul,coeff_C]
    split_ifs with h
    · omega
    · simp only [smul_zero]
  dsimp only [Fce] at hFK
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,hBe,hcd,
    coeff_eq_zero_of_natDegree_lt hB3low,
    coeff_eq_zero_of_natDegree_lt hdLow,
    coeff_eq_zero_of_natDegree_lt hBLow,mul_zero,sub_zero,add_zero]
    at hFK
  simpa only [add_assoc] using hFK

#print axioms coeff_mul_one_below_bounds68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_top_next68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroTopNext68

end Max11DegreeRoutes
