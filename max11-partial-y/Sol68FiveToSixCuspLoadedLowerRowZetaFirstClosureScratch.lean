import Sol68FiveToSixCuspTerminalSimultaneousNextScratch

/-! # The zeta-first successor after the loaded lower row

The surviving earlier-cusp wall has `mu=R-S<S`, `zeta=0`, and vanishing
reflected discriminant through depth `mu`.  This file first turns that
coefficient packet into its sharp support drop.  The simultaneous sibling
is discharged by its verified equality-wall consumer; the terminal cusp is
handled by the imported terminal finite-stopping closure.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstClosure68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Vanishing of the first `r+1` reflected coefficients is exactly a
strict support drop in the original polynomial. -/
theorem natDegree_le_of_reflect_initial_zero68
    (p : k[X]) (u r : ℕ) (hp : p.natDegree ≤ u) (hr : r < u)
    (hzero : ∀ q, q ≤ r → (p.reflect u).coeff q = 0) :
    p.natDegree ≤ u-r-1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  by_cases hu : u < j
  · exact coeff_eq_zero_of_natDegree_lt (hp.trans_lt hu)
  · have hq : u-j ≤ r := by omega
    have hz := hzero (u-j) hq
    rw [coeff_reflect,revAt_le (by omega),show u-(u-j)=j by omega] at hz
    exact hz

/-- Exact witness-preserving survivor of the loaded lower-row split. -/
def FiveToSixCuspZetaFirstSupportPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  let R:=7*N-2*G
  let mu:=min S (R-S)
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  let U:=8*N-2*G
  0<S ∧ S<R ∧
    d.natDegree≤5*N-G-S ∧ e.natDegree≤6*N-G-S ∧
    FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G S ∧
    R-S<S ∧ mu=R-S ∧ zeta=0 ∧
    (∀ q, q ≤ mu → (Delta.reflect U).coeff q=0) ∧
    Delta.natDegree≤N+S-1

/-- The simultaneous loaded wall is already impossible.  Hence the exact
loaded-lower-row classification leaves only the zeta-first support drop. -/
theorem fiveToSix_cuspLoadedLowerRow_zetaFirst_support68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hp:FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G S)
    (hS:0<S) (hSR:S<7*N-2*G)
    (hd:d.natDegree≤5*N-G-S) (he:e.natDegree≤6*N-G-S)
    (hwall:FiveToSixCuspLoadedLowerRowClassification68 zeta A B c d e N G S):
    FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G S := by
  let R:=7*N-2*G
  let mu:=min S (R-S)
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  let U:=8*N-2*G
  change (∀ q, q < mu → (Delta.reflect U).coeff q=0) ∧ _ at hwall
  rcases hwall with ⟨hbelow,hzfirst | hsim⟩
  · rcases hzfirst with ⟨hless,hmu,hz,hmu0⟩
    have hall : ∀ q, q ≤ mu → (Delta.reflect U).coeff q=0 := by
      intro q hq
      by_cases heq:q=mu
      · simpa only [heq] using hmu0
      · exact hbelow q (by omega)
    rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
    have hDelta:Delta.natDegree≤U:=by
      dsimp only [Delta,U,fiveToSixCuspDiscriminantPolynomial68]
      compute_degree
      omega
    have hsupp:=natDegree_le_of_reflect_initial_zero68 Delta U mu hDelta
      (by dsimp only [U,mu,R] at *;omega) hall
    change FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S
    dsimp only [FiveToSixCuspZetaFirstSupportPacket68]
    refine ⟨hS,hSR,hd,he,
      ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩,hless,hmu,hz,hall,?_⟩
    simpa only [show U-mu-1=N+S-1 by dsimp only [U,mu,R] at *;omega]
      using hsupp
  · exfalso
    exact fiveToSix_cusp_simultaneous_false68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S hp hS hsim.1 hd he

/-- Away from the four genuine next load thresholds, the exact first-
integral combination kills the reflected discriminant coefficient at
`mu+1`.  The vanished zeta term is retained through its source identity. -/
theorem fiveToSix_zetaFirst_next_discriminant_zero68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (htS : min S (7*N-2*G-S)+1 < S)
    (htBc : min S (7*N-2*G-S)+1 < G-S)
    (htGamma : min S (7*N-2*G-S)+1 < 4*N-G)
    (htB3 : min S (7*N-2*G-S)+1 < 4*N-S) :
    ((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
      (8*N-2*G)).coeff (min S (7*N-2*G-S)+1) = 0 := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let t := mu+1
  change 0 < S ∧ S < R ∧ d.natDegree ≤ V ∧ e.natDegree ≤ 6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S < S ∧ mu = R-S ∧ zeta = 0 ∧
      (∀ q, q ≤ mu → (Delta.reflect U).coeff q = 0) ∧ _ at hs
  rcases hs with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  change t<S at htS
  change t<G-S at htBc
  change t<4*N-G at htGamma
  change t<4*N-S at htB3
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases hcusp with ⟨hb,hcn,hds,hes,hcusp0⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hDelta : Delta.natDegree ≤ U := by
    dsimp only [Delta,U,fiveToSixCuspDiscriminantPolynomial68]
    compute_degree
    omega
  have htB2 : t < 7*N-G-S := by dsimp only [t,mu,R] at *;omega
  have hBzero : B.coeff (U+V-t) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  have hczero : c.coeff (U+V-t) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  have hB3c : (B^3*c).coeff (U+V-t) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hB2 : (B^2).coeff (U+V-t) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hcd : (c*d).coeff (U+V-t) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hBe : (B*e).coeff (U+V-t) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hB3 : (B^3).coeff (U+V-t) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hBd2 : (B*d^2).coeff (U+V-t) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hid := fiveToSix_firstIntegrals_cuspCombination68 gamma epsilon zeta
    A B c d e
  have hcoef := congrArg (fun p : k[X] => p.coeff (U+V-t)) hid
  rw [hi3,hi4,hz] at hcoef
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,coeff_mul_C,
    hBzero,hczero,hB3c,hB2,hcd,hBe,hB3,hBd2,zero_mul,mul_zero,
    zero_smul,add_zero,sub_zero] at hcoef
  have hprod : (Delta*d).coeff (U+V-t) = 0 := by
    change 0 = (Delta*d).coeff (U+V-t) at hcoef
    exact hcoef.symm
  have href := coeff_mul_at_reflect_of_left_lower_zero68 Delta d U V t hDelta
    hd (by dsimp only [t,mu,R,U,V] at *;omega)
    (by
      intro j hj
      exact hzero j (by dsimp only [t] at hj;omega))
  rw [href] at hprod
  have hdsR : (d.reflect V).coeff 0 ≠ 0 := by
    simpa only [coeff_reflect,revAt_zero,V] using hds
  have hznext : (Delta.reflect U).coeff t = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hdsR
  simpa only [Delta,U,t,mu,R] using hznext

/-- Smallest honest successor after consuming `mu+1`: either that index is
one of the four literal load walls, or the discriminant support drops by
one more degree. -/
def FiveToSixCuspZetaFirstNextResidual68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  let R:=7*N-2*G
  let mu:=min S (R-S)
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  let U:=8*N-2*G
  let t:=mu+1
  FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G S ∧
    (S≤t ∨ G-S≤t ∨ 4*N-G≤t ∨ 4*N-S≤t ∨
      ((Delta.reflect U).coeff t=0 ∧ Delta.natDegree≤N+S-2))

theorem fiveToSix_zetaFirst_next_residual68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstNextResidual68 alpha gamma epsilon zeta eta terminal
      A B c d e N G S := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let t := mu+1
  refine ⟨hs, ?_⟩
  by_cases hS : t < S
  · by_cases hBc : t < G-S
    · by_cases hGamma : t < 4*N-G
      · by_cases hB3 : t < 4*N-S
        · right;right;right;right
          have hnext := fiveToSix_zetaFirst_next_discriminant_zero68 alpha gamma
            epsilon zeta eta terminal A B c d e N G S hs
            (by simpa only [t,mu,R] using hS)
            (by simpa only [t,mu,R] using hBc)
            (by simpa only [t,mu,R] using hGamma)
            (by simpa only [t,mu,R] using hB3)
          have h0 := hs
          change 0 < S ∧ S < R ∧ _ ∧ _ ∧
            FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta
              terminal A B c d e N G S ∧ _ ∧ mu = R-S ∧ _ ∧
            (∀ q, q ≤ mu → (Delta.reflect U).coeff q = 0) ∧ _ at h0
          rcases h0 with ⟨hSp,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
          have hall : ∀ q, q ≤ t → (Delta.reflect U).coeff q = 0 := by
            intro q hq
            by_cases heq:q=t
            · simpa only [heq,t,mu,R,Delta,U] using hnext
            · exact hzero q (by dsimp only [t] at hq;omega)
          rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
          have hDelta : Delta.natDegree ≤ U := by
            dsimp only [Delta,U,fiveToSixCuspDiscriminantPolynomial68]
            compute_degree
            omega
          have hdrop := natDegree_le_of_reflect_initial_zero68 Delta U t hDelta
            (by dsimp only [U,t,mu,R] at *;omega) hall
          refine ⟨?_,?_⟩
          · simpa only [t,mu,R,Delta,U] using hnext
          · simpa only [show U-t-1=N+S-2 by
                dsimp only [U,t,mu,R] at *;omega] using hdrop
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)

#print axioms natDegree_le_of_reflect_initial_zero68
#print axioms fiveToSix_cuspLoadedLowerRow_zetaFirst_support68
#print axioms fiveToSix_zetaFirst_next_discriminant_zero68
#print axioms fiveToSix_zetaFirst_next_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstClosure68

end Max11DegreeRoutes
