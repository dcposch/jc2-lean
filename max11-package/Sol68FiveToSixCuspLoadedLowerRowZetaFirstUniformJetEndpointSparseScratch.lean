import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointCellsScratch

/-! # The sparse endpoint chamber of the zeta-first recurrence

If `2*S<G` and `S<4*N-G`, all endpoint thresholds except the literal
`S`-load lie beyond the bounded recurrence.  Hence the least loaded depth
is exactly `q=S`; the endpoint convolution sum is empty and the I3/I4
equation determines the first live discriminant jet.  The other endpoint
cells are retained verbatim as the exact residual.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparse68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The exact collapsed scalar and the three still-independent endpoint
rows in the chamber where only the `S`-load is visible. -/
def FiveToSixCuspZetaFirstSparseEndpointPacket68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  q = S ∧
    let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
    let U := 8*N-2*G
    let V := 5*N-G-S
    (Delta.reflect U).coeff S =
      (3/2 : k) * B.coeff (3*N-G) * d.coeff V ∧
    FiveToSixCuspZetaFirstUniformJetRowZeroScalar68
      gamma epsilon A B c d e N G S S 0 ∧
    FiveToSixCuspZetaFirstUniformJetRowOneScalar68
      gamma epsilon A B c d e N G S S 0 ∧
    FiveToSixCuspZetaFirstUniformJetRowTwoScalar68
      gamma epsilon A B c d e N G S S 0

/-- In the sparse cell, the least-load disjunction forces `q=S`. -/
theorem fiveToSix_zetaFirst_sparse_endpoint_q_eq68
    (N G S q : ℕ) (hqS : q ≤ S)
    (hload : FiveToSixCuspZetaFirstLoadAt68 N G S q)
    (hBc : 2*S < G) (hGamma : S < 4*N-G)
    (hB3 : S < 4*N-S) : q = S := by
  change S ≤ q ∨ G-S ≤ q ∨ 4*N-G ≤ q ∨ 4*N-S ≤ q at hload
  rcases hload with hS | hBc' | hGamma' | hB3' <;> omega

/-- Exact sparse-cell contraction.  Nonvanishing of the cusp `d` edge
cancels the unavoidable endpoint load without division. -/
theorem fiveToSix_zetaFirst_sparse_endpoint_packet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS : q ≤ S)
    (hload : FiveToSixCuspZetaFirstLoadAt68 N G S q)
    (hcell : FiveToSixCuspZetaFirstEndpointCellPacket68
      gamma epsilon A B c d e N G S q)
    (hBc : 2*S < G) (hGamma : S < 4*N-G) :
    FiveToSixCuspZetaFirstSparseEndpointPacket68
      gamma epsilon A B c d e N G S q := by
  have hB3 := hcell.1.2.2
  have hq := fiveToSix_zetaFirst_sparse_endpoint_q_eq68
    N G S q hqS hload hBc hGamma hB3
  have hp := hs
  change _ ∧ _ ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp.2.2.2.2.1 with
    ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hdne := hcusp.2.2.1
  have hscalar := hcell.2.1
  dsimp only [FiveToSixCuspZetaFirstEndpointReducedScalar68] at hscalar
  rw [hq] at hscalar
  simp only [if_neg (by omega : ¬ G ≤ 2*S),
    if_neg (by omega : ¬ 4*N-G ≤ S),Finset.Ico_self,
    Finset.sum_empty,zero_add,mul_zero,sub_zero] at hscalar
  have hdreflect :
      (d.reflect (5*N-G-S)).coeff 0 = d.coeff (5*N-G-S) := by
    simp only [coeff_reflect,revAt_zero,Nat.sub_zero]
  rw [hdreflect] at hscalar
  have hedge :
      ((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
          (8*N-2*G)).coeff S =
        (3/2 : k) * B.coeff (3*N-G) * d.coeff (5*N-G-S) := by
    apply (mul_right_cancel₀ hdne)
    linear_combination hscalar
  change FiveToSixCuspZetaFirstSparseEndpointPacket68
    gamma epsilon A B c d e N G S q
  dsimp only [FiveToSixCuspZetaFirstSparseEndpointPacket68]
  refine ⟨hq,hedge,?_,?_,?_⟩
  · simpa only [hq,Nat.sub_self] using hcell.2.2.1
  · simpa only [hq,Nat.sub_self] using hcell.2.2.2.1
  · simpa only [hq,Nat.sub_self] using hcell.2.2.2.2

/-- Source-facing split: either a non-sparse load cell remains, or the
sparse cell has the exact collapsed discriminant jet and all three endpoint
rows.  The complete endpoint residual is retained in either case. -/
def FiveToSixCuspZetaFirstEndpointSparseSplitResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧
    (G ≤ 2*S ∨ 4*N-G ≤ S ∨
      ∃ q, FiveToSixCuspZetaFirstSparseEndpointPacket68
        gamma epsilon A B c d e N G S q)

theorem fiveToSix_zetaFirst_endpoint_sparse_split_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hj : FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstEndpointSparseSplitResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hj,?_⟩
  rcases hj.2 with ⟨q,hmuq,hqS,hprior,hminimal,hload,hcell⟩
  rcases hcell.1.1 with hBc | hBc
  · rcases hcell.1.2.1 with hGamma | hGamma
    · right
      right
      have hu := hj.1.1
      have hnext2 := hu.1
      have hn2 := hnext2.1
      have hn1 := hn2.1
      have hn0 := hn1.1
      have hn := hn0.1
      have hr2 := hn.1
      change FiveToSixCuspZetaFirstFiniteLoadedRowOneResidual68
          alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr2
      have hr1 := hr2.1
      change FiveToSixCuspZetaFirstFiniteLoadedRowZeroResidual68
          alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr1
      have hr0 := hr1.1
      change FiveToSixCuspZetaFirstFiniteLoadedResidual68
          alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr0
      have hl := hr0.1
      change FiveToSixCuspZetaFirstFiniteStoppingResidual68
          alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hl
      have hf := hl.1
      change FiveToSixCuspZetaFirstDepthFiveResidual68
          alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hf
      have hfour := hf.1
      change FiveToSixCuspZetaFirstDepthFourResidual68
          alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hfour
      have hthree := hfour.1
      change FiveToSixCuspZetaFirstDepthThreeResidual68
          alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hthree
      have hsupport := hthree.1
      change FiveToSixCuspZetaFirstSupportPacket68
          alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hsupport
      exact ⟨q,fiveToSix_zetaFirst_sparse_endpoint_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S q
        hsupport.1 hqS hload hcell hBc hGamma⟩
    · exact Or.inr (Or.inl hGamma)
  · exact Or.inl hBc

#print axioms fiveToSix_zetaFirst_sparse_endpoint_q_eq68
#print axioms fiveToSix_zetaFirst_sparse_endpoint_packet68
#print axioms fiveToSix_zetaFirst_endpoint_sparse_split_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparse68

end Max11DegreeRoutes
