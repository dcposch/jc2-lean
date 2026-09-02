import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3RowZeroScratch

/-! # Exact depth cells after the B3-loaded endpoint row zero

In the gamma-inactive B3 chamber, the least loaded depth is not an
arbitrary witness: it is exactly the `B^3*c` threshold `q=G-S`.  Hence the
remaining row-zero convolution has depth `t=S-q=2*S-G`.  This file records
the equality cell, where the tail is empty, and the three honest strict
depth comparisons.  No algebraic closure is claimed for those cells.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3CellSplit68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- In the B3-loaded, gamma-inactive endpoint cell, minimality forces the
least loaded coefficient to be the exact `G-S` threshold. -/
theorem fiveToSix_zetaFirst_B3_least_q_eq68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:G≤2*S) (hGamma:S<4*N-G)
    (hmuq:min S (7*N-2*G-S)<q) (hqS:q≤S)
    (hminimal:∀ j,min S (7*N-2*G-S)<j→j<q→
      ¬FiveToSixCuspZetaFirstLoadAt68 N G S j)
    (hload:FiveToSixCuspZetaFirstLoadAt68 N G S q):
    q=G-S:=by
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hthreshold:min S (7*N-2*G-S)<G-S:=by omega
  have hqle:q≤G-S:=by
    by_contra hn
    exact hminimal (G-S) hthreshold (by omega)
      (Or.inr (Or.inl (le_refl _)))
  have hB3:S<4*N-S:=by
    exact (fiveToSix_zetaFirst_endpoint_cells68 N G S hgt hle hS hSR).2.2
  change S≤q ∨ G-S≤q ∨ 4*N-G≤q ∨ 4*N-S≤q at hload
  rcases hload with hSq|hGq|hGammaq|hB3q
  · omega
  · omega
  · omega
  · omega

/-- Exact arithmetic cells for the endpoint depth `t=2*S-G`. -/
def FiveToSixCuspZetaFirstB3EndpointDepthCells68
    (N G S q:ℕ):Prop:=
  q=G-S ∧ q+(2*S-G)=S ∧
    ((G=2*S ∧ q=S ∧ 2*S-G=0) ∨
      (G<2*S ∧ 0<2*S-G ∧
        ((3*S<2*G ∧ 2*S-G<q) ∨
          (3*S=2*G ∧ 2*S-G=q) ∨
          (2*G<3*S ∧ q<2*S-G))))

theorem fiveToSix_zetaFirst_B3_endpoint_depth_cells68
    (N G S q:ℕ) (hGS:0<G-S) (hBc:G≤2*S) (hq:q=G-S):
    FiveToSixCuspZetaFirstB3EndpointDepthCells68 N G S q:=by
  change q=G-S ∧ q+(2*S-G)=S ∧ _
  refine ⟨hq,by omega,?_⟩
  by_cases heq:G=2*S
  · left
    omega
  · right
    refine ⟨by omega,by omega,?_⟩
    omega

/-- Source-facing row-zero handoff with the exact least-load and depth-cell
classification attached. -/
def FiveToSixCuspZetaFirstB3EndpointCellSplitPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EndpointRowZeroPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧
    ∃ q, min S (7*N-2*G-S)<q ∧ q≤S ∧
      (∀ j,j<q→((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
        (8*N-2*G)).coeff j=0) ∧
      (∀ j,min S (7*N-2*G-S)<j→j<q→
        ¬FiveToSixCuspZetaFirstLoadAt68 N G S j) ∧
      FiveToSixCuspZetaFirstLoadAt68 N G S q ∧
      FiveToSixCuspZetaFirstB3EndpointDepthCells68 N G S q

theorem fiveToSix_zetaFirst_endpoint_B3_cellSplit_or_gamma_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    4*N-G≤S ∨ FiveToSixCuspZetaFirstB3EndpointCellSplitPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_rowZero_or_gamma_packet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hrow
  · exact Or.inl hGamma
  · right
    have hb3:=hrow.1.1
    rcases hb3 with ⟨hs,hBc,hGamma,q,hmuq,hqS,hprior,hminimal,hload,
      hi3,hi4,hrow2⟩
    have hq:=fiveToSix_zetaFirst_B3_least_q_eq68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q hs hBc
      hGamma hmuq hqS hminimal hload
    have hqpos:0<G-S:=by
      have hp:=hs
      change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hp
      omega
    exact ⟨hrow,⟨q,hmuq,hqS,hprior,hminimal,hload,
      fiveToSix_zetaFirst_B3_endpoint_depth_cells68 N G S q hqpos hBc hq⟩⟩

#print axioms fiveToSix_zetaFirst_B3_least_q_eq68
#print axioms fiveToSix_zetaFirst_B3_endpoint_depth_cells68
#print axioms fiveToSix_zetaFirst_endpoint_B3_cellSplit_or_gamma_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3CellSplit68

end Max11DegreeRoutes
