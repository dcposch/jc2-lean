import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseI4ClosureScratch

/-! # The B3-loaded, gamma-inactive endpoint I4 adapter

After closing the sparse cell, every endpoint lies on `G≤2*S` or on the
gamma wall `4*N-G≤S`.  In the former, gamma-inactive subcell the individual
I4 polynomial identifies the depth-`S` jet of `H=B*e+c*d` with the shifted
depth `2*S-G` jet of `B^3`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3I4Adapter68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Recover the exact retained source/support witness from the endpoint
residual. -/
theorem fiveToSix_zetaFirst_support_of_endpoint_cells_residual68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S:=by
  have hu:=hj.1.1
  have hnext2:=hu.1
  have hn2:=hnext2.1
  have hn1:=hn2.1
  have hn0:=hn1.1
  have hn:=hn0.1
  have hr2:=hn.1
  change FiveToSixCuspZetaFirstFiniteLoadedRowOneResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr2
  have hr1:=hr2.1
  change FiveToSixCuspZetaFirstFiniteLoadedRowZeroResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr1
  have hr0:=hr1.1
  change FiveToSixCuspZetaFirstFiniteLoadedResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr0
  have hl:=hr0.1
  change FiveToSixCuspZetaFirstFiniteStoppingResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hl
  have hf:=hl.1
  change FiveToSixCuspZetaFirstDepthFiveResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hf
  have hfour:=hf.1
  change FiveToSixCuspZetaFirstDepthFourResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hfour
  have hthree:=hfour.1
  change FiveToSixCuspZetaFirstDepthThreeResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hthree
  have hsupport:=hthree.1
  change FiveToSixCuspZetaFirstSupportPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hsupport
  exact hsupport.1

/-- The verified sparse closure turns the four endpoint cells into the
exact two-branch inventory. -/
theorem fiveToSix_zetaFirst_endpoint_inventory68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    G≤2*S ∨ 4*N-G≤S:=by
  rcases hj.2 with ⟨q,hmuq,hqS,hprior,hminimal,hload,hcell⟩
  rcases hcell.1.1 with hBc | hBc
  · rcases hcell.1.2.1 with hGamma | hGamma
    · have hs:=fiveToSix_zetaFirst_support_of_endpoint_cells_residual68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hj
      have hsp:=fiveToSix_zetaFirst_sparse_endpoint_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S q hs hqS
        hload hcell hBc hGamma
      have hr2:=fiveToSix_zetaFirst_sparse_endpoint_rowTwo_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S q hs hBc
        hGamma hsp
      have hrc:=fiveToSix_zetaFirst_sparse_endpoint_rowTwo_contraction_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S q hs hBc
        hGamma hr2
      have hr1:=fiveToSix_zetaFirst_sparse_endpoint_rowOne_rowTwo_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S q hrc
      have hr0:=fiveToSix_zetaFirst_sparse_endpoint_rowZero_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S q hr1
      exact False.elim (fiveToSix_zetaFirst_sparse_endpoint_false68
        alpha gamma epsilon zeta eta terminal A B c d e N G S q hr0)
    · exact Or.inr hGamma
  · exact Or.inl hBc

/-- I4 remainder after removing its only endpoint-visible `B^3` term. -/
def FiveToSixCuspZetaFirstEndpointB3I4Packet68
    (gamma:k) (B c d e:k[X]) (N G S:ℕ):Prop:=
  let H:=B*e+c*d
  let P:=9*N-2*G-S
  let b3U:=9*N-3*G
  let t:=2*S-G
  (H-(1/9:k)•B^3).natDegree≤P-S-1 ∧
    FixedReflectedJet68 H P S=
      (1/9:k)*FixedReflectedJet68 (B^3) b3U t

theorem fiveToSix_zetaFirst_endpoint_B3_I4_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:G≤2*S) (hGamma:S<4*N-G):
    FiveToSixCuspZetaFirstEndpointB3I4Packet68 gamma B c d e N G S:=by
  let H:=B*e+c*d
  let P:=9*N-2*G-S
  let b3U:=9*N-3*G
  let t:=2*S-G
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases fiveToSix_zetaFirst_sparse_compensatedI4_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
    ⟨i4,hpoly⟩
  have hrem:H-(1/9:k)•B^3=
      -(3/4*epsilon:k)•B+(3/8:k)•C i4-(3/2*gamma:k)•d:=by
    dsimp only [H]
    simp only [neg_smul]
    linear_combination hpoly
  have hdeg:(H-(1/9:k)•B^3).natDegree≤P-S-1:=by
    rw [hrem]
    dsimp only [P]
    compute_degree
    omega
  have hidx:0<P-S:=by dsimp only [P];omega
  have hz:(H-(1/9:k)•B^3).coeff (P-S)=0:=by
    apply coeff_eq_zero_of_natDegree_lt
    exact hdeg.trans_lt (by omega)
  simp only [coeff_sub,coeff_smul,smul_eq_mul] at hz
  have hSP:S≤P:=by dsimp only [P];omega
  have htb:t≤b3U:=by dsimp only [t,b3U];omega
  have hi:P-S=b3U-t:=by dsimp only [P,b3U,t];omega
  change FiveToSixCuspZetaFirstEndpointB3I4Packet68 gamma B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstEndpointB3I4Packet68,H,P,b3U,t]
  refine ⟨hdeg,?_⟩
  dsimp only [FixedReflectedJet68]
  rw [coeff_reflect,revAt_le hSP,coeff_reflect,revAt_le htb,←hi]
  linear_combination hz

#print axioms fiveToSix_zetaFirst_support_of_endpoint_cells_residual68
#print axioms fiveToSix_zetaFirst_endpoint_inventory68
#print axioms fiveToSix_zetaFirst_endpoint_B3_I4_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3I4Adapter68

end Max11DegreeRoutes
