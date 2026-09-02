import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetContractionScratch

/-! # Exact endpoint cells of the bounded zeta-first jet recurrence

At `t=S`, the `B*d^2` load is always present and `B^3` is always absent.
Only `G ≤ 2*S` (the `B^3*c` load) and `4*N-G ≤ S` (the gamma pair)
remain as independent endpoint switches.  This file freezes the resulting
four-cell algebraic packet without claiming a contradiction.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointCells68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The depth-zero convolution is the product of the two edge jets. -/
theorem fixedReflectedJetConvolution_zero68
    (p r : k[X]) (u v : ℕ) :
    FixedReflectedJetConvolution68 p u r v 0 =
      p.coeff u * r.coeff v := by
  simp only [FixedReflectedJetConvolution68,Finset.sum_range_succ,
    Finset.sum_range_zero,zero_add,FixedReflectedJet68,
    coeff_reflect,revAt_zero,Nat.zero_sub]

/-- Exact endpoint contractions of all five load products. -/
def FiveToSixCuspZetaFirstEndpointLoadReduction68
    (B c d e : k[X]) (N G S : ℕ) : Prop :=
  let U := 8*N-2*G
  let V := 5*N-G-S
  let idx := U+V-S
  let bU := 3*N-G
  let cU := 4*N-G
  let eU := 6*N-G-S
  ((B^3*c).coeff idx =
      if G ≤ 2*S then
        FixedReflectedJetConvolution68
          (B^3) (3*bU) c cU (2*S-G)
      else 0) ∧
    (B*d^2).coeff idx = B.coeff bU * d.coeff V^2 ∧
    ((c*d).coeff idx =
      if 4*N-G ≤ S then
        FixedReflectedJetConvolution68 c cU d V (S-(4*N-G))
      else 0) ∧
    ((B*e).coeff idx =
      if 4*N-G ≤ S then
        FixedReflectedJetConvolution68 B bU e eU (S-(4*N-G))
      else 0) ∧
    (B^3).coeff idx = 0

/-- The endpoint threshold contraction, including the exact nonzero-edge
`B*d^2` coefficient. -/
theorem fiveToSix_zetaFirst_endpoint_load_reduction68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstEndpointLoadReduction68 B c d e N G S := by
  let R := 7*N-2*G
  let V := 5*N-G-S
  change 0 < S ∧ S < R ∧ d.natDegree ≤ V ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hs
  have hS := hs.1
  have hSR := hs.2.1
  have hd := hs.2.2.1
  have hp := hs.2.2.2.2.1
  change 0 < N ∧ 5*N < 2*G ∧ 2*G ≤ 6*N ∧ _ at hp
  have hn := hp.1
  have hgt := hp.2.1
  have hle := hp.2.2.1
  have hloads := fiveToSix_zetaFirst_fiveLoad_jet_contractions68
    alpha gamma epsilon zeta eta terminal A B c d e N G S S hs (le_refl S)
  change FiveToSixCuspZetaFirstFiveLoadJetContractions68 B c d e N G S S
    at hloads
  dsimp only [FiveToSixCuspZetaFirstFiveLoadJetContractions68] at hloads
  rcases hloads with ⟨hB3c,hBd2,hcd,hBe,hB3⟩
  change FiveToSixCuspZetaFirstEndpointLoadReduction68 B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstEndpointLoadReduction68]
  constructor
  · by_cases hcella : G ≤ 2*S
    · have hload : G-S ≤ S := by omega
      rw [if_pos hload] at hB3c
      rw [if_pos hcella]
      simpa only [show S-(G-S)=2*S-G by omega] using hB3c
    · have hload : ¬ G-S ≤ S := by omega
      rw [if_neg hload] at hB3c
      rw [if_neg hcella]
      exact hB3c
  constructor
  · rw [if_pos (le_refl S)] at hBd2
    simp only [Nat.sub_self] at hBd2
    rw [fixedReflectedJetConvolution_zero68] at hBd2
    have hdtop := coeff_mul_at_bounds68 d d V V hd hd
    have hdtop' : (d^2).coeff (2*V) = d.coeff V^2 := by
      rw [show 2*V=V+V by omega]
      simpa only [pow_two] using hdtop
    rw [hdtop'] at hBd2
    simpa only [V] using hBd2
  constructor
  · exact hcd
  constructor
  · exact hBe
  · have hno : ¬ 4*N-S ≤ S := by omega
    rw [if_neg hno] at hB3
    exact hB3

/-- The two genuine endpoint switches and the permanently absent `B^3`
wall. -/
def FiveToSixCuspZetaFirstEndpointCells68 (N G S : ℕ) : Prop :=
  (2*S < G ∨ G ≤ 2*S) ∧
    (S < 4*N-G ∨ 4*N-G ≤ S) ∧
    S < 4*N-S

theorem fiveToSix_zetaFirst_endpoint_cells68
    (N G S : ℕ) (hgt : 5*N < 2*G) (hle : 2*G ≤ 6*N)
    (hS : 0 < S) (hSR : S < 7*N-2*G) :
    FiveToSixCuspZetaFirstEndpointCells68 N G S := by
  change (2*S<G ∨ G≤2*S) ∧
    (S<4*N-G ∨ 4*N-G≤S) ∧ S<4*N-S
  omega

/-- Endpoint triangular scalar after substituting the exact load cells. -/
def FiveToSixCuspZetaFirstEndpointReducedScalar68
    (gamma : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let bU := 3*N-G
  let cU := 4*N-G
  let eU := 6*N-G-S
  let idx := U+V-S
  let bc := if G ≤ 2*S then
      FixedReflectedJetConvolution68 (B^3) (3*bU) c cU (2*S-G)
    else 0
  let cd := if 4*N-G ≤ S then
      FixedReflectedJetConvolution68 c cU d V (S-(4*N-G))
    else 0
  let be := if 4*N-G ≤ S then
      FixedReflectedJetConvolution68 B bU e eU (S-(4*N-G))
    else 0
  (Delta.reflect U).coeff S * (d.reflect V).coeff 0 =
    -((∑ j ∈ Finset.Ico q S,
        (Delta.reflect U).coeff j * (d.reflect V).coeff (S-j)) +
      (2/3 : k)*bc - (3/2 : k)*B.coeff bU*d.coeff V^2 +
      (9/2*gamma : k)*(cd-be))

theorem fiveToSix_zetaFirst_endpoint_reduced_scalar68
    (gamma : k) (A B c d e : k[X]) (N G S q : ℕ)
    (hqS : q ≤ S)
    (htri : FiveToSixCuspZetaFirstTriangularJetScalar68
      gamma A B c d e N G S q (S-q))
    (hloads : FiveToSixCuspZetaFirstEndpointLoadReduction68
      B c d e N G S) :
    FiveToSixCuspZetaFirstEndpointReducedScalar68
      gamma A B c d e N G S q := by
  have hqm : q+(S-q)=S := by omega
  dsimp only [FiveToSixCuspZetaFirstTriangularJetScalar68] at htri
  rw [hqm] at htri
  dsimp only [FiveToSixCuspZetaFirstFiveLoadExpression68] at htri
  dsimp only [FiveToSixCuspZetaFirstEndpointLoadReduction68] at hloads
  rcases hloads with ⟨hB3c,hBd2,hcd,hBe,hB3⟩
  rw [hB3c,hBd2,hcd,hBe,hB3] at htri
  simp only [mul_zero,add_zero] at htri
  change FiveToSixCuspZetaFirstEndpointReducedScalar68
    gamma A B c d e N G S q
  dsimp only [FiveToSixCuspZetaFirstEndpointReducedScalar68]
  linear_combination htri

/-- The four-cell endpoint algebraic packet. -/
def FiveToSixCuspZetaFirstEndpointCellPacket68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  FiveToSixCuspZetaFirstEndpointCells68 N G S ∧
    FiveToSixCuspZetaFirstEndpointReducedScalar68
      gamma A B c d e N G S q ∧
    FiveToSixCuspZetaFirstUniformJetRowZeroScalar68
      gamma epsilon A B c d e N G S q (S-q) ∧
    FiveToSixCuspZetaFirstUniformJetRowOneScalar68
      gamma epsilon A B c d e N G S q (S-q) ∧
    FiveToSixCuspZetaFirstUniformJetRowTwoScalar68
      gamma epsilon A B c d e N G S q (S-q)

theorem fiveToSix_zetaFirst_endpoint_cell_packet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS : q ≤ S)
    (hrec : FiveToSixCuspZetaFirstUniformJetRecurrence68
      gamma epsilon A B c d e N G S q) :
    FiveToSixCuspZetaFirstEndpointCellPacket68
      gamma epsilon A B c d e N G S q := by
  have hsrc := hs
  change 0 < S ∧ S < 7*N-2*G ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hsrc
  have hp := hsrc.2.2.2.2.1
  change 0 < N ∧ 5*N < 2*G ∧ 2*G ≤ 6*N ∧ _ at hp
  have hend := hrec (S-q) (le_refl _)
  have hloads := fiveToSix_zetaFirst_endpoint_load_reduction68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs
  exact ⟨fiveToSix_zetaFirst_endpoint_cells68 N G S
      hp.2.1 hp.2.2.1 hsrc.1 hsrc.2.1,
    fiveToSix_zetaFirst_endpoint_reduced_scalar68
      gamma A B c d e N G S q hqS hend.1 hloads,
    hend.2.2.1,hend.2.2.2.1,hend.2.2.2.2⟩

/-- Source-facing exact least-q residual with its endpoint cell packet. -/
def FiveToSixCuspZetaFirstEndpointCellsResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  FiveToSixCuspZetaFirstUniformJetContractionResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧
    ∃ q, min S (7*N-2*G-S) < q ∧ q ≤ S ∧
      (∀ j, j < q →
        ((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
          (8*N-2*G)).coeff j = 0) ∧
      (∀ j, min S (7*N-2*G-S) < j → j < q →
        ¬ FiveToSixCuspZetaFirstLoadAt68 N G S j) ∧
      FiveToSixCuspZetaFirstLoadAt68 N G S q ∧
      FiveToSixCuspZetaFirstEndpointCellPacket68
        gamma epsilon A B c d e N G S q

theorem fiveToSix_zetaFirst_endpoint_cells_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hj : FiveToSixCuspZetaFirstUniformJetContractionResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hj,?_⟩
  have hu := hj.1
  rcases hu.2 with ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hfamily⟩
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
  change FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧ _ at hsupport
  have hrec := fiveToSix_zetaFirst_uniform_jet_recurrence68
    alpha gamma epsilon zeta eta terminal A B c d e N G S q
    hsupport.1 hqS hfamily
  exact ⟨q,hmuq,hqS,hprior,hminimal,hload,
    fiveToSix_zetaFirst_endpoint_cell_packet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q
      hsupport.1 hqS hrec⟩

#print axioms fixedReflectedJetConvolution_zero68
#print axioms fiveToSix_zetaFirst_endpoint_load_reduction68
#print axioms fiveToSix_zetaFirst_endpoint_cells68
#print axioms fiveToSix_zetaFirst_endpoint_reduced_scalar68
#print axioms fiveToSix_zetaFirst_endpoint_cell_packet68
#print axioms fiveToSix_zetaFirst_endpoint_cells_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointCells68

end Max11DegreeRoutes
