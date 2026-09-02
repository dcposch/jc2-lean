import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3CellSplitScratch

/-! # Outer strict B3 row-zero contraction

When `3*S<2*G`, the B3 endpoint depth `t=2*S-G` lies strictly below the
least discriminant depth `q=G-S`.  Thus the `B*Delta` part of every `Q` jet
in the row-zero tail vanishes, and the tail is exactly the corresponding
tail for `A*B^3`.  The other depth cells are retained without alteration.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3OuterRowZero68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A product with the discriminant has zero reflected jet below the exact
least discriminant depth. -/
theorem fiveToSix_zetaFirst_BDelta_jet_zero_below_q68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q r:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hprior:∀ j,j<q→((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
      (8*N-2*G)).coeff j=0)
    (hrq:r<q):
    FixedReflectedJet68
      (B*fiveToSixCuspDiscriminantPolynomial68 A B c) (11*N-3*G) r=0:=by
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  let U:=8*N-2*G
  let bU:=3*N-G
  have hp:=hs
  change _ ∧ _ ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  have hpacket:=hp.2.2.2.2.1
  change 0<N ∧ 5*N<2*G ∧ 2*G≤6*N ∧ _ at hpacket
  have hB:B.natDegree≤bU:=by exact hpacket.2.2.2.2.1
  have hDelta:Delta.natDegree≤U:=by
    dsimp only [Delta,U,fiveToSixCuspDiscriminantPolynomial68]
    compute_degree
    omega
  have hsum:bU+U=11*N-3*G:=by
    dsimp only [bU,U]
    omega
  change FixedReflectedJet68 (B*Delta) (11*N-3*G) r=0
  rw [←hsum,fixedReflectedJet_mul68 B Delta bU U r hB hDelta]
  dsimp only [FixedReflectedJetConvolution68]
  apply Finset.sum_eq_zero
  intro j hj
  dsimp only [FixedReflectedJet68,Delta,U]
  rw [hprior (r-j) (by omega),mul_zero]

/-- Below `q`, the row-two primitive `Q` is exactly its `A*B^3` part. -/
theorem fiveToSix_zetaFirst_B3_Q_jet_below_q68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q r:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hprior:∀ j,j<q→((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
      (8*N-2*G)).coeff j=0)
    (hqS:q≤S)
    (hrq:r<q):
    let Q:=B*c^2-(1/9:k)•(A*B^3)
    let qU:=11*N-3*G
    FixedReflectedJet68 Q qU r=
      -(4/9:k)*FixedReflectedJet68 (A*B^3) qU r:=by
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let qU:=11*N-3*G
  have hp:=hs
  change _ ∧ _ ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  have hpacket:=hp.2.2.2.2.1
  change 0<N ∧ 5*N<2*G ∧ 2*G≤6*N ∧ _ at hpacket
  have hrU:r≤qU:=by dsimp only [qU];omega
  have hBD:=fiveToSix_zetaFirst_BDelta_jet_zero_below_q68
    alpha gamma epsilon zeta eta terminal A B c d e N G S q r hs hprior hrq
  change FixedReflectedJet68 (B*Delta) qU r=0 at hBD
  have hQpoly:Q=(1/3:k)•(B*Delta)-(4/9:k)•(A*B^3):=by
    dsimp only [Q,Delta,fiveToSixCuspDiscriminantPolynomial68]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [Polynomial.smul_eq_C_mul,map_add,map_sub,map_mul,map_pow,
      RatFunc.algebraMap_C,map_div₀,map_ofNat,map_one]
    ring
  change FixedReflectedJet68 Q qU r=
    -(4/9:k)*FixedReflectedJet68 (A*B^3) qU r
  rw [←coeff_top_sub_eq_fixedReflectedJet68 Q qU r hrU,
    ←coeff_top_sub_eq_fixedReflectedJet68 (A*B^3) qU r hrU,hQpoly,
    coeff_sub,coeff_smul,coeff_smul,smul_eq_mul]
  have hBD':(B*Delta).coeff (qU-r)=0:=by
    rw [coeff_top_sub_eq_fixedReflectedJet68 (B*Delta) qU r hrU]
    exact hBD
  rw [hBD']
  ring

/-- The exact strict-outer row-zero remainder after all lower discriminant
jets are removed. -/
def FiveToSixCuspZetaFirstB3OuterRowZeroTailScalar68
    (A B:k[X]) (N G S:ℕ):Prop:=
  let aU:=2*N-1
  let qU:=11*N-3*G
  let t:=2*S-G
  FixedReflectedJetConvolution68 (derivative A) aU (A*B^3) qU t-
    FixedReflectedJet68 (derivative A) aU 0*
      FixedReflectedJet68 (A*B^3) qU t=0

theorem fiveToSix_zetaFirst_B3_outer_rowZero_tail68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hq:q=G-S)
    (hqS:q≤S)
    (hprior:∀ j,j<q→((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
      (8*N-2*G)).coeff j=0)
    (houter:3*S<2*G)
    (htail:FiveToSixCuspZetaFirstB3EndpointRowZeroTailScalar68
      A B c d e N G S):
    FiveToSixCuspZetaFirstB3OuterRowZeroTailScalar68 A B N G S:=by
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let aU:=2*N-1
  let qU:=11*N-3*G
  let t:=2*S-G
  have htq:t<q:=by dsimp only [t];omega
  have hQ:∀ r,r≤t→FixedReflectedJet68 Q qU r=
      -(4/9:k)*FixedReflectedJet68 (A*B^3) qU r:=by
    intro r hr
    exact fiveToSix_zetaFirst_B3_Q_jet_below_q68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q r hs hprior
      hqS (by omega)
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowZeroTailScalar68] at htail
  change FixedReflectedJetConvolution68 (derivative A) aU Q qU t-
      FixedReflectedJet68 (derivative A) aU 0*
        FixedReflectedJet68 Q qU t=0 at htail
  have hsum:FixedReflectedJetConvolution68 (derivative A) aU Q qU t=
      -(4/9:k)*FixedReflectedJetConvolution68
        (derivative A) aU (A*B^3) qU t:=by
    dsimp only [FixedReflectedJetConvolution68]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [hQ (t-j) (by omega)]
    ring
  rw [hsum,hQ t (le_refl _)] at htail
  change FiveToSixCuspZetaFirstB3OuterRowZeroTailScalar68 A B N G S
  dsimp only [FiveToSixCuspZetaFirstB3OuterRowZeroTailScalar68,aU,qU,t]
  have hn:(-(4/9:k))≠0:=by norm_num
  apply (mul_eq_zero.mp ?_).resolve_left hn
  linear_combination htail

/-- Source-facing strict outer cell.  Equality and the two inner depth
comparisons, as well as the gamma wall, remain explicit. -/
def FiveToSixCuspZetaFirstB3OuterRowZeroPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EndpointCellSplitPacket68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S ∧
    3*S<2*G ∧
    FiveToSixCuspZetaFirstB3OuterRowZeroTailScalar68 A B N G S

theorem fiveToSix_zetaFirst_endpoint_B3_outer_rowZero_split68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    4*N-G≤S ∨
      (FiveToSixCuspZetaFirstB3EndpointCellSplitPacket68 alpha gamma epsilon
        zeta eta terminal A B c d e N G S ∧ 2*G≤3*S) ∨
      FiveToSixCuspZetaFirstB3OuterRowZeroPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_cellSplit_or_gamma_packet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hcell
  · exact Or.inl hGamma
  · by_cases hinner:2*G≤3*S
    · exact Or.inr (Or.inl ⟨hcell,hinner⟩)
    · right
      right
      have houter:3*S<2*G:=by omega
      rcases hcell.2 with ⟨q,hmuq,hqS,hprior,hminimal,hload,hdepth⟩
      have htail:=fiveToSix_zetaFirst_B3_outer_rowZero_tail68
        alpha gamma epsilon zeta eta terminal A B c d e N G S q
        hcell.1.1.1.1 hdepth.1 hqS hprior houter hcell.1.2.2.1
      exact ⟨hcell,houter,htail⟩

#print axioms fiveToSix_zetaFirst_BDelta_jet_zero_below_q68
#print axioms fiveToSix_zetaFirst_B3_Q_jet_below_q68
#print axioms fiveToSix_zetaFirst_B3_outer_rowZero_tail68
#print axioms fiveToSix_zetaFirst_endpoint_B3_outer_rowZero_split68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3OuterRowZero68

end Max11DegreeRoutes
