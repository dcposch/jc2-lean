import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3RowOneScratch

/-! # The B3-loaded endpoint row-zero contraction

Row zero retains one additional `A' * B * c^2` jet in the B3 cell.  After
the individual I4 support drop, its exact content is a convolution of
`A'` with the row-two primitive.  The top convolution term cancels against
the verified row-two jet, leaving a genuine lower-depth tail when
`G < 2*S`; at `G=2*S` row zero is exactly dependent.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3RowZero68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Literal row-zero terms surviving in the B3-loaded, gamma-inactive
endpoint cell. -/
def FiveToSixCuspZetaFirstB3EndpointRowZeroCore68
    (A B c d e:k[X]):k[X]:=
  A*derivative A*B*e+A*derivative A*c*d-
    derivative A*B*c^2+(3:k)•(derivative A*d*e)

def FiveToSixCuspZetaFirstB3EndpointRowZeroScalar68
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  let K:=13*N-2*G-2*S-1
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e).coeff K=0

/-- Exact literal source reduction of row zero. -/
theorem fiveToSix_zetaFirst_B3_endpoint_rowZero68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:G≤2*S) (hGamma:S<4*N-G) (hqS:q≤S)
    (hrow:FiveToSixCuspZetaFirstUniformJetRowZeroScalar68
      gamma epsilon A B c d e N G S q (S-q)):
    FiveToSixCuspZetaFirstB3EndpointRowZeroScalar68 A B c d e N G S:=by
  let K:=13*N-2*G-2*S-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hlowABd:(A*B^2*derivative d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowABBd:(A*B*derivative B*d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBce:(B*c*derivative e).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBdd:(B*d*derivative d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBd2:(derivative B*d^2).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowccd:(c*derivative c*d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBAc:(B*derivative A*c).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBe:(B*derivative e).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowABA:(A*B*derivative A).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowAAd:(A*derivative A*d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowdc:(d*derivative c).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowdA:(d*derivative A).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hSW:S≤13*N-2*G-S-1:=by omega
  have hqm:q+(S-q)=S:=by omega
  dsimp only [FiveToSixCuspZetaFirstUniformJetRowZeroScalar68,
    FixedReflectedJet68] at hrow
  rw [hqm] at hrow
  simp only [coeff_reflect,revAt_le hSW] at hrow
  rw [show 13*N-2*G-S-1-S=K by dsimp only [K];omega] at hrow
  simp only [secondaryResidualRowZeroPolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlowABd,
    coeff_eq_zero_of_natDegree_lt hlowABBd,
    coeff_eq_zero_of_natDegree_lt hlowBce,
    coeff_eq_zero_of_natDegree_lt hlowBdd,
    coeff_eq_zero_of_natDegree_lt hlowBd2,
    coeff_eq_zero_of_natDegree_lt hlowccd,
    coeff_eq_zero_of_natDegree_lt hlowBAc,
    coeff_eq_zero_of_natDegree_lt hlowBe,
    coeff_eq_zero_of_natDegree_lt hlowABA,
    coeff_eq_zero_of_natDegree_lt hlowAAd,
    coeff_eq_zero_of_natDegree_lt hlowdc,
    coeff_eq_zero_of_natDegree_lt hlowdA,
    mul_zero,add_zero,sub_zero] at hrow
  change FiveToSixCuspZetaFirstB3EndpointRowZeroScalar68 A B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowZeroScalar68,
    FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,K]
  simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
  linear_combination (-27/4:k)*hrow

/-- Row zero is the I4 remainder block plus `A'` times the row-two
primitive defect. -/
theorem fiveToSix_zetaFirst_B3_endpoint_rowZero_core_factor68
    (A B c d e:k[X]):
    let H:=B*e+c*d
    let F:=H-(1/9:k)•B^3
    let Q:=B*c^2-(1/9:k)•(A*B^3)
    FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e=
      A*derivative A*F+derivative A*(-Q+(3:k)•(d*e)):=by
  dsimp only
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,
    Polynomial.smul_eq_C_mul,map_add,map_sub,map_mul,map_pow,map_neg,map_zero,
    RatFunc.algebraMap_C,map_div₀,map_ofNat,map_one]
  ring

/-- Common-bound row-zero convolution before its top row-two term is
removed. -/
def FiveToSixCuspZetaFirstB3EndpointRowZeroConvolutionScalar68
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  let aU:=2*N-1
  let qU:=11*N-3*G
  let t:=2*S-G
  let V:=5*N-G-S
  let E:=6*N-G-S
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  FixedReflectedJetConvolution68 (derivative A) aU Q qU t=
    3*((2*N:ℕ):k)*A.coeff (2*N)*d.coeff V*e.coeff E

theorem fiveToSix_zetaFirst_B3_endpoint_rowZero_convolution68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:G≤2*S) (hGamma:S<4*N-G)
    (hi4:FiveToSixCuspZetaFirstEndpointB3I4Packet68
      gamma B c d e N G S)
    (hrow:FiveToSixCuspZetaFirstB3EndpointRowZeroScalar68
      A B c d e N G S):
    FiveToSixCuspZetaFirstB3EndpointRowZeroConvolutionScalar68
      A B c d e N G S:=by
  let H:=B*e+c*d
  let F:=H-(1/9:k)•B^3
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let aU:=2*N-1
  let qU:=11*N-3*G
  let t:=2*S-G
  let V:=5*N-G-S
  let E:=6*N-G-S
  let K:=13*N-2*G-2*S-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤V ∧ e.natDegree≤E ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  dsimp only [FiveToSixCuspZetaFirstEndpointB3I4Packet68] at hi4
  have hF:F.natDegree≤9*N-2*G-2*S-1:=by
    dsimp only [F,H]
    have hh:=hi4.1
    omega
  have hdA0:=natDegree_derivative_le A
  have hdA:(derivative A).natDegree≤aU:=by dsimp only [aU];omega
  have hAFF:(A*derivative A*F).natDegree<K:=by
    dsimp only [K] at hF ⊢
    compute_degree
    omega
  have hFzero:(A*derivative A*F).coeff K=0:=
    coeff_eq_zero_of_natDegree_lt hAFF
  have hcore:(FiveToSixCuspZetaFirstB3EndpointRowZeroCore68
      A B c d e).coeff K=0:=by
    exact hrow
  rw [fiveToSix_zetaFirst_B3_endpoint_rowZero_core_factor68
      (k:=k) A B c d e] at hcore
  change (A*derivative A*F+derivative A*(-Q+(3:k)•(d*e))).coeff K=0
    at hcore
  have hQ:Q.natDegree≤qU:=by
    dsimp only [Q,qU]
    compute_degree
    omega
  have htq:t≤qU:=by dsimp only [t,qU];omega
  have hWa:(aU+qU)-t=K:=by dsimp only [aU,qU,t,K];omega
  have hprod:(derivative A*Q).coeff K=
      FixedReflectedJetConvolution68 (derivative A) aU Q qU t:=by
    rw [←hWa,coeff_top_sub_eq_fixedReflectedJet68 _ _ _ (by omega),
      fixedReflectedJet_mul68 (derivative A) Q aU qU t hdA hQ]
  have hAde:=coeff_mul_mul_derivative_at_bounds68 d e A V E (2*N)
    (by omega) hd he hA
  rw [show V+E+2*N-1=K by dsimp only [V,E,K];omega] at hAde
  have hAde':(derivative A*(d*e)).coeff K=
      ((2*N:ℕ):k)*A.coeff (2*N)*d.coeff V*e.coeff E:=by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hAde
  rw [mul_add,mul_neg,mul_smul_comm] at hcore
  simp only [coeff_add,coeff_neg,coeff_smul,smul_eq_mul,hFzero,zero_add,
    hprod,hAde'] at hcore
  change FiveToSixCuspZetaFirstB3EndpointRowZeroConvolutionScalar68
    A B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowZeroConvolutionScalar68,
    Q,aU,qU,t,V,E]
  linear_combination -hcore

/-- The genuinely new part of row zero after cancelling its top row-two
jet.  It is identically empty exactly when `t=0`. -/
def FiveToSixCuspZetaFirstB3EndpointRowZeroTailScalar68
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  let aU:=2*N-1
  let qU:=11*N-3*G
  let t:=2*S-G
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  FixedReflectedJetConvolution68 (derivative A) aU Q qU t-
    FixedReflectedJet68 (derivative A) aU 0*
      FixedReflectedJet68 Q qU t=0

theorem fiveToSix_zetaFirst_B3_endpoint_rowZero_tail68
    (A B c d e:k[X]) (N G S:ℕ)
    (hN:0<N) (hBc:G≤2*S)
    (hrow0:FiveToSixCuspZetaFirstB3EndpointRowZeroConvolutionScalar68
      A B c d e N G S)
    (hrow2:FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68
      A B c d e N G S):
    FiveToSixCuspZetaFirstB3EndpointRowZeroTailScalar68
      A B c d e N G S:=by
  let aU:=2*N-1
  let qU:=11*N-3*G
  let t:=2*S-G
  let V:=5*N-G-S
  let E:=6*N-G-S
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowZeroConvolutionScalar68]
    at hrow0
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68]
    at hrow2
  have hAtop:FixedReflectedJet68 (derivative A) aU 0=
      ((2*N:ℕ):k)*A.coeff (2*N):=by
    dsimp only [FixedReflectedJet68,aU]
    rw [coeff_reflect,revAt_zero,coeff_derivative]
    have hi:2*N-1+1=2*N:=by omega
    have hik:(((2*N-1:ℕ):k)+1)=((2*N:ℕ):k):=by
      have hh:=congrArg (fun n:ℕ↦(n:k)) hi
      simpa only [Nat.cast_add,Nat.cast_one] using hh
    rw [hi]
    rw [hik]
    push_cast
    ring
  change FiveToSixCuspZetaFirstB3EndpointRowZeroTailScalar68
    A B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowZeroTailScalar68,
    Q,aU,qU,t]
  rw [hAtop]
  linear_combination hrow0-
    ((2*N:ℕ):k)*A.coeff (2*N)*hrow2

/-- Complete B3 row-zero packet and the exact equality/strict-depth cell
split. -/
def FiveToSixCuspZetaFirstB3EndpointRowZeroPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EndpointRowOnePacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧
    FiveToSixCuspZetaFirstB3EndpointRowZeroConvolutionScalar68
      A B c d e N G S ∧
    FiveToSixCuspZetaFirstB3EndpointRowZeroTailScalar68
      A B c d e N G S ∧
    (G=2*S ∨ (G<2*S ∧ 0<2*S-G))

/-- Source-facing endpoint split after row zero. -/
theorem fiveToSix_zetaFirst_endpoint_B3_rowZero_or_gamma_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    4*N-G≤S ∨ FiveToSixCuspZetaFirstB3EndpointRowZeroPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_rowOne_or_gamma_packet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hb3
  · exact Or.inl hGamma
  · right
    rcases hb3 with ⟨hbase,hrow1⟩
    rcases hbase with ⟨hs,hBc,hGamma,q,hmuq,hqS,hprior,hminimal,hload,
      hi3,hi4,hrow2⟩
    rcases hj.2 with ⟨q',hmuq',hqS',hprior',hminimal',hload',hcell⟩
    have hrow:=fiveToSix_zetaFirst_B3_endpoint_rowZero68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q' hs hBc
      hGamma hqS' hcell.2.2.1
    have hconv:=fiveToSix_zetaFirst_B3_endpoint_rowZero_convolution68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hBc
      hGamma hi4 hrow
    have hN:=hs.2.2.2.2.1.1
    have htail:=fiveToSix_zetaFirst_B3_endpoint_rowZero_tail68
      A B c d e N G S hN hBc hconv hrow2
    refine ⟨⟨⟨hs,hBc,hGamma,q,hmuq,hqS,hprior,hminimal,hload,
      hi3,hi4,hrow2⟩,hrow1⟩,hconv,htail,?_⟩
    omega

#print axioms fiveToSix_zetaFirst_B3_endpoint_rowZero68
#print axioms fiveToSix_zetaFirst_B3_endpoint_rowZero_core_factor68
#print axioms fiveToSix_zetaFirst_B3_endpoint_rowZero_convolution68
#print axioms fiveToSix_zetaFirst_B3_endpoint_rowZero_tail68
#print axioms fiveToSix_zetaFirst_endpoint_B3_rowZero_or_gamma_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3RowZero68

end Max11DegreeRoutes
