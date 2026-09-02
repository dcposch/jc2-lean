import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3I4AdapterScratch

/-! # The full B3-loaded endpoint row-two contraction

In the cell `G ≤ 2*S` and `S < 4*N-G`, the endpoint first-integral row
retains the shifted `B^3*c` convolution.  The individual I4 identity also
replaces the endpoint jet of `H=B*e+c*d` by the shifted `B^3` jet.  The
literal row-two equation then contracts, without division by an edge, to
one reflected scalar involving `B*c^2-(1/9)A*B^3`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3RowTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The exact endpoint I3/I4 scalar after retaining the `B^3*c` load and
removing both gamma loads. -/
def FiveToSixCuspZetaFirstB3EndpointI3Scalar68
    (A B c d : k[X]) (N G S q : ℕ) : Prop :=
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let bU := 3*N-G
  let cU := 4*N-G
  (Delta.reflect U).coeff S * (d.reflect V).coeff 0 =
    -((∑ j ∈ Finset.Ico q S,
        (Delta.reflect U).coeff j * (d.reflect V).coeff (S-j)) +
      (2/3 : k) * FixedReflectedJetConvolution68
        (B^3) (3*bU) c cU (2*S-G) -
      (3/2 : k) * B.coeff bU * d.coeff V^2)

theorem fiveToSix_zetaFirst_B3_endpoint_I3_scalar68
    (gamma : k) (A B c d e : k[X]) (N G S q : ℕ)
    (hBc : G≤2*S) (hGamma : S<4*N-G)
    (hred : FiveToSixCuspZetaFirstEndpointReducedScalar68
      gamma A B c d e N G S q) :
    FiveToSixCuspZetaFirstB3EndpointI3Scalar68 A B c d N G S q := by
  have hno : ¬ 4*N-G≤S := by omega
  dsimp only [FiveToSixCuspZetaFirstEndpointReducedScalar68] at hred
  rw [if_pos hBc,if_neg hno,if_neg hno] at hred
  simp only [sub_self,mul_zero,add_zero] at hred
  change FiveToSixCuspZetaFirstB3EndpointI3Scalar68 A B c d N G S q
  dsimp only [FiveToSixCuspZetaFirstB3EndpointI3Scalar68]
  exact hred

/-- The terms of the literal row-two polynomial which survive in the
`B^3`-loaded, gamma-inactive cell. -/
def FiveToSixCuspZetaFirstB3EndpointRowTwoCore68
    (A B c d e : k[X]) : k[X] :=
  -(6:k) • (A*B*derivative e) -
    (6:k) • (A*derivative B*e) -
    (6:k) • (A*c*derivative d) -
    (6:k) • (A*derivative c*d) - derivative A*B^3 +
    (3:k) • (derivative A*B*e) +
    (3:k) • (derivative A*c*d) +
    (12:k) • (B*c*derivative c) +
    (6:k) • (derivative B*c^2) -
    (18:k) • (d*derivative e) -
    (18:k) • (derivative d*e)

def FiveToSixCuspZetaFirstB3EndpointRowTwoScalar68
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let K := 11*N-2*G-2*S-1
  (-4/27:k) *
    (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff K = 0

/-- Literal support reduction of row two.  Only the `A'B^3`, `Bcc'`, and
`B'c^2` terms are retained beyond the sparse eight-term row. -/
theorem fiveToSix_zetaFirst_B3_endpoint_rowTwo68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:G≤2*S) (hGamma:S<4*N-G) (hqS:q≤S)
    (hrow:FiveToSixCuspZetaFirstUniformJetRowTwoScalar68
      gamma epsilon A B c d e N G S q (S-q)):
    FiveToSixCuspZetaFirstB3EndpointRowTwoScalar68 A B c d e N G S:=by
  let W:=11*N-2*G-S-1
  let K:=11*N-2*G-2*S-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hlowB2d:(B^2*derivative d).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hlowBBd:(B*derivative B*d).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hlowAd:(A*derivative d).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hlowBc:(B*derivative c).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hlowcB:(c*derivative B).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hlowdA:(d*derivative A).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hlowAB1:(derivative A*B).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hlowAB2:(A*derivative B).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hlowd:(derivative d).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hSW:S≤W:=by dsimp only [W];omega
  dsimp only [W] at hSW
  have hqm:q+(S-q)=S:=by omega
  dsimp only [FiveToSixCuspZetaFirstUniformJetRowTwoScalar68,
    FixedReflectedJet68] at hrow
  rw [hqm] at hrow
  simp only [coeff_reflect,revAt_le hSW] at hrow
  rw [show 11*N-2*G-S-1-S=K by dsimp only [K];omega] at hrow
  simp only [secondaryResidualRowTwoPolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlowB2d,
    coeff_eq_zero_of_natDegree_lt hlowBBd,
    coeff_eq_zero_of_natDegree_lt hlowAd,
    coeff_eq_zero_of_natDegree_lt hlowBc,
    coeff_eq_zero_of_natDegree_lt hlowcB,
    coeff_eq_zero_of_natDegree_lt hlowdA,
    coeff_eq_zero_of_natDegree_lt hlowAB1,
    coeff_eq_zero_of_natDegree_lt hlowAB2,
    coeff_eq_zero_of_natDegree_lt hlowd,
    mul_zero,add_zero,sub_zero] at hrow
  change FiveToSixCuspZetaFirstB3EndpointRowTwoScalar68 A B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowTwoScalar68,
    FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,K]
  simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
  linear_combination hrow

/-- Factored form of the retained row. -/
theorem fiveToSix_zetaFirst_B3_endpoint_rowTwo_core_factor68
    (A B c d e:k[X]):
    FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e =
      -(6:k) • (A*derivative (B*e+c*d))+
        (3:k) • (derivative A*(B*e+c*d))-derivative A*B^3+
        (6:k) • derivative (B*c^2)-(18:k) • derivative (d*e):=by
  have hcSq:derivative (c^2)=(2:k)•(c*derivative c):=by
    rw [show c^2=c*c by ring,derivative_mul,
      show derivative c*c=c*derivative c by ring]
    module
  have hc2:derivative (B*c^2)=
      (2:k)•(B*c*derivative c)+derivative B*c^2:=by
    rw [derivative_mul,hcSq]
    simp only [mul_smul_comm,mul_assoc]
    module
  rw [hc2]
  simp only [FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,derivative_add,
    derivative_mul,mul_add,add_mul,mul_assoc]
  module

/-- Division-free contracted row-two scalar after the I4 jet transport. -/
def FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  let T:=11*N-3*G
  let t:=2*S-G
  let V:=5*N-G-S
  let E:=6*N-G-S
  FixedReflectedJet68 (B*c^2-(1/9:k)•(A*B^3)) T t=
    3*d.coeff V*e.coeff E

theorem fiveToSix_zetaFirst_B3_endpoint_rowTwo_contracted68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:G≤2*S) (hGamma:S<4*N-G)
    (hi4:FiveToSixCuspZetaFirstEndpointB3I4Packet68
      gamma B c d e N G S)
    (hrow:FiveToSixCuspZetaFirstB3EndpointRowTwoScalar68
      A B c d e N G S):
    FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68
      A B c d e N G S:=by
  let H:=B*e+c*d
  let F:=H-(1/9:k)•B^3
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let P:=9*N-2*G-S
  let T:=11*N-3*G
  let t:=2*S-G
  let V:=5*N-G-S
  let E:=6*N-G-S
  let K:=11*N-2*G-2*S-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤V ∧ e.natDegree≤E ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  change F.natDegree≤P-S-1 ∧ _ at hi4
  have hF:=hi4.1
  have hL:0<P-S-1:=by dsimp only [P];omega
  have hdF0:=natDegree_derivative_le F
  have hdF:(derivative F).natDegree<P-S-1:=by omega
  have hdA0:=natDegree_derivative_le A
  have hdA:(derivative A).natDegree<2*N:=by omega
  have hAF:(A*derivative F).natDegree<K:=by
    dsimp only [P,K] at hF hdF ⊢
    compute_degree
    omega
  have hA'F:(derivative A*F).natDegree<K:=by
    dsimp only [P,K] at hF hdA ⊢
    compute_degree
    omega
  have hFblock:(-(6:k)•(A*derivative F)+
      (3:k)•(derivative A*F)).coeff K=0:=by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hfactor:=fiveToSix_zetaFirst_B3_endpoint_rowTwo_core_factor68
    (k:=k) A B c d e
  have hfactor':FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e=
      (-(6:k)•(A*derivative F)+(3:k)•(derivative A*F))+
        (6:k)•derivative Q-(18:k)•derivative (d*e):=by
    dsimp only [F,H,Q]
    rw [hfactor]
    simp only [derivative_sub,derivative_smul,derivative_mul,mul_sub,
      mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_sub,smul_add,
      smul_smul,mul_assoc]
    module
  have hcore:(FiveToSixCuspZetaFirstB3EndpointRowTwoCore68
      A B c d e).coeff K=0:=by
    dsimp only [FiveToSixCuspZetaFirstB3EndpointRowTwoScalar68] at hrow
    linear_combination (-27/4:k)*hrow
  rw [hfactor'] at hcore
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,hFblock,
    zero_add] at hcore
  have htT:t≤T:=by dsimp only [t,T];omega
  have hTK:T-t=K+1:=by dsimp only [T,t,K];omega
  have hQjet:Q.coeff (K+1)=FixedReflectedJet68 Q T t:=by
    rw [←hTK]
    exact coeff_top_sub_eq_fixedReflectedJet68 Q T t htT
  have hde:=coeff_mul_at_bounds68 d e V E hd he
  have hVE:V+E=K+1:=by dsimp only [V,E,K];omega
  rw [hVE] at hde
  simp only [coeff_derivative,hQjet,hde] at hcore
  have hK:0<K+1:=by dsimp only [K];omega
  have hKc:((((K+1:ℕ)):k))≠0:=by
    exact_mod_cast (show K+1≠0 by omega)
  have hprod:((K+1:ℕ):k)*
      (FixedReflectedJet68 Q T t-3*d.coeff V*e.coeff E)=0:=by
    push_cast at hcore ⊢
    linear_combination (1/6:k)*hcore
  have hz:FixedReflectedJet68 Q T t-3*d.coeff V*e.coeff E=0:=
    (mul_eq_zero.mp hprod).resolve_left hKc
  change FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68
    A B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68,
    Q,T,t,V,E]
  linear_combination hz

/-- Source-facing B3 cell: the exact least-load witness, its endpoint I3
scalar, the individual-I4 transport, and the contracted row two are kept
together. -/
def FiveToSixCuspZetaFirstB3EndpointPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G S ∧ G≤2*S ∧ S<4*N-G ∧
    ∃ q, min S (7*N-2*G-S)<q ∧ q≤S ∧
      (∀ j,j<q→((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
        (8*N-2*G)).coeff j=0) ∧
      (∀ j,min S (7*N-2*G-S)<j→j<q→
        ¬FiveToSixCuspZetaFirstLoadAt68 N G S j) ∧
      FiveToSixCuspZetaFirstLoadAt68 N G S q ∧
      FiveToSixCuspZetaFirstB3EndpointI3Scalar68 A B c d N G S q ∧
      FiveToSixCuspZetaFirstEndpointB3I4Packet68 gamma B c d e N G S ∧
      FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68
        A B c d e N G S

/-- Exact remaining endpoint split: either the gamma wall is active, or
the complete B3-loaded row-two/I3 packet is available. -/
theorem fiveToSix_zetaFirst_endpoint_B3_or_gamma_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    4*N-G≤S ∨ FiveToSixCuspZetaFirstB3EndpointPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_inventory68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hBc|hGamma
  · by_cases hwall:4*N-G≤S
    · exact Or.inl hwall
    · right
      have hGamma:S<4*N-G:=by omega
      have hs:=fiveToSix_zetaFirst_support_of_endpoint_cells_residual68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hj
      rcases hj.2 with ⟨q,hmuq,hqS,hprior,hminimal,hload,hcell⟩
      have hi3:=fiveToSix_zetaFirst_B3_endpoint_I3_scalar68
        gamma A B c d e N G S q hBc hGamma hcell.2.1
      have hi4:=fiveToSix_zetaFirst_endpoint_B3_I4_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hBc hGamma
      have hrow:=fiveToSix_zetaFirst_B3_endpoint_rowTwo68
        alpha gamma epsilon zeta eta terminal A B c d e N G S q hs hBc
        hGamma hqS hcell.2.2.2.2
      have hcontract:=fiveToSix_zetaFirst_B3_endpoint_rowTwo_contracted68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hBc
        hGamma hi4 hrow
      exact ⟨hs,hBc,hGamma,q,hmuq,hqS,hprior,hminimal,hload,
        hi3,hi4,hcontract⟩
  · exact Or.inl hGamma

#print axioms fiveToSix_zetaFirst_B3_endpoint_I3_scalar68
#print axioms fiveToSix_zetaFirst_B3_endpoint_rowTwo68
#print axioms fiveToSix_zetaFirst_B3_endpoint_rowTwo_core_factor68
#print axioms fiveToSix_zetaFirst_B3_endpoint_rowTwo_contracted68
#print axioms fiveToSix_zetaFirst_endpoint_B3_or_gamma_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3RowTwo68

end Max11DegreeRoutes
