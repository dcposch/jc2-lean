import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseScratch

/-! # Exact row-two expansion in the sparse zeta-first endpoint cell

At `q=S`, the endpoint row-two index is
`K=11*N-2*G-2*S-1`.  In the sparse cell `2*S<G` and `S<4*N-G`, every
gamma/epsilon correction and the five lower-support monomials in the
residual row-two polynomial vanish at `K`.  This leaves one exact eight-term
row, retained together with the already verified discriminant edge value.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The eight terms that remain from the literal residual row-two
polynomial at a sparse endpoint. -/
def FiveToSixCuspZetaFirstSparseEndpointRowTwoInner68
    (A B c d e : k[X]) : k[X] :=
  -(6 : k) • (A*B*derivative e) -
    (6 : k) • (A*derivative B*e) -
    (6 : k) • (A*c*derivative d) -
    (6 : k) • (A*derivative c*d) +
    (3 : k) • (derivative A*B*e) +
    (3 : k) • (derivative A*c*d) -
    (18 : k) • (d*derivative e) -
    (18 : k) • (derivative d*e)

def FiveToSixCuspZetaFirstSparseEndpointRowTwoScalar68
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let K := 11*N-2*G-2*S-1
  (-4/27 : k) *
    (FiveToSixCuspZetaFirstSparseEndpointRowTwoInner68 A B c d e).coeff K = 0

/-- Literal support reduction of row two.  No total-degree or `X`-degree
bound is used: every zero below comes from the component support packet. -/
theorem fiveToSix_zetaFirst_sparse_endpoint_rowTwo68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc : 2*S < G) (hGamma : S < 4*N-G)
    (hrow : FiveToSixCuspZetaFirstUniformJetRowTwoScalar68
      gamma epsilon A B c d e N G S S 0) :
    FiveToSixCuspZetaFirstSparseEndpointRowTwoScalar68 A B c d e N G S := by
  let K := 11*N-2*G-2*S-1
  have hp := hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hlowA3 : (derivative A*B^3).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hlowB2d : (B^2*derivative d).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hlowBBd : (B*derivative B*d).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hlowBcc : (B*c*derivative c).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hlowBc2 : (derivative B*c^2).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hlowAd : (A*derivative d).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hlowBc : (B*derivative c).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hlowcB : (c*derivative B).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hlowdA : (d*derivative A).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hlowAB1 : (derivative A*B).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hlowAB2 : (A*derivative B).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hlowd : (derivative d).natDegree < K := by
    dsimp only [K]
    compute_degree
    omega
  have hSW : S ≤ 11*N-2*G-S-1 := by omega
  dsimp only [FiveToSixCuspZetaFirstUniformJetRowTwoScalar68,
    FixedReflectedJet68,Nat.add_zero] at hrow
  simp only [coeff_reflect,revAt_le hSW] at hrow
  rw [show 11*N-2*G-S-1-S=K by dsimp only [K];omega] at hrow
  simp only [secondaryResidualRowTwoPolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlowA3,
    coeff_eq_zero_of_natDegree_lt hlowB2d,
    coeff_eq_zero_of_natDegree_lt hlowBBd,
    coeff_eq_zero_of_natDegree_lt hlowBcc,
    coeff_eq_zero_of_natDegree_lt hlowBc2,
    coeff_eq_zero_of_natDegree_lt hlowAd,
    coeff_eq_zero_of_natDegree_lt hlowBc,
    coeff_eq_zero_of_natDegree_lt hlowcB,
    coeff_eq_zero_of_natDegree_lt hlowdA,
    coeff_eq_zero_of_natDegree_lt hlowAB1,
    coeff_eq_zero_of_natDegree_lt hlowAB2,
    coeff_eq_zero_of_natDegree_lt hlowd,
    mul_zero,add_zero,sub_zero] at hrow
  change FiveToSixCuspZetaFirstSparseEndpointRowTwoScalar68 A B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowTwoScalar68,
    FiveToSixCuspZetaFirstSparseEndpointRowTwoInner68,K]
  simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
  linear_combination hrow

/-- The sparse chamber now carries both its exact discriminant edge and the
fully expanded independent row-two equation. -/
def FiveToSixCuspZetaFirstSparseEndpointRowTwoPacket68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  FiveToSixCuspZetaFirstSparseEndpointPacket68
      gamma epsilon A B c d e N G S q ∧
    FiveToSixCuspZetaFirstSparseEndpointRowTwoScalar68 A B c d e N G S

theorem fiveToSix_zetaFirst_sparse_endpoint_rowTwo_packet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc : 2*S < G) (hGamma : S < 4*N-G)
    (hsp : FiveToSixCuspZetaFirstSparseEndpointPacket68
      gamma epsilon A B c d e N G S q) :
    FiveToSixCuspZetaFirstSparseEndpointRowTwoPacket68
      gamma epsilon A B c d e N G S q := by
  refine ⟨hsp,?_⟩
  change q=S ∧ _ at hsp
  exact fiveToSix_zetaFirst_sparse_endpoint_rowTwo68
    alpha gamma epsilon zeta eta terminal A B c d e N G S
    hs hBc hGamma hsp.2.2.2.2

#print axioms fiveToSix_zetaFirst_sparse_endpoint_rowTwo68
#print axioms fiveToSix_zetaFirst_sparse_endpoint_rowTwo_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowTwo68

end Max11DegreeRoutes
