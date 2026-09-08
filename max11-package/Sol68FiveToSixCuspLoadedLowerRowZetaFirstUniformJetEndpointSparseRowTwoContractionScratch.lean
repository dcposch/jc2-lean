import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowTwoScratch

/-! # Reflected contraction of the sparse endpoint row two

The six `A`-coupled terms are placed at one common reflected bound and
depth `S`.  The remaining `d,e` derivative pair is exactly its top
coefficient.  Multiplying by the nonzero `B` edge and using
`Delta_S=(3/2) B_top d_top` gives a division-free coupled equation.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowTwoContraction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The six common-bound reflected `S`-jets in the sparse row. -/
def FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedBlock68
    (A B c d e : k[X]) (N G S : ℕ) : k :=
  let W := 11*N-2*G-S-1
  (-(6 : k) * FixedReflectedJet68 (A*B*derivative e) W S -
    6 * FixedReflectedJet68 (A*derivative B*e) W S -
    6 * FixedReflectedJet68 (A*c*derivative d) W S -
    6 * FixedReflectedJet68 (A*derivative c*d) W S +
    3 * FixedReflectedJet68 (derivative A*B*e) W S +
    3 * FixedReflectedJet68 (derivative A*c*d) W S)

/-- Exact reflected row after evaluating the two top derivative loads. -/
def FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedScalar68
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let V := 5*N-G-S
  let E := 6*N-G-S
  FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedBlock68
      A B c d e N G S -
    18 * (((V+E : ℕ) : k)) * d.coeff V * e.coeff E = 0

/-- Division-free use of the endpoint discriminant edge. -/
def FiveToSixCuspZetaFirstSparseEndpointRowTwoDeltaScalar68
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let E := 6*N-G-S
  B.coeff (3*N-G) *
      FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedBlock68
        A B c d e N G S -
    12 * (((V+E : ℕ) : k)) * (Delta.reflect U).coeff S * e.coeff E = 0

/-- Coefficient-to-reflection transport of the verified eight-term row. -/
theorem fiveToSix_zetaFirst_sparse_endpoint_rowTwo_reflected68
    (A B c d e : k[X]) (N G S : ℕ)
    (hN : 0<N) (hgt : 5*N<2*G) (hle : 2*G≤6*N)
    (hS : 0<S) (hSR : S<7*N-2*G)
    (hd : d.natDegree≤5*N-G-S) (he : e.natDegree≤6*N-G-S)
    (hrow : FiveToSixCuspZetaFirstSparseEndpointRowTwoScalar68
      A B c d e N G S) :
    FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedScalar68
      A B c d e N G S := by
  let W := 11*N-2*G-S-1
  let K := 11*N-2*G-2*S-1
  let V := 5*N-G-S
  let E := 6*N-G-S
  have hSW : S≤W := by dsimp only [W];omega
  have hWK : W-S=K := by dsimp only [W,K];omega
  have hVE : V+E-1=K := by dsimp only [V,E,K];omega
  have hEV : E+V-1=K := by dsimp only [V,E,K];omega
  have hV : 0<V := by dsimp only [V];omega
  have hE : 0<E := by dsimp only [E];omega
  have hde := coeff_mul_derivative_at_bounds68 d e V E hE hd he
  rw [hVE] at hde
  have hed := coeff_mul_derivative_at_bounds68 e d E V hV he hd
  rw [show e*derivative d=derivative d*e by ring,hEV] at hed
  have hjet (p : k[X]) : p.coeff K=FixedReflectedJet68 p W S := by
    rw [← hWK]
    exact coeff_top_sub_eq_fixedReflectedJet68 p W S hSW
  dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowTwoScalar68,
    FiveToSixCuspZetaFirstSparseEndpointRowTwoInner68] at hrow
  rw [show 11*N-2*G-2*S-1=K by rfl] at hrow
  simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul] at hrow
  have hinner :
      -(6:k)*(A*B*derivative e).coeff K-
        6*(A*derivative B*e).coeff K-
        6*(A*c*derivative d).coeff K-
        6*(A*derivative c*d).coeff K+
        3*(derivative A*B*e).coeff K+
        3*(derivative A*c*d).coeff K-
        18*(d*derivative e).coeff K-
        18*(derivative d*e).coeff K=0 := by
    linear_combination (-27/4:k)*hrow
  rw [hjet (A*B*derivative e),hjet (A*derivative B*e),
    hjet (A*c*derivative d),hjet (A*derivative c*d),
    hjet (derivative A*B*e),hjet (derivative A*c*d)] at hinner
  rw [hde,hed] at hinner
  change FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedScalar68
    A B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedScalar68,
    FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedBlock68,V,E,W]
  push_cast
  linear_combination hinner

/-- The source witness, sparse thresholds, discriminant edge, reflected row,
and their division-free coupled consequence are retained together. -/
def FiveToSixCuspZetaFirstSparseEndpointRowTwoContractionPacket68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ) : Prop :=
  FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G S ∧
    2*S<G ∧ S<4*N-G ∧
    FiveToSixCuspZetaFirstSparseEndpointRowTwoPacket68
      gamma epsilon A B c d e N G S q ∧
    FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedScalar68
      A B c d e N G S ∧
    FiveToSixCuspZetaFirstSparseEndpointRowTwoDeltaScalar68
      A B c d e N G S

theorem fiveToSix_zetaFirst_sparse_endpoint_rowTwo_contraction_packet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc : 2*S<G) (hGamma : S<4*N-G)
    (hsp : FiveToSixCuspZetaFirstSparseEndpointRowTwoPacket68
      gamma epsilon A B c d e N G S q) :
    FiveToSixCuspZetaFirstSparseEndpointRowTwoContractionPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q := by
  have hp := hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have href := fiveToSix_zetaFirst_sparse_endpoint_rowTwo_reflected68
    A B c d e N G S hN hgt hle hS hSR hd he hsp.2
  have hdelta := hsp.1
  change q=S ∧ _ at hdelta
  have hcoupled : FiveToSixCuspZetaFirstSparseEndpointRowTwoDeltaScalar68
      A B c d e N G S := by
    dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowTwoDeltaScalar68]
    dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedScalar68]
      at href
    linear_combination B.coeff (3*N-G)*href-
      12*((((5*N-G-S)+(6*N-G-S):ℕ):k))*e.coeff (6*N-G-S)*hdelta.2.1
  exact ⟨hs,hBc,hGamma,hsp,href,hcoupled⟩

#print axioms fiveToSix_zetaFirst_sparse_endpoint_rowTwo_reflected68
#print axioms fiveToSix_zetaFirst_sparse_endpoint_rowTwo_contraction_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowTwoContraction68

end Max11DegreeRoutes
