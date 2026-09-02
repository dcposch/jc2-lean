import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowZeroScratch

/-! # I4 closure of the sparse zeta-first endpoint

The individual compensated I4 identity was not used by the cusp
combination.  In the sparse cell all of its nonconstant right-hand terms
lie strictly below reflected depth `S`.  Hence `H=B*e+c*d` drops below that
depth, forcing the contracted row-two block to vanish.  Its already
verified nonzero `d*e` edge then gives the contradiction.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseI4Closure68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact individual I4 source adapter at the retained earlier cusp. -/
theorem fiveToSix_zetaFirst_sparse_compensatedI4_polynomial68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S):
    ∃ i4:k,(B*e+c*d)+(3/2*gamma:k)•d=
      (1/9:k)•B^3-(3/4*epsilon:k)•B+(3/8:k)•C i4:=by
  have hp:=hs
  change _ ∧ _ ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  refine ⟨i4,?_⟩
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,hz]
    at hi4
  simp only [secondaryResidualInvariantFourPolynomial68] at hi4
  rw [←hi4]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul,map_add,map_sub,map_mul,map_pow,map_neg,
    map_zero,RatFunc.algebraMap_C,map_div₀,map_ofNat,map_natCast,map_one]
  ring

/-- Sparse thresholds force the compensated I4 polynomial below its
reflected `S` endpoint. -/
theorem fiveToSix_zetaFirst_sparse_compensatedI4_support68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:2*S<G) (hGamma:S<4*N-G):
    (B*e+c*d).natDegree≤9*N-2*G-2*S-1:=by
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
  have hH:(B*e+c*d)=
      (1/9:k)•B^3-(3/4*epsilon:k)•B+(3/8:k)•C i4-
        (3/2*gamma:k)•d:=by
    linear_combination hpoly
  rw [hH]
  compute_degree
  omega

/-- The six-term row-two jet is the coefficient of
`-6*A*H' + 3*A'*H`; the I4 support drop kills it. -/
theorem fiveToSix_zetaFirst_sparse_rowTwo_block_zero68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:2*S<G) (hGamma:S<4*N-G):
    FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedBlock68
      A B c d e N G S=0:=by
  let H:=B*e+c*d
  let W:=11*N-2*G-S-1
  let K:=11*N-2*G-2*S-1
  have hp:=hs
  change _ ∧ _ ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  have hA:=hp.2.2.2.2.1.2.2.2.1
  have hH:=fiveToSix_zetaFirst_sparse_compensatedI4_support68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hBc hGamma
  change H.natDegree≤9*N-2*G-2*S-1 at hH
  have hL:0<9*N-2*G-2*S-1:=by omega
  have hdH0:=natDegree_derivative_le H
  have hdH:(derivative H).natDegree<9*N-2*G-2*S-1:=by omega
  have hdA0:=natDegree_derivative_le A
  have hdA:(derivative A).natDegree<2*N:=by omega
  have hAH:(A*derivative H).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hA'H:(derivative A*H).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hP:(-(6:k)•(A*derivative H)+(3:k)•(derivative A*H)).natDegree<K:=by
    compute_degree
    omega
  have hcoeff:
      (-(6:k)•(A*derivative H)+(3:k)•(derivative A*H)).coeff K=0:=
    coeff_eq_zero_of_natDegree_lt hP
  have hSW:S≤11*N-2*G-S-1:=by omega
  change FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedBlock68
    A B c d e N G S=0
  dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedBlock68,
    FixedReflectedJet68,W]
  simp only [coeff_reflect,revAt_le hSW]
  rw [show 11*N-2*G-S-1-S=K by dsimp only [K];omega]
  dsimp only [H] at hcoeff
  simp only [derivative_add,derivative_mul,coeff_add,coeff_smul,smul_eq_mul,
    add_mul,mul_add] at hcoeff
  simp only [mul_assoc] at hcoeff ⊢
  linear_combination hcoeff

/-- The complete verified row-zero endpoint packet has no sparse-cell
realization.  The row-zero resultant is preserved in the input packet; the
unused individual I4 identity closes the cell one step earlier. -/
theorem fiveToSix_zetaFirst_sparse_endpoint_false68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ)
    (hp:FiveToSixCuspZetaFirstSparseEndpointRowZeroPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q):False:=by
  rcases hp with ⟨hprev,hrow0,hrel,hres⟩
  rcases hprev with ⟨hbase,hrow1,hres12⟩
  rcases hbase with ⟨hs,hBc,hGamma,hsp,hrow2,hcoupled⟩
  have hJ2:=fiveToSix_zetaFirst_sparse_rowTwo_block_zero68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hBc hGamma
  have hrow2':=hrow2
  dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedScalar68]
    at hrow2'
  rw [hJ2] at hrow2'
  have hp0:=hs
  change _ ∧ _ ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0.2.2.2.2.1 with
    ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hdne:=hcusp.2.2.1
  have hene:=hcusp.2.2.2.1
  have hTn:0<(5*N-G-S)+(6*N-G-S):=by omega
  have hTc:((((5*N-G-S)+(6*N-G-S):ℕ):k))≠0:=by
    exact_mod_cast (show (5*N-G-S)+(6*N-G-S)≠0 by omega)
  have hcoef:(18:k)*((((5*N-G-S)+(6*N-G-S):ℕ):k))≠0:=
    mul_ne_zero (by norm_num) hTc
  have hprod:(18:k)*((((5*N-G-S)+(6*N-G-S):ℕ):k))*
      d.coeff (5*N-G-S)*e.coeff (6*N-G-S)=0:=by
    linear_combination -hrow2'
  have hprefix:(18:k)*((((5*N-G-S)+(6*N-G-S):ℕ):k))*
      d.coeff (5*N-G-S)≠0:=mul_ne_zero hcoef hdne
  exact hene ((mul_eq_zero.mp hprod).resolve_left hprefix)

#print axioms fiveToSix_zetaFirst_sparse_compensatedI4_polynomial68
#print axioms fiveToSix_zetaFirst_sparse_compensatedI4_support68
#print axioms fiveToSix_zetaFirst_sparse_rowTwo_block_zero68
#print axioms fiveToSix_zetaFirst_sparse_endpoint_false68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseI4Closure68

end Max11DegreeRoutes
