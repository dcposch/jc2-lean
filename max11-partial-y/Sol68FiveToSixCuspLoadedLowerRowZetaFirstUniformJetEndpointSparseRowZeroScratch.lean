import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowOneScratch

/-! # Row-zero bridge at the sparse zeta-first endpoint

Only two common-bound `S`-jets and the literal top `A'*d*e` edge survive
row zero.  Together with row two this eliminates `d*e`, relates `J0` and
`J2`, and removes `J2` from the verified row-one/row-two resultant.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowZero68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedBlock68
    (A B c d e:k[X]) (N G S:ℕ):k:=
  let W:=13*N-2*G-S-1
  FixedReflectedJet68 (A*derivative A*B*e) W S+
    FixedReflectedJet68 (A*derivative A*c*d) W S

def FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedScalar68
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  let V:=5*N-G-S
  let E:=6*N-G-S
  FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedBlock68
      A B c d e N G S+
    3*A.coeff (2*N)*d.coeff V*e.coeff E*(((2*N:ℕ):k))=0

/-- Direct `J0/J2` relation after eliminating the common top `d*e` edge. -/
def FiveToSixCuspZetaFirstSparseEndpointRowZeroRowTwoRelation68
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  let V:=5*N-G-S
  let E:=6*N-G-S
  let T:=V+E
  let C:=A.coeff (2*N)*(((2*N:ℕ):k))
  let J0:=FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedBlock68
    A B c d e N G S
  let J2:=FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedBlock68
    A B c d e N G S
  6*((T:ℕ):k)*J0+C*J2=0

/-- Resultant after removing both `e_E` and the independent `J2` block. -/
def FiveToSixCuspZetaFirstSparseEndpointRowZeroRowOneResultant68
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  let U:=8*N-2*G
  let V:=5*N-G-S
  let E:=6*N-G-S
  let C:=A.coeff (2*N)*(((2*N:ℕ):k))
  let J0:=FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedBlock68
    A B c d e N G S
  let J1:=FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedBlock68
    A B c d e N G S
  9*((E:ℕ):k)*B.coeff (3*N-G)^2*J0^2-
    2*(Delta.reflect U).coeff S^2*C^2*(J1+3*C*d.coeff V^2)=0

theorem fiveToSix_zetaFirst_sparse_endpoint_rowZero_reflected68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:2*S<G) (hGamma:S<4*N-G)
    (hrow:FiveToSixCuspZetaFirstUniformJetRowZeroScalar68
      gamma epsilon A B c d e N G S S 0):
    FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedScalar68
      A B c d e N G S:=by
  let W:=13*N-2*G-S-1
  let K:=13*N-2*G-2*S-1
  let V:=5*N-G-S
  let E:=6*N-G-S
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
  have hlowABc:(derivative A*B*c^2).natDegree<K:=by
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
  dsimp only [FiveToSixCuspZetaFirstUniformJetRowZeroScalar68,
    FixedReflectedJet68,Nat.add_zero] at hrow
  simp only [coeff_reflect,revAt_le hSW] at hrow
  rw [show 13*N-2*G-S-1-S=K by dsimp only [K];omega] at hrow
  simp only [secondaryResidualRowZeroPolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlowABd,
    coeff_eq_zero_of_natDegree_lt hlowABBd,
    coeff_eq_zero_of_natDegree_lt hlowABc,
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
  have hinner:(A*derivative A*B*e).coeff K+
      (A*derivative A*c*d).coeff K+
      3*(derivative A*d*e).coeff K=0:=by
    linear_combination (-27/4:k)*hrow
  have hWK:W-S=K:=by dsimp only [W,K];omega
  have hjet(p:k[X]):p.coeff K=FixedReflectedJet68 p W S:=by
    rw [←hWK]
    exact coeff_top_sub_eq_fixedReflectedJet68 p W S (by dsimp only [W];omega)
  rw [hjet (A*derivative A*B*e),hjet (A*derivative A*c*d)] at hinner
  have hV:0<V:=by dsimp only [V];omega
  have hE:0<E:=by dsimp only [E];omega
  have hAde:=coeff_mul_mul_derivative_at_bounds68 d e A V E (2*N)
    (by omega) hd he hA
  rw [show V+E+2*N-1=K by dsimp only [V,E,K];omega] at hAde
  have hAde':(derivative A*d*e).coeff K=
      A.coeff (2*N)*d.coeff V*e.coeff E*(((2*N:ℕ):k)):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hAde
  rw [hAde'] at hinner
  change FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedScalar68
    A B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedScalar68,
    FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedBlock68,V,E,W]
  linear_combination hinner

def FiveToSixCuspZetaFirstSparseEndpointRowZeroPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ):Prop:=
  FiveToSixCuspZetaFirstSparseEndpointRowOneRowTwoPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q ∧
    FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedScalar68
      A B c d e N G S ∧
    FiveToSixCuspZetaFirstSparseEndpointRowZeroRowTwoRelation68
      A B c d e N G S ∧
    FiveToSixCuspZetaFirstSparseEndpointRowZeroRowOneResultant68
      A B c d e N G S

theorem fiveToSix_zetaFirst_sparse_endpoint_rowZero_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ)
    (hp:FiveToSixCuspZetaFirstSparseEndpointRowOneRowTwoPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q):
    FiveToSixCuspZetaFirstSparseEndpointRowZeroPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q:=by
  rcases hp with ⟨hbase,hrow1,hres⟩
  rcases hbase with ⟨hs,hBc,hGamma,hsp,hrow2,hcoupled⟩
  have hrow0:=fiveToSix_zetaFirst_sparse_endpoint_rowZero_reflected68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hBc hGamma
    hsp.1.2.2.1
  have hrel:FiveToSixCuspZetaFirstSparseEndpointRowZeroRowTwoRelation68
      A B c d e N G S:=by
    dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowZeroRowTwoRelation68]
    dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedScalar68]
      at hrow0
    dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedScalar68]
      at hrow2
    linear_combination 6*((((5*N-G-S)+(6*N-G-S):ℕ):k))*hrow0+
      A.coeff (2*N)*(((2*N:ℕ):k))*hrow2
  have hfinal:FiveToSixCuspZetaFirstSparseEndpointRowZeroRowOneResultant68
      A B c d e N G S:=by
    dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowZeroRowOneResultant68]
    dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowZeroRowTwoRelation68]
      at hrel
    dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowOneRowTwoResultant68]
      at hres
    have heq:
        A.coeff (2*N)*(((2*N:ℕ):k))*
            FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedBlock68
              A B c d e N G S=
          -6*((((5*N-G-S)+(6*N-G-S):ℕ):k))*
            FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedBlock68
              A B c d e N G S:=by
      linear_combination hrel
    have hsq:=congrArg (fun x:k↦x^2) heq
    have hTn:0<(5*N-G-S)+(6*N-G-S):=by omega
    have hTc:((((5*N-G-S)+(6*N-G-S):ℕ):k))≠0:=by
      exact_mod_cast (show (5*N-G-S)+(6*N-G-S)≠0 by omega)
    have hfac:
        ((((5*N-G-S)+(6*N-G-S):ℕ):k))^2*
          (36*(((6*N-G-S:ℕ):k))*B.coeff (3*N-G)^2*
              FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedBlock68
                A B c d e N G S^2-
            8*((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
                (8*N-2*G)).coeff S^2*
              (A.coeff (2*N)*(((2*N:ℕ):k)))^2*
              (FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedBlock68
                  A B c d e N G S+
                3*(A.coeff (2*N)*(((2*N:ℕ):k)))*
                  d.coeff (5*N-G-S)^2))=0:=by
      linear_combination
        (A.coeff (2*N)*(((2*N:ℕ):k)))^2*hres-
        (((6*N-G-S:ℕ):k))*B.coeff (3*N-G)^2*hsq
    have hcore:36*(((6*N-G-S:ℕ):k))*B.coeff (3*N-G)^2*
          FiveToSixCuspZetaFirstSparseEndpointRowZeroReflectedBlock68
            A B c d e N G S^2-
        8*((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
            (8*N-2*G)).coeff S^2*
          (A.coeff (2*N)*(((2*N:ℕ):k)))^2*
          (FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedBlock68
              A B c d e N G S+
            3*(A.coeff (2*N)*(((2*N:ℕ):k)))*
              d.coeff (5*N-G-S)^2)=0:=
      (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hTc)
    linear_combination (1/4:k)*hcore
  exact ⟨⟨⟨hs,hBc,hGamma,hsp,hrow2,hcoupled⟩,hrow1,hres⟩,
    hrow0,hrel,hfinal⟩

#print axioms fiveToSix_zetaFirst_sparse_endpoint_rowZero_reflected68
#print axioms fiveToSix_zetaFirst_sparse_endpoint_rowZero_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowZero68

end Max11DegreeRoutes
