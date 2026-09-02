import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowTwoContractionScratch

/-! # Independent row-one jet at the sparse zeta-first endpoint

Row one leaves five common-bound reflected `S`-jets and two literal edge
terms.  Crossing it with the verified row-two/Delta equation eliminates the
top `e` edge without division and yields one exact endpoint resultant.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowOne68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedBlock68
    (A B c d e : k[X]) (N G S : ℕ) : k :=
  let W := 12*N-2*G-S-1
  (2:k)*FixedReflectedJet68 (A^2*B*derivative d) W S+
    2*FixedReflectedJet68 (A^2*derivative B*d) W S+
    2*FixedReflectedJet68 (A*derivative A*B*d) W S-
    6*FixedReflectedJet68 (A*c*derivative e) W S-
    6*FixedReflectedJet68 (A*derivative c*e) W S

def FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedScalar68
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let V := 5*N-G-S
  let E := 6*N-G-S
  FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedBlock68
      A B c d e N G S+
    3*A.coeff (2*N)*d.coeff V^2*(((2*N:ℕ):k))-
    18*e.coeff E^2*((E:ℕ):k)=0

/-- Eliminate `e_E^2` between row one and the squared row-two/Delta
equation.  No edge is divided out. -/
def FiveToSixCuspZetaFirstSparseEndpointRowOneRowTwoResultant68
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let E := 6*N-G-S
  let T := V+E
  let J1 := FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedBlock68
    A B c d e N G S
  let J2 := FiveToSixCuspZetaFirstSparseEndpointRowTwoReflectedBlock68
    A B c d e N G S
  ((E:ℕ):k)*(B.coeff (3*N-G)*J2)^2-
    8*((T:ℕ):k)^2*(Delta.reflect U).coeff S^2*
      (J1+3*A.coeff (2*N)*d.coeff V^2*(((2*N:ℕ):k)))=0

/-- Exact row-one support reduction at the sparse endpoint. -/
theorem fiveToSix_zetaFirst_sparse_endpoint_rowOne_reflected68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc : 2*S<G) (hGamma : S<4*N-G)
    (hrow : FiveToSixCuspZetaFirstUniformJetRowOneScalar68
      gamma epsilon A B c d e N G S S 0) :
    FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedScalar68
      A B c d e N G S := by
  let W := 12*N-2*G-S-1
  let K := 12*N-2*G-2*S-1
  let V := 5*N-G-S
  let E := 6*N-G-S
  have hp := hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hlowABc : (derivative A*B^2*c).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowB2e : (B^2*derivative e).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowBcd : (B*c*derivative d).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowBdc : (B*derivative c*d).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowBcd' : (derivative B*c*d).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowc3 : (c^2*derivative c).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowAe : (A*derivative e).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowcc : (c*derivative c).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowAB2 : (derivative A*B^2).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowBd : (B*derivative d).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowdB : (d*derivative B).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowAc : (A*derivative c).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hlowe : (derivative e).natDegree<K := by
    dsimp only [K];compute_degree;omega
  have hSW:S≤12*N-2*G-S-1:=by omega
  dsimp only [FiveToSixCuspZetaFirstUniformJetRowOneScalar68,
    FixedReflectedJet68,Nat.add_zero] at hrow
  simp only [coeff_reflect,revAt_le hSW] at hrow
  rw [show 12*N-2*G-S-1-S=K by dsimp only [K];omega] at hrow
  simp only [secondaryResidualRowOnePolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlowABc,
    coeff_eq_zero_of_natDegree_lt hlowB2e,
    coeff_eq_zero_of_natDegree_lt hlowBcd,
    coeff_eq_zero_of_natDegree_lt hlowBdc,
    coeff_eq_zero_of_natDegree_lt hlowBcd',
    coeff_eq_zero_of_natDegree_lt hlowc3,
    coeff_eq_zero_of_natDegree_lt hlowAe,
    coeff_eq_zero_of_natDegree_lt hlowcc,
    coeff_eq_zero_of_natDegree_lt hlowAB2,
    coeff_eq_zero_of_natDegree_lt hlowBd,
    coeff_eq_zero_of_natDegree_lt hlowdB,
    coeff_eq_zero_of_natDegree_lt hlowAc,
    coeff_eq_zero_of_natDegree_lt hlowe,
    mul_zero,add_zero,sub_zero] at hrow
  have hinner:
      (2:k)*(A^2*B*derivative d).coeff K+
        2*(A^2*derivative B*d).coeff K+
        2*(A*derivative A*B*d).coeff K-
        6*(A*c*derivative e).coeff K-
        6*(A*derivative c*e).coeff K+
        3*(derivative A*d^2).coeff K-
        18*(e*derivative e).coeff K=0:=by
    linear_combination (-27/4:k)*hrow
  have hWK:W-S=K:=by dsimp only [W,K];omega
  have hjet (p:k[X]):p.coeff K=FixedReflectedJet68 p W S:=by
    rw [←hWK]
    exact coeff_top_sub_eq_fixedReflectedJet68 p W S hSW
  rw [hjet (A^2*B*derivative d),hjet (A^2*derivative B*d),
    hjet (A*derivative A*B*d),hjet (A*c*derivative e),
    hjet (A*derivative c*e)] at hinner
  have hV:0<V:=by dsimp only [V];omega
  have hE:0<E:=by dsimp only [E];omega
  have hAd2:=coeff_mul_mul_derivative_at_bounds68 d d A V V (2*N)
    (by omega) hd hd hA
  rw [show V+V+2*N-1=K by dsimp only [V,K];omega] at hAd2
  have hAd2':(derivative A*d^2).coeff K=
      A.coeff (2*N)*d.coeff V^2*(((2*N:ℕ):k)):=by
    simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hAd2
  have hee:=coeff_mul_derivative_at_bounds68 e e E E hE he he
  rw [show E+E-1=K by dsimp only [E,K];omega] at hee
  rw [hAd2',hee] at hinner
  change FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedScalar68
    A B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedScalar68,
    FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedBlock68,V,E,W]
  linear_combination hinner

/-- Full source-preserving endpoint packet with the division-free resultant. -/
def FiveToSixCuspZetaFirstSparseEndpointRowOneRowTwoPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ):Prop:=
  FiveToSixCuspZetaFirstSparseEndpointRowTwoContractionPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q ∧
    FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedScalar68
      A B c d e N G S ∧
    FiveToSixCuspZetaFirstSparseEndpointRowOneRowTwoResultant68
      A B c d e N G S

theorem fiveToSix_zetaFirst_sparse_endpoint_rowOne_rowTwo_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ)
    (hp:FiveToSixCuspZetaFirstSparseEndpointRowTwoContractionPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q):
    FiveToSixCuspZetaFirstSparseEndpointRowOneRowTwoPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q:=by
  rcases hp with ⟨hs,hBc,hGamma,hsp,hrow2,hcoupled⟩
  have hrow1:=fiveToSix_zetaFirst_sparse_endpoint_rowOne_reflected68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hBc hGamma
    hsp.1.2.2.2.1
  have hres:FiveToSixCuspZetaFirstSparseEndpointRowOneRowTwoResultant68
      A B c d e N G S:=by
    dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowOneRowTwoResultant68]
    dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowOneReflectedScalar68]
      at hrow1
    dsimp only [FiveToSixCuspZetaFirstSparseEndpointRowTwoDeltaScalar68]
      at hcoupled
    have h2eq:=sub_eq_zero.mp hcoupled
    have h2sq:=congrArg (fun x:k↦x^2) h2eq
    linear_combination (((6*N-G-S:ℕ):k))*h2sq-
      8*((((5*N-G-S)+(6*N-G-S):ℕ):k))^2*
        ((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
          (8*N-2*G)).coeff S^2*hrow1
  exact ⟨⟨hs,hBc,hGamma,hsp,hrow2,hcoupled⟩,hrow1,hres⟩

#print axioms fiveToSix_zetaFirst_sparse_endpoint_rowOne_reflected68
#print axioms fiveToSix_zetaFirst_sparse_endpoint_rowOne_rowTwo_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointSparseRowOne68

end Max11DegreeRoutes
