import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonContractionScratch

/-! # The first post-epsilon equality coefficient

The exact rows at `m=w+1` have indices `7*N-2*S-2` and
`5*N-2*S-2`.  Before the support wall they contain the same compensated
I4/J pair as the epsilon wall.  Their determinant is again `3*N`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualityEpsilonNextRowZeroScalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=7*N-2*S-2
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e).coeff K+
      (3/2*gamma:k)*(A*derivative A*d).coeff K+
      (3/4*epsilon:k)*(A*B*derivative A).coeff K=0

def FiveToSixCuspZetaFirstB3EqualityEpsilonNextRowTwoScalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=5*N-2*S-2
  (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff K-
      (9*gamma:k)*(A*derivative d).coeff K+
      (9/2*gamma:k)*(d*derivative A).coeff K+
      (9/4*epsilon:k)*(derivative A*B).coeff K-
      (9/2*epsilon:k)*(A*derivative B).coeff K=0

/-- Abstract two-row edge contraction.  The determinant hypothesis is kept
as the exact natural-number equality used after coefficient extraction. -/
theorem fiveToSix_zetaFirst_B3_equality_twoRow_edge_drop68
    (A Fce J:k[X]) (N D j K0 K2:ℕ)
    (hN:0<N) (hD:0<D) (hj:0<j)
    (hA:A.natDegree≤2*N) (ha:A.coeff (2*N)≠0)
    (hFce:Fce.natDegree≤D) (hJ:J.natDegree≤j)
    (hK0:2*N+D+2*N-1=K0) (hK0j:(2*N-1)+j=K0)
    (hK2:2*N+D-1=K2) (hK2j:j-1=K2)
    (hdet:D+3*N=N+j)
    (hrow0:(A*derivative A*Fce-derivative A*J).coeff K0=0)
    (hrow2:(-(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
      (6:k)•derivative J).coeff K2=0):
    Fce.natDegree≤D-1 ∧ J.natDegree≤j-1:=by
  have hAAFce:=coeff_mul_mul_derivative_at_bounds68 A Fce A
    (2*N) D (2*N) (by omega) hA hFce hA
  rw [hK0] at hAAFce
  have hdA:=natDegree_derivative_le A
  have hdAsharp:(derivative A).natDegree≤2*N-1:=by omega
  have hAJ:=coeff_mul_at_bounds68 (derivative A) J (2*N-1) j
    hdAsharp hJ
  rw [hK0j] at hAJ
  have hAtop:=coeff_derivative_at_bound68 A (2*N) (by omega)
  have hAAFce':(A*derivative A*Fce).coeff K0=
      A.coeff (2*N)^2*Fce.coeff D*((2*N:ℕ):k):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm,pow_two] using hAAFce
  rw [coeff_sub,hAAFce',hAJ,hAtop] at hrow0
  have hfac:A.coeff (2*N)*((2*N:ℕ):k)≠0:=by
    exact mul_ne_zero ha (by exact_mod_cast (show 2*N≠0 by omega))
  have htri0:A.coeff (2*N)*Fce.coeff D-J.coeff j=0:=by
    apply (mul_eq_zero.mp ?_).resolve_left hfac
    linear_combination hrow0
  have hAFce:=coeff_mul_derivative_at_bounds68 A Fce (2*N) D hD hA hFce
  rw [hK2] at hAFce
  have hA'Fce:=coeff_mul_at_bounds68 (derivative A) Fce (2*N-1) D
    hdAsharp hFce
  rw [show (2*N-1)+D=K2 by omega] at hA'Fce
  have hJder:=coeff_derivative_at_bound68 J j hj
  rw [hK2j] at hJder
  simp only [coeff_add,coeff_smul,smul_eq_mul,hAFce,hA'Fce,hAtop,hJder]
    at hrow2
  have htri2:A.coeff (2*N)*Fce.coeff D*
        (-((D:ℕ):k)+((N:ℕ):k))+((j:ℕ):k)*J.coeff j=0:=by
    push_cast at hrow2 ⊢
    linear_combination (1/6:k)*hrow2
  have hdetk:=congrArg (fun t:ℕ=>(t:k)) hdet
  push_cast at hdetk
  have hcoef:-((D:ℕ):k)+((N:ℕ):k)+((j:ℕ):k)=((3*N:ℕ):k):=by
    push_cast
    linear_combination -hdetk
  have hprod':(A.coeff (2*N)*Fce.coeff D)*
      (-((D:ℕ):k)+((N:ℕ):k)+((j:ℕ):k))=0:=by
    linear_combination htri2+((j:ℕ):k)*htri0
  rw [hcoef] at hprod'
  have hprod:((3*N:ℕ):k)*(A.coeff (2*N)*Fce.coeff D)=0:=by
    simpa only [mul_comm] using hprod'
  have h3Ncast:((3*N:ℕ):k)≠0:=by
    exact_mod_cast (show 3*N≠0 by omega)
  have hAFceZero:A.coeff (2*N)*Fce.coeff D=0:=
    (mul_eq_zero.mp hprod).resolve_left h3Ncast
  have hFceZero:Fce.coeff D=0:=
    (mul_eq_zero.mp hAFceZero).resolve_left ha
  have hJzero:J.coeff j=0:=by
    rw [hAFceZero,zero_sub] at htri0
    exact neg_eq_zero.mp htri0
  exact ⟨natDegree_le_pred hFce hFceZero,natDegree_le_pred hJ hJzero⟩

/-- Exact source reduction at `m=w+1`, provided it is still strictly
before the support wall. -/
theorem fiveToSix_zetaFirst_B3_equality_epsilon_next_literal_rows68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S w:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hw:w=2*(3*N-2*S)) (hw1S:w+1<S)
    (hrow0:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S (w+1))
    (hrow2:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S (w+1)):
    FiveToSixCuspZetaFirstB3EqualityEpsilonNextRowZeroScalar68
        gamma epsilon A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityEpsilonNextRowTwoScalar68
        gamma epsilon A B c d e N S:=by
  let K0:=7*N-2*S-2
  let K2:=5*N-2*S-2
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hidx0:13*N-2*G-S-(S+(w+1))-1=K0:=by
    rw [heq,hw]
    dsimp only [K0]
    omega
  have hidx2:11*N-2*G-S-(S+(w+1))-1=K2:=by
    rw [heq,hw]
    dsimp only [K2]
    omega
  have h0ABd:(A*B^2*derivative d).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0ABBd:(A*B*derivative B*d).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0Bce:(B*c*derivative e).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0Bdd:(B*d*derivative d).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0Bd2:(derivative B*d^2).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0ccd:(c*derivative c*d).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0BAc:(B*derivative A*c).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0Be:(B*derivative e).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0dc:(d*derivative c).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0dA:(d*derivative A).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h2B2d:(B^2*derivative d).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2BBd:(B*derivative B*d).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2Bc:(B*derivative c).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2cB:(c*derivative B).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2d:(derivative d).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68] at hrow0
  rw [hidx0] at hrow0
  simp only [secondaryResidualRowZeroPolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt h0ABd,
    coeff_eq_zero_of_natDegree_lt h0ABBd,
    coeff_eq_zero_of_natDegree_lt h0Bce,
    coeff_eq_zero_of_natDegree_lt h0Bdd,
    coeff_eq_zero_of_natDegree_lt h0Bd2,
    coeff_eq_zero_of_natDegree_lt h0ccd,
    coeff_eq_zero_of_natDegree_lt h0BAc,
    coeff_eq_zero_of_natDegree_lt h0Be,
    coeff_eq_zero_of_natDegree_lt h0dc,
    coeff_eq_zero_of_natDegree_lt h0dA,
    mul_zero,add_zero,sub_zero] at hrow0
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68] at hrow2
  rw [hidx2] at hrow2
  simp only [secondaryResidualRowTwoPolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt h2B2d,
    coeff_eq_zero_of_natDegree_lt h2BBd,
    coeff_eq_zero_of_natDegree_lt h2Bc,
    coeff_eq_zero_of_natDegree_lt h2cB,
    coeff_eq_zero_of_natDegree_lt h2d,
    mul_zero,add_zero,sub_zero] at hrow2
  constructor
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityEpsilonNextRowZeroScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,K0]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow0
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityEpsilonNextRowTwoScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,K2]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow2

/-- The literal next rows contract by the reusable determinant lemma. -/
theorem fiveToSix_zetaFirst_B3_equality_epsilon_next_contracted68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ)
    (hN:0<N) (hA:A.natDegree≤2*N) (ha:A.coeff (2*N)≠0)
    (hD:1<3*N-2*S)
    (hstate:
      let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
        (3/4*epsilon:k)•B
      let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
      Fce.natDegree≤3*N-2*S-1 ∧ J.natDegree≤5*N-2*S-1)
    (hrows:FiveToSixCuspZetaFirstB3EqualityEpsilonNextRowZeroScalar68
        gamma epsilon A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityEpsilonNextRowTwoScalar68
        gamma epsilon A B c d e N S):
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
    Fce.natDegree≤3*N-2*S-2 ∧ J.natDegree≤5*N-2*S-2:=by
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let D:=3*N-2*S-1
  let j:=5*N-2*S-1
  let K0:=7*N-2*S-2
  let K2:=5*N-2*S-2
  change Fce.natDegree≤D ∧ J.natDegree≤j at hstate
  have hfactor:=fiveToSix_zetaFirst_B3_equality_epsilon_load_factor68
    (k:=k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  have hrow0:=hrows.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualityEpsilonNextRowZeroScalar68]
    at hrow0
  have hrow0':(A*derivative A*Fce-derivative A*J).coeff K0=0:=by
    rw [←hfactor.1]
    simpa only [coeff_add,coeff_smul,smul_eq_mul] using hrow0
  have hrow2:=hrows.2
  dsimp only [FiveToSixCuspZetaFirstB3EqualityEpsilonNextRowTwoScalar68]
    at hrow2
  have hrow2':(-(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
      (6:k)•derivative J).coeff K2=0:=by
    rw [←hfactor.2]
    simpa only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul] using hrow2
  have hdrop:=fiveToSix_zetaFirst_B3_equality_twoRow_edge_drop68
    A Fce J N D j K0 K2 hN (by dsimp only [D];omega)
      (by dsimp only [j];omega) hA ha hstate.1 hstate.2
      (by dsimp only [D,K0];omega) (by dsimp only [j,K0];omega)
      (by dsimp only [D,K2];omega) (by dsimp only [j,K2];omega)
      (by dsimp only [D,j];omega) hrow0' hrow2'
  change Fce.natDegree≤3*N-2*S-2 ∧ J.natDegree≤5*N-2*S-2
  exact hdrop

def FiveToSixCuspZetaFirstB3EqualityEpsilonSupportWallPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualityEpsilonContractedPacket68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S ∧
    let w:=2*(3*N-2*S)
    w+1=S ∧
      FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
        gamma epsilon A B c d e N G S S (w+1) ∧
      FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
        gamma epsilon A B c d e N G S S (w+1)

def FiveToSixCuspZetaFirstB3EqualityEpsilonNextContractedPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualityEpsilonContractedPacket68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S ∧
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
    Fce.natDegree≤3*N-2*S-2 ∧ J.natDegree≤5*N-2*S-2

theorem fiveToSix_zetaFirst_endpoint_B3_equality_epsilonNext_or_residual68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    4*N-G≤S ∨
      (FiveToSixCuspZetaFirstB3EqualityNextPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S ∧ 4*N-3*S=1) ∨
      (FiveToSixCuspZetaFirstB3EqualityNextTwoPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S ∧
        (4*N-3*S=2 ∨ 3*N-2*S=1)) ∨
      FiveToSixCuspZetaFirstB3EqualityEpsilonSupportWallPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S ∨
      FiveToSixCuspZetaFirstB3EqualityEpsilonNextContractedPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_epsilonContracted_or_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hwallOne|hsmall|hcur
  · exact Or.inl hGamma
  · exact Or.inr (Or.inl hwallOne)
  · exact Or.inr (Or.inr (Or.inl hsmall))
  · right;right;right
    rcases hcur with ⟨hstop,hstate⟩
    have hcurCopy:FiveToSixCuspZetaFirstB3EqualityEpsilonContractedPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S:=
      ⟨hstop,hstate⟩
    rcases hstop with ⟨hterminal,hJold,hrowOld0,hrowOld2⟩
    rcases hterminal with ⟨hgamma,hY⟩
    rcases hgamma with ⟨hgammaStop,hcontract⟩
    rcases hgammaStop with ⟨hnext,ha,hjet,hgammaRow0,hgammaRow2⟩
    rcases hnext.1 with ⟨hGS,hcell,hprev⟩
    have hs:=hcell.1.1.1.1
    have hp:=hs
    change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
        e.natDegree≤6*N-G-S ∧
        FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
          A B c d e N G S ∧ _ at hp
    rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
    rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
    let w:=2*(3*N-2*S)
    have hwS:w<S:=by dsimp only [w];omega
    have hrpos:0<13*N-2*G-S-(S+(w+1))-1:=by dsimp only [w];omega
    have hrow0:=fiveToSix_zetaFirst_equality_uniform_source_rowZero68
      alpha gamma epsilon zeta eta terminal A B c d e N G S (w+1) hs hrpos
    have hrow2:=fiveToSix_zetaFirst_loaded_uniform_rowTwo68
      alpha gamma epsilon zeta eta terminal A B c d e N G S S (w+1) hs
    by_cases hwall:w+1=S
    · exact Or.inl ⟨hcurCopy,hwall,hrow0,hrow2⟩
    · right
      have hw1S:w+1<S:=by omega
      have hlit:=fiveToSix_zetaFirst_B3_equality_epsilon_next_literal_rows68
        alpha gamma epsilon zeta eta terminal A B c d e N G S w hs hGS
        (by rfl) hw1S hrow0 hrow2
      have hD:1<3*N-2*S:=by omega
      have hdrop:=fiveToSix_zetaFirst_B3_equality_epsilon_next_contracted68
        gamma epsilon A B c d e N S hN hA hatop hD hstate hlit
      exact ⟨hcurCopy,hdrop⟩

#print axioms fiveToSix_zetaFirst_B3_equality_twoRow_edge_drop68
#print axioms fiveToSix_zetaFirst_B3_equality_epsilon_next_literal_rows68
#print axioms fiveToSix_zetaFirst_B3_equality_epsilon_next_contracted68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_epsilonNext_or_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonNext68

end Max11DegreeRoutes
