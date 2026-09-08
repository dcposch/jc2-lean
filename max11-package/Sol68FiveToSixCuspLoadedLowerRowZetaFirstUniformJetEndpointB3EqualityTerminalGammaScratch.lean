import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityFiniteStoppingScratch

/-! # The terminal gamma-loaded equality coefficient

At `G=2*S` and `a=4*N-3*S`, row zero retains exactly `A*A'*d`,
while row two retains exactly `A*d'` and `d*A'`.  The compensated I4
identity absorbs this load.  Row zero then kills the terminal edge of
`J= B*c^2-(1/9)A*B^3-3*d*e`; row two records the same compatibility.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityTerminalGamma68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualityTerminalGammaRowZeroScalar68
    (gamma:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=9*N-3*S-1
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e).coeff K+
    (3/2*gamma:k)*(A*derivative A*d).coeff K=0

def FiveToSixCuspZetaFirstB3EqualityTerminalGammaRowTwoScalar68
    (gamma:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=7*N-3*S-1
  (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff K-
      (9*gamma:k)*(A*derivative d).coeff K+
      (9/2*gamma:k)*(d*derivative A).coeff K=0

/-- Literal reduction at the first gamma-loaded equality depth. -/
theorem fiveToSix_zetaFirst_B3_equality_terminalGamma_literal_rows68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S a:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (ha:a=4*N-3*S) (ha2:2<a) (haS:a<S)
    (haEpsilon:a<2*(3*N-2*S))
    (hrow0:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S a)
    (hrow2:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S a):
    FiveToSixCuspZetaFirstB3EqualityTerminalGammaRowZeroScalar68
        gamma A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityTerminalGammaRowTwoScalar68
        gamma A B c d e N S:=by
  let K0:=9*N-3*S-1
  let K2:=7*N-3*S-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hidx0:13*N-2*G-S-(S+a)-1=K0:=by
    rw [heq,ha]
    dsimp only [K0]
    omega
  have hidx2:11*N-2*G-S-(S+a)-1=K2:=by
    rw [heq,ha]
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
  have h0ABA:(A*B*derivative A).natDegree<K0:=by
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
  have h2AB1:(derivative A*B).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2AB2:(A*derivative B).natDegree<K2:=by
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
    coeff_eq_zero_of_natDegree_lt h0ABA,
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
    coeff_eq_zero_of_natDegree_lt h2AB1,
    coeff_eq_zero_of_natDegree_lt h2AB2,
    coeff_eq_zero_of_natDegree_lt h2d,
    mul_zero,add_zero,sub_zero] at hrow2
  constructor
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityTerminalGammaRowZeroScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,K0]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow0
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityTerminalGammaRowTwoScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,K2]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow2

def FiveToSixCuspZetaFirstB3EqualityTerminalGammaContracted68
    (gamma:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let Fc:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  Fc.natDegree≤3*N-2*S ∧ J.natDegree≤7*N-3*S-1

/-- The loaded row-zero equation is triangular in the compensated I4
remainder and `J`.  The exact I4 polynomial kills the former edge, hence
the terminal `J` edge vanishes. -/
theorem fiveToSix_zetaFirst_B3_equality_terminalGamma_contracted68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S a:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (ha:a=4*N-3*S) (ha2:2<a)
    (hstate:FiveToSixCuspZetaFirstB3EqualityJetState68
      A B c d e N S (a-1))
    (hrows:FiveToSixCuspZetaFirstB3EqualityTerminalGammaRowZeroScalar68
        gamma A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityTerminalGammaRowTwoScalar68
        gamma A B c d e N S):
    FiveToSixCuspZetaFirstB3EqualityTerminalGammaContracted68
      gamma A B c d e N S:=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Fc:=F+(3/2*gamma:k)•d
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let J:=Q-(3:k)•(d*e)
  let D:=5*N-3*S
  let j:=7*N-3*S
  let bU:=3*N-2*S
  let K0:=9*N-3*S-1
  let K2:=7*N-3*S-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hD:0<D:=by dsimp only [D];omega
  have hbD:bU<D:=by dsimp only [bU,D];omega
  have hstate':=hstate
  dsimp only [FiveToSixCuspZetaFirstB3EqualityJetState68] at hstate'
  change F.natDegree≤9*N-6*S-(a-1)-1 ∧
    J.natDegree≤11*N-6*S-(a-1)-1 at hstate'
  have hfidx:9*N-6*S-(a-1)-1=D:=by dsimp only [D];omega
  have hjidx:11*N-6*S-(a-1)-1=j:=by dsimp only [j];omega
  rw [hfidx,hjidx] at hstate'
  rcases fiveToSix_zetaFirst_sparse_compensatedI4_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
    ⟨i4,hi4⟩
  have hFcEq:Fc=-(3/4*epsilon:k)•B+(3/8:k)•C i4:=by
    dsimp only [Fc,F]
    simp only [neg_smul]
    linear_combination hi4
  have hFc:Fc.natDegree≤bU:=by
    rw [hFcEq]
    dsimp only [bU]
    compute_degree
    omega
  have hFcD:Fc.coeff D=0:=coeff_eq_zero_of_natDegree_lt
    (hFc.trans_lt hbD)
  dsimp only [Fc] at hFcD
  simp only [coeff_add,coeff_smul,smul_eq_mul] at hFcD
  have hdEq:d.natDegree≤D:=by dsimp only [D];convert hd using 1 <;> omega
  have hAAF:=coeff_mul_mul_derivative_at_bounds68 A F A (2*N) D (2*N)
    (by omega) hA hstate'.1 hA
  rw [show 2*N+D+2*N-1=K0 by dsimp only [D,K0];omega] at hAAF
  have hdA:=natDegree_derivative_le A
  have hdAsharp:(derivative A).natDegree≤2*N-1:=by omega
  have hAJ:=coeff_mul_at_bounds68 (derivative A) J (2*N-1) j
    hdAsharp hstate'.2
  rw [show (2*N-1)+j=K0 by dsimp only [j,K0];omega] at hAJ
  have hAAd:=coeff_mul_mul_derivative_at_bounds68 A d A (2*N) D (2*N)
    (by omega) hA hdEq hA
  rw [show 2*N+D+2*N-1=K0 by dsimp only [D,K0];omega] at hAAd
  have hAtop:=coeff_derivative_at_bound68 A (2*N) (by omega)
  have hcore0:=hrows.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualityTerminalGammaRowZeroScalar68]
    at hcore0
  rw [fiveToSix_zetaFirst_B3_endpoint_rowZero_core_factor68
      (k:=k) A B c d e] at hcore0
  change (A*derivative A*F+derivative A*(-Q+(3:k)•(d*e))).coeff K0+
    (3/2*gamma:k)*(A*derivative A*d).coeff K0=0 at hcore0
  have hminus:-Q+(3:k)•(d*e)=-J:=by dsimp only [J];module
  rw [hminus,coeff_add] at hcore0
  have hAAF':(A*derivative A*F).coeff K0=
      A.coeff (2*N)^2*F.coeff D*((2*N:ℕ):k):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm,pow_two] using hAAF
  have hAJ':(derivative A*(-J)).coeff K0=
      -(A.coeff (2*N)*((2*N:ℕ):k)*J.coeff j):=by
    rw [mul_neg,coeff_neg,hAJ,hAtop]
  have hAAd':(A*derivative A*d).coeff K0=
      A.coeff (2*N)^2*d.coeff D*((2*N:ℕ):k):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm,pow_two] using hAAd
  rw [hAAF',hAJ',hAAd'] at hcore0
  have hfac:A.coeff (2*N)*((2*N:ℕ):k)≠0:=by
    exact mul_ne_zero hatop (by exact_mod_cast (show 2*N≠0 by omega))
  have htri:A.coeff (2*N)*F.coeff D-J.coeff j+
      (3/2*gamma:k)*A.coeff (2*N)*d.coeff D=0:=by
    apply (mul_eq_zero.mp ?_).resolve_left hfac
    linear_combination hcore0
  have hJzero0:J.coeff j=0:=by
    linear_combination A.coeff (2*N)*hFcD-htri
  have hAF:=coeff_mul_derivative_at_bounds68 A F (2*N) D hD
    hA hstate'.1
  rw [show 2*N+D-1=K2 by dsimp only [D,K2];omega] at hAF
  have hA'F:=coeff_mul_at_bounds68 (derivative A) F (2*N-1) D
    hdAsharp hstate'.1
  rw [show (2*N-1)+D=K2 by dsimp only [D,K2];omega] at hA'F
  have hJder:=coeff_derivative_at_bound68 J j (by dsimp only [j];omega)
  rw [show j-1=K2 by rfl] at hJder
  have hAd:=coeff_mul_derivative_at_bounds68 A d (2*N) D hD hA hdEq
  rw [show 2*N+D-1=K2 by dsimp only [D,K2];omega] at hAd
  have hdAterm:=coeff_mul_at_bounds68 d (derivative A) D (2*N-1)
    hdEq hdAsharp
  rw [show D+(2*N-1)=K2 by dsimp only [D,K2];omega] at hdAterm
  have hfactor2:FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e=
      -(6:k)•(A*derivative F)+(3:k)•(derivative A*F)+
        (6:k)•derivative J:=by
    dsimp only [F,Q,J]
    rw [fiveToSix_zetaFirst_B3_endpoint_rowTwo_core_factor68
      (k:=k) A B c d e]
    simp only [derivative_sub,derivative_smul,derivative_mul,mul_sub,
      mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_sub,smul_add,
      smul_smul,mul_assoc]
    module
  have hcore2:=hrows.2
  dsimp only [FiveToSixCuspZetaFirstB3EqualityTerminalGammaRowTwoScalar68]
    at hcore2
  change (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff K2-
      (9*gamma:k)*(A*derivative d).coeff K2+
      (9/2*gamma:k)*(d*derivative A).coeff K2=0 at hcore2
  rw [hfactor2] at hcore2
  simp only [coeff_add,coeff_smul,smul_eq_mul,hAF,hA'F,hAtop,hJder,
    hAd,hdAterm] at hcore2
  have htri2:A.coeff (2*N)*F.coeff D*
        (-((D:ℕ):k)+((N:ℕ):k))+((j:ℕ):k)*J.coeff j+
      (3/2*gamma:k)*A.coeff (2*N)*d.coeff D*
        (((N:ℕ):k)-((D:ℕ):k))=0:=by
    push_cast at hcore2 ⊢
    linear_combination (1/6:k)*hcore2
  have hjcast:((j:ℕ):k)≠0:=by
    exact_mod_cast (show j≠0 by dsimp only [j];omega)
  have hJprod:((j:ℕ):k)*J.coeff j=0:=by
    linear_combination htri2-
      A.coeff (2*N)*(((N:ℕ):k)-((D:ℕ):k))*hFcD
  have hJzero2:J.coeff j=0:=(mul_eq_zero.mp hJprod).resolve_left hjcast
  have hJdrop:J.natDegree≤j-1:=natDegree_le_pred hstate'.2 hJzero2
  change Fc.natDegree≤3*N-2*S ∧ J.natDegree≤7*N-3*S-1
  exact ⟨hFc,hJdrop⟩

def FiveToSixCuspZetaFirstB3EqualityTerminalGammaPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualityFiniteStoppingPacket68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S ∧
    FiveToSixCuspZetaFirstB3EqualityTerminalGammaContracted68
      gamma A B c d e N S

theorem fiveToSix_zetaFirst_endpoint_B3_equality_terminalGamma_or_residual68
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
      FiveToSixCuspZetaFirstB3EqualityTerminalGammaPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_finiteStopping_or_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hwallOne|hsmall|hstop
  · exact Or.inl hGamma
  · exact Or.inr (Or.inl hwallOne)
  · exact Or.inr (Or.inr (Or.inl hsmall))
  · right;right;right
    let a:=4*N-3*S
    rcases hstop with ⟨hnext,ha,hstate,hrow0,hrow2⟩
    rcases hnext.1 with ⟨hGS,hcell,hprev⟩
    have hbase:=hcell.1.1.1
    rcases hbase with ⟨hs,hBc,hGammaLt,q,hmuq,hqS,hprior,hminimal,hload,
      hi3,hi4,hend⟩
    have hp:=hs
    change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
        e.natDegree≤6*N-G-S ∧
        FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
          A B c d e N G S ∧ _ at hp
    rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
    rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
    have haS:a<S:=by dsimp only [a];omega
    have haE:a<2*(3*N-2*S):=by dsimp only [a];omega
    have hlit:=fiveToSix_zetaFirst_B3_equality_terminalGamma_literal_rows68
      alpha gamma epsilon zeta eta terminal A B c d e N G S a hs hGS
      (by rfl) ha haS haE hrow0 hrow2
    have hcontract:=fiveToSix_zetaFirst_B3_equality_terminalGamma_contracted68
      alpha gamma epsilon zeta eta terminal A B c d e N G S a hs hGS
      (by rfl) ha hstate hlit
    exact ⟨⟨hnext,ha,hstate,hrow0,hrow2⟩,hcontract⟩

#print axioms fiveToSix_zetaFirst_B3_equality_terminalGamma_literal_rows68
#print axioms fiveToSix_zetaFirst_B3_equality_terminalGamma_contracted68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_terminalGamma_or_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityTerminalGamma68

end Max11DegreeRoutes
