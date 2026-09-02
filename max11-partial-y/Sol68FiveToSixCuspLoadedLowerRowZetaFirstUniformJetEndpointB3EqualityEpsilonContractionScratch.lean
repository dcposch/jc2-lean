import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityCompensatedStoppingScratch

/-! # The coincident epsilon/B equality wall

At `w=2*(3*N-2*S)`, the row-zero loads `A*B*A'` and the row-two
loads `A'*B`, `A*B'` occur for the first time.  They are exactly the
derivative expansion of `(3/4*epsilon) B`, so the two rows remain the
same triangular `J` equation after replacing the compensated I4
remainder by `Fc+(3/4*epsilon) B`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonContraction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualityEpsilonRowZeroScalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=7*N-2*S-1
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e).coeff K+
      (3/2*gamma:k)*(A*derivative A*d).coeff K+
      (3/4*epsilon:k)*(A*B*derivative A).coeff K=0

def FiveToSixCuspZetaFirstB3EqualityEpsilonRowTwoScalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=5*N-2*S-1
  (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff K-
      (9*gamma:k)*(A*derivative d).coeff K+
      (9/2*gamma:k)*(d*derivative A).coeff K+
      (9/4*epsilon:k)*(derivative A*B).coeff K-
      (9/2*epsilon:k)*(A*derivative B).coeff K=0

/-- Small exact load identity: both coincident epsilon loads are absorbed
by the same compensated I4 polynomial. -/
theorem fiveToSix_zetaFirst_B3_equality_epsilon_load_factor68
    (gamma epsilon:k) (A B c d e:k[X]):
    let F:=(B*e+c*d)-(1/9:k)•B^3
    let Fce:=F+(3/2*gamma:k)•d+(3/4*epsilon:k)•B
    let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
    FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
          (3/2*gamma:k)•(A*derivative A*d)+
          (3/4*epsilon:k)•(A*B*derivative A)=
        A*derivative A*Fce-derivative A*J ∧
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
          (9*gamma:k)•(A*derivative d)+
          (9/2*gamma:k)•(d*derivative A)+
          (9/4*epsilon:k)•(derivative A*B)-
          (9/2*epsilon:k)•(A*derivative B)=
        -(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
          (6:k)•derivative J:=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Fce:=F+(3/2*gamma:k)•d+(3/4*epsilon:k)•B
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let J:=Q-(3:k)•(d*e)
  have hbase0:
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e=
        A*derivative A*F-derivative A*J:=by
    rw [fiveToSix_zetaFirst_B3_endpoint_rowZero_core_factor68
      (k:=k) A B c d e]
    change A*derivative A*F+derivative A*(-Q+(3:k)•(d*e))=
      A*derivative A*F-derivative A*J
    have hminus:-Q+(3:k)•(d*e)=-J:=by
      dsimp only [J]
      module
    rw [hminus,mul_neg]
    simp only [sub_eq_add_neg]
  have hbase2:
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e=
        -(6:k)•(A*derivative F)+(3:k)•(derivative A*F)+
          (6:k)•derivative J:=by
    dsimp only [F,Q,J]
    rw [fiveToSix_zetaFirst_B3_endpoint_rowTwo_core_factor68
      (k:=k) A B c d e]
    simp only [derivative_sub,derivative_smul,derivative_mul,mul_sub,
      mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_sub,smul_add,
      smul_smul,mul_assoc]
    module
  constructor
  · rw [hbase0]
    simp only [mul_add,mul_smul_comm,smul_mul_assoc,smul_add,smul_sub]
    rw [show A*B*derivative A=A*derivative A*B by ring]
    module
  · rw [hbase2]
    simp only [derivative_add,derivative_smul,mul_add,mul_smul_comm,
      smul_mul_assoc,smul_add,smul_sub,smul_smul]
    rw [show d*derivative A=derivative A*d by ring]
    module

/-- Literal reduction of the two full source rows at the first epsilon/B
wall. -/
theorem fiveToSix_zetaFirst_B3_equality_epsilon_literal_rows68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S w:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hw:w=2*(3*N-2*S)) (hwS:w<S)
    (hrow0:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S w)
    (hrow2:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S w):
    FiveToSixCuspZetaFirstB3EqualityEpsilonRowZeroScalar68
        gamma epsilon A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityEpsilonRowTwoScalar68
        gamma epsilon A B c d e N S:=by
  let K0:=7*N-2*S-1
  let K2:=5*N-2*S-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hidx0:13*N-2*G-S-(S+w)-1=K0:=by
    rw [heq,hw]
    dsimp only [K0]
    omega
  have hidx2:11*N-2*G-S-(S+w)-1=K2:=by
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
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityEpsilonRowZeroScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,K0]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow0
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityEpsilonRowTwoScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,K2]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow2

/-- Division-free contraction of the exact epsilon/B wall.  Row zero and
row two give the same next `J` edge. -/
theorem fiveToSix_zetaFirst_B3_equality_epsilon_contracted68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ)
    (hN:0<N) (hA:A.natDegree≤2*N) (ha:A.coeff (2*N)≠0)
    (hD:0<3*N-2*S)
    (hFce:
      let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
        (3/4*epsilon:k)•B
      Fce.natDegree≤3*N-2*S)
    (hJ:
      let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
      J.natDegree≤5*N-2*S)
    (hrows:FiveToSixCuspZetaFirstB3EqualityEpsilonRowZeroScalar68
        gamma epsilon A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityEpsilonRowTwoScalar68
        gamma epsilon A B c d e N S):
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
    Fce.natDegree≤3*N-2*S-1 ∧ J.natDegree≤5*N-2*S-1:=by
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let D:=3*N-2*S
  let j:=5*N-2*S
  let K0:=7*N-2*S-1
  let K2:=5*N-2*S-1
  change Fce.natDegree≤3*N-2*S at hFce
  change J.natDegree≤j at hJ
  have hjpos:0<j:=by dsimp only [D,j] at hD ⊢;omega
  have hdA:=natDegree_derivative_le A
  have hdAsharp:(derivative A).natDegree≤2*N-1:=by omega
  have hAAFce:=coeff_mul_mul_derivative_at_bounds68 A Fce A
    (2*N) D (2*N) (by omega) hA hFce hA
  rw [show 2*N+D+2*N-1=K0 by dsimp only [D,K0];omega] at hAAFce
  have hAJ:=coeff_mul_at_bounds68 (derivative A) J (2*N-1) j
    hdAsharp hJ
  rw [show (2*N-1)+j=K0 by dsimp only [j,K0];omega] at hAJ
  have hAtop:=coeff_derivative_at_bound68 A (2*N) (by omega)
  have hAFce:=coeff_mul_derivative_at_bounds68 A Fce (2*N) D hD hA hFce
  rw [show 2*N+D-1=K2 by dsimp only [D,K2];omega] at hAFce
  have hA'Fce:=coeff_mul_at_bounds68 (derivative A) Fce (2*N-1) D
    hdAsharp hFce
  rw [show (2*N-1)+D=K2 by dsimp only [D,K2];omega] at hA'Fce
  have hJder:=coeff_derivative_at_bound68 J j hjpos
  rw [show j-1=K2 by rfl] at hJder
  have hfactor:=fiveToSix_zetaFirst_B3_equality_epsilon_load_factor68
    (k:=k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  have hzero0:=hrows.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualityEpsilonRowZeroScalar68]
    at hzero0
  have hpoly0:(FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
        (3/2*gamma:k)•(A*derivative A*d)+
        (3/4*epsilon:k)•(A*B*derivative A)).coeff K0=0:=by
    simpa only [coeff_add,coeff_smul,smul_eq_mul] using hzero0
  rw [hfactor.1,coeff_sub,
    hAJ,hAtop] at hpoly0
  have hAAFce':(A*derivative A*Fce).coeff K0=
      A.coeff (2*N)^2*Fce.coeff D*((2*N:ℕ):k):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm,pow_two] using hAAFce
  rw [hAAFce'] at hpoly0
  have hfac:A.coeff (2*N)*((2*N:ℕ):k)≠0:=by
    exact mul_ne_zero ha (by exact_mod_cast (show 2*N≠0 by omega))
  have htri0:A.coeff (2*N)*Fce.coeff D-J.coeff j=0:=by
    apply (mul_eq_zero.mp ?_).resolve_left hfac
    linear_combination hpoly0
  have hzero2:=hrows.2
  dsimp only [FiveToSixCuspZetaFirstB3EqualityEpsilonRowTwoScalar68]
    at hzero2
  have hpoly2:(FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
        (9*gamma:k)•(A*derivative d)+
        (9/2*gamma:k)•(d*derivative A)+
        (9/4*epsilon:k)•(derivative A*B)-
        (9/2*epsilon:k)•(A*derivative B)).coeff K2=0:=by
    simpa only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul] using hzero2
  rw [hfactor.2] at hpoly2
  change (-(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
      (6:k)•derivative J).coeff K2=0 at hpoly2
  simp only [coeff_add,coeff_smul,smul_eq_mul,hAFce,hA'Fce,hAtop,hJder]
    at hpoly2
  have htri2:A.coeff (2*N)*Fce.coeff D*
        (-((D:ℕ):k)+((N:ℕ):k))+((j:ℕ):k)*J.coeff j=0:=by
    push_cast at hpoly2 ⊢
    linear_combination (1/6:k)*hpoly2
  have hcoef:-((D:ℕ):k)+((N:ℕ):k)+((j:ℕ):k)=((3*N:ℕ):k):=by
    have harith:D+3*N=N+j:=by dsimp only [D,j];omega
    have harithk:=congrArg (fun t:ℕ=>(t:k)) harith
    push_cast at harithk ⊢
    linear_combination -harithk
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
  change Fce.natDegree≤3*N-2*S-1 ∧ J.natDegree≤5*N-2*S-1
  exact ⟨natDegree_le_pred hFce hFceZero,natDegree_le_pred hJ hJzero⟩

def FiveToSixCuspZetaFirstB3EqualityEpsilonContractedPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualityEpsilonStoppingPacket68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S ∧
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
    Fce.natDegree≤3*N-2*S-1 ∧ J.natDegree≤5*N-2*S-1

/-- Full source backwire.  All nonordinary side cells are carried without
change. -/
theorem fiveToSix_zetaFirst_endpoint_B3_equality_epsilonContracted_or_residual68
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
      FiveToSixCuspZetaFirstB3EqualityEpsilonContractedPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_epsilonStopping_or_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hwallOne|hsmall|hstop
  · exact Or.inl hGamma
  · exact Or.inr (Or.inl hwallOne)
  · exact Or.inr (Or.inr (Or.inl hsmall))
  · right;right;right
    have hstopCopy:=hstop
    rcases hstop with ⟨hterminal,hJstate,hrow0,hrow2⟩
    rcases hterminal with ⟨hgamma,hY⟩
    rcases hgamma with ⟨hgammaStop,hcontract⟩
    rcases hgammaStop with ⟨hnext,ha,hstate,hgammaRow0,hgammaRow2⟩
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
    have hlit:=fiveToSix_zetaFirst_B3_equality_epsilon_literal_rows68
      alpha gamma epsilon zeta eta terminal A B c d e N G S w hs hGS
      (by rfl) hwS hrow0 hrow2
    have hc:=hcontract
    dsimp only [FiveToSixCuspZetaFirstB3EqualityTerminalGammaContracted68]
      at hc
    let Fc:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d
    let Fce:=Fc+(3/4*epsilon:k)•B
    have hFc:Fc.natDegree≤3*N-2*S:=by
      change Fc.natDegree≤3*N-2*S
      exact hc.1
    have hB':B.natDegree≤3*N-2*S:=by
      convert hB using 1 <;> omega
    have hFce:Fce.natDegree≤3*N-2*S:=by
      dsimp only [Fce]
      compute_degree
      exact max_le hFc hB'
    have hJ:=hJstate
    dsimp only [FiveToSixCuspZetaFirstB3EqualityJState68] at hJ
    change ((B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)).natDegree≤
      11*N-6*S-(2*(3*N-2*S)-1)-1 at hJ
    have hJ':
        let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
        J.natDegree≤5*N-2*S:=by
      change ((B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)).natDegree≤
        5*N-2*S
      convert hJ using 1 <;> omega
    have hdrop:=fiveToSix_zetaFirst_B3_equality_epsilon_contracted68
      gamma epsilon A B c d e N S hN hA hatop (by omega) hFce hJ' hlit
    exact ⟨hstopCopy,hdrop⟩

#print axioms fiveToSix_zetaFirst_B3_equality_epsilon_load_factor68
#print axioms fiveToSix_zetaFirst_B3_equality_epsilon_literal_rows68
#print axioms fiveToSix_zetaFirst_B3_equality_epsilon_contracted68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_epsilonContracted_or_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonContraction68

end Max11DegreeRoutes
