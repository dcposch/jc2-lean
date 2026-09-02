import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNextTwoScratch

/-! # Finite stopping on the equality B3 endpoint

On `G=2*S` the row-zero/row-two triangular contraction is uniform.  Before
the gamma depth `a=4*N-3*S`, all discarded terms are below the two source
indices.  The contraction therefore lowers the `F` and `J` degree bounds at
every depth.  Since `a<S` and `a<2*(3*N-2*S)`, the first unavoidable wall is
the literal gamma-loaded coefficient at depth `S+a`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityFiniteStopping68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualityJetState68
    (A B c d e:k[X]) (N S m:ℕ):Prop:=
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let J:=Q-(3:k)•(d*e)
  F.natDegree≤9*N-6*S-m-1 ∧ J.natDegree≤11*N-6*S-m-1

def FiveToSixCuspZetaFirstB3EqualityUniformRowZeroScalar68
    (A B c d e:k[X]) (N S m:ℕ):Prop:=
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e).coeff
    (13*N-6*S-m-1)=0

def FiveToSixCuspZetaFirstB3EqualityUniformRowTwoScalar68
    (A B c d e:k[X]) (N S m:ℕ):Prop:=
  (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff
    (11*N-6*S-m-1)=0

/-- The positive constant-RHS row-zero adapter is valid at every requested
equality depth whose literal coefficient index is positive. -/
theorem fiveToSix_zetaFirst_equality_uniform_source_rowZero68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S m:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hrpos:0<13*N-2*G-S-(S+m)-1):
    FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S m:=by
  let R:=7*N-2*G
  let mu:=min S (R-S)
  let ridx:=13*N-2*G-S-(S+m)-1
  have hp:=hs
  change 0<S ∧ S<R ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S<S ∧ mu=R-S ∧ zeta=0 ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hrow:=hpos ridx (by dsimp only [ridx];exact hrpos)
  rw [coeff_add,cubicLoadRowZeroPolynomial68_uniform_pinned_eq68,hz] at hrow
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,zero_mul,
    mul_zero,zero_smul,add_zero] at hrow
  change FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
    gamma epsilon A B c d e N G S S m
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68,ridx]
  dsimp only [ridx] at hrow
  linear_combination hrow

/-- Uniform support reduction before all three possible equality loads:
the `S` support wall, the gamma wall, and the epsilon/B wall. -/
theorem fiveToSix_zetaFirst_B3_equality_uniform_literal_rows68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S m:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hmS:m<S) (hmGamma:m<4*N-3*S)
    (hmEpsilon:m<2*(3*N-2*S))
    (hrow0:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S m)
    (hrow2:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S m):
    FiveToSixCuspZetaFirstB3EqualityUniformRowZeroScalar68
        A B c d e N S m ∧
      FiveToSixCuspZetaFirstB3EqualityUniformRowTwoScalar68
        A B c d e N S m:=by
  let K0:=13*N-6*S-m-1
  let K2:=11*N-6*S-m-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
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
  have h0AAd:(A*derivative A*d).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0dc:(d*derivative c).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0dA:(d*derivative A).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h2B2d:(B^2*derivative d).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2BBd:(B*derivative B*d).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2Ad:(A*derivative d).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2Bc:(B*derivative c).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2cB:(c*derivative B).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2dA:(d*derivative A).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2AB1:(derivative A*B).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2AB2:(A*derivative B).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  have h2d:(derivative d).natDegree<K2:=by
    dsimp only [K2];compute_degree;omega
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68] at hrow0
  rw [show 13*N-2*G-S-(S+m)-1=K0 by dsimp only [K0];omega] at hrow0
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
    coeff_eq_zero_of_natDegree_lt h0AAd,
    coeff_eq_zero_of_natDegree_lt h0dc,
    coeff_eq_zero_of_natDegree_lt h0dA,
    mul_zero,add_zero,sub_zero] at hrow0
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68] at hrow2
  rw [show 11*N-2*G-S-(S+m)-1=K2 by dsimp only [K2];omega] at hrow2
  simp only [secondaryResidualRowTwoPolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt h2B2d,
    coeff_eq_zero_of_natDegree_lt h2BBd,
    coeff_eq_zero_of_natDegree_lt h2Ad,
    coeff_eq_zero_of_natDegree_lt h2Bc,
    coeff_eq_zero_of_natDegree_lt h2cB,
    coeff_eq_zero_of_natDegree_lt h2dA,
    coeff_eq_zero_of_natDegree_lt h2AB1,
    coeff_eq_zero_of_natDegree_lt h2AB2,
    coeff_eq_zero_of_natDegree_lt h2d,
    mul_zero,add_zero,sub_zero] at hrow2
  constructor
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityUniformRowZeroScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,K0]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow0
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityUniformRowTwoScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,K2]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow2

/-- One uniform triangular step.  Its premise is precisely the degree state
left by the preceding depth. -/
theorem fiveToSix_zetaFirst_B3_equality_uniform_step68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S m:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq : G = 2*S) (hm : 0 < m) (hmGamma : m < 4*N-3*S)
    (hstate:
      let F:=(B*e+c*d)-(1/9:k)•B^3
      let Q:=B*c^2-(1/9:k)•(A*B^3)
      let J:=Q-(3:k)•(d*e)
      F.natDegree≤9*N-6*S-m ∧ J.natDegree≤11*N-6*S-m)
    (hrows:FiveToSixCuspZetaFirstB3EqualityUniformRowZeroScalar68
        A B c d e N S m ∧
      FiveToSixCuspZetaFirstB3EqualityUniformRowTwoScalar68
        A B c d e N S m):
    FiveToSixCuspZetaFirstB3EqualityJetState68 A B c d e N S m:=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let J:=Q-(3:k)•(d*e)
  let f:=9*N-6*S-m
  let j:=11*N-6*S-m
  let K0:=13*N-6*S-m-1
  let K2:=11*N-6*S-m-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  change F.natDegree≤f ∧ J.natDegree≤j at hstate
  have hfpos:0<f:=by dsimp only [f];omega
  have hjpos:0<j:=by dsimp only [j];omega
  have hdA:=natDegree_derivative_le A
  have hdAsharp:(derivative A).natDegree≤2*N-1:=by omega
  have hAF:=coeff_mul_derivative_at_bounds68 A F (2*N) f hfpos
    hA hstate.1
  rw [show 2*N+f-1=K2 by dsimp only [f,K2];omega] at hAF
  have hA'F:=coeff_mul_at_bounds68 (derivative A) F (2*N-1) f
    hdAsharp hstate.1
  rw [show (2*N-1)+f=K2 by dsimp only [f,K2];omega] at hA'F
  have hAJ:=coeff_mul_at_bounds68 (derivative A) J (2*N-1) j
    hdAsharp hstate.2
  rw [show (2*N-1)+j=K0 by dsimp only [j,K0];omega] at hAJ
  have hAAF:=coeff_mul_mul_derivative_at_bounds68 A F A (2*N) f (2*N)
    (by omega) hA hstate.1 hA
  rw [show 2*N+f+2*N-1=K0 by dsimp only [f,K0];omega] at hAAF
  have hAtop:=coeff_derivative_at_bound68 A (2*N) (by omega)
  have hJder:=coeff_derivative_at_bound68 J j hjpos
  rw [show j-1=K2 by rfl] at hJder
  have hcore0:=hrows.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualityUniformRowZeroScalar68]
    at hcore0
  rw [fiveToSix_zetaFirst_B3_endpoint_rowZero_core_factor68
      (k:=k) A B c d e] at hcore0
  change (A*derivative A*F+derivative A*(-Q+(3:k)•(d*e))).coeff K0=0
    at hcore0
  have hminus:-Q+(3:k)•(d*e)=-J:=by dsimp only [J];module
  rw [hminus,coeff_add] at hcore0
  have hAAF':(A*derivative A*F).coeff K0=
      A.coeff (2*N)^2*F.coeff f*((2*N:ℕ):k):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm,pow_two] using hAAF
  have hAJ':(derivative A*(-J)).coeff K0=
      -(A.coeff (2*N)*((2*N:ℕ):k)*J.coeff j):=by
    rw [mul_neg,coeff_neg,hAJ,hAtop]
  rw [hAAF',hAJ'] at hcore0
  have hfac:A.coeff (2*N)*((2*N:ℕ):k)≠0:=by
    exact mul_ne_zero ha (by exact_mod_cast (show 2*N≠0 by omega))
  have hFJ:A.coeff (2*N)*F.coeff f-J.coeff j=0:=by
    apply (mul_eq_zero.mp ?_).resolve_left hfac
    linear_combination hcore0
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
  dsimp only [FiveToSixCuspZetaFirstB3EqualityUniformRowTwoScalar68]
    at hcore2
  change (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68
    A B c d e).coeff K2=0 at hcore2
  rw [hfactor2] at hcore2
  simp only [coeff_add,coeff_smul,smul_eq_mul,hAF,hA'F,hAtop,hJder] at hcore2
  have hnext:A.coeff (2*N)*F.coeff f*
      (-((f:ℕ):k)+((N:ℕ):k))+((j:ℕ):k)*J.coeff j=0:=by
    push_cast at hcore2 ⊢
    linear_combination (1/6:k)*hcore2
  have hsumNat:N+j=f+3*N:=by dsimp only [j,f];omega
  have hsum:-((f:ℕ):k)+((N:ℕ):k)+((j:ℕ):k)=((3*N:ℕ):k):=by
    have hc:=congrArg (fun n:ℕ↦(n:k)) hsumNat
    push_cast at hc ⊢
    linear_combination hc
  have hNcast:((3*N:ℕ):k)≠0:=by
    exact_mod_cast (show 3*N≠0 by omega)
  have hprod:((3*N:ℕ):k)*(A.coeff (2*N)*F.coeff f)=0:=by
    calc
      _ = A.coeff (2*N)*F.coeff f*
          (-((f:ℕ):k)+((N:ℕ):k)+((j:ℕ):k)):=by rw [hsum];ring
      _ = 0:=by linear_combination hnext+((j:ℕ):k)*hFJ
  have haF:A.coeff (2*N)*F.coeff f=0:=
    (mul_eq_zero.mp hprod).resolve_left hNcast
  have hFzero:F.coeff f=0:=(mul_eq_zero.mp haF).resolve_left ha
  have hJzero:J.coeff j=0:=by
    have hh:=hFJ
    rw [hFzero,mul_zero,zero_sub] at hh
    exact neg_eq_zero.mp hh
  change F.natDegree≤9*N-6*S-m-1 ∧ J.natDegree≤11*N-6*S-m-1
  constructor
  · exact natDegree_le_pred hstate.1 hFzero
  · exact natDegree_le_pred hstate.2 hJzero

/-- The verified first equality jet and endpoint scalar give the induction
base after depth one. -/
theorem fiveToSix_zetaFirst_B3_equality_state_one68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hGamma:S<4*N-G)
    (hend:FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68
      A B c d e N G S)
    (hprev:FiveToSixCuspZetaFirstB3EqualityNextContracted68
      gamma A B c d e N S):
    FiveToSixCuspZetaFirstB3EqualityJetState68 A B c d e N S 1:=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let J:=Q-(3:k)•(d*e)
  let fU:=9*N-6*S-1
  let T:=11*N-6*S
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hi4:=fiveToSix_zetaFirst_endpoint_B3_I4_packet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs
    (by omega) hGamma
  dsimp only [FiveToSixCuspZetaFirstEndpointB3I4Packet68] at hi4
  have hF:F.natDegree≤fU:=by
    dsimp only [F,fU]
    convert hi4.1 using 1 <;> omega
  have hQ:Q.natDegree≤T:=by dsimp only [Q,T];compute_degree;omega
  have hde:(d*e).natDegree≤T:=by dsimp only [T];compute_degree;omega
  have hJ:J.natDegree≤T:=by dsimp only [J];compute_degree;omega
  dsimp only [FiveToSixCuspZetaFirstB3EqualityNextContracted68] at hprev
  change F.coeff fU=0 ∧ J.coeff (T-1)=0 at hprev
  have hJtop:J.coeff T=0:=by
    dsimp only [FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68,
      FixedReflectedJet68] at hend
    have ht0:2*S-G=0:=by omega
    have hb:11*N-3*G=T:=by dsimp only [T];omega
    rw [ht0,coeff_reflect,revAt_zero,hb] at hend
    have hdetop:=coeff_mul_at_bounds68 d e (5*N-G-S) (6*N-G-S) hd he
    rw [show (5*N-G-S)+(6*N-G-S)=T by dsimp only [T];omega] at hdetop
    dsimp only [J]
    simp only [coeff_sub,coeff_smul,smul_eq_mul]
    rw [hdetop]
    linear_combination hend
  have hFdrop:=natDegree_le_pred hF hprev.1
  have hJone:=natDegree_le_pred hJ hJtop
  have hJdrop:=natDegree_le_pred hJone hprev.2
  change F.natDegree≤9*N-6*S-1-1 ∧ J.natDegree≤11*N-6*S-1-1
  exact ⟨hFdrop,hJdrop⟩

/-- Pure finite induction: a uniform step from depth `m-1` to `m` cannot
continue forever before a fixed positive terminal depth `a`. -/
theorem fiveToSix_zetaFirst_B3_equality_finite_induction68
    (A B c d e:k[X]) (N S a:ℕ)
    (ha:2<a)
    (hbase:FiveToSixCuspZetaFirstB3EqualityJetState68 A B c d e N S 1)
    (hstep:∀ m : ℕ, 2 ≤ m → m < a →
      FiveToSixCuspZetaFirstB3EqualityJetState68 A B c d e N S (m-1)→
      FiveToSixCuspZetaFirstB3EqualityJetState68 A B c d e N S m):
    FiveToSixCuspZetaFirstB3EqualityJetState68 A B c d e N S (a-1):=by
  have hind:∀ t : ℕ, 1+t<a →
      FiveToSixCuspZetaFirstB3EqualityJetState68 A B c d e N S (1+t):=by
    intro t
    induction t with
    | zero =>
        intro hlt
        simpa using hbase
    | succ t ih =>
        intro hlt
        have hp:1+t<a:=by omega
        have ht:=ih hp
        apply hstep (1+(t+1)) (by omega) hlt
        convert ht using 1 <;> omega
  have hh:=hind (a-2) (by omega)
  convert hh using 1 <;> omega

def FiveToSixCuspZetaFirstB3EqualityFiniteStoppingPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualityNextTwoPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧
    let a:=4*N-3*S
    2<a ∧
      FiveToSixCuspZetaFirstB3EqualityJetState68 A B c d e N S (a-1) ∧
      FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
        gamma epsilon A B c d e N G S S a ∧
      FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
        gamma epsilon A B c d e N G S S a

/-- Source-facing finite stopping.  The ordinary equality chamber reaches
the exact gamma-loaded row at `a=4*N-3*S`; all smaller equality loads and the
gamma-active sibling remain literal alternatives. -/
theorem fiveToSix_zetaFirst_endpoint_B3_equality_finiteStopping_or_residual68
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
      FiveToSixCuspZetaFirstB3EqualityFiniteStoppingPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_nextTwo_or_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hwall|hnext
  · exact Or.inl hGamma
  · exact Or.inr (Or.inl hwall)
  · rcases hnext.2 with hgammaTwo|hepsilonOne|hordinary
    · exact Or.inr (Or.inr (Or.inl ⟨hnext,Or.inl hgammaTwo.1⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hnext,Or.inr hepsilonOne.1⟩))
    · right;right;right
      let a:=4*N-3*S
      rcases hnext.1 with ⟨hGS,hcell,hprevBranch⟩
      rcases hprevBranch with hwallImpossible|hprevOrdinary
      · omega
      · rcases hprevOrdinary with ⟨hgap,hprev⟩
        rcases hordinary with ⟨ha,hb,hcurrent⟩
        have hbasePacket:=hcell.1.1.1
        rcases hbasePacket with
          ⟨hs,hBc,hGammaLt,q,hmuq,hqS,hprior,hminimal,hload,
            hi3,hi4,hend⟩
        have hstateOne:=fiveToSix_zetaFirst_B3_equality_state_one68
          alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS
          hGammaLt hend hprev
        have hp:=hs
        change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
            e.natDegree≤6*N-G-S ∧
            FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta
              terminal A B c d e N G S ∧ _ at hp
        rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
        rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
        have haS:a<S:=by dsimp only [a];omega
        have haE:a<2*(3*N-2*S):=by dsimp only [a];omega
        have hstep:∀ m : ℕ, 2 ≤ m → m < a →
            FiveToSixCuspZetaFirstB3EqualityJetState68 A B c d e N S (m-1)→
            FiveToSixCuspZetaFirstB3EqualityJetState68 A B c d e N S m:=by
          intro m hm2 hma hstate
          have hmS:m<S:=hma.trans haS
          have hmE:m<2*(3*N-2*S):=hma.trans haE
          have hrpos:0<13*N-2*G-S-(S+m)-1:=by omega
          have hrow0:=fiveToSix_zetaFirst_equality_uniform_source_rowZero68
            alpha gamma epsilon zeta eta terminal A B c d e N G S m hs hrpos
          have hrow2:=fiveToSix_zetaFirst_loaded_uniform_rowTwo68
            alpha gamma epsilon zeta eta terminal A B c d e N G S S m hs
          have hlit:=fiveToSix_zetaFirst_B3_equality_uniform_literal_rows68
            alpha gamma epsilon zeta eta terminal A B c d e N G S m hs hGS
            hmS hma hmE hrow0 hrow2
          have hst:=hstate
          dsimp only [FiveToSixCuspZetaFirstB3EqualityJetState68] at hst
          have hfidx:9*N-6*S-(m-1)-1=9*N-6*S-m:=by omega
          have hjidx:11*N-6*S-(m-1)-1=11*N-6*S-m:=by omega
          rw [hfidx,hjidx] at hst
          exact fiveToSix_zetaFirst_B3_equality_uniform_step68
            alpha gamma epsilon zeta eta terminal A B c d e N G S m hs hGS
            (by omega) hma hst hlit
        have hterminal:=fiveToSix_zetaFirst_B3_equality_finite_induction68
          A B c d e N S a ha hstateOne hstep
        have hrpos:0<13*N-2*G-S-(S+a)-1:=by dsimp only [a];omega
        have hrow0:=fiveToSix_zetaFirst_equality_uniform_source_rowZero68
          alpha gamma epsilon zeta eta terminal A B c d e N G S a hs hrpos
        have hrow2:=fiveToSix_zetaFirst_loaded_uniform_rowTwo68
          alpha gamma epsilon zeta eta terminal A B c d e N G S S a hs
        exact ⟨hnext,ha,hterminal,hrow0,hrow2⟩

#print axioms fiveToSix_zetaFirst_equality_uniform_source_rowZero68
#print axioms fiveToSix_zetaFirst_B3_equality_uniform_literal_rows68
#print axioms fiveToSix_zetaFirst_B3_equality_uniform_step68
#print axioms fiveToSix_zetaFirst_B3_equality_state_one68
#print axioms fiveToSix_zetaFirst_B3_equality_finite_induction68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_finiteStopping_or_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityFiniteStopping68

end Max11DegreeRoutes
