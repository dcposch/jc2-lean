import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3StrictClosureScratch

/-! # The first coefficient beyond the equality B3 endpoint

On `G=2*S`, the endpoint row zero is dependent.  The literal source rows
at depth `S+1` are nevertheless available: row two is a zero-RHS identity,
and row zero has a positive index.  Contracting them together kills both
the first I4-remainder edge and the first lower jet of `Q-3*d*e`.  On the
only coincident I4 load, `4*N-3*S=1`, this also forces `gamma=0`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact positive row-zero source coefficient at the first depth beyond
the bounded endpoint. -/
theorem fiveToSix_zetaFirst_equality_next_source_rowZero68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S):
    FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S 1:=by
  let R:=7*N-2*G
  let mu:=min S (R-S)
  let ridx:=13*N-2*G-S-(S+1)-1
  have hp:=hs
  change 0<S ∧ S<R ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S<S ∧ mu=R-S ∧ zeta=0 ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hrpos:0<ridx:=by dsimp only [ridx];omega
  have hrow:=hpos ridx hrpos
  rw [coeff_add,cubicLoadRowZeroPolynomial68_uniform_pinned_eq68,hz] at hrow
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,zero_mul,
    mul_zero,zero_smul,add_zero] at hrow
  change FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
    gamma epsilon A B c d e N G S S 1
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68,ridx]
  dsimp only [ridx] at hrow
  linear_combination hrow

def FiveToSixCuspZetaFirstB3EqualityNextRowTwoScalar68
    (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=11*N-6*S-2
  (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff K=0

def FiveToSixCuspZetaFirstB3EqualityNextRowZeroScalar68
    (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=13*N-6*S-2
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e).coeff K=0

/-- Literal support reductions of the two `S+1` source rows. -/
theorem fiveToSix_zetaFirst_B3_equality_next_literal_rows68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S)
    (hgap:1<4*N-3*S)
    (hrow0:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S 1)
    (hrow2:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S 1):
    FiveToSixCuspZetaFirstB3EqualityNextRowZeroScalar68 A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityNextRowTwoScalar68 A B c d e N S:=by
  let K0:=13*N-6*S-2
  let K2:=11*N-6*S-2
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
  simp only [Nat.add_one] at hrow0
  rw [show 13*N-2*G-S-(S+1)-1=K0 by dsimp only [K0];omega] at hrow0
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
  simp only [Nat.add_one] at hrow2
  rw [show 11*N-2*G-S-(S+1)-1=K2 by dsimp only [K2];omega] at hrow2
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
  · change FiveToSixCuspZetaFirstB3EqualityNextRowZeroScalar68
      A B c d e N S
    dsimp only [FiveToSixCuspZetaFirstB3EqualityNextRowZeroScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,K0]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow0
  · change FiveToSixCuspZetaFirstB3EqualityNextRowTwoScalar68
      A B c d e N S
    dsimp only [FiveToSixCuspZetaFirstB3EqualityNextRowTwoScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,K2]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow2

/-- Exact contracted gain at depth `S+1`. -/
def FiveToSixCuspZetaFirstB3EqualityNextContracted68
    (gamma:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let J:=Q-(3:k)•(d*e)
  let fU:=9*N-6*S-1
  let T:=11*N-6*S
  F.coeff fU=0 ∧ J.coeff (T-1)=0

theorem fiveToSix_zetaFirst_B3_equality_next_contracted68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S)
    (hGamma:S<4*N-G) (hgap:1<4*N-3*S)
    (hend:FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68
      A B c d e N G S)
    (hrows:FiveToSixCuspZetaFirstB3EqualityNextRowZeroScalar68
        A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityNextRowTwoScalar68 A B c d e N S):
    FiveToSixCuspZetaFirstB3EqualityNextContracted68
      gamma A B c d e N S:=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let J:=Q-(3:k)•(d*e)
  let fU:=9*N-6*S-1
  let T:=11*N-6*S
  let K0:=13*N-6*S-2
  let K2:=11*N-6*S-2
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
  have hFraw:=hi4.1
  have hF:F.natDegree≤fU:=by
    dsimp only [F,fU]
    convert hFraw using 1 <;> omega
  have hQ:Q.natDegree≤T:=by
    dsimp only [Q,T]
    compute_degree
    omega
  have hde:(d*e).natDegree≤T:=by
    dsimp only [T]
    compute_degree
    omega
  have hJ:J.natDegree≤T:=by
    dsimp only [J]
    compute_degree
    omega
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68]
    at hend
  have hdetop:=coeff_mul_at_bounds68 d e (5*N-G-S) (6*N-G-S) hd he
  rw [show (5*N-G-S)+(6*N-G-S)=T by dsimp only [T];omega] at hdetop
  have hJtop:J.coeff T=0:=by
    dsimp only [J]
    simp only [coeff_sub,coeff_smul,smul_eq_mul]
    dsimp only [FixedReflectedJet68] at hend
    have ht0:2*S-G=0:=by omega
    have hbound:11*N-3*G=T:=by dsimp only [T];omega
    rw [ht0,coeff_reflect,revAt_zero,hbound] at hend
    change Q.coeff T=3*d.coeff (5*N-G-S)*e.coeff (6*N-G-S) at hend
    rw [hdetop]
    linear_combination hend
  have hJdrop:J.natDegree≤T-1:=natDegree_le_pred hJ hJtop
  have hdA:=natDegree_derivative_le A
  have hdAsharp:(derivative A).natDegree≤2*N-1:=by omega
  have hfpos:0<fU:=by dsimp only [fU];omega
  have hTpos:0<T-1:=by dsimp only [T];omega
  have hAF:=coeff_mul_derivative_at_bounds68 A F (2*N) fU hfpos hA hF
  rw [show 2*N+fU-1=K2 by dsimp only [fU,K2];omega] at hAF
  have hA'F:=coeff_mul_at_bounds68 (derivative A) F (2*N-1) fU
    hdAsharp hF
  rw [show (2*N-1)+fU=K2 by dsimp only [fU,K2];omega] at hA'F
  have hAJ:=coeff_mul_at_bounds68 (derivative A) J (2*N-1) (T-1)
    hdAsharp hJdrop
  rw [show (2*N-1)+(T-1)=K0 by dsimp only [T,K0];omega] at hAJ
  have hAAF:=coeff_mul_mul_derivative_at_bounds68 A F A (2*N) fU (2*N)
    (by omega) hA hF hA
  rw [show 2*N+fU+2*N-1=K0 by dsimp only [fU,K0];omega] at hAAF
  have hAtop:=coeff_derivative_at_bound68 A (2*N) (by omega)
  have hJder:=coeff_derivative_at_bound68 J (T-1) hTpos
  rw [show T-1-1=K2 by dsimp only [T,K2];omega] at hJder
  have hcore0:=hrows.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualityNextRowZeroScalar68] at hcore0
  rw [fiveToSix_zetaFirst_B3_endpoint_rowZero_core_factor68
      (k:=k) A B c d e] at hcore0
  change (A*derivative A*F+derivative A*(-Q+(3:k)•(d*e))).coeff K0=0
    at hcore0
  have hminus:-Q+(3:k)•(d*e)=-J:=by dsimp only [J];module
  rw [hminus,coeff_add] at hcore0
  have hAAF':(A*derivative A*F).coeff K0=
      A.coeff (2*N)^2*F.coeff fU*((2*N:ℕ):k):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm,pow_two] using hAAF
  have hAJ':(derivative A*(-J)).coeff K0=
      -(A.coeff (2*N)*((2*N:ℕ):k)*J.coeff (T-1)):=by
    rw [mul_neg,coeff_neg,hAJ,hAtop]
  rw [hAAF',hAJ'] at hcore0
  have hfac: A.coeff (2*N)*((2*N:ℕ):k)≠0:=by
    exact mul_ne_zero ha (by exact_mod_cast (show 2*N≠0 by omega))
  have hFJ:A.coeff (2*N)*F.coeff fU-J.coeff (T-1)=0:=by
    apply (mul_eq_zero.mp ?_).resolve_left hfac
    linear_combination hcore0
  have hcore2:=hrows.2
  change (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68
    A B c d e).coeff K2=0 at hcore2
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
  rw [hfactor2] at hcore2
  simp only [coeff_add,coeff_smul,smul_eq_mul,hAF,hA'F,hAtop,hJder] at hcore2
  have hnext:
      A.coeff (2*N)*F.coeff fU*(-((fU:ℕ):k)+((N:ℕ):k))+
        ((T-1:ℕ):k)*J.coeff (T-1)=0:=by
    push_cast at hcore2 ⊢
    linear_combination (1/6:k)*hcore2
  have hFzero:F.coeff fU=0:=by
    have hNcast:((3*N:ℕ):k)≠0:=by
      exact_mod_cast (show 3*N≠0 by omega)
    have hsumNat:N+(T-1)=fU+3*N:=by dsimp only [T,fU];omega
    have hsum:-((fU:ℕ):k)+((N:ℕ):k)+((T-1:ℕ):k)=((3*N:ℕ):k):=by
      have hc:=congrArg (fun n:ℕ↦(n:k)) hsumNat
      push_cast at hc ⊢
      linear_combination hc
    have hprod:((3*N:ℕ):k)*(A.coeff (2*N)*F.coeff fU)=0:=by
      calc
        _ = A.coeff (2*N)*F.coeff fU*
            (-((fU:ℕ):k)+((N:ℕ):k)+((T-1:ℕ):k)):=by rw [hsum];ring
        _ = 0:=by linear_combination hnext+((T-1:ℕ):k)*hFJ
    have haF:A.coeff (2*N)*F.coeff fU=0:=
      (mul_eq_zero.mp hprod).resolve_left hNcast
    exact (mul_eq_zero.mp haF).resolve_left ha
  have hJzero:J.coeff (T-1)=0:=by
    have hh:=hFJ
    rw [hFzero,mul_zero,zero_sub] at hh
    exact neg_eq_zero.mp hh
  exact ⟨hFzero,hJzero⟩

def FiveToSixCuspZetaFirstB3EqualityNextPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  G=2*S ∧
    FiveToSixCuspZetaFirstB3EndpointCellSplitPacket68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S ∧
    ((4*N-3*S=1 ∧
        FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
          gamma epsilon A B c d e N G S S 1 ∧
        FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
          gamma epsilon A B c d e N G S S 1) ∨
      (1<4*N-3*S ∧
        FiveToSixCuspZetaFirstB3EqualityNextContracted68
          gamma A B c d e N S))

theorem fiveToSix_zetaFirst_endpoint_B3_equality_next_or_gamma68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    4*N-G≤S ∨ FiveToSixCuspZetaFirstB3EqualityNextPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_or_gamma68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|heq
  · exact Or.inl hGamma
  · right
    rcases heq with ⟨hGS,hcell⟩
    have hs:=hcell.1.1.1.1
    have hrow0:=fiveToSix_zetaFirst_equality_next_source_rowZero68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS
    have hrow2:=fiveToSix_zetaFirst_loaded_uniform_rowTwo68
      alpha gamma epsilon zeta eta terminal A B c d e N G S S 1 hs
    have hbase:=hcell.1.1.1
    rcases hbase with ⟨hs',hBc,hGamma,q,hmuq,hqS,hprior,hminimal,hload,
      hi3,hi4,hend⟩
    by_cases hwall:4*N-3*S=1
    · exact ⟨hGS,hcell,Or.inl ⟨hwall,hrow0,hrow2⟩⟩
    · have hgap:1<4*N-3*S:=by omega
      have hlit:=fiveToSix_zetaFirst_B3_equality_next_literal_rows68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS hgap
        hrow0 hrow2
      have hcontract:=fiveToSix_zetaFirst_B3_equality_next_contracted68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS
        hGamma hgap hend hlit
      exact ⟨hGS,hcell,Or.inr ⟨hgap,hcontract⟩⟩

#print axioms fiveToSix_zetaFirst_equality_next_source_rowZero68
#print axioms fiveToSix_zetaFirst_B3_equality_next_literal_rows68
#print axioms fiveToSix_zetaFirst_B3_equality_next_contracted68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_next_or_gamma68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNext68

end Max11DegreeRoutes
