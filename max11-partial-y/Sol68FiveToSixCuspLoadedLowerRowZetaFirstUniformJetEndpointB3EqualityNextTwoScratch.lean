import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNextScratch

/-! # The second coefficient beyond the equality B3 endpoint

The ordinary equality cell already has the top `F` edge and first lower
`J=Q-3*d*e` edge equal to zero.  At depth `S+2`, the same row-zero/row-two
triangular pair kills the next two edges unless either the gamma-d threshold
`4*N-3*S=2` or the epsilon-B threshold `3*N-2*S=1` fires.  Both loaded
walls retain their complete literal source equations.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNextTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem fiveToSix_zetaFirst_equality_nextTwo_source_rowZero68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S):
    FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S 2:=by
  let R:=7*N-2*G
  let mu:=min S (R-S)
  let ridx:=13*N-2*G-S-(S+2)-1
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
    gamma epsilon A B c d e N G S S 2
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68,ridx]
  dsimp only [ridx] at hrow
  linear_combination hrow

def FiveToSixCuspZetaFirstB3EqualityNextTwoRowTwoScalar68
    (A B c d e:k[X]) (N S:ℕ):Prop:=
  (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff
    (11*N-6*S-3)=0

def FiveToSixCuspZetaFirstB3EqualityNextTwoRowZeroScalar68
    (A B c d e:k[X]) (N S:ℕ):Prop:=
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e).coeff
    (13*N-6*S-3)=0

theorem fiveToSix_zetaFirst_B3_equality_nextTwo_literal_rows68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hgamma:2<4*N-3*S) (hepsilon:1<3*N-2*S)
    (hrow0:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S 2)
    (hrow2:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S 2):
    FiveToSixCuspZetaFirstB3EqualityNextTwoRowZeroScalar68 A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityNextTwoRowTwoScalar68
        A B c d e N S:=by
  let K0:=13*N-6*S-3
  let K2:=11*N-6*S-3
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
  rw [show 13*N-2*G-S-(S+2)-1=K0 by dsimp only [K0];omega] at hrow0
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
  rw [show 11*N-2*G-S-(S+2)-1=K2 by dsimp only [K2];omega] at hrow2
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
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityNextTwoRowZeroScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,K0]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow0
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityNextTwoRowTwoScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,K2]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow2

def FiveToSixCuspZetaFirstB3EqualityNextTwoContracted68
    (A B c d e:k[X]) (N S:ℕ):Prop:=
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let J:=Q-(3:k)•(d*e)
  F.coeff (9*N-6*S-2)=0 ∧ J.coeff (11*N-6*S-2)=0

theorem fiveToSix_zetaFirst_B3_equality_nextTwo_contracted68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hGamma:S<4*N-G)
    (hend:FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68
      A B c d e N G S)
    (hprev:FiveToSixCuspZetaFirstB3EqualityNextContracted68
      gamma A B c d e N S)
    (hrows:FiveToSixCuspZetaFirstB3EqualityNextTwoRowZeroScalar68
        A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityNextTwoRowTwoScalar68 A B c d e N S):
    FiveToSixCuspZetaFirstB3EqualityNextTwoContracted68 A B c d e N S:=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let J:=Q-(3:k)•(d*e)
  let fU:=9*N-6*S-1
  let T:=11*N-6*S
  let f1:=fU-1
  let j2:=T-2
  let K0:=13*N-6*S-3
  let K2:=11*N-6*S-3
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
  dsimp only [FiveToSixCuspZetaFirstB3EqualityNextContracted68] at hprev
  change F.coeff fU=0 ∧ J.coeff (T-1)=0 at hprev
  have hFdrop:F.natDegree≤f1:=by
    dsimp only [f1]
    exact natDegree_le_pred hF hprev.1
  have hQ:Q.natDegree≤T:=by dsimp only [Q,T];compute_degree;omega
  have hde:(d*e).natDegree≤T:=by dsimp only [T];compute_degree;omega
  have hJ:J.natDegree≤T:=by dsimp only [J];compute_degree;omega
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
  have hJone:J.natDegree≤T-1:=natDegree_le_pred hJ hJtop
  have hJdrop:J.natDegree≤j2:=by
    dsimp only [j2]
    exact natDegree_le_pred hJone hprev.2
  have hdA:=natDegree_derivative_le A
  have hdAsharp:(derivative A).natDegree≤2*N-1:=by omega
  have hfpos:0<f1:=by dsimp only [f1,fU];omega
  have hjpos:0<j2:=by dsimp only [j2,T];omega
  have hAF:=coeff_mul_derivative_at_bounds68 A F (2*N) f1 hfpos hA hFdrop
  rw [show 2*N+f1-1=K2 by dsimp only [f1,fU,K2];omega] at hAF
  have hA'F:=coeff_mul_at_bounds68 (derivative A) F (2*N-1) f1
    hdAsharp hFdrop
  rw [show (2*N-1)+f1=K2 by dsimp only [f1,fU,K2];omega] at hA'F
  have hAJ:=coeff_mul_at_bounds68 (derivative A) J (2*N-1) j2
    hdAsharp hJdrop
  rw [show (2*N-1)+j2=K0 by dsimp only [j2,T,K0];omega] at hAJ
  have hAAF:=coeff_mul_mul_derivative_at_bounds68 A F A (2*N) f1 (2*N)
    (by omega) hA hFdrop hA
  rw [show 2*N+f1+2*N-1=K0 by dsimp only [f1,fU,K0];omega] at hAAF
  have hAtop:=coeff_derivative_at_bound68 A (2*N) (by omega)
  have hJder:=coeff_derivative_at_bound68 J j2 hjpos
  rw [show j2-1=K2 by dsimp only [j2,T,K2];omega] at hJder
  have hcore0:=hrows.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualityNextTwoRowZeroScalar68] at hcore0
  rw [fiveToSix_zetaFirst_B3_endpoint_rowZero_core_factor68
      (k:=k) A B c d e] at hcore0
  change (A*derivative A*F+derivative A*(-Q+(3:k)•(d*e))).coeff K0=0
    at hcore0
  have hminus:-Q+(3:k)•(d*e)=-J:=by dsimp only [J];module
  rw [hminus,coeff_add] at hcore0
  have hAAF':(A*derivative A*F).coeff K0=
      A.coeff (2*N)^2*F.coeff f1*((2*N:ℕ):k):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm,pow_two] using hAAF
  have hAJ':(derivative A*(-J)).coeff K0=
      -(A.coeff (2*N)*((2*N:ℕ):k)*J.coeff j2):=by
    rw [mul_neg,coeff_neg,hAJ,hAtop]
  rw [hAAF',hAJ'] at hcore0
  have hfac:A.coeff (2*N)*((2*N:ℕ):k)≠0:=by
    exact mul_ne_zero ha (by exact_mod_cast (show 2*N≠0 by omega))
  have hFJ:A.coeff (2*N)*F.coeff f1-J.coeff j2=0:=by
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
  change (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68
    A B c d e).coeff K2=0 at hcore2
  rw [hfactor2] at hcore2
  simp only [coeff_add,coeff_smul,smul_eq_mul,hAF,hA'F,hAtop,hJder] at hcore2
  have hnext:A.coeff (2*N)*F.coeff f1*
      (-((f1:ℕ):k)+((N:ℕ):k))+((j2:ℕ):k)*J.coeff j2=0:=by
    push_cast at hcore2 ⊢
    linear_combination (1/6:k)*hcore2
  have hsumNat:N+j2=f1+3*N:=by dsimp only [j2,T,f1,fU];omega
  have hsum:-((f1:ℕ):k)+((N:ℕ):k)+((j2:ℕ):k)=((3*N:ℕ):k):=by
    have hc:=congrArg (fun n:ℕ↦(n:k)) hsumNat
    push_cast at hc ⊢
    linear_combination hc
  have hNcast:((3*N:ℕ):k)≠0:=by
    exact_mod_cast (show 3*N≠0 by omega)
  have hprod:((3*N:ℕ):k)*(A.coeff (2*N)*F.coeff f1)=0:=by
    calc
      _ = A.coeff (2*N)*F.coeff f1*
          (-((f1:ℕ):k)+((N:ℕ):k)+((j2:ℕ):k)):=by rw [hsum];ring
      _ = 0:=by linear_combination hnext+((j2:ℕ):k)*hFJ
  have haF:A.coeff (2*N)*F.coeff f1=0:=
    (mul_eq_zero.mp hprod).resolve_left hNcast
  have hFzero:F.coeff f1=0:=(mul_eq_zero.mp haF).resolve_left ha
  have hJzero:J.coeff j2=0:=by
    have hh:=hFJ
    rw [hFzero,mul_zero,zero_sub] at hh
    exact neg_eq_zero.mp hh
  change F.coeff (9*N-6*S-2)=0 ∧ J.coeff (11*N-6*S-2)=0
  constructor
  · dsimp only [f1,fU] at hFzero
    simpa only [Nat.sub_sub,one_add_one_eq_two] using hFzero
  · dsimp only [j2,T] at hJzero
    exact hJzero

def FiveToSixCuspZetaFirstB3EqualityNextTwoPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualityNextPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧
    let hrow0:=FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S 2
    let hrow2:=FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S 2
    ((4*N-3*S=2 ∧ hrow0 ∧ hrow2) ∨
      (3*N-2*S=1 ∧ hrow0 ∧ hrow2) ∨
      (2<4*N-3*S ∧ 1<3*N-2*S ∧
        FiveToSixCuspZetaFirstB3EqualityNextTwoContracted68 A B c d e N S))

theorem fiveToSix_zetaFirst_endpoint_B3_equality_nextTwo_or_residual68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    4*N-G≤S ∨
      (FiveToSixCuspZetaFirstB3EqualityNextPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S ∧ 4*N-3*S=1) ∨
      FiveToSixCuspZetaFirstB3EqualityNextTwoPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_next_or_gamma68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|heq
  · exact Or.inl hGamma
  · rcases heq.2.2 with hwall|hordinary
    · exact Or.inr (Or.inl ⟨heq,hwall.1⟩)
    · right;right
      rcases heq with ⟨hGS,hcell,hprev⟩
      rcases hordinary with ⟨hgap,hcontract⟩
      have hs:=hcell.1.1.1.1
      have hrow0:=fiveToSix_zetaFirst_equality_nextTwo_source_rowZero68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS
      have hrow2:=fiveToSix_zetaFirst_loaded_uniform_rowTwo68
        alpha gamma epsilon zeta eta terminal A B c d e N G S S 2 hs
      have hbase:=hcell.1.1.1
      rcases hbase with ⟨hs',hBc,hGammaLt,q,hmuq,hqS,hprior,hminimal,hload,
        hi3,hi4,hend⟩
      by_cases hgammaWall:4*N-3*S=2
      · exact ⟨⟨hGS,hcell,Or.inr ⟨hgap,hcontract⟩⟩,
          Or.inl ⟨hgammaWall,hrow0,hrow2⟩⟩
      · by_cases hepsilonWall:3*N-2*S=1
        · exact ⟨⟨hGS,hcell,Or.inr ⟨hgap,hcontract⟩⟩,
            Or.inr (Or.inl ⟨hepsilonWall,hrow0,hrow2⟩)⟩
        · have hgamma:2<4*N-3*S:=by omega
          have hepsilon:1<3*N-2*S:=by omega
          have hlit:=fiveToSix_zetaFirst_B3_equality_nextTwo_literal_rows68
            alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS
            hgamma hepsilon hrow0 hrow2
          have hnext:=fiveToSix_zetaFirst_B3_equality_nextTwo_contracted68
            alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS
            hGammaLt hend hcontract hlit
          exact ⟨⟨hGS,hcell,Or.inr ⟨hgap,hcontract⟩⟩,
            Or.inr (Or.inr ⟨hgamma,hepsilon,hnext⟩)⟩

#print axioms fiveToSix_zetaFirst_equality_nextTwo_source_rowZero68
#print axioms fiveToSix_zetaFirst_B3_equality_nextTwo_literal_rows68
#print axioms fiveToSix_zetaFirst_B3_equality_nextTwo_contracted68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_nextTwo_or_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNextTwo68

end Max11DegreeRoutes
