import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityTerminalRowOneScratch

/-! # Compensated equality descent to the epsilon/B wall

Beyond the gamma wall the I4-compensated remainder is already below both
lower-row indices.  Row zero and row two therefore kill the same successive
`J` edge until the exact epsilon/B threshold `m=2*(3*N-2*S)`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityCompensatedStopping68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualityCompensatedRowZeroScalar68
    (gamma:k) (A B c d e:k[X]) (N S m:ℕ):Prop:=
  let K:=13*N-6*S-m-1
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e).coeff K+
    (3/2*gamma:k)*(A*derivative A*d).coeff K=0

def FiveToSixCuspZetaFirstB3EqualityCompensatedRowTwoScalar68
    (gamma:k) (A B c d e:k[X]) (N S m:ℕ):Prop:=
  let K:=11*N-6*S-m-1
  (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff K-
      (9*gamma:k)*(A*derivative d).coeff K+
      (9/2*gamma:k)*(d*derivative A).coeff K=0

def FiveToSixCuspZetaFirstB3EqualityJState68
    (A B c d e:k[X]) (N S m:ℕ):Prop:=
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  J.natDegree≤11*N-6*S-m-1

/-- Literal compensated pair before the epsilon/B threshold. -/
theorem fiveToSix_zetaFirst_B3_equality_compensated_literal_rows68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S m:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hmS:m<S) (hmE:m<2*(3*N-2*S))
    (hrow0:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S m)
    (hrow2:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S m):
    FiveToSixCuspZetaFirstB3EqualityCompensatedRowZeroScalar68
        gamma A B c d e N S m ∧
      FiveToSixCuspZetaFirstB3EqualityCompensatedRowTwoScalar68
        gamma A B c d e N S m:=by
  let K0:=13*N-6*S-m-1
  let K2:=11*N-6*S-m-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hidx0:13*N-2*G-S-(S+m)-1=K0:=by
    rw [heq]
    dsimp only [K0]
    omega
  have hidx2:11*N-2*G-S-(S+m)-1=K2:=by
    rw [heq]
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
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityCompensatedRowZeroScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,K0]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow0
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityCompensatedRowTwoScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,K2]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow2

/-- Both compensated rows independently kill the next `J` edge. -/
theorem fiveToSix_zetaFirst_B3_equality_compensated_step68
    (gamma:k) (A B c d e:k[X]) (N S m:ℕ)
    (hN:0<N) (hA:A.natDegree≤2*N) (ha:A.coeff (2*N)≠0)
    (hFc:
      let Fc:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d
      Fc.natDegree≤3*N-2*S)
    (hJ:
      let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
      J.natDegree≤11*N-6*S-m)
    (hm: m<2*(3*N-2*S))
    (hrows:FiveToSixCuspZetaFirstB3EqualityCompensatedRowZeroScalar68
        gamma A B c d e N S m ∧
      FiveToSixCuspZetaFirstB3EqualityCompensatedRowTwoScalar68
        gamma A B c d e N S m):
    FiveToSixCuspZetaFirstB3EqualityJState68 A B c d e N S m:=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Fc:=F+(3/2*gamma:k)•d
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let J:=Q-(3:k)•(d*e)
  let j:=11*N-6*S-m
  let K0:=13*N-6*S-m-1
  let K2:=11*N-6*S-m-1
  change Fc.natDegree≤3*N-2*S at hFc
  change J.natDegree≤j at hJ
  have hjpos:0<j:=by dsimp only [j];omega
  have hdA:=natDegree_derivative_le A
  have hdAsharp:(derivative A).natDegree≤2*N-1:=by omega
  have hFc0:(A*derivative A*Fc).natDegree<K0:=by
    dsimp only [K0]
    compute_degree
    omega
  have hFc2a:(A*derivative Fc).natDegree<K2:=by
    dsimp only [K2]
    compute_degree
    omega
  have hFc2b:(derivative A*Fc).natDegree<K2:=by
    dsimp only [K2]
    compute_degree
    omega
  have hAJ:=coeff_mul_at_bounds68 (derivative A) J (2*N-1) j
    hdAsharp hJ
  rw [show (2*N-1)+j=K0 by dsimp only [j,K0];omega] at hAJ
  have hAtop:=coeff_derivative_at_bound68 A (2*N) (by omega)
  have hJder:=coeff_derivative_at_bound68 J j hjpos
  rw [show j-1=K2 by rfl] at hJder
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
  have hfactor0:
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
          (3/2*gamma:k)•(A*derivative A*d)=
        A*derivative A*Fc-derivative A*J:=by
    rw [hbase0]
    dsimp only [Fc]
    simp only [mul_add,mul_smul_comm,smul_mul_assoc,smul_add,smul_sub]
    module
  have hzero0:FiveToSixCuspZetaFirstB3EqualityCompensatedRowZeroScalar68
      gamma A B c d e N S m:=hrows.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualityCompensatedRowZeroScalar68]
    at hzero0
  have hpoly0:(FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
      (3/2*gamma:k)•(A*derivative A*d)).coeff K0=0:=by
    simpa only [coeff_add,coeff_smul,smul_eq_mul] using hzero0
  rw [hfactor0,coeff_sub,
    coeff_eq_zero_of_natDegree_lt hFc0,zero_sub,hAJ,hAtop] at hpoly0
  have hJzero0:J.coeff j=0:=by
    have hfac:A.coeff (2*N)*((2*N:ℕ):k)≠0:=by
      exact mul_ne_zero ha (by exact_mod_cast (show 2*N≠0 by omega))
    apply (mul_eq_zero.mp ?_).resolve_left hfac
    linear_combination -hpoly0
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
  have hfactor2:
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
          (9*gamma:k)•(A*derivative d)+
          (9/2*gamma:k)•(d*derivative A)=
        -(6:k)•(A*derivative Fc)+(3:k)•(derivative A*Fc)+
          (6:k)•derivative J:=by
    rw [hbase2]
    dsimp only [Fc]
    simp only [derivative_add,derivative_smul,mul_add,mul_smul_comm,
      smul_mul_assoc,smul_add,smul_sub,smul_smul]
    rw [show d*derivative A=derivative A*d by ring]
    module
  have hzero2:FiveToSixCuspZetaFirstB3EqualityCompensatedRowTwoScalar68
      gamma A B c d e N S m:=hrows.2
  dsimp only [FiveToSixCuspZetaFirstB3EqualityCompensatedRowTwoScalar68]
    at hzero2
  have hpoly2:(FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
      (9*gamma:k)•(A*derivative d)+
      (9/2*gamma:k)•(d*derivative A)).coeff K2=0:=by
    simpa only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul] using hzero2
  rw [hfactor2] at hpoly2
  simp only [coeff_add,coeff_smul,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hFc2a,
    coeff_eq_zero_of_natDegree_lt hFc2b,
    hJder,mul_zero,neg_zero,zero_add] at hpoly2
  have hjcast:((j:ℕ):k)≠0:=by exact_mod_cast (show j≠0 by omega)
  have hJzero2:J.coeff j=0:=by
    apply (mul_eq_zero.mp ?_).resolve_left hjcast
    linear_combination (1/6:k)*hpoly2
  change J.natDegree≤11*N-6*S-m-1
  exact natDegree_le_pred hJ hJzero2

/-- Source-backed finite continuation from the gamma wall to the first
epsilon/B-loaded pair. -/
theorem fiveToSix_zetaFirst_B3_equality_reaches_epsilon68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S a w:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (ha:a=4*N-3*S) (ha2:2<a)
    (hw:w=2*(3*N-2*S))
    (hFc:
      let Fc:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d
      Fc.natDegree≤3*N-2*S)
    (hbase:FiveToSixCuspZetaFirstB3EqualityJState68
      A B c d e N S a):
    FiveToSixCuspZetaFirstB3EqualityJState68 A B c d e N S (w-1) ∧
      FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
        gamma epsilon A B c d e N G S S w ∧
      FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
        gamma epsilon A B c d e N G S S w:=by
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have haw:a<w:=by omega
  have hwS:w<S:=by omega
  have hind:∀t,a+t<w→
      FiveToSixCuspZetaFirstB3EqualityJState68 A B c d e N S (a+t):=by
    intro t
    induction t with
    | zero =>
        intro hlt
        simpa using hbase
    | succ t ih =>
        intro hlt
        have hprev:=ih (by omega)
        let m:=a+(t+1)
        have hmW:m<w:=by dsimp only [m];omega
        have hmS:m<S:=hmW.trans hwS
        have hrpos:0<13*N-2*G-S-(S+m)-1:=by dsimp only [m];omega
        have hrow0:=fiveToSix_zetaFirst_equality_uniform_source_rowZero68
          alpha gamma epsilon zeta eta terminal A B c d e N G S m hs hrpos
        have hrow2:=fiveToSix_zetaFirst_loaded_uniform_rowTwo68
          alpha gamma epsilon zeta eta terminal A B c d e N G S S m hs
        have hlit:=fiveToSix_zetaFirst_B3_equality_compensated_literal_rows68
          alpha gamma epsilon zeta eta terminal A B c d e N G S m hs heq
          hmS (by simpa only [hw] using hmW) hrow0 hrow2
        have hpdeg:=hprev
        dsimp only [FiveToSixCuspZetaFirstB3EqualityJState68] at hpdeg
        have hidx:11*N-6*S-(a+t)-1=11*N-6*S-m:=by
          dsimp only [m]
          omega
        rw [hidx] at hpdeg
        exact fiveToSix_zetaFirst_B3_equality_compensated_step68
          gamma A B c d e N S m hN hA hatop hFc hpdeg
          (by simpa only [hw] using hmW) hlit
  have hlast:=hind (w-a-1) (by omega)
  have hlast':FiveToSixCuspZetaFirstB3EqualityJState68
      A B c d e N S (w-1):=by
    convert hlast using 1 <;> omega
  have hrpos:0<13*N-2*G-S-(S+w)-1:=by omega
  have hrow0:=fiveToSix_zetaFirst_equality_uniform_source_rowZero68
    alpha gamma epsilon zeta eta terminal A B c d e N G S w hs hrpos
  have hrow2:=fiveToSix_zetaFirst_loaded_uniform_rowTwo68
    alpha gamma epsilon zeta eta terminal A B c d e N G S S w hs
  exact ⟨hlast',hrow0,hrow2⟩

def FiveToSixCuspZetaFirstB3EqualityEpsilonStoppingPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualityTerminalRowOnePacket68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S ∧
    let w:=2*(3*N-2*S)
    FiveToSixCuspZetaFirstB3EqualityJState68 A B c d e N S (w-1) ∧
      FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
        gamma epsilon A B c d e N G S S w ∧
      FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
        gamma epsilon A B c d e N G S S w

theorem fiveToSix_zetaFirst_endpoint_B3_equality_epsilonStopping_or_residual68
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
      FiveToSixCuspZetaFirstB3EqualityEpsilonStoppingPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_terminalRowOne_or_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hwallOne|hsmall|hterminal
  · exact Or.inl hGamma
  · exact Or.inr (Or.inl hwallOne)
  · exact Or.inr (Or.inr (Or.inl hsmall))
  · right;right;right
    let a:=4*N-3*S
    let w:=2*(3*N-2*S)
    have hterminalCopy:=hterminal
    rcases hterminal with ⟨hgamma,hY⟩
    rcases hgamma with ⟨hstop,hcontract⟩
    rcases hstop with ⟨hnext,ha,hstate,hrow0,hrow2⟩
    rcases hnext.1 with ⟨hGS,hcell,hprev⟩
    have hs:=hcell.1.1.1.1
    have hc:=hcontract
    dsimp only [FiveToSixCuspZetaFirstB3EqualityTerminalGammaContracted68]
      at hc
    have hFc:=hc.1
    have hJbase:FiveToSixCuspZetaFirstB3EqualityJState68
        A B c d e N S a:=by
      dsimp only [FiveToSixCuspZetaFirstB3EqualityJState68]
      convert hc.2 using 1 <;> dsimp only [a] <;> omega
    have hreach:=fiveToSix_zetaFirst_B3_equality_reaches_epsilon68
      alpha gamma epsilon zeta eta terminal A B c d e N G S a w hs hGS
      (by rfl) ha (by rfl) hFc hJbase
    exact ⟨hterminalCopy,hreach.1,hreach.2.1,hreach.2.2⟩

#print axioms fiveToSix_zetaFirst_B3_equality_compensated_literal_rows68
#print axioms fiveToSix_zetaFirst_B3_equality_compensated_step68
#print axioms fiveToSix_zetaFirst_B3_equality_reaches_epsilon68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_epsilonStopping_or_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityCompensatedStopping68

end Max11DegreeRoutes
