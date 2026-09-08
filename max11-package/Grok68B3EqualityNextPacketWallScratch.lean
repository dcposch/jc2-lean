import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNextScratch

/-! # B3-equality `NextPacket` wall `4N-3S=1`

`FiveToSixCuspZetaFirstB3EqualityNextPacket68` is produced by
`fiveToSix_zetaFirst_endpoint_B3_equality_next_or_gamma68`.  Off the wall
`1<4N-3S` the triangular contraction already kills `F.coeff (9N-6S-1)` and
`J.coeff (11N-6S-1)`.  On the extreme wall `4N-3S=1` those two source
indices coincide with the first `gamma d` load, so the cores retain
`A A' d` / `A d'` / `d A'`.

The compensated I4 identity is nevertheless an equality of polynomials
`Fc := F+(3/2)gamma d = -(3/4)epsilon B + (3/8) C i4`.  Wall arithmetic
gives `deg d = N+1` and `deg B = (N+2)/3`, so `deg Fc ≤ deg B < deg d`.
The `Fc` block therefore lies strictly below both `S+1` source indices
(sparse-endpoint style).  Row two collapses to `J'`, forcing
`J.coeff (11N-6S-1)=0`.  Combined with the endpoint top `J.coeff (11N-6S)=0`
this drops `J` two steps.

The same I4 identity plus a two-case degree comparison of `F` against `d`
records the exact `F` profile: `gamma=0` implies `deg F ≤ deg B`, while
`gamma≠0` implies `deg F = deg d`.  Neither case contradicts the known
leading edges of `A,B,c,d,e`, because `J.coeff (T-1)` mixes unknown
subleadings.  That is the GAP to `False`.

Exact gain: consume the two `S+1` source rows on `4N-3S=1`; replace them
by `deg Fc ≤ 3N-2S` and `deg J ≤ 11N-6S-2`, with the two-case `F`
profile attached.  Next unused row: loaded uniform row one at depth
`S+1` (index `12N-6S-2`).
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNextPacketWall68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Wall arithmetic `4N = 3S+1` -/

/-- Degree dictionary on the wall: `deg B = D = (N+2)/3`, `deg d = V = N+1`,
with `D < V`, `2D < V`, and the `Fc` block strictly below both `S+1`
source indices.  The hypothesis `5N < 4S` is `5N < 2G` after `G=2S`. -/
theorem fiveToSix_nextPacket_wall_degree_arith68
    (N S : ℕ) (hN : 0 < N) (hEq : 4 * N = 3 * S + 1) (hgt : 5 * N < 4 * S) :
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    0 < S ∧ 2 < N ∧ N ≤ S ∧ 0 < D ∧ D < V ∧ 2 * D < V ∧
      V = 9 * N - 6 * S - 1 ∧ 11 * N - 6 * S - 1 = 3 * N + 1 ∧
      13 * N - 6 * S - 2 = 5 * N ∧ 11 * N - 6 * S - 2 = 3 * N ∧
      2 * N + D - 1 < 11 * N - 6 * S - 2 ∧
      (2 * N - 1) + D < 11 * N - 6 * S - 2 ∧
      2 * N + (2 * N - 1) + D < 13 * N - 6 * S - 2 := by
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  change 0 < S ∧ 2 < N ∧ N ≤ S ∧ 0 < D ∧ D < V ∧ 2 * D < V ∧
    V = 9 * N - 6 * S - 1 ∧ 11 * N - 6 * S - 1 = 3 * N + 1 ∧
    13 * N - 6 * S - 2 = 5 * N ∧ 11 * N - 6 * S - 2 = 3 * N ∧
    2 * N + D - 1 < 11 * N - 6 * S - 2 ∧
    (2 * N - 1) + D < 11 * N - 6 * S - 2 ∧
    2 * N + (2 * N - 1) + D < 13 * N - 6 * S - 2
  have hN1 : 3 ∣ N - 1 := by
    have h : N - 1 = 3 * (S - N) := by omega
    exact ⟨S - N, h⟩
  obtain ⟨m, hm⟩ := hN1
  have hNform : N = 3 * m + 1 := by omega
  have hSform : S = 4 * m + 1 := by
    have hmul : 4 * (3 * m + 1) = 3 * S + 1 := by
      rw [← hNform]
      exact hEq
    omega
  have hmpos : 1 < m := by
    have hgt' : 5 * (3 * m + 1) < 4 * (4 * m + 1) := by
      rw [← hNform, ← hSform]
      exact hgt
    omega
  subst hNform
  subst hSform
  dsimp only [D, V]
  omega

/-! ## Ring identities -/

/-- Absorbing the first `gamma d` load into the compensated I4 remainder. -/
theorem fiveToSix_nextPacket_wall_load_factor68
    (gamma:k) (A B c d e:k[X]):
    let F:=(B*e+c*d)-(1/9:k)•B^3
    let Fc:=F+(3/2*gamma:k)•d
    let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
    FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
          (3/2*gamma:k)•(A*derivative A*d)=
        A*derivative A*Fc-derivative A*J ∧
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
          (9*gamma:k)•(A*derivative d)+
          (9/2*gamma:k)•(d*derivative A)=
        -(6:k)•(A*derivative Fc)+(3:k)•(derivative A*Fc)+
          (6:k)•derivative J:=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Fc:=F+(3/2*gamma:k)•d
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
    module
  · rw [hbase2]
    simp only [derivative_add,derivative_smul,mul_add,mul_smul_comm,
      smul_mul_assoc,smul_add,smul_sub,smul_smul]
    rw [show d*derivative A=derivative A*d by ring]
    module

/-! ## Literal `S+1` rows, keeping the coincident `gamma d` load -/

def FiveToSixCuspZetaFirstB3EqualityNextPacketWallRowZeroScalar68
    (gamma:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=13*N-6*S-2
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e).coeff K+
    (3/2*gamma:k)*(A*derivative A*d).coeff K=0

def FiveToSixCuspZetaFirstB3EqualityNextPacketWallRowTwoScalar68
    (gamma:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=11*N-6*S-2
  (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff K-
      (9*gamma:k)*(A*derivative d).coeff K+
      (9/2*gamma:k)*(d*derivative A).coeff K=0

/-- On `4N-3S=1` the only extra attaining terms at the two `S+1` indices
are the first `gamma d` loads.  Every epsilon/`B` load and every other
residual product lies strictly below. -/
theorem fiveToSix_zetaFirst_B3_equality_next_wall_literal_rows68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hwall:4*N-3*S=1)
    (hrow0:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S 1)
    (hrow2:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S 1):
    FiveToSixCuspZetaFirstB3EqualityNextPacketWallRowZeroScalar68
        gamma A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityNextPacketWallRowTwoScalar68
        gamma A B c d e N S:=by
  let K0:=13*N-6*S-2
  let K2:=11*N-6*S-2
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hEq:4*N=3*S+1:=by omega
  have hgt4:5*N<4*S:=by omega
  have harith:=fiveToSix_nextPacket_wall_degree_arith68 N S hN hEq hgt4
  have hidx0:13*N-2*G-S-(S+1)-1=K0:=by
    rw [heq]
    dsimp only [K0]
    omega
  have hidx2:11*N-2*G-S-(S+1)-1=K2:=by
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
  simp only [Nat.add_one] at hrow0
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
  simp only [Nat.add_one] at hrow2
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
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityNextPacketWallRowZeroScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,K0]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow0
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityNextPacketWallRowTwoScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,K2]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow2

/-! ## Compensated I4 support drop -/

/-- Exact polynomial form of the compensated remainder on every
gamma-inactive equality cell. -/
theorem fiveToSix_nextPacket_wall_Fc_polynomial68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S):
    let Fc:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d
    ∃ i4:k, Fc=-(3/4*epsilon:k)•B+(3/8:k)•C i4:=by
  rcases fiveToSix_zetaFirst_sparse_compensatedI4_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
    ⟨i4,hpoly⟩
  refine ⟨i4,?_⟩
  simp only [neg_smul]
  linear_combination hpoly

/-- On the wall, `deg Fc ≤ deg B < deg d`. -/
theorem fiveToSix_nextPacket_wall_Fc_degree68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hwall:4*N-3*S=1):
    let Fc:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d
    Fc.natDegree≤3*N-2*S:=by
  let Fc:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  rcases fiveToSix_nextPacket_wall_Fc_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
    ⟨i4,hFc⟩
  change Fc.natDegree≤3*N-2*S
  dsimp only [Fc]
  rw [hFc]
  compute_degree
  omega

/-! ## Two-case degree comparison of `F` -/

/-- The I4 identity at degree `V=deg d` forces
`F.coeff V + (3/2) gamma d.coeff V = 0`. -/
theorem fiveToSix_nextPacket_wall_F_top_identity68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hwall:4*N-3*S=1):
    let F:=(B*e+c*d)-(1/9:k)•B^3
    let V:=5*N-3*S
    F.coeff V+(3/2*gamma:k)*d.coeff V=0:=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Fc:=F+(3/2*gamma:k)•d
  let D:=3*N-2*S
  let V:=5*N-3*S
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,hedeg,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hEq:4*N=3*S+1:=by omega
  have hgt4:5*N<4*S:=by omega
  have harith:=fiveToSix_nextPacket_wall_degree_arith68 N S hN hEq hgt4
  have hFcdeg:=fiveToSix_nextPacket_wall_Fc_degree68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  have hDltV:D<V:=by
    dsimp only [D,V]
    omega
  have hFcV:Fc.coeff V=0:=by
    change Fc.natDegree≤3*N-2*S at hFcdeg
    exact coeff_eq_zero_of_natDegree_lt (hFcdeg.trans_lt hDltV)
  dsimp only [Fc] at hFcV
  change F.coeff V+(3/2*gamma:k)*d.coeff V=0
  simpa only [coeff_add,coeff_smul,smul_eq_mul] using hFcV

/-- If `gamma=0`, then `deg F ≤ deg B`.  If `gamma≠0`, then `deg F = deg d`.
Both cases are compatible with the cusp leading edges; neither is `False`. -/
theorem fiveToSix_nextPacket_wall_F_degree_cases68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hwall:4*N-3*S=1):
    let F:=(B*e+c*d)-(1/9:k)•B^3
    let D:=3*N-2*S
    let V:=5*N-3*S
    (gamma=0 ∧ F.natDegree≤D) ∨
      (gamma≠0 ∧ F.natDegree=V):=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Fc:=F+(3/2*gamma:k)•d
  let D:=3*N-2*S
  let V:=5*N-3*S
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,hedeg,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hEq:4*N=3*S+1:=by omega
  have hgt4:5*N<4*S:=by omega
  have harith:=fiveToSix_nextPacket_wall_degree_arith68 N S hN hEq hgt4
  have htop:=fiveToSix_nextPacket_wall_F_top_identity68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  have hFcdeg:=fiveToSix_nextPacket_wall_Fc_degree68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  have hdV:d.natDegree≤V:=by
    dsimp only [V]
    convert hd using 1 <;> omega
  have hdidx:V=5*N-G-S:=by dsimp only [V];omega
  have hdcoeff:d.coeff V≠0:=by rw [hdidx];exact hcusp.2.2.1
  have hddeg:d.natDegree=V:=
    natDegree_eq_of_le_of_coeff_ne_zero hdV hdcoeff
  change (gamma=0 ∧ F.natDegree≤D) ∨ (gamma≠0 ∧ F.natDegree=V)
  by_cases hgamma:gamma=0
  · left
    refine ⟨hgamma,?_⟩
    have hFeq:F=Fc:=by
      dsimp only [Fc]
      rw [hgamma]
      simp only [mul_zero,zero_smul,add_zero]
    rw [hFeq]
    change Fc.natDegree≤3*N-2*S at hFcdeg
    exact hFcdeg
  · right
    refine ⟨hgamma,?_⟩
    have h32:(3/2:k)≠0:=by norm_num
    have hFcoeff:F.coeff V≠0:=by
      intro hz
      have hsum:F.coeff V+(3/2*gamma:k)*d.coeff V=0:=by
        convert htop
      rw [hz,zero_add] at hsum
      have hne:(3/2*gamma:k)*d.coeff V≠0:=
        mul_ne_zero (mul_ne_zero h32 hgamma) hdcoeff
      exact hne hsum
    have hi4:=fiveToSix_zetaFirst_endpoint_B3_I4_packet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs
      (by omega) (by omega)
    have hFraw:=hi4.1
    have hFle:F.natDegree≤V:=by
      dsimp only [F,V]
      convert hFraw using 1 <;> omega
    exact natDegree_eq_of_le_of_coeff_ne_zero hFle hFcoeff

/-! ## Sparse `Fc` drop and the `J` gain -/

/-- The `Fc` block of loaded row two lies strictly below `K2=11N-6S-2`. -/
theorem fiveToSix_nextPacket_wall_Fc_block_below_rowTwo68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hwall:4*N-3*S=1):
    let Fc:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d
    let K2:=11*N-6*S-2
    (-(6:k)•(A*derivative Fc)+(3:k)•(derivative A*Fc)).coeff K2=0:=by
  let Fc:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d
  let D:=3*N-2*S
  let K2:=11*N-6*S-2
  change (-(6:k)•(A*derivative Fc)+(3:k)•(derivative A*Fc)).coeff K2=0
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,hedeg,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hEq:4*N=3*S+1:=by omega
  have hgt4:5*N<4*S:=by omega
  have harith:=fiveToSix_nextPacket_wall_degree_arith68 N S hN hEq hgt4
  have hFc:=fiveToSix_nextPacket_wall_Fc_degree68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  change Fc.natDegree≤D at hFc
  have hDpos:0<D:=by
    dsimp only [D]
    omega
  have hdF0:=natDegree_derivative_le Fc
  have hdF:(derivative Fc).natDegree<D:=by omega
  have hdA0:=natDegree_derivative_le A
  have hdA:(derivative A).natDegree<2*N:=by omega
  have hAF:(A*derivative Fc).natDegree<K2:=by
    dsimp only [D,K2] at hFc hdF ⊢
    compute_degree
    omega
  have hA'F:(derivative A*Fc).natDegree<K2:=by
    dsimp only [D,K2] at hFc hdA ⊢
    compute_degree
    omega
  have hP:(-(6:k)•(A*derivative Fc)+
      (3:k)•(derivative A*Fc)).natDegree<K2:=by
    compute_degree
    omega
  exact coeff_eq_zero_of_natDegree_lt hP

/-- Loaded row two on the wall is a pure `J'` coefficient. -/
theorem fiveToSix_nextPacket_wall_J_first_lower68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hwall:4*N-3*S=1)
    (hrow2:FiveToSixCuspZetaFirstB3EqualityNextPacketWallRowTwoScalar68
      gamma A B c d e N S):
    let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
    J.coeff (11*N-6*S-1)=0:=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Fc:=F+(3/2*gamma:k)•d
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let K2:=11*N-6*S-2
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,hedeg,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hfactor:=fiveToSix_nextPacket_wall_load_factor68
    (k:=k) gamma A B c d e
  have hblock:=fiveToSix_nextPacket_wall_Fc_block_below_rowTwo68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  dsimp only [FiveToSixCuspZetaFirstB3EqualityNextPacketWallRowTwoScalar68]
    at hrow2
  have hpoly2:(FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
        (9*gamma:k)•(A*derivative d)+
        (9/2*gamma:k)•(d*derivative A)).coeff K2=0:=by
    simpa only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul] using hrow2
  rw [hfactor.2] at hpoly2
  change (-(6:k)•(A*derivative Fc)+(3:k)•(derivative A*Fc)+
      (6:k)•derivative J).coeff K2=0 at hpoly2
  simp only [coeff_add,coeff_smul,smul_eq_mul,coeff_derivative] at hpoly2
  have hblock0:(-(6:k)*(A*derivative Fc).coeff K2+
      (3:k)*(derivative A*Fc).coeff K2)=0:=by
    have hb:=hblock
    dsimp only at hb
    simpa only [coeff_add,coeff_smul,smul_eq_mul] using hb
  have hJprod:J.coeff (K2+1)*((K2:k)+1)=0:=by
    linear_combination (1/6:k)*hpoly2-(1/6:k)*hblock0
  have hcast:(K2:k)+1=((K2+1:ℕ):k):=by
    push_cast
    rfl
  have hK2c:((K2:k)+1)≠0:=by
    rw [hcast]
    exact_mod_cast (show K2+1≠0 by dsimp only [K2];omega)
  have hJzero:J.coeff (K2+1)=0:=
    (mul_eq_zero.mp hJprod).resolve_right hK2c
  have hidx:K2+1=11*N-6*S-1:=by dsimp only [K2];omega
  rw [hidx] at hJzero
  exact hJzero

/-! ## Contracted wall packet -/

def FiveToSixCuspZetaFirstB3EqualityNextPacketWallContracted68
    (gamma:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let Fc:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  Fc.natDegree≤3*N-2*S ∧ J.natDegree≤11*N-6*S-2

def FiveToSixCuspZetaFirstB3EqualityNextPacketWallPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  G=2*S ∧ 4*N-3*S=1 ∧
    FiveToSixCuspZetaFirstB3EndpointCellSplitPacket68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S ∧
    FiveToSixCuspZetaFirstB3EqualityNextPacketWallContracted68
      gamma A B c d e N S

theorem fiveToSix_zetaFirst_B3_equality_next_wall_contracted68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hwall:4*N-3*S=1)
    (hend:FiveToSixCuspZetaFirstB3EndpointRowTwoContractedScalar68
      A B c d e N G S)
    (hrows:FiveToSixCuspZetaFirstB3EqualityNextPacketWallRowZeroScalar68
        gamma A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualityNextPacketWallRowTwoScalar68
        gamma A B c d e N S):
    FiveToSixCuspZetaFirstB3EqualityNextPacketWallContracted68
      gamma A B c d e N S:=by
  let F:=(B*e+c*d)-(1/9:k)•B^3
  let Fc:=F+(3/2*gamma:k)•d
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let J:=Q-(3:k)•(d*e)
  let T:=11*N-6*S
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hFc:=fiveToSix_nextPacket_wall_Fc_degree68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
  have hJfirst:=fiveToSix_nextPacket_wall_J_first_lower68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq hwall
    hrows.2
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
  have hJdrop:J.natDegree≤T-2:=natDegree_le_pred hJone hJfirst
  change Fc.natDegree≤3*N-2*S ∧ J.natDegree≤11*N-6*S-2
  refine ⟨hFc,?_⟩
  dsimp only [T] at hJdrop
  simpa only [Nat.sub_sub,one_add_one_eq_two] using hJdrop

/-! ## Source-facing assembly -/

/-- The `NextPacket` wall chamber reduces to the contracted `Fc`/`J`
bounds.  The two `S+1` source rows are consumed. -/
theorem fiveToSix_zetaFirst_B3_equality_next_wall_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hp:FiveToSixCuspZetaFirstB3EqualityNextPacket68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S)
    (hwall:4*N-3*S=1):
    FiveToSixCuspZetaFirstB3EqualityNextPacketWallPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S:=by
  rcases hp with ⟨hGS,hcell,hsplit⟩
  have hbase:=hcell.1.1.1
  rcases hbase with ⟨hs,hBc,hGamma,q,hmuq,hqS,hprior,hminimal,hload,
    hi3,hi4,hend⟩
  rcases hsplit with hwallrows|hordinary
  · have hlit:=fiveToSix_zetaFirst_B3_equality_next_wall_literal_rows68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS hwall
      hwallrows.2.1 hwallrows.2.2
    have hcontract:=fiveToSix_zetaFirst_B3_equality_next_wall_contracted68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS hwall
      hend hlit
    exact ⟨hGS,hwall,hcell,hcontract⟩
  · exfalso
    omega

/-- Source-facing residual after consuming the `4N-3S=1` chamber.
The ordinary off-wall `NextPacket` disjunct is unchanged. -/
theorem fiveToSix_zetaFirst_endpoint_B3_equality_next_wall_or_residual68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    4*N-G≤S ∨
      FiveToSixCuspZetaFirstB3EqualityNextPacketWallPacket68 alpha gamma
        epsilon zeta eta terminal A B c d e N G S ∨
      (FiveToSixCuspZetaFirstB3EqualityNextPacket68 alpha gamma epsilon zeta
        eta terminal A B c d e N G S ∧ 1<4*N-3*S):=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_next_or_gamma68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|heq
  · exact Or.inl hGamma
  · rcases heq.2.2 with hwall|hordinary
    · exact Or.inr (Or.inl
        (fiveToSix_zetaFirst_B3_equality_next_wall_packet68
          alpha gamma epsilon zeta eta terminal A B c d e N G S heq
          hwall.1))
    · exact Or.inr (Or.inr ⟨heq,hordinary.1⟩)

#print axioms fiveToSix_nextPacket_wall_degree_arith68
#print axioms fiveToSix_nextPacket_wall_load_factor68
#print axioms fiveToSix_zetaFirst_B3_equality_next_wall_literal_rows68
#print axioms fiveToSix_nextPacket_wall_Fc_polynomial68
#print axioms fiveToSix_nextPacket_wall_Fc_degree68
#print axioms fiveToSix_nextPacket_wall_F_top_identity68
#print axioms fiveToSix_nextPacket_wall_F_degree_cases68
#print axioms fiveToSix_nextPacket_wall_Fc_block_below_rowTwo68
#print axioms fiveToSix_nextPacket_wall_J_first_lower68
#print axioms fiveToSix_zetaFirst_B3_equality_next_wall_contracted68
#print axioms fiveToSix_zetaFirst_B3_equality_next_wall_packet68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_next_wall_or_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityNextPacketWall68

end Max11DegreeRoutes
