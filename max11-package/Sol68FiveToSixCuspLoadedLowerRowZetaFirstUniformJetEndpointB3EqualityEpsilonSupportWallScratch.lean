import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonConstantWallScratch

/-! # The post-epsilon support wall

At `m=S`, row zero acquires four support-top products and row two acquires
the `B^2*d'`, `B*B'*d` pair.  This file records the exact literal source
reduction, including the coincidence with the constant-Fce wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportWall68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68
    (A B c d e:k[X]):k[X]:=
  A*B^2*derivative d+A*B*derivative B*d-
    (3:k)•(B*c*derivative e)+(3:k)•(c*derivative c*d)

def FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68
    (B d:k[X]):k[X]:=
  (6:k)•(B^2*derivative d)+(12:k)•(B*derivative B*d)

def FiveToSixCuspZetaFirstB3EqualitySupportRowZeroScalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=13*N-7*S-1
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
      (3/2*gamma:k)•(A*derivative A*d)+
      (3/4*epsilon:k)•(A*B*derivative A)+
      FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e).coeff K=0

def FiveToSixCuspZetaFirstB3EqualitySupportRowTwoScalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let K:=11*N-7*S-1
  (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
      (9*gamma:k)•(A*derivative d)+
      (9/2*gamma:k)•(d*derivative A)+
      (9/4*epsilon:k)•(derivative A*B)-
      (9/2*epsilon:k)•(A*derivative B)+
      FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d).coeff K=0

/-- The two named load blocks appended to the already-verified compensated
factorizations. -/
theorem fiveToSix_zetaFirst_B3_equality_support_load_factor68
    (gamma epsilon:k) (A B c d e:k[X]):
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
    FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
        (3/2*gamma:k)•(A*derivative A*d)+
        (3/4*epsilon:k)•(A*B*derivative A)+
        FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e=
      A*derivative A*Fce-derivative A*J+
        FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e ∧
    FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
        (9*gamma:k)•(A*derivative d)+
        (9/2*gamma:k)•(d*derivative A)+
        (9/4*epsilon:k)•(derivative A*B)-
        (9/2*epsilon:k)•(A*derivative B)+
        FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d=
      (-(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
        (6:k)•derivative J)+
        FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d:=by
  have h:=fiveToSix_zetaFirst_B3_equality_epsilon_load_factor68
    (k:=k) gamma epsilon A B c d e
  change _ ∧ _ at h
  exact ⟨congrArg (fun p=>p+
      FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e) h.1,
    congrArg (fun p=>p+
      FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d) h.2⟩

/-- Exact literal support reduction of the full source rows at `m=S`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_literal_rows68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hGamma:3*S<4*N)
    (hrow0:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S S)
    (hrow2:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S S):
    FiveToSixCuspZetaFirstB3EqualitySupportRowZeroScalar68
        gamma epsilon A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualitySupportRowTwoScalar68
        gamma epsilon A B c d e N S:=by
  let K0:=13*N-7*S-1
  let K2:=11*N-7*S-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hidx0:13*N-2*G-S-(S+S)-1=K0:=by
    rw [heq];dsimp only [K0];omega
  have hidx2:11*N-2*G-S-(S+S)-1=K2:=by
    rw [heq];dsimp only [K2];omega
  have h0Bdd:(B*d*derivative d).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0Bd2:(derivative B*d^2).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0BAc:(B*derivative A*c).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0Be:(B*derivative e).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0dc:(d*derivative c).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
  have h0dA:(d*derivative A).natDegree<K0:=by
    dsimp only [K0];compute_degree;omega
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
    coeff_eq_zero_of_natDegree_lt h0Bdd,
    coeff_eq_zero_of_natDegree_lt h0Bd2,
    coeff_eq_zero_of_natDegree_lt h0BAc,
    coeff_eq_zero_of_natDegree_lt h0Be,
    coeff_eq_zero_of_natDegree_lt h0dc,
    coeff_eq_zero_of_natDegree_lt h0dA,
    mul_zero,add_zero,sub_zero] at hrow0
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68] at hrow2
  rw [hidx2] at hrow2
  simp only [secondaryResidualRowTwoPolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt h2Bc,
    coeff_eq_zero_of_natDegree_lt h2cB,
    coeff_eq_zero_of_natDegree_lt h2d,
    mul_zero,add_zero,sub_zero] at hrow2
  constructor
  · dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportRowZeroScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,
      FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68,K0]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow0
  · dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportRowTwoScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,
      FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68,K2]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow2

def FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualitySupportWallResidualPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S ∧
    FiveToSixCuspZetaFirstB3EqualitySupportRowZeroScalar68
        gamma epsilon A B c d e N S ∧
      FiveToSixCuspZetaFirstB3EqualitySupportRowTwoScalar68
        gamma epsilon A B c d e N S

theorem fiveToSix_zetaFirst_endpoint_B3_equality_constant_or_supportLoaded68
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
      FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S ∨
      FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_constant_or_support68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hwallOne|hsmall|hconstant|hsupport
  · exact Or.inl hGamma
  · exact Or.inr (Or.inl hwallOne)
  · exact Or.inr (Or.inr (Or.inl hsmall))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hconstant)))
  · right;right;right;right
    have hsupportCopy:=hsupport
    rcases hsupport with ⟨hstop,hTD⟩
    rcases hstop with ⟨hcur,ht,hstate,hclass,hrow0,hrow2⟩
    let D:=3*N-2*S
    let w:=2*D
    let T:=S-w
    let t:=min D T
    have htT:t=T:=by dsimp only [t];exact Nat.min_eq_right hTD
    have hrow0S:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
        gamma epsilon A B c d e N G S S S:=by
      convert hrow0 using 1 <;> dsimp only [D,w,T,t] at htT ⊢ <;> omega
    have hrow2S:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
        gamma epsilon A B c d e N G S S S:=by
      convert hrow2 using 1 <;> dsimp only [D,w,T,t] at htT ⊢ <;> omega
    rcases hcur with ⟨hbase,hbaseDrop⟩
    rcases hbase with ⟨hterminal,hJold,hrowOld0,hrowOld2⟩
    rcases hterminal with ⟨hgamma,hY⟩
    rcases hgamma with ⟨hgammaStop,hcontract⟩
    rcases hgammaStop with ⟨hnext,ha,hjet,hgammaRow0,hgammaRow2⟩
    rcases hnext.1 with ⟨hGS,hcell,hprev⟩
    have hs:=hcell.1.1.1.1
    have hlit:=fiveToSix_zetaFirst_B3_equality_support_literal_rows68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGS
        (by omega) hrow0S hrow2S
    exact ⟨hsupportCopy,hlit⟩

#print axioms fiveToSix_zetaFirst_B3_equality_support_load_factor68
#print axioms fiveToSix_zetaFirst_B3_equality_support_literal_rows68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_constant_or_supportLoaded68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportWall68

end Max11DegreeRoutes
