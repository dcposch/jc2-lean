import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonNextScratch

/-! # Uniform post-epsilon stopping

The determinant `3*N` is independent of the post-epsilon depth.  We iterate
the exact source rows until the earlier of the compensated-I4 constant wall
and the support wall.  The row at that first wall is retained literally.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonFiniteStopping68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68
    (gamma epsilon:k) (A B c d e:k[X]) (N S r:ℕ):Prop:=
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  Fce.natDegree≤3*N-2*S-r-1 ∧ J.natDegree≤5*N-2*S-r-1

def FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowZeroScalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S r:ℕ):Prop:=
  let K:=7*N-2*S-r-1
  (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e).coeff K+
      (3/2*gamma:k)*(A*derivative A*d).coeff K+
      (3/4*epsilon:k)*(A*B*derivative A).coeff K=0

def FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowTwoScalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S r:ℕ):Prop:=
  let K:=5*N-2*S-r-1
  (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff K-
      (9*gamma:k)*(A*derivative d).coeff K+
      (9/2*gamma:k)*(d*derivative A).coeff K+
      (9/4*epsilon:k)*(derivative A*B).coeff K-
      (9/2*epsilon:k)*(A*derivative B).coeff K=0

/-- Uniform literal reduction at post-epsilon offset `r`, strictly before
the support wall. -/
theorem fiveToSix_zetaFirst_B3_equality_postEpsilon_literal_rows68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S w r:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (hw:w=2*(3*N-2*S)) (hGamma:3*S<4*N)
    (hrS:w+r<S)
    (hrow0:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S S (w+r))
    (hrow2:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S S (w+r)):
    FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowZeroScalar68
        gamma epsilon A B c d e N S r ∧
      FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowTwoScalar68
        gamma epsilon A B c d e N S r:=by
  let K0:=7*N-2*S-r-1
  let K2:=5*N-2*S-r-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hidx0:13*N-2*G-S-(S+(w+r))-1=K0:=by
    rw [heq,hw]
    dsimp only [K0]
    omega
  have hidx2:11*N-2*G-S-(S+(w+r))-1=K2:=by
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
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowZeroScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,K0]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow0
  · dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowTwoScalar68,
      FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,K2]
    simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
    linear_combination (-27/4:k)*hrow2

/-- One uniform post-epsilon contraction at offset `r`. -/
theorem fiveToSix_zetaFirst_B3_equality_postEpsilon_step68
    (gamma epsilon:k) (A B c d e:k[X]) (N S r:ℕ)
    (hN:0<N) (hA:A.natDegree≤2*N) (ha:A.coeff (2*N)≠0)
    (hrD:r<3*N-2*S)
    (hstate:
      let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
        (3/4*epsilon:k)•B
      let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
      Fce.natDegree≤3*N-2*S-r ∧ J.natDegree≤5*N-2*S-r)
    (hrows:FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowZeroScalar68
        gamma epsilon A B c d e N S r ∧
      FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowTwoScalar68
        gamma epsilon A B c d e N S r):
    FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68
      gamma epsilon A B c d e N S r:=by
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let D:=3*N-2*S-r
  let j:=5*N-2*S-r
  let K0:=7*N-2*S-r-1
  let K2:=5*N-2*S-r-1
  change Fce.natDegree≤D ∧ J.natDegree≤j at hstate
  have hfactor:=fiveToSix_zetaFirst_B3_equality_epsilon_load_factor68
    (k:=k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  have hrow0:=hrows.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowZeroScalar68]
    at hrow0
  have hrow0':(A*derivative A*Fce-derivative A*J).coeff K0=0:=by
    rw [←hfactor.1]
    simpa only [coeff_add,coeff_smul,smul_eq_mul] using hrow0
  have hrow2:=hrows.2
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowTwoScalar68]
    at hrow2
  have hrow2':(-(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
      (6:k)•derivative J).coeff K2=0:=by
    rw [←hfactor.2]
    simpa only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul] using hrow2
  have hdrop:=fiveToSix_zetaFirst_B3_equality_twoRow_edge_drop68
    A Fce J N D j K0 K2 hN (by dsimp only [D];omega)
      (by dsimp only [j];omega) hA ha hstate.1 hstate.2
      (by dsimp only [D,K0];omega) (by dsimp only [j,K0];omega)
      (by dsimp only [D,K2];omega) (by rfl)
      (by dsimp only [D,j];omega) hrow0' hrow2'
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68]
  exact hdrop

def FiveToSixCuspZetaFirstB3EqualityPostEpsilonStoppingPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualityEpsilonContractedPacket68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S ∧
    let D:=3*N-2*S
    let w:=2*D
    let T:=S-w
    let t:=min D T
    0<t ∧
      FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68
        gamma epsilon A B c d e N S (t-1) ∧
      (t=D ∨ t=T) ∧
      FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
        gamma epsilon A B c d e N G S S (w+t) ∧
      FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
        gamma epsilon A B c d e N G S S (w+t)

theorem fiveToSix_zetaFirst_endpoint_B3_equality_postEpsilonStopping_or_residual68
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
      FiveToSixCuspZetaFirstB3EqualityPostEpsilonStoppingPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_epsilonContracted_or_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hwallOne|hsmall|hcur
  · exact Or.inl hGamma
  · exact Or.inr (Or.inl hwallOne)
  · exact Or.inr (Or.inr (Or.inl hsmall))
  · right;right;right
    have hcurCopy:=hcur
    rcases hcur with ⟨hstop,hbase⟩
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
    let D:=3*N-2*S
    let w:=2*D
    let T:=S-w
    let t:=min D T
    have hD:0<D:=by dsimp only [D];omega
    have hT:0<T:=by dsimp only [D,w,T];omega
    have ht:0<t:=by
      dsimp only [t]
      simpa only [lt_min_iff] using And.intro hD hT
    have htD:t≤D:=by dsimp only [t];exact min_le_left D T
    have htT:t≤T:=by dsimp only [t];exact min_le_right D T
    have hind:∀r,r<t→
        FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68
          gamma epsilon A B c d e N S r:=by
      intro r
      induction r with
      | zero =>
          intro hr
          dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68]
          exact hbase
      | succ r ih =>
          intro hr
          have hprevState:=ih (by omega)
          have hrD:r+1<D:=by omega
          have hrS:w+(r+1)<S:=by dsimp only [T] at htT;omega
          have hrpos:0<13*N-2*G-S-(S+(w+(r+1)))-1:=by
            dsimp only [D,w,T] at *
            omega
          have hrow0:=fiveToSix_zetaFirst_equality_uniform_source_rowZero68
            alpha gamma epsilon zeta eta terminal A B c d e N G S
              (w+(r+1)) hs hrpos
          have hrow2:=fiveToSix_zetaFirst_loaded_uniform_rowTwo68
            alpha gamma epsilon zeta eta terminal A B c d e N G S S
              (w+(r+1)) hs
          have hlit:=fiveToSix_zetaFirst_B3_equality_postEpsilon_literal_rows68
            alpha gamma epsilon zeta eta terminal A B c d e N G S w (r+1)
              hs hGS (by dsimp only [D,w]) (by omega) hrS hrow0 hrow2
          have hpdeg:=hprevState
          dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68]
            at hpdeg
          have hpdeg':
              let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
                (3/4*epsilon:k)•B
              let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
              Fce.natDegree≤3*N-2*S-(r+1) ∧
                J.natDegree≤5*N-2*S-(r+1):=by
            exact hpdeg
          exact fiveToSix_zetaFirst_B3_equality_postEpsilon_step68
            gamma epsilon A B c d e N S (r+1) hN hA hatop hrD hpdeg' hlit
    have hlast:=hind (t-1) (by omega)
    have hclass:t=D ∨ t=T:=by
      by_cases hDT:D≤T
      · left;dsimp only [t];exact Nat.min_eq_left hDT
      · right;dsimp only [t];exact Nat.min_eq_right (by omega)
    have hwtS:w+t≤S:=by dsimp only [T] at htT;omega
    have hrpos:0<13*N-2*G-S-(S+(w+t))-1:=by
      dsimp only [D,w,T] at *
      omega
    have hrow0:=fiveToSix_zetaFirst_equality_uniform_source_rowZero68
      alpha gamma epsilon zeta eta terminal A B c d e N G S (w+t) hs hrpos
    have hrow2:=fiveToSix_zetaFirst_loaded_uniform_rowTwo68
      alpha gamma epsilon zeta eta terminal A B c d e N G S S (w+t) hs
    exact ⟨hcurCopy,ht,hlast,hclass,hrow0,hrow2⟩

#print axioms fiveToSix_zetaFirst_B3_equality_postEpsilon_literal_rows68
#print axioms fiveToSix_zetaFirst_B3_equality_postEpsilon_step68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_postEpsilonStopping_or_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonFiniteStopping68

end Max11DegreeRoutes
