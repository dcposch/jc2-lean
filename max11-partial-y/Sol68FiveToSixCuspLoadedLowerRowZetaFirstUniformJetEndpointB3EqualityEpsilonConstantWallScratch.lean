import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonFiniteStoppingScratch

/-! # The strict constant-Fce stopping wall

When `D=3*N-2*S` is strictly smaller than the remaining distance to the
support wall, the stopping row has indices `4*N-1` and `2*N-1`.  The
compensated I4 remainder is constant.  The two rows force that constant to
vanish and lower `J` from degree `2*N` to `2*N-1`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonConstantWall68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact constant-boundary contraction of the two factored rows. -/
theorem fiveToSix_zetaFirst_B3_equality_constantFce_edge68
    (A Fce J:k[X]) (N:ℕ)
    (hN:0<N) (hA:A.natDegree≤2*N) (ha:A.coeff (2*N)≠0)
    (hFce:Fce.natDegree≤0) (hJ:J.natDegree≤2*N)
    (hrow0:(A*derivative A*Fce-derivative A*J).coeff (4*N-1)=0)
    (hrow2:(-(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
      (6:k)•derivative J).coeff (2*N-1)=0):
    Fce=0 ∧ J.natDegree≤2*N-1:=by
  have hAAFce:=coeff_mul_mul_derivative_at_bounds68 A Fce A
    (2*N) 0 (2*N) (by omega) hA hFce hA
  rw [show 2*N+0+2*N-1=4*N-1 by omega] at hAAFce
  have hdA:=natDegree_derivative_le A
  have hdAsharp:(derivative A).natDegree≤2*N-1:=by omega
  have hAJ:=coeff_mul_at_bounds68 (derivative A) J (2*N-1) (2*N)
    hdAsharp hJ
  rw [show (2*N-1)+2*N=4*N-1 by omega] at hAJ
  have hAtop:=coeff_derivative_at_bound68 A (2*N) (by omega)
  have hAAFce':(A*derivative A*Fce).coeff (4*N-1)=
      A.coeff (2*N)^2*Fce.coeff 0*((2*N:ℕ):k):=by
    simpa only [mul_assoc,mul_comm,mul_left_comm,pow_two] using hAAFce
  rw [coeff_sub,hAAFce',hAJ,hAtop] at hrow0
  have hfac:A.coeff (2*N)*((2*N:ℕ):k)≠0:=by
    exact mul_ne_zero ha (by exact_mod_cast (show 2*N≠0 by omega))
  have htri0:A.coeff (2*N)*Fce.coeff 0-J.coeff (2*N)=0:=by
    apply (mul_eq_zero.mp ?_).resolve_left hfac
    linear_combination hrow0
  have hFceC:Fce=C (Fce.coeff 0):=eq_C_of_natDegree_le_zero hFce
  have hFceDeriv:derivative Fce=0:=by rw [hFceC,derivative_C]
  have hA'Fce:=coeff_mul_at_bounds68 (derivative A) Fce (2*N-1) 0
    hdAsharp hFce
  rw [show (2*N-1)+0=2*N-1 by omega] at hA'Fce
  have hJder:=coeff_derivative_at_bound68 J (2*N) (by omega)
  rw [show 2*N-1=2*N-1 by rfl] at hJder
  rw [hFceDeriv,mul_zero,smul_zero,zero_add] at hrow2
  simp only [coeff_add,coeff_smul,smul_eq_mul,hA'Fce,hAtop,hJder] at hrow2
  have hNcast:((2*N:ℕ):k)≠0:=by
    exact_mod_cast (show 2*N≠0 by omega)
  have htri2:A.coeff (2*N)*Fce.coeff 0+2*J.coeff (2*N)=0:=by
    apply (mul_eq_zero.mp ?_).resolve_left hNcast
    linear_combination (1/3:k)*hrow2
  have hJprod:(3:k)*J.coeff (2*N)=0:=by
    linear_combination htri2-htri0
  have h3:(3:k)≠0:=by norm_num
  have hJzero:J.coeff (2*N)=0:=(mul_eq_zero.mp hJprod).resolve_left h3
  have hFceCoeff:Fce.coeff 0=0:=by
    apply (mul_eq_zero.mp ?_).resolve_left ha
    linear_combination htri0+hJzero
  have hFceZero:Fce=0:=by
    rw [hFceC,hFceCoeff,C_0]
  exact ⟨hFceZero,natDegree_le_pred hJ hJzero⟩

/-- Apply the constant-boundary algebra to the literal post-epsilon rows. -/
theorem fiveToSix_zetaFirst_B3_equality_constantFce_contracted68
    (gamma epsilon:k) (A B c d e:k[X]) (N S D:ℕ)
    (hD:D=3*N-2*S)
    (hDpos:0<D)
    (hN:0<N) (hA:A.natDegree≤2*N) (ha:A.coeff (2*N)≠0)
    (hstate:FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68
      gamma epsilon A B c d e N S (D-1))
    (hrows:FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowZeroScalar68
        gamma epsilon A B c d e N S D ∧
      FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowTwoScalar68
        gamma epsilon A B c d e N S D):
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
    Fce=0 ∧ J.natDegree≤2*N-1:=by
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  have hstate':=hstate
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68] at hstate'
  have hFidx:3*N-2*S-(D-1)-1=0:=by omega
  have hJidx:5*N-2*S-(D-1)-1=2*N:=by omega
  rw [hFidx,hJidx] at hstate'
  have hfactor:=fiveToSix_zetaFirst_B3_equality_epsilon_load_factor68
    (k:=k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  have hrow0:=hrows.1
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowZeroScalar68]
    at hrow0
  rw [show 7*N-2*S-D-1=4*N-1 by omega] at hrow0
  have hrow0':(A*derivative A*Fce-derivative A*J).coeff (4*N-1)=0:=by
    rw [←hfactor.1]
    simpa only [coeff_add,coeff_smul,smul_eq_mul] using hrow0
  have hrow2:=hrows.2
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonRowTwoScalar68]
    at hrow2
  rw [show 5*N-2*S-D-1=2*N-1 by omega] at hrow2
  have hrow2':(-(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
      (6:k)•derivative J).coeff (2*N-1)=0:=by
    rw [←hfactor.2]
    simpa only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul] using hrow2
  exact fiveToSix_zetaFirst_B3_equality_constantFce_edge68
    A Fce J N hN hA ha hstate'.1 hstate'.2 hrow0' hrow2'

def FiveToSixCuspZetaFirstB3EqualityConstantFceContractedPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualityPostEpsilonStoppingPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S ∧
    let D:=3*N-2*S
    let T:=S-2*D
    D<T ∧
      let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
        (3/4*epsilon:k)•B
      let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
      Fce=0 ∧ J.natDegree≤2*N-1

def FiveToSixCuspZetaFirstB3EqualitySupportWallResidualPacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualityPostEpsilonStoppingPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S ∧
    let D:=3*N-2*S
    let T:=S-2*D
    T≤D

theorem fiveToSix_zetaFirst_endpoint_B3_equality_constant_or_support68
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
      FiveToSixCuspZetaFirstB3EqualitySupportWallResidualPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_postEpsilonStopping_or_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hwallOne|hsmall|hstop
  · exact Or.inl hGamma
  · exact Or.inr (Or.inl hwallOne)
  · exact Or.inr (Or.inr (Or.inl hsmall))
  · right;right;right
    have hstopCopy:=hstop
    rcases hstop with ⟨hcur,ht,hstate,hclass,hrow0,hrow2⟩
    let D:=3*N-2*S
    let w:=2*D
    let T:=S-w
    let t:=min D T
    by_cases hDT:D<T
    · left
      have htD:t=D:=by dsimp only [t];exact Nat.min_eq_left (by omega)
      have hstateD:FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68
          gamma epsilon A B c d e N S (D-1):=by
        convert hstate using 1 <;> dsimp only [D,w,T,t] at htD ⊢ <;> omega
      have hrow0D:FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
          gamma epsilon A B c d e N G S S (w+D):=by
        convert hrow0 using 1 <;> dsimp only [D,w,T,t] at htD ⊢ <;> omega
      have hrow2D:FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
          gamma epsilon A B c d e N G S S (w+D):=by
        convert hrow2 using 1 <;> dsimp only [D,w,T,t] at htD ⊢ <;> omega
      rcases hcur with ⟨hbase,hbaseDrop⟩
      rcases hbase with ⟨hterminal,hJold,hrowOld0,hrowOld2⟩
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
      have hstrict:w+D<S:=by dsimp only [T] at hDT;omega
      have hlit:=fiveToSix_zetaFirst_B3_equality_postEpsilon_literal_rows68
        alpha gamma epsilon zeta eta terminal A B c d e N G S w D hs hGS
          (by dsimp only [D,w]) (by omega) hstrict hrow0D hrow2D
      have hdrop:=fiveToSix_zetaFirst_B3_equality_constantFce_contracted68
        gamma epsilon A B c d e N S D (by rfl) (by dsimp only [D];omega)
          hN hA hatop hstateD hlit
      exact ⟨hstopCopy,hDT,hdrop⟩
    · right
      exact ⟨hstopCopy,by omega⟩

#print axioms fiveToSix_zetaFirst_B3_equality_constantFce_edge68
#print axioms fiveToSix_zetaFirst_B3_equality_constantFce_contracted68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_constant_or_support68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonConstantWall68

end Max11DegreeRoutes
