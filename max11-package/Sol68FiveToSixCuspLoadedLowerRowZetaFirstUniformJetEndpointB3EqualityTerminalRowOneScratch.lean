import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityTerminalGammaScratch

/-! # Uniform compensated row one through the equality gamma wall

The row-one gamma load is absorbed by the compensated I3 remainder.
Consequently every row-one coefficient through `a=4*N-3*S` kills one
successive edge of the primitive `Y`; this file packages the whole finite
descent, rather than another fixed-depth tower.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityTerminalRowOne68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualityLoadedRowOneScalar68
    (gamma:k) (A B c d e:k[X]) (N S m:ℕ):Prop:=
  let K:=12*N-6*S-m-1
  (FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e).coeff K-
    (9*gamma:k)*(A*derivative e).coeff K=0

def FiveToSixCuspZetaFirstB3EqualityYState68
    (A B c d e:k[X]) (N S m:ℕ):Prop:=
  let Y:=-(2:k)•(A*B^2*c)+(3:k)•(A*d^2)+
    (2:k)•c^3-(9:k)•e^2
  Y.natDegree≤12*N-6*S-m-1

/-- Literal row one at any depth no later than the gamma wall. -/
theorem fiveToSix_zetaFirst_B3_equality_loaded_rowOne_literal68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S m a:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (ha:a=4*N-3*S) (ha2:2<a)
    (hm:m≤a) (haS:a<S) (haE:a<2*(3*N-2*S))
    (hrow:FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68
      gamma epsilon A B c d e N G S S m):
    FiveToSixCuspZetaFirstB3EqualityLoadedRowOneScalar68
      gamma A B c d e N S m:=by
  let K:=12*N-6*S-m-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hidx:12*N-2*G-S-(S+m)-1=K:=by
    rw [heq]
    dsimp only [K]
    omega
  have hlowB2e:(B^2*derivative e).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBcd:(B*c*derivative d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBdc:(B*derivative c*d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBcd':(derivative B*c*d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowcc:(c*derivative c).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowAB2:(derivative A*B^2).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBd:(B*derivative d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowdB:(d*derivative B).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowAc:(A*derivative c).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowe:(derivative e).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68] at hrow
  rw [hidx] at hrow
  simp only [secondaryResidualRowOnePolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlowB2e,
    coeff_eq_zero_of_natDegree_lt hlowBcd,
    coeff_eq_zero_of_natDegree_lt hlowBdc,
    coeff_eq_zero_of_natDegree_lt hlowBcd',
    coeff_eq_zero_of_natDegree_lt hlowcc,
    coeff_eq_zero_of_natDegree_lt hlowAB2,
    coeff_eq_zero_of_natDegree_lt hlowBd,
    coeff_eq_zero_of_natDegree_lt hlowdB,
    coeff_eq_zero_of_natDegree_lt hlowAc,
    coeff_eq_zero_of_natDegree_lt hlowe,
    mul_zero,add_zero,sub_zero] at hrow
  change FiveToSixCuspZetaFirstB3EqualityLoadedRowOneScalar68
    gamma A B c d e N S m
  dsimp only [FiveToSixCuspZetaFirstB3EqualityLoadedRowOneScalar68,
    FiveToSixCuspZetaFirstB3EndpointRowOneCore68,K]
  simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
  linear_combination (-27/4:k)*hrow

/-- The I3 remainder after adding its gamma-`e` compensation. -/
theorem fiveToSix_zetaFirst_B3_equality_compensatedI3_support68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S):
    let R:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2
    let Rc:=R+(9/2*gamma:k)•e
    Rc.natDegree≤4*N-2*S:=by
  dsimp only
  let R:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2
  let Rc:=R+(9/2*gamma:k)•e
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  rcases fiveToSix_zetaFirst_B3_compensatedI3_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
    ⟨i3,hi3⟩
  have hRc:Rc=-(9/4*epsilon:k)•c+(3/4*gamma:k)•B^2+
      (9/8:k)•C i3:=by
    dsimp only [Rc,R]
    simp only [neg_smul]
    linear_combination hi3
  change Rc.natDegree≤4*N-2*S
  rw [hRc]
  compute_degree
  omega

/-- Each compensated row-one coefficient kills exactly one `Y` edge. -/
theorem fiveToSix_zetaFirst_B3_equality_loaded_rowOne_edge_zero68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S m a:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (ha:a=4*N-3*S) (ha2:2<a) (hm:m≤a)
    (hrow:FiveToSixCuspZetaFirstB3EqualityLoadedRowOneScalar68
      gamma A B c d e N S m):
    let Y:=-(2:k)•(A*B^2*c)+(3:k)•(A*d^2)+
      (2:k)•c^3-(9:k)•e^2
    Y.coeff (12*N-6*S-m)=0:=by
  let R:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2
  let Rc:=R+(9/2*gamma:k)•e
  let Y:=-(2:k)•(A*B^2*c)+(3:k)•(A*d^2)+
    (2:k)•c^3-(9:k)•e^2
  let K:=12*N-6*S-m-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hRc:=fiveToSix_zetaFirst_B3_equality_compensatedI3_support68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs heq
  change Rc.natDegree≤4*N-2*S at hRc
  have hdRc0:=natDegree_derivative_le Rc
  have hdRc:(derivative Rc).natDegree≤4*N-2*S-1:=by omega
  have hlow:(A*derivative Rc).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hRcZero:(-(2:k)•(A*derivative Rc)).coeff K=0:=by
    simp only [coeff_smul,smul_eq_mul,
      coeff_eq_zero_of_natDegree_lt hlow,mul_zero]
  have hfactor:
      FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e-
          (9*gamma:k)•(A*derivative e)=
        -(2:k)•(A*derivative Rc)+derivative Y:=by
    rw [fiveToSix_zetaFirst_B3_endpoint_rowOne_core_factor68
      (k:=k) A B c d e]
    dsimp only [Rc,R]
    simp only [derivative_add,derivative_smul,mul_add,mul_smul_comm,
      smul_mul_assoc,smul_add,smul_sub,smul_smul]
    module
  have hr:=hrow
  dsimp only [FiveToSixCuspZetaFirstB3EqualityLoadedRowOneScalar68] at hr
  have hrpoly:(FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e-
      (9*gamma:k)•(A*derivative e)).coeff K=0:=by
    simp only [coeff_sub,coeff_smul,smul_eq_mul]
    exact hr
  rw [hfactor,coeff_add,hRcZero,zero_add,coeff_derivative] at hrpoly
  have hidx:K+1=12*N-6*S-m:=by dsimp only [K];omega
  have hcast:((((K:ℕ):k)+1))≠0:=by
    have hk:K+1≠0:=by dsimp only [K];omega
    have hc:((K+1:ℕ):k)≠0:=by exact_mod_cast hk
    push_cast at hc
    exact hc
  change Y.coeff (12*N-6*S-m)=0
  rw [←hidx]
  apply (mul_eq_zero.mp hrpoly).resolve_right hcast

/-- Finite row-one descent through the gamma wall. -/
theorem fiveToSix_zetaFirst_B3_equality_terminal_rowOne_descent68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S a:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (heq:G=2*S) (ha:a=4*N-3*S) (ha2:2<a)
    (hend:FiveToSixCuspZetaFirstB3EndpointRowOneContractedScalar68
      A B c d e N G S):
    FiveToSixCuspZetaFirstB3EqualityYState68 A B c d e N S a:=by
  let Y:=-(2:k)•(A*B^2*c)+(3:k)•(A*d^2)+
    (2:k)•c^3-(9:k)•e^2
  let T:=12*N-6*S
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have haS:a<S:=by omega
  have haE:a<2*(3*N-2*S):=by omega
  have hY:Y.natDegree≤T:=by dsimp only [Y,T];compute_degree;omega
  have htop:=hend
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowOneContractedScalar68,
    FixedReflectedJet68] at htop
  have ht0:2*S-G=0:=by omega
  have hT:12*N-3*G=T:=by dsimp only [T];omega
  rw [ht0,coeff_reflect,revAt_zero,hT] at htop
  have hbase:FiveToSixCuspZetaFirstB3EqualityYState68
      A B c d e N S 0:=by
    dsimp only [FiveToSixCuspZetaFirstB3EqualityYState68]
    change Y.natDegree≤T-1
    exact natDegree_le_pred hY htop
  have hind:∀m,m≤a→
      FiveToSixCuspZetaFirstB3EqualityYState68 A B c d e N S m:=by
    intro m
    induction m with
    | zero =>
        intro hm
        exact hbase
    | succ m ih =>
        intro hm
        have hma:m≤a:=by omega
        have hprev:=ih hma
        have hsource:=fiveToSix_zetaFirst_loaded_uniform_rowOne68
          alpha gamma epsilon zeta eta terminal A B c d e N G S S (m+1) hs
        have hlit:=fiveToSix_zetaFirst_B3_equality_loaded_rowOne_literal68
          alpha gamma epsilon zeta eta terminal A B c d e N G S (m+1) a
          hs heq ha ha2 hm haS haE hsource
        have hedge:=fiveToSix_zetaFirst_B3_equality_loaded_rowOne_edge_zero68
          alpha gamma epsilon zeta eta terminal A B c d e N G S (m+1) a
          hs heq ha ha2 hm hlit
        dsimp only at hedge
        have hpdeg:=hprev
        dsimp only [FiveToSixCuspZetaFirstB3EqualityYState68] at hpdeg
        change Y.natDegree≤12*N-6*S-m-1 at hpdeg
        have hidx:12*N-6*S-m-1=T-(m+1):=by dsimp only [T];omega
        rw [hidx] at hpdeg
        have hedge':Y.coeff (T-(m+1))=0:=by
          dsimp only [T] at hedge ⊢
          exact hedge
        dsimp only [FiveToSixCuspZetaFirstB3EqualityYState68]
        change Y.natDegree≤T-(m+1)-1
        exact natDegree_le_pred hpdeg hedge'
  exact hind a (le_refl a)

def FiveToSixCuspZetaFirstB3EqualityTerminalRowOnePacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EqualityTerminalGammaPacket68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S ∧
    let a:=4*N-3*S
    FiveToSixCuspZetaFirstB3EqualityYState68 A B c d e N S a

theorem fiveToSix_zetaFirst_endpoint_B3_equality_terminalRowOne_or_residual68
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
      FiveToSixCuspZetaFirstB3EqualityTerminalRowOnePacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_terminalGamma_or_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hwallOne|hsmall|hterminal
  · exact Or.inl hGamma
  · exact Or.inr (Or.inl hwallOne)
  · exact Or.inr (Or.inr (Or.inl hsmall))
  · right;right;right
    let a:=4*N-3*S
    rcases hterminal with ⟨hstop,hcontract⟩
    rcases hstop with ⟨hnext,ha,hstate,hrow0,hrow2⟩
    rcases hnext.1 with ⟨hGS,hcell,hprev⟩
    have hrowOneEndpoint:=hcell.1.1.2
    have hs:=hcell.1.1.1.1
    have hY:=fiveToSix_zetaFirst_B3_equality_terminal_rowOne_descent68
      alpha gamma epsilon zeta eta terminal A B c d e N G S a hs hGS
      (by rfl) ha hrowOneEndpoint
    exact ⟨⟨⟨hnext,ha,hstate,hrow0,hrow2⟩,hcontract⟩,hY⟩

#print axioms fiveToSix_zetaFirst_B3_equality_loaded_rowOne_literal68
#print axioms fiveToSix_zetaFirst_B3_equality_compensatedI3_support68
#print axioms fiveToSix_zetaFirst_B3_equality_loaded_rowOne_edge_zero68
#print axioms fiveToSix_zetaFirst_B3_equality_terminal_rowOne_descent68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_terminalRowOne_or_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityTerminalRowOne68

end Max11DegreeRoutes
