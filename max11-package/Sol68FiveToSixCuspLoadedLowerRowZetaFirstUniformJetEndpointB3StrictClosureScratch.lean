import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3OuterRowZeroScratch

/-! # Closure of the strict B3 endpoint cell

At the exact first B3 load `q=G-S`, row two is used at `m=0`, rather than
only at the later endpoint.  If `G<2*S`, the `d*e` edge lies strictly below
this coefficient.  The row therefore kills the top jet of
`Q=B*c^2-(1/9)A*B^3`, while the cusp and its nonzero `A,B` edges make that
jet `-(4/9)a*b^3`, a contradiction.  The equality `G=2*S` is retained.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3StrictClosure68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3FirstRowTwoScalar68
    (A B c d e:k[X]) (N G:ℕ):Prop:=
  let K:=11*N-3*G-1
  (-4/27:k)*(FiveToSixCuspZetaFirstB3EndpointRowTwoCore68
    A B c d e).coeff K=0

/-- Literal row-two reduction at the first exact B3 load. -/
theorem fiveToSix_zetaFirst_B3_first_rowTwo68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:G≤2*S) (hGamma:S<4*N-G) (hq:q=G-S)
    (hrow:FiveToSixCuspZetaFirstUniformJetRowTwoScalar68
      gamma epsilon A B c d e N G S q 0):
    FiveToSixCuspZetaFirstB3FirstRowTwoScalar68 A B c d e N G:=by
  let W:=11*N-2*G-S-1
  let K:=11*N-3*G-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hlowB2d:(B^2*derivative d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBBd:(B*derivative B*d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowAd:(A*derivative d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBc:(B*derivative c).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowcB:(c*derivative B).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowdA:(d*derivative A).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowAB1:(derivative A*B).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowAB2:(A*derivative B).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowd:(derivative d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hqW:q≤W:=by dsimp only [W];omega
  dsimp only [W] at hqW
  dsimp only [FiveToSixCuspZetaFirstUniformJetRowTwoScalar68,
    FixedReflectedJet68] at hrow
  simp only [Nat.add_zero] at hrow
  simp only [coeff_reflect,revAt_le hqW] at hrow
  rw [show 11*N-2*G-S-1-q=K by dsimp only [K];omega] at hrow
  simp only [secondaryResidualRowTwoPolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlowB2d,
    coeff_eq_zero_of_natDegree_lt hlowBBd,
    coeff_eq_zero_of_natDegree_lt hlowAd,
    coeff_eq_zero_of_natDegree_lt hlowBc,
    coeff_eq_zero_of_natDegree_lt hlowcB,
    coeff_eq_zero_of_natDegree_lt hlowdA,
    coeff_eq_zero_of_natDegree_lt hlowAB1,
    coeff_eq_zero_of_natDegree_lt hlowAB2,
    coeff_eq_zero_of_natDegree_lt hlowd,
    mul_zero,add_zero,sub_zero] at hrow
  change FiveToSixCuspZetaFirstB3FirstRowTwoScalar68 A B c d e N G
  dsimp only [FiveToSixCuspZetaFirstB3FirstRowTwoScalar68,
    FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,K]
  simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
  linear_combination hrow

/-- At a strict B3 load, first row two forces the top `Q` jet to vanish. -/
theorem fiveToSix_zetaFirst_B3_first_Q_zero68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:G<2*S) (hGamma:S<4*N-G)
    (hrow:FiveToSixCuspZetaFirstB3FirstRowTwoScalar68 A B c d e N G):
    let Q:=B*c^2-(1/9:k)•(A*B^3)
    Q.coeff (11*N-3*G)=0:=by
  let H:=B*e+c*d
  let F:=H-(1/9:k)•B^3
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let P:=9*N-2*G-S
  let T:=11*N-3*G
  let K:=T-1
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
  change F.natDegree≤P-S-1 ∧ _ at hi4
  have hF:=hi4.1
  have hdF0:=natDegree_derivative_le F
  have hdF:(derivative F).natDegree<P-S-1:=by omega
  have hdA0:=natDegree_derivative_le A
  have hdA:(derivative A).natDegree<2*N:=by omega
  have hAF:(A*derivative F).natDegree<K:=by
    dsimp only [P,T,K] at hF hdF ⊢
    compute_degree
    omega
  have hA'F:(derivative A*F).natDegree<K:=by
    dsimp only [P,T,K] at hF hdA ⊢
    compute_degree
    omega
  have hFblock:(-(6:k)•(A*derivative F)+
      (3:k)•(derivative A*F)).coeff K=0:=by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hdeprod:(d*e).natDegree<K+1:=by
    dsimp only [T,K]
    compute_degree
    omega
  have hdecoef:(d*e).coeff (K+1)=0:=
    coeff_eq_zero_of_natDegree_lt hdeprod
  have hdezero:(derivative (d*e)).coeff K=0:=by
    rw [coeff_derivative,hdecoef,zero_mul]
  have hfactor:=fiveToSix_zetaFirst_B3_endpoint_rowTwo_core_factor68
    (k:=k) A B c d e
  have hfactor':FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e=
      (-(6:k)•(A*derivative F)+(3:k)•(derivative A*F))+
        (6:k)•derivative Q-(18:k)•derivative (d*e):=by
    dsimp only [F,H,Q]
    rw [hfactor]
    simp only [derivative_sub,derivative_smul,derivative_mul,mul_sub,
      mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_sub,smul_add,
      smul_smul,mul_assoc]
    module
  have hcore:(FiveToSixCuspZetaFirstB3EndpointRowTwoCore68
      A B c d e).coeff K=0:=by
    dsimp only [FiveToSixCuspZetaFirstB3FirstRowTwoScalar68] at hrow
    change (-4/27:k)*
      (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e).coeff K=0
      at hrow
    linear_combination (-27/4:k)*hrow
  rw [hfactor'] at hcore
  simp only [coeff_add,coeff_sub,coeff_smul,smul_eq_mul,hFblock,
    hdezero,zero_add,mul_zero,sub_zero,coeff_derivative] at hcore
  have hTK:K+1=T:=by dsimp only [K,T];omega
  have hTKc:((K:k)+1)=(T:k):=by
    exact_mod_cast hTK
  rw [hTK,hTKc] at hcore
  have hTc:((T:ℕ):k)≠0:=by
    exact_mod_cast (show T≠0 by dsimp only [T];omega)
  have hprod:((T:ℕ):k)*Q.coeff T=0:=by
    push_cast at hcore ⊢
    linear_combination (1/6:k)*hcore
  have hz:= (mul_eq_zero.mp hprod).resolve_left hTc
  simpa only [Q,T] using hz

/-- The top `Q` jet is nonzero on every strict B3 cusp. -/
theorem fiveToSix_zetaFirst_B3_first_Q_ne_zero68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS:q≤S)
    (hprior:∀ j,j<q→((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
      (8*N-2*G)).coeff j=0)
    (hqpos:0<q):
    let Q:=B*c^2-(1/9:k)•(A*B^3)
    Q.coeff (11*N-3*G)≠0:=by
  let Q:=B*c^2-(1/9:k)•(A*B^3)
  let T:=11*N-3*G
  let bU:=3*N-G
  have hp:=hs
  change _ ∧ _ ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp.2.2.2.2.1 with
    ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hqjet:=fiveToSix_zetaFirst_B3_Q_jet_below_q68
    alpha gamma epsilon zeta eta terminal A B c d e N G S q 0 hs hprior
    hqS hqpos
  change FixedReflectedJet68 Q T 0=
      -(4/9:k)*FixedReflectedJet68 (A*B^3) T 0 at hqjet
  dsimp only [FixedReflectedJet68] at hqjet
  simp only [coeff_reflect,revAt_zero] at hqjet
  have hB3deg:(B^3).natDegree≤3*bU:=by
    dsimp only [bU]
    compute_degree
    omega
  have hB3:=coeff_pow_at_bound68 B bU 3 hB
  have hAB3:=coeff_mul_at_bounds68 A (B^3) (2*N) (3*bU) hA hB3deg
  have hsum:2*N+3*bU=T:=by dsimp only [bU,T];omega
  rw [hsum,hB3] at hAB3
  rw [hAB3] at hqjet
  have hab: A.coeff (2*N)*B.coeff bU^3≠0:=
    mul_ne_zero ha (pow_ne_zero 3 hcusp.1)
  have hscalar:(-(4/9:k))≠0:=by norm_num
  change Q.coeff T≠0
  intro hQzero
  have hzero:(-(4/9:k))*(A.coeff (2*N)*B.coeff bU^3)=0:=by
    calc
      _ = Q.coeff T := hqjet.symm
      _ = 0 := hQzero
  exact (mul_ne_zero hscalar hab) hzero

/-- Every strict gamma-inactive B3 endpoint is impossible already at the
first loaded row-two coefficient. -/
theorem fiveToSix_zetaFirst_B3_strict_false68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hBc:G<2*S) (hGamma:S<4*N-G):False:=by
  have hs:=fiveToSix_zetaFirst_support_of_endpoint_cells_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj
  have hu:=hj.1.1
  rcases hu.2 with ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hfamily⟩
  have hq:=fiveToSix_zetaFirst_B3_least_q_eq68
    alpha gamma epsilon zeta eta terminal A B c d e N G S q hs (by omega)
    hGamma hmuq hqS hminimal hload
  have hqpos:0<q:=by omega
  have hrec:=fiveToSix_zetaFirst_uniform_jet_recurrence68
    alpha gamma epsilon zeta eta terminal A B c d e N G S q hs hqS hfamily
  have hrow:=fiveToSix_zetaFirst_B3_first_rowTwo68
    alpha gamma epsilon zeta eta terminal A B c d e N G S q hs (by omega)
    hGamma hq (hrec 0 (by omega)).2.2.2.2
  have hz:=fiveToSix_zetaFirst_B3_first_Q_zero68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hBc hGamma hrow
  have hn:=fiveToSix_zetaFirst_B3_first_Q_ne_zero68
    alpha gamma epsilon zeta eta terminal A B c d e N G S q hs hqS hprior
    hqpos
  exact hn hz

/-- Exact source-facing reduction after closing all strict B3 cells. -/
theorem fiveToSix_zetaFirst_endpoint_B3_equality_or_gamma68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    4*N-G≤S ∨
      (G=2*S ∧ FiveToSixCuspZetaFirstB3EndpointCellSplitPacket68
        alpha gamma epsilon zeta eta terminal A B c d e N G S):=by
  rcases fiveToSix_zetaFirst_endpoint_B3_cellSplit_or_gamma_packet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hb3
  · exact Or.inl hGamma
  · right
    have hbase:=hb3.1.1.1
    rcases hbase with ⟨hs,hBcLe,hGammaLt,q,hmuq,hqS,hprior,hminimal,
      hload,hi3,hi4,hrow2⟩
    by_cases heq:G=2*S
    · exact ⟨heq,hb3⟩
    · exfalso
      exact fiveToSix_zetaFirst_B3_strict_false68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hj
        (by omega) hGammaLt

#print axioms fiveToSix_zetaFirst_B3_first_rowTwo68
#print axioms fiveToSix_zetaFirst_B3_first_Q_zero68
#print axioms fiveToSix_zetaFirst_B3_first_Q_ne_zero68
#print axioms fiveToSix_zetaFirst_B3_strict_false68
#print axioms fiveToSix_zetaFirst_endpoint_B3_equality_or_gamma68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3StrictClosure68

end Max11DegreeRoutes
