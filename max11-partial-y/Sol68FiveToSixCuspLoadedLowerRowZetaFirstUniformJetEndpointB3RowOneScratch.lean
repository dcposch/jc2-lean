import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3RowTwoScratch

/-! # The B3-loaded endpoint row-one contraction

The row-one endpoint has two extra terms in the `G≤2*S` cell.  The exact
compensated I3 identity absorbs them: after its lower support is removed,
the entire retained row is the derivative of one reflected primitive.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3RowOne68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact compensated I3 identity at the retained source witness. -/
theorem fiveToSix_zetaFirst_B3_compensatedI3_polynomial68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S):
    ∃ i3:k,
      (-(A*B*d)+(3:k)•(c*e))+(9/4*epsilon:k)•c+
          (9/2*gamma:k)•e-(3/4*gamma:k)•B^2=
        B^2*c-(3/2:k)•d^2+(9/8:k)•C i3:=by
  have hp:=hs
  change _ ∧ _ ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases had with ⟨i4,i3,hi4,hi3,hrow0,hrow1,hrow2,hpos,hiff⟩
  refine ⟨i3,?_⟩
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,hz]
    at hi3
  simp only [secondaryResidualInvariantThreePolynomial68] at hi3
  rw [←hi3]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul,map_add,map_sub,map_mul,map_pow,map_neg,
    map_zero,RatFunc.algebraMap_C,map_div₀,map_ofNat,map_natCast,map_one]
  ring

/-- After subtracting its two principal terms, compensated I3 lies one
full endpoint jet below the row-one index. -/
theorem fiveToSix_zetaFirst_B3_compensatedI3_support68
    (alpha gamma epsilon zeta eta terminal:k) (A B c d e:k[X])
    (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) (hGamma:S<4*N-G):
    let F:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2
    F.natDegree≤10*N-2*G-2*S-1:=by
  dsimp only
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  rcases fiveToSix_zetaFirst_B3_compensatedI3_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs with
    ⟨i3,hpoly⟩
  have hF:(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2=
      -(9/4*epsilon:k)•c-(9/2*gamma:k)•e+
        (3/4*gamma:k)•B^2+(9/8:k)•C i3:=by
    simp only [neg_smul]
    linear_combination hpoly
  rw [hF]
  compute_degree
  omega

/-- Literal terms surviving row one in the B3-loaded, gamma-inactive
endpoint cell. -/
def FiveToSixCuspZetaFirstB3EndpointRowOneCore68
    (A B c d e:k[X]):k[X]:=
  (2:k)•(A^2*B*derivative d)+
    (2:k)•(A^2*derivative B*d)+
    (2:k)•(A*derivative A*B*d)-
    (6:k)•(A*c*derivative e)-
    (6:k)•(A*derivative c*e)-
    (2:k)•(derivative A*B^2*c)+
    (3:k)•(derivative A*d^2)+
    (6:k)•(c^2*derivative c)-
    (18:k)•(e*derivative e)

def FiveToSixCuspZetaFirstB3EndpointRowOneScalar68
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  let K:=12*N-2*G-2*S-1
  (-4/27:k)*(FiveToSixCuspZetaFirstB3EndpointRowOneCore68
    A B c d e).coeff K=0

/-- Exact literal source reduction; no total-degree bound is used. -/
theorem fiveToSix_zetaFirst_B3_endpoint_rowOne68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S q:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:G≤2*S) (hGamma:S<4*N-G) (hqS:q≤S)
    (hrow:FiveToSixCuspZetaFirstUniformJetRowOneScalar68
      gamma epsilon A B c d e N G S q (S-q)):
    FiveToSixCuspZetaFirstB3EndpointRowOneScalar68 A B c d e N G S:=by
  let W:=12*N-2*G-S-1
  let K:=12*N-2*G-2*S-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hlowB2e:(B^2*derivative e).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBcd:(B*c*derivative d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBdc:(B*derivative c*d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowBcd':(derivative B*c*d).natDegree<K:=by
    dsimp only [K];compute_degree;omega
  have hlowAe:(A*derivative e).natDegree<K:=by
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
  have hSW:S≤12*N-2*G-S-1:=by omega
  have hqm:q+(S-q)=S:=by omega
  dsimp only [FiveToSixCuspZetaFirstUniformJetRowOneScalar68,
    FixedReflectedJet68] at hrow
  rw [hqm] at hrow
  simp only [coeff_reflect,revAt_le hSW] at hrow
  rw [show 12*N-2*G-S-1-S=K by dsimp only [K];omega] at hrow
  simp only [secondaryResidualRowOnePolynomial68,coeff_smul,coeff_add,
    coeff_sub,smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlowB2e,
    coeff_eq_zero_of_natDegree_lt hlowBcd,
    coeff_eq_zero_of_natDegree_lt hlowBdc,
    coeff_eq_zero_of_natDegree_lt hlowBcd',
    coeff_eq_zero_of_natDegree_lt hlowAe,
    coeff_eq_zero_of_natDegree_lt hlowcc,
    coeff_eq_zero_of_natDegree_lt hlowAB2,
    coeff_eq_zero_of_natDegree_lt hlowBd,
    coeff_eq_zero_of_natDegree_lt hlowdB,
    coeff_eq_zero_of_natDegree_lt hlowAc,
    coeff_eq_zero_of_natDegree_lt hlowe,
    mul_zero,add_zero,sub_zero] at hrow
  change FiveToSixCuspZetaFirstB3EndpointRowOneScalar68 A B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowOneScalar68,
    FiveToSixCuspZetaFirstB3EndpointRowOneCore68,K]
  simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul]
  linear_combination hrow

/-- The retained row is an I3 remainder derivative plus one primitive
derivative. -/
theorem fiveToSix_zetaFirst_B3_endpoint_rowOne_core_factor68
    (A B c d e:k[X]):
    let F:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2
    let Y:=-(2:k)•(A*B^2*c)+(3:k)•(A*d^2)+
      (2:k)•c^3-(9:k)•e^2
    FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e=
      -(2:k)•(A*derivative F)+derivative Y:=by
  let Xc:=-(A*B*d)+(3:k)•(c*e)
  let F:=Xc-B^2*c+(3/2:k)•d^2
  let Y:=-(2:k)•(A*B^2*c)+(3:k)•(A*d^2)+
    (2:k)•c^3-(9:k)•e^2
  change FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e=
    -(2:k)•(A*derivative F)+derivative Y
  have hsq (p:k[X]):derivative (p^2)=(2:k)•(p*derivative p):=by
    rw [show p^2=p*p by ring,derivative_mul,
      show derivative p*p=p*derivative p by ring]
    module
  have hcube (p:k[X]):derivative (p^3)=(3:k)•(p^2*derivative p):=by
    rw [show p^3=p*p^2 by ring,derivative_mul,hsq]
    rw [show derivative p*p^2=p^2*derivative p by ring]
    have hm:p*((2:k)•(p*derivative p))=
        (2:k)•(p^2*derivative p):=by
      rw [mul_smul_comm]
      congr 1
      ring
    rw [hm]
    module
  have hX:derivative Xc=
      -(derivative A*B*d+A*derivative B*d+A*B*derivative d)+
        (3:k)•(derivative c*e+c*derivative e) := by
    dsimp only [Xc]
    simp only [derivative_add,derivative_neg,derivative_smul,derivative_mul,
      mul_add,add_mul,mul_assoc]
    module
  have hcoreX:FiveToSixCuspZetaFirstB3EndpointRowOneCore68 A B c d e=
      -(2:k)•(A*derivative Xc)-(2:k)•(derivative A*B^2*c)+
        (3:k)•(derivative A*d^2)+(6:k)•(c^2*derivative c)-
        (18:k)•(e*derivative e):=by
    rw [hX]
    simp only [FiveToSixCuspZetaFirstB3EndpointRowOneCore68]
    rw [show A^2=A*A by ring]
    simp only [mul_add,mul_sub,add_mul,sub_mul,mul_smul_comm,
      smul_mul_assoc,smul_add,smul_sub,smul_smul,mul_assoc,mul_neg,
      neg_mul,smul_neg,neg_smul,neg_neg]
    module
  have hFder:derivative F=
      derivative Xc-derivative (B^2*c)+(3/2:k)•derivative (d^2):=by
    dsimp only [F]
    simp only [derivative_add,derivative_sub,derivative_smul]
  have hYder:derivative Y=
      -(2:k)•(derivative A*B^2*c+A*derivative (B^2*c))+
        (3:k)•(derivative A*d^2+A*derivative (d^2))+
        (6:k)•(c^2*derivative c)-(18:k)•(e*derivative e):=by
    dsimp only [Y]
    simp only [derivative_add,derivative_sub,derivative_neg,derivative_smul,
      derivative_mul]
    rw [hcube c,hsq e]
    simp only [mul_smul_comm,smul_mul_assoc,smul_add,smul_sub,smul_smul,
      mul_add,mul_sub,add_mul,sub_mul,mul_assoc]
    module
  rw [hcoreX,hFder,hYder]
  simp only [mul_add,mul_sub,mul_smul_comm,smul_mul_assoc,smul_add,
    smul_sub,smul_smul,mul_assoc]
  module

/-- Reflected primitive forced to vanish by the row-one coefficient. -/
def FiveToSixCuspZetaFirstB3EndpointRowOneContractedScalar68
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  let T:=12*N-3*G
  let t:=2*S-G
  let Y:=-(2:k)•(A*B^2*c)+(3:k)•(A*d^2)+
    (2:k)•c^3-(9:k)•e^2
  FixedReflectedJet68 Y T t=0

theorem fiveToSix_zetaFirst_B3_endpoint_rowOne_contracted68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hBc:G≤2*S) (hGamma:S<4*N-G)
    (hrow:FiveToSixCuspZetaFirstB3EndpointRowOneScalar68
      A B c d e N G S):
    FiveToSixCuspZetaFirstB3EndpointRowOneContractedScalar68
      A B c d e N G S:=by
  let F:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2
  let Y:=-(2:k)•(A*B^2*c)+(3:k)•(A*d^2)+
    (2:k)•c^3-(9:k)•e^2
  let T:=12*N-3*G
  let t:=2*S-G
  let K:=12*N-2*G-2*S-1
  have hp:=hs
  change 0<S ∧ S<7*N-2*G ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hF:=fiveToSix_zetaFirst_B3_compensatedI3_support68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hGamma
  change F.natDegree≤10*N-2*G-2*S-1 at hF
  have hLF:0<10*N-2*G-2*S-1:=by omega
  have hdF0:=natDegree_derivative_le F
  have hdF:(derivative F).natDegree<10*N-2*G-2*S-1:=by omega
  have hAF:(A*derivative F).natDegree<K:=by
    dsimp only [K]
    compute_degree
    omega
  have hFzero:(-(2:k)•(A*derivative F)).coeff K=0:=by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  dsimp only [F] at hFzero
  have hcore:(FiveToSixCuspZetaFirstB3EndpointRowOneCore68
      A B c d e).coeff K=0:=by
    dsimp only [FiveToSixCuspZetaFirstB3EndpointRowOneScalar68] at hrow
    linear_combination (-27/4:k)*hrow
  rw [fiveToSix_zetaFirst_B3_endpoint_rowOne_core_factor68
      (k:=k) A B c d e] at hcore
  simp only [coeff_add,hFzero,zero_add,coeff_derivative] at hcore
  have htT:t≤T:=by dsimp only [t,T];omega
  have hTK:T-t=K+1:=by dsimp only [T,t,K];omega
  have hYjet:Y.coeff (K+1)=FixedReflectedJet68 Y T t:=by
    rw [←hTK]
    exact coeff_top_sub_eq_fixedReflectedJet68 Y T t htT
  rw [hYjet] at hcore
  have hKc:((((K+1:ℕ)):k))≠0:=by
    exact_mod_cast (show K+1≠0 by dsimp only [K];omega)
  have hzero:FixedReflectedJet68 Y T t=0:=by
    apply (mul_eq_zero.mp ?_).resolve_left hKc
    push_cast at hcore ⊢
    simpa only [mul_comm] using hcore
  change FiveToSixCuspZetaFirstB3EndpointRowOneContractedScalar68
    A B c d e N G S
  dsimp only [FiveToSixCuspZetaFirstB3EndpointRowOneContractedScalar68,
    Y,T,t]
  exact hzero

/-- The verified row-two/I3 packet with the independent contracted row one
attached.  The earlier exact I3 scalar remains literally in the base. -/
def FiveToSixCuspZetaFirstB3EndpointRowOnePacket68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ):Prop:=
  FiveToSixCuspZetaFirstB3EndpointPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧
    FiveToSixCuspZetaFirstB3EndpointRowOneContractedScalar68
      A B c d e N G S

/-- Source-facing endpoint split after adding row one. -/
theorem fiveToSix_zetaFirst_endpoint_B3_rowOne_or_gamma_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hj:FiveToSixCuspZetaFirstEndpointCellsResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S):
    4*N-G≤S ∨ FiveToSixCuspZetaFirstB3EndpointRowOnePacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S:=by
  rcases fiveToSix_zetaFirst_endpoint_B3_or_gamma_packet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hj with
    hGamma|hb3
  · exact Or.inl hGamma
  · right
    rcases hb3 with ⟨hs,hBc,hGamma,q,hmuq,hqS,hprior,hminimal,hload,
      hi3,hi4,hrow2⟩
    rcases hj.2 with ⟨q',hmuq',hqS',hprior',hminimal',hload',hcell⟩
    have hrow:=fiveToSix_zetaFirst_B3_endpoint_rowOne68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q' hs hBc
      hGamma hqS' hcell.2.2.2.1
    have hcontract:=fiveToSix_zetaFirst_B3_endpoint_rowOne_contracted68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hBc
      hGamma hrow
    exact ⟨⟨hs,hBc,hGamma,q,hmuq,hqS,hprior,hminimal,hload,
      hi3,hi4,hrow2⟩,hcontract⟩

#print axioms fiveToSix_zetaFirst_B3_compensatedI3_polynomial68
#print axioms fiveToSix_zetaFirst_B3_compensatedI3_support68
#print axioms fiveToSix_zetaFirst_B3_endpoint_rowOne68
#print axioms fiveToSix_zetaFirst_B3_endpoint_rowOne_core_factor68
#print axioms fiveToSix_zetaFirst_B3_endpoint_rowOne_contracted68
#print axioms fiveToSix_zetaFirst_endpoint_B3_rowOne_or_gamma_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3RowOne68

end Max11DegreeRoutes
