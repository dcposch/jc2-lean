import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionScratch

/-! # Expanded one-lower remainders on the `q=0` support wall

Both named remainders are normalized back to the literal source rows and
expanded before applying degree bounds.  The equation `9*N=7*S` leaves
exactly the minimal chart `(N,S)=(7,9)` or `14≤N`.  Only in the latter are
the remaining `B*c'`, `c*B'`, and `B*A'*c` terms deleted by degree.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainder68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
    (gamma epsilon:k) (A B c d e:k[X]):k[X]:=
  (3:k)•(B*d*derivative d)+(3:k)•(derivative B*d^2)-
    (3/2*gamma:k)•(B*derivative A*c)-
    (9/2*gamma:k)•(B*derivative e)+
    (9/2*gamma:k)•(d*derivative c)+
    (9/4*epsilon:k)•(d*derivative A)

def FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
    (gamma epsilon:k) (B c d:k[X]):k[X]:=
  (9*gamma:k)•(B*derivative c)+(9*gamma:k)•(c*derivative B)-
    (27/2*epsilon:k)•derivative d

/-- Exact normalized expansion of the full terminal row at `zeta=0`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_clean_rowZero_expansion68
    (alpha gamma epsilon eta:k) (A B c d e:k[X]):
    (-27/4:k)•
        FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
          alpha gamma epsilon 0 eta A B c d e=
      (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
        (3/2*gamma:k)•(A*derivative A*d)+
        (3/4*epsilon:k)•(A*B*derivative A)+
        FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e)+
      FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
        gamma epsilon A B c d e:=by
  rw [show FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
      alpha gamma epsilon 0 eta A B c d e=
      secondaryResidualRowZeroPolynomial68 A B c d e+
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1/3:k)•(A*B)+d) e by rfl,
    cubicLoadRowZeroPolynomial68_uniform_pinned_eq68]
  simp only [secondaryResidualRowZeroPolynomial68,
    FiveToSixCuspZetaFirstB3EndpointRowZeroCore68,
    FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68,
    FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68,
    zero_smul,add_zero]
  module

/-- Exact normalized expansion of the full first row at `zeta=0`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_clean_rowTwo_expansion68
    (alpha gamma epsilon eta:k) (A B c d e:k[X]):
    (-27/4:k)•
        FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
          alpha gamma epsilon 0 eta A B c d e=
      (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
        (9*gamma:k)•(A*derivative d)+
        (9/2*gamma:k)•(d*derivative A)+
        (9/4*epsilon:k)•(derivative A*B)-
        (9/2*epsilon:k)•(A*derivative B)+
        FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d)+
      FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
        gamma epsilon B c d:=by
  rw [show FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
      alpha gamma epsilon 0 eta A B c d e=
      secondaryResidualRowTwoPolynomial68 A B c d e+
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1/3:k)•(A*B)+d) e by rfl,
    cubicLoadRowTwoPolynomial68_uniform_pinned_eq68]
  simp only [secondaryResidualRowTwoPolynomial68,
    FiveToSixCuspZetaFirstB3EndpointRowTwoCore68,
    FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68,
    FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68,
    zero_smul,add_zero]
  module

/-- The old exact-difference remainder and the expanded normalized
remainder agree at the two consumed source coefficients. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_transport68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let i0:=4*N-2
    let i2:=2*N-2
    let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
      alpha gamma epsilon zeta eta A B c d e
    let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
      alpha gamma epsilon zeta eta A B c d e
    W0.coeff i0=
        (FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
          gamma epsilon A B c d e).coeff i0 ∧
      W2.coeff i2=
        (FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
          gamma epsilon B c d).coeff i2:=by
  let i0:=4*N-2
  let i2:=2*N-2
  let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hz:zeta=0:=hrest.2.2.1
  rcases had with ⟨j4,j3,hj4,hj3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hi0pos : 0 < (i0 : ℕ) := by
    dsimp only [i0]
    omega
  have hfull0:=hpos i0 hi0pos
  change (FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
    alpha gamma epsilon zeta eta A B c d e).coeff i0=0 at hfull0
  rw [hz] at hfull0 ⊢
  have hfull2:
      (FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
        alpha gamma epsilon 0 eta A B c d e).coeff i2=0:=by
    rw [hz] at hrow2
    rw [show FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
      alpha gamma epsilon 0 eta A B c d e=
      secondaryResidualRowTwoPolynomial68 A B c d e+
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1/3:k)•(A*B)+d) e by rfl,hrow2]
    simp
  have hexp0:=fiveToSix_zetaFirst_B3_equality_support_clean_rowZero_expansion68
    (k:=k) alpha gamma epsilon eta A B c d e
  have hexp2:=fiveToSix_zetaFirst_B3_equality_support_clean_rowTwo_expansion68
    (k:=k) alpha gamma epsilon eta A B c d e
  have hc0:=congrArg (fun Q:k[X]=>Q.coeff i0) hexp0
  have hc2:=congrArg (fun Q:k[X]=>Q.coeff i2) hexp2
  simp only [coeff_smul,coeff_add,smul_eq_mul,hfull0,mul_zero] at hc0
  simp only [coeff_smul,coeff_add,coeff_sub,smul_eq_mul,hfull2,mul_zero]
    at hc2
  have hfull0':
      (FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
        alpha gamma epsilon 0 eta A B c d e).coeff (4*N-2)=0:=by
    simpa only [i0] using hfull0
  have hfull2':
      (FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
        alpha gamma epsilon 0 eta A B c d e).coeff (2*N-2)=0:=by
    simpa only [i2] using hfull2
  constructor
  · rw [show FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
        alpha gamma epsilon 0 eta A B c d e=
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowZero68
          alpha gamma epsilon 0 eta A B c d e-
        (FiveToSixCuspZetaFirstB3EndpointRowZeroCore68 A B c d e+
          (3/2*gamma:k)•(A*derivative A*d)+
          (3/4*epsilon:k)•(A*B*derivative A)+
          FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68
            A B c d e) by rfl]
    simp only [coeff_sub,hfull0',zero_sub,coeff_add,coeff_smul,smul_eq_mul]
    linear_combination hc0
  · rw [show FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
        alpha gamma epsilon 0 eta A B c d e=
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
          alpha gamma epsilon 0 eta A B c d e-
        (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
          (9*gamma:k)•(A*derivative d)+
          (9/2*gamma:k)•(d*derivative A)+
          (9/4*epsilon:k)•(derivative A*B)-
          (9/2*epsilon:k)•(A*derivative B)+
          FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d) by rfl]
    simp only [coeff_sub,hfull2',zero_sub,coeff_add,coeff_smul,smul_eq_mul]
    dsimp only [i2] at hc2 ⊢
    linear_combination hc2

/-- Exact arithmetic and coefficient split.  No term is deleted in the
minimal chart. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_clean_split68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let i0:=4*N-2
    let i2:=2*N-2
    let W0:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
      gamma epsilon A B c d e
    let W2:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
      gamma epsilon B c d
    (N=7 ∧ S=9 ∧
      W0.coeff i0=-(21:k)*gamma*A.coeff (2*N)*B.coeff D*c.coeff Cc ∧
      W2.coeff i2=(117:k)*gamma*B.coeff D*c.coeff Cc) ∨
    (14≤N ∧ W0.coeff i0=0 ∧ W2.coeff i2=0):=by
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let i0:=4*N-2
  let i2:=2*N-2
  let W0:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
    gamma epsilon A B c d e
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
    gamma epsilon B c d
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  rcases hs.1 with ⟨hsupport,hrows⟩
  rcases hsupport with ⟨hstop,hTD⟩
  have hEq:9*N=7*S:=by dsimp only at hTD;omega
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  have hc':c.natDegree≤Cc:=by simpa [Cc,hGS] using hc
  have hd':d.natDegree≤V:=by dsimp only [V];rw [hGS] at hd;omega
  have he':e.natDegree≤E:=by dsimp only [E];rw [hGS] at he;omega
  have harith:(N=7 ∧ S=9) ∨ 14≤N:=by omega
  rcases harith with hsmall|hlarge
  · left
    rcases hsmall with ⟨hN7,hS9⟩
    subst N;subst S
    norm_num [D,Cc,V,E] at hB' hc' hd' he'
    have hBAc:=coeff_mul_mul_derivative_at_bounds68 B c A 3 10 14
      (by norm_num) hB' hc' hA
    norm_num at hBAc
    have hBAc':(B*derivative A*c).coeff 26=
        B.coeff 3*A.coeff 14*c.coeff 10*(14:k):=by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hBAc
    have hBc:=coeff_mul_derivative_at_bounds68 B c 3 10
      (by norm_num) hB' hc'
    norm_num at hBc
    have hcB:=coeff_mul_derivative_at_bounds68 c B 10 3
      (by norm_num) hc' hB'
    norm_num at hcB
    have hlow0:(
        (3:k)•(B*d*derivative d)+(3:k)•(derivative B*d^2)-
          (9/2*gamma:k)•(B*derivative e)+
          (9/2*gamma:k)•(d*derivative c)+
          (9/4*epsilon:k)•(d*derivative A)).natDegree<26:=by
      compute_degree
      omega
    have hlow2:((27/2*epsilon:k)•derivative d).natDegree<12:=by
      compute_degree
      omega
    refine ⟨rfl,rfl,?_,?_⟩
    · have hdecomp:
          FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
              gamma epsilon A B c d e=
            -(3/2*gamma:k)•(B*derivative A*c)+
              ((3:k)•(B*d*derivative d)+(3:k)•(derivative B*d^2)-
                (9/2*gamma:k)•(B*derivative e)+
                (9/2*gamma:k)•(d*derivative c)+
                (9/4*epsilon:k)•(d*derivative A)):=by
          dsimp only [
            FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68]
          module
      simp only [hdecomp,coeff_add,coeff_smul,hBAc',
        coeff_eq_zero_of_natDegree_lt hlow0,smul_eq_mul,add_zero]
      norm_num
      ring
    · have hdecomp:
          FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
              gamma epsilon B c d=
            ((9*gamma:k)•(B*derivative c)+
              (9*gamma:k)•(c*derivative B))-
              (27/2*epsilon:k)•derivative d:=by rfl
      simp only [hdecomp,coeff_sub,coeff_add,coeff_smul,hBc,hcB,
        coeff_eq_zero_of_natDegree_lt hlow2,smul_eq_mul,sub_zero]
      norm_num
      ring
  · right
    refine ⟨hlarge,?_,?_⟩
    · apply coeff_eq_zero_of_natDegree_lt
      dsimp only [W0,i0,
        FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68]
      compute_degree
      omega
    · apply coeff_eq_zero_of_natDegree_lt
      dsimp only [W2,i2,
        FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68]
      compute_degree
      omega

/-- Clean source-facing resultant plus its exact arithmetic leaf split. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_clean_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionScalar68
      alpha gamma epsilon zeta eta A B c d e N S ∧
    (let D:=3*N-2*S
     let Cc:=4*N-2*S
     let i0:=4*N-2
     let i2:=2*N-2
     let W0:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
       gamma epsilon A B c d e
     let W2:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
       gamma epsilon B c d
     (N=7 ∧ S=9 ∧
       W0.coeff i0=-(21:k)*gamma*A.coeff (2*N)*B.coeff D*c.coeff Cc ∧
       W2.coeff i2=(117:k)*gamma*B.coeff D*c.coeff Cc) ∨
     (14≤N ∧ W0.coeff i0=0 ∧ W2.coeff i2=0)):=by
  exact ⟨fiveToSix_zetaFirst_B3_equality_support_qZero_companion68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq,
    fiveToSix_zetaFirst_B3_equality_support_qZero_clean_split68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq⟩

/-- The arithmetic split expressed on the literal source-row remainders,
rather than only on their normalized expansions. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_source_split68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let i0:=4*N-2
    let i2:=2*N-2
    let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
      alpha gamma epsilon zeta eta A B c d e
    let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
      alpha gamma epsilon zeta eta A B c d e
    (N=7 ∧ S=9 ∧
      W0.coeff i0=-(21:k)*gamma*A.coeff (2*N)*B.coeff D*c.coeff Cc ∧
      W2.coeff i2=(117:k)*gamma*B.coeff D*c.coeff Cc) ∨
    (14≤N ∧ W0.coeff i0=0 ∧ W2.coeff i2=0):=by
  have ht:=fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_transport68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hspl:=fiveToSix_zetaFirst_B3_equality_support_qZero_clean_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at ht hspl ⊢
  rcases hspl with hsmall|hlarge
  · rcases hsmall with ⟨hN,hS,h0,h2⟩
    exact Or.inl ⟨hN,hS,ht.1.trans h0,ht.2.trans h2⟩
  · rcases hlarge with ⟨hN,h0,h2⟩
    exact Or.inr ⟨hN,ht.1.trans h0,ht.2.trans h2⟩

/-- Source-facing companion equation together with the literal one-lower
remainder split. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_source_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionScalar68
      alpha gamma epsilon zeta eta A B c d e N S ∧
    (let D:=3*N-2*S
     let Cc:=4*N-2*S
     let i0:=4*N-2
     let i2:=2*N-2
     let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
       alpha gamma epsilon zeta eta A B c d e
     let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
       alpha gamma epsilon zeta eta A B c d e
     (N=7 ∧ S=9 ∧
       W0.coeff i0=-(21:k)*gamma*A.coeff (2*N)*B.coeff D*c.coeff Cc ∧
       W2.coeff i2=(117:k)*gamma*B.coeff D*c.coeff Cc) ∨
     (14≤N ∧ W0.coeff i0=0 ∧ W2.coeff i2=0)):=by
  exact ⟨fiveToSix_zetaFirst_B3_equality_support_qZero_companion68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq,
    fiveToSix_zetaFirst_B3_equality_support_qZero_source_split68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq⟩

#print axioms fiveToSix_zetaFirst_B3_equality_support_clean_rowZero_expansion68
#print axioms fiveToSix_zetaFirst_B3_equality_support_clean_rowTwo_expansion68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_transport68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_clean_split68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_clean_packet68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_source_split68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_source_packet68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainder68

end Max11DegreeRoutes
