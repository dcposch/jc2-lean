import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionThirdScratch
import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderNextScratch

/-! # Literal remainder transport for the third companion on `q=0`

The third source coefficient has exactly three exceptional arithmetic charts.
Their remainder contributions cancel against the two previously extracted
row-two jets; from `N ≥ 28` all four remainders vanish separately.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderThird68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Literal and normalized remainders agree at the third companion's two
new coefficients. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_third_transport68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let i0:=4*N-4
    let i2:=2*N-4
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
  let i0:=4*N-4
  let i2:=2*N-4
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
  have hi0pos : 0 < i0 := by dsimp only [i0];omega
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
        alpha gamma epsilon 0 eta A B c d e).coeff (4*N-4)=0:=by
    simpa only [i0] using hfull0
  have hfull2':
      (FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
        alpha gamma epsilon 0 eta A B c d e).coeff (2*N-4)=0:=by
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

/-- Exact four-chart expansion at the third source coefficients. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_clean_third_split68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let i0:=4*N-4
    let i2:=2*N-4
    let W0:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
      gamma epsilon A B c d e
    let W2:=FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
      gamma epsilon B c d
    (N=7 ∧ S=9 ∧
      W0.coeff i0=
        -(21:k)*gamma*A.coeff (2*N)*B.coeff (D-2)*c.coeff Cc-
        (39/2:k)*gamma*A.coeff (2*N-1)*B.coeff (D-1)*c.coeff Cc-
        (18:k)*gamma*A.coeff (2*N-2)*B.coeff D*c.coeff Cc-
        (21:k)*gamma*A.coeff (2*N)*B.coeff (D-1)*c.coeff (Cc-1)-
        (39/2:k)*gamma*A.coeff (2*N-1)*B.coeff D*c.coeff (Cc-1)-
        (21:k)*gamma*A.coeff (2*N)*B.coeff D*c.coeff (Cc-2) ∧
      W2.coeff i2=(99:k)*gamma*
        (B.coeff (D-2)*c.coeff Cc+B.coeff (D-1)*c.coeff (Cc-1)+
          B.coeff D*c.coeff (Cc-2))) ∨
    (N=14 ∧ S=18 ∧
      W0.coeff i0=
        -(42:k)*gamma*A.coeff (2*N)*B.coeff (D-1)*c.coeff Cc-
        (81/2:k)*gamma*A.coeff (2*N-1)*B.coeff D*c.coeff Cc-
        (42:k)*gamma*A.coeff (2*N)*B.coeff D*c.coeff (Cc-1) ∧
      W2.coeff i2=(225:k)*gamma*
        (B.coeff (D-1)*c.coeff Cc+B.coeff D*c.coeff (Cc-1))) ∨
    (N=21 ∧ S=27 ∧
      W0.coeff i0=-(63:k)*gamma*A.coeff (2*N)*B.coeff D*c.coeff Cc ∧
      W2.coeff i2=(351:k)*gamma*B.coeff D*c.coeff Cc) ∨
    (28≤N ∧ W0.coeff i0=0 ∧ W2.coeff i2=0):=by
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let i0:=4*N-4
  let i2:=2*N-4
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
  have harith:(N=7 ∧ S=9) ∨ (N=14 ∧ S=18) ∨
      (N=21 ∧ S=27) ∨ 28≤N:=by omega
  rcases harith with h7|h14|h21|hlarge
  · left
    rcases h7 with ⟨hN7,hS9⟩
    subst N;subst S
    norm_num [D,Cc,V,E] at hB' hc' hd' he'
    have hdA:(derivative A).natDegree≤13:=by
      have h:=natDegree_derivative_le A
      omega
    have hBAc:=coeff_mul_mul_two_below_bounds68 B (derivative A) c
      3 13 10 (by norm_num) (by norm_num) (by norm_num) hB' hdA hc'
    norm_num at hBAc
    have hdA13:(derivative A).coeff 13=A.coeff 14*(14:k):=by
      rw [coeff_derivative];norm_num
    have hdA12:(derivative A).coeff 12=A.coeff 13*(13:k):=by
      rw [coeff_derivative];norm_num
    have hdA11:(derivative A).coeff 11=A.coeff 12*(12:k):=by
      rw [coeff_derivative];norm_num
    rw [hdA13,hdA12,hdA11] at hBAc
    have hBc:=coeff_mul_two_below_bounds68 B (derivative c) 3 9
      (by norm_num) (by norm_num) hB'
      (by have h:=natDegree_derivative_le c;omega)
    have hcB:=coeff_mul_two_below_bounds68 c (derivative B) 10 2
      (by norm_num) (by norm_num) hc'
      (by have h:=natDegree_derivative_le B;omega)
    norm_num at hBc hcB
    simp only [coeff_derivative] at hBc hcB
    norm_num at hBc hcB
    have hlow0:((3:k)•(B*d*derivative d)+(3:k)•(derivative B*d^2)-
          (9/2*gamma:k)•(B*derivative e)+
          (9/2*gamma:k)•(d*derivative c)+
          (9/4*epsilon:k)•(d*derivative A)).natDegree<24:=by
      compute_degree
      omega
    have hlow2:((27/2*epsilon:k)•derivative d).natDegree<10:=by
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
      simp only [hdecomp,coeff_add,coeff_smul,hBAc,
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
  · right;left
    rcases h14 with ⟨hN14,hS18⟩
    subst N;subst S
    norm_num [D,Cc,V,E] at hB' hc' hd' he'
    have hdA:(derivative A).natDegree≤27:=by
      have h:=natDegree_derivative_le A
      omega
    have hBAc:=coeff_mul_mul_one_below_bounds68 B (derivative A) c
      6 27 20 (by norm_num) (by norm_num) (by norm_num) hB' hdA hc'
    norm_num at hBAc
    simp only [coeff_derivative] at hBAc
    norm_num at hBAc
    have hBc:=coeff_mul_one_below_bounds68 B (derivative c) 6 19
      (by norm_num) (by norm_num) hB'
      (by have h:=natDegree_derivative_le c;omega)
    have hcB:=coeff_mul_one_below_bounds68 c (derivative B) 20 5
      (by norm_num) (by norm_num) hc'
      (by have h:=natDegree_derivative_le B;omega)
    norm_num at hBc hcB
    simp only [coeff_derivative] at hBc hcB
    norm_num at hBc hcB
    have hlow0:((3:k)•(B*d*derivative d)+(3:k)•(derivative B*d^2)-
          (9/2*gamma:k)•(B*derivative e)+
          (9/2*gamma:k)•(d*derivative c)+
          (9/4*epsilon:k)•(d*derivative A)).natDegree<52:=by
      compute_degree
      omega
    have hlow2:((27/2*epsilon:k)•derivative d).natDegree<24:=by
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
      simp only [hdecomp,coeff_add,coeff_smul,hBAc,
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
  · right;right;left
    rcases h21 with ⟨hN21,hS27⟩
    subst N;subst S
    norm_num [D,Cc,V,E] at hB' hc' hd' he'
    have hBAc:=coeff_mul_mul_derivative_at_bounds68 B c A 9 30 42
      (by norm_num) hB' hc' hA
    norm_num at hBAc
    have hBAc':(B*derivative A*c).coeff 80=
        B.coeff 9*A.coeff 42*c.coeff 30*(42:k):=by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hBAc
    have hBc:=coeff_mul_derivative_at_bounds68 B c 9 30
      (by norm_num) hB' hc'
    have hcB:=coeff_mul_derivative_at_bounds68 c B 30 9
      (by norm_num) hc' hB'
    norm_num at hBc hcB
    have hlow0:((3:k)•(B*d*derivative d)+(3:k)•(derivative B*d^2)-
          (9/2*gamma:k)•(B*derivative e)+
          (9/2*gamma:k)•(d*derivative c)+
          (9/4*epsilon:k)•(d*derivative A)).natDegree<80:=by
      compute_degree
      omega
    have hlow2:((27/2*epsilon:k)•derivative d).natDegree<38:=by
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
  · right;right;right
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

/-- The complete literal-remainder contribution to the third companion
cancels on all four arithmetic charts. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_third_cancel68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
      alpha gamma epsilon zeta eta A B c d e
    let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
      alpha gamma epsilon zeta eta A B c d e
    (6:k)*((p-3:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*
        W0.coeff (2*p-4)+
      ((p:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*A.coeff p*
        W2.coeff (p-4)+
      ((p-3:ℕ):k)*((p-1:ℕ):k)^2*A.coeff (p-1)*
        W2.coeff (p-3)+
      ((p-3:ℕ):k)*((p-2:ℕ):k)^2*A.coeff (p-2)*
        W2.coeff (p-2)=0:=by
  let p:=2*N
  let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hold:=fiveToSix_zetaFirst_B3_equality_support_qZero_source_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hnext:=fiveToSix_zetaFirst_B3_equality_support_qZero_clean_next_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hthird:=fiveToSix_zetaFirst_B3_equality_support_qZero_clean_third_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have htransport:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_third_transport68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have htransportNext:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_next_transport68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hold hnext hthird htransport htransportNext ⊢
  rcases hthird with h7|h14|h21|hlarge
  · rcases h7 with ⟨hN,hS,hW0,hW23⟩
    rcases hnext with hn7|hn14|hnlarge
    · rcases hn7 with ⟨hN',hS',hW02,hW22⟩
      rcases hold with ho7|holarge
      · rcases ho7 with ⟨hN'',hS'',hW01,hW21⟩
        subst N;subst S
        norm_num at hW0 hW23 hW22 hW21 htransport htransportNext ⊢
        rw [htransport.1,hW0,htransport.2,hW23,
          htransportNext.2,hW22,hW21]
        ring
      · omega
    · omega
    · omega
  · rcases h14 with ⟨hN,hS,hW0,hW23⟩
    rcases hnext with hn7|hn14|hnlarge
    · omega
    · rcases hn14 with ⟨hN',hS',hW02,hW22⟩
      rcases hold with ho7|holarge
      · omega
      · rcases holarge with ⟨hNl,hW01,hW21⟩
        subst N;subst S
        norm_num at hW0 hW23 hW22 hW21 htransport htransportNext ⊢
        rw [htransport.1,hW0,htransport.2,hW23,
          htransportNext.2,hW22,hW21]
        ring
    · omega
  · rcases h21 with ⟨hN,hS,hW0,hW23⟩
    rcases hnext with hn7|hn14|hnlarge
    · omega
    · omega
    · rcases hnlarge with ⟨hNl,hW02,hW22⟩
      rcases hold with ho7|holarge
      · omega
      · rcases holarge with ⟨hNl',hW01,hW21⟩
        subst N;subst S
        norm_num at hW0 hW23 hW22 hW21 htransport htransportNext ⊢
        rw [htransport.1,hW0,htransport.2,hW23,
          htransportNext.2,hW22,hW21]
        ring
  · rcases hlarge with ⟨hNl,hW0,hW23⟩
    rcases hnext with hn7|hn14|hnlarge
    · omega
    · omega
    · rcases hnlarge with ⟨hNl',hW02,hW22⟩
      rcases hold with ho7|holarge
      · omega
      · rcases holarge with ⟨hNl'',hW01,hW21⟩
        rw [show 2*(2*N)-4=4*N-4 by omega]
        rw [htransport.1,hW0,htransport.2,hW23,
          htransportNext.2,hW22,hW21]
        ring

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_third_transport68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_clean_third_split68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_third_cancel68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderThird68

end Max11DegreeRoutes
