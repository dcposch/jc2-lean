import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionThirdReductionScratch

/-! # Global consequences of the zero constant-`I4` branch -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroGlobal68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixQZeroFceZeroDeltaDescent68
    (gamma epsilon i3:k) (A B c d:k[X]):k[X]:=
  let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
  (24:k)•(d*Delta)+(16:k)•(B^3*c)+(6*gamma:k)•B^3-
    (36:k)•(B*d^2)+(81*epsilon*gamma:k)•B+
    (216*gamma:k)•(c*d)+(162*gamma^2:k)•d+(27*i3:k)•B

/-- Universal elimination identity behind the first global descent on the
zero-`Fce` branch. -/
theorem fiveToSix_qZero_Fce_Rce_Delta_descent_algebra68
    (gamma epsilon i3:k) (A B c d e:k[X]):
    let Delta:=fiveToSixCuspDiscriminantPolynomial68 A B c
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let Rce:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2+
      (9/2*gamma:k)•e+(9/4*epsilon:k)•c
    FiveToSixQZeroFceZeroDeltaDescent68 gamma epsilon i3 A B c d+
      (24:k)•(B*(Rce-(3/4*gamma:k)•B^2-(9/8:k)•C i3))=
      ((72:k)•c+(108*gamma:k)•(1:k[X]))*Fce:=by
  dsimp only [FiveToSixQZeroFceZeroDeltaDescent68,
    fiveToSixCuspDiscriminantPolynomial68]
  simp only [smul_eq_C_mul]
  ring_nf
  have hC (x:k):C x=x•(1:k[X]):=by
    rw [smul_eq_C_mul,mul_one]
  simp_rw [hC]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,one_mul,mul_one]
  module

/-- On the zero constant-coefficient branch the compensated `I4` identity
is the zero polynomial, not merely a vanishing jet.  Eliminating it from the
global compensated `I3` identity gives a new exact discriminant descent. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_global68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0)
    (hf:(((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B).coeff 0=0):
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let Rce:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2+
      (9/2*gamma:k)•e+(9/4*epsilon:k)•c
    ∃ i3:k, Fce=0 ∧
      Rce=(3/4*gamma:k)•B^2+(9/8:k)•C i3 ∧
      FiveToSixQZeroFceZeroDeltaDescent68 gamma epsilon i3 A B c d=0:=by
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let Rce:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2+
    (9/2*gamma:k)•e+(9/4*epsilon:k)•c
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  rcases hnxt.2.1 with ⟨i4,i3,hFce,hRce,hRceDeg⟩
  have hFconst:Fce=C (Fce.coeff 0):=by
    apply eq_C_of_natDegree_le_zero
    dsimp only [Fce]
    rw [hFce]
    compute_degree
  have hFzero:Fce=0:=by rw [hFconst,hf,C_0]
  have halg:=fiveToSix_qZero_Fce_Rce_Delta_descent_algebra68
    gamma epsilon i3 A B c d e
  dsimp only at halg
  have hdescent:FiveToSixQZeroFceZeroDeltaDescent68
      gamma epsilon i3 A B c d=0:=by
    dsimp only [Fce,Rce] at hFzero hRce
    rw [hFzero,hRce] at halg
    simpa only [add_sub_cancel_left,sub_self,mul_zero,smul_zero,add_zero]
      using halg
  exact ⟨i3,hFzero,hRce,hdescent⟩

#print axioms fiveToSix_qZero_Fce_Rce_Delta_descent_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_global68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroGlobal68

end Max11DegreeRoutes
