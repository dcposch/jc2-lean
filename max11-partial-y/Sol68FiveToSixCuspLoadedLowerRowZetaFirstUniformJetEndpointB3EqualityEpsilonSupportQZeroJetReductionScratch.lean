import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadExpansionScratch

/-! # The explicit first-jet companion on the `q=0` wall

Substituting both retained load expansions into the uniform companion and
cancelling its nonzero common factor leaves one completely explicit scalar
equation on the first jets.  No literal source remainder or polynomial
coefficient remains hidden in this formulation.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetReduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The exact row-zero first-jet scalar, separated out to keep the final
companion legible. -/
def FiveToSixCuspZetaFirstB3EqualitySupportQZeroRowZeroJet68
    (A B c d e:k[X]) (p D Cc V E:ℕ):k:=
  (((V:ℕ):k)+((D:ℕ):k))*
      A.coeff (p-1)*B.coeff D^2*d.coeff V+
  ((2:k)*((V:ℕ):k)+(2:k)*((D:ℕ):k)-1)*
      A.coeff p*B.coeff D*B.coeff (D-1)*d.coeff V+
  (((V:ℕ):k)+((D:ℕ):k)-1)*
      A.coeff p*B.coeff D^2*d.coeff (V-1)-
  (3:k)*(((E:ℕ):k)*B.coeff (D-1)*c.coeff Cc*e.coeff E+
    ((E:ℕ):k)*B.coeff D*c.coeff (Cc-1)*e.coeff E+
    (((E:ℕ):k)-1)*B.coeff D*c.coeff Cc*e.coeff (E-1))+
  (3:k)*(((2:k)*((Cc:ℕ):k)-1)*
      c.coeff Cc*c.coeff (Cc-1)*d.coeff V+
    ((Cc:ℕ):k)*c.coeff Cc^2*d.coeff (V-1))

/-- After expansion and cancellation, this is the complete source-backed
first-jet constraint on the exact `q=0` wall. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_jet_reduction68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    let Z0:=FiveToSixCuspZetaFirstB3EqualitySupportQZeroRowZeroJet68
      A B c d e p D Cc V E
    A.coeff (p-1)*
        ((3:k)*((2*p-1:ℕ):k)*A.coeff p*Fce.coeff 0+
          (2:k)*((p-1:ℕ):k)*B.coeff D^2*d.coeff V)+
      (2:k)*Z0+
      (2:k)*((p:ℕ):k)*A.coeff p*
        (B.coeff D^2*d.coeff (V-1)+
          (2:k)*B.coeff D*B.coeff (D-1)*d.coeff V)=0:=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let Z0:=FiveToSixCuspZetaFirstB3EqualitySupportQZeroRowZeroJet68
    A B c d e p D Cc V E
  change A.coeff (p-1)*
      ((3:k)*((2*p-1:ℕ):k)*A.coeff p*Fce.coeff 0+
        (2:k)*((p-1:ℕ):k)*B.coeff D^2*d.coeff V)+
    (2:k)*Z0+
    (2:k)*((p:ℕ):k)*A.coeff p*
      (B.coeff D^2*d.coeff (V-1)+
        (2:k)*B.coeff D*B.coeff (D-1)*d.coeff V)=0
  have hred:=fiveToSix_zetaFirst_B3_equality_support_qZero_reduction68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hred
  have hL2:=fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hL2
  have hL0:=fiveToSix_zetaFirst_B3_equality_support_qZero_rowZero_load68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hL0
  have hL0':L0.coeff (2*p-2)=Z0:=by
    dsimp only [L0,Z0,p,D,Cc,V,E,
      FiveToSixCuspZetaFirstB3EqualitySupportQZeroRowZeroJet68]
    exact hL0
  have hL2':L2.coeff (p-2)=
      (6:k)*((p-1:ℕ):k)*
        (B.coeff D^2*d.coeff (V-1)+
          (2:k)*B.coeff D*B.coeff (D-1)*d.coeff V):=by
    dsimp only [L2,p,D,V]
    exact hL2
  have hred':
      (3:k)*((p-1:ℕ):k)*A.coeff (p-1)*
          ((3:k)*((2*p-1:ℕ):k)*A.coeff p*Fce.coeff 0+
            (2:k)*((p-1:ℕ):k)*B.coeff D^2*d.coeff V)+
        (6:k)*((p-1:ℕ):k)*Z0+
        ((p:ℕ):k)*A.coeff p*
          ((6:k)*((p-1:ℕ):k)*
            (B.coeff D^2*d.coeff (V-1)+
              (2:k)*B.coeff D*B.coeff (D-1)*d.coeff V))=0:=by
    rw [hL0',hL2'] at hred
    exact hred
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hpOld:11*N-7*S=p:=by dsimp only [p];omega
  have hpk:((p-1:ℕ):k)≠0:=by
    rw [← hpOld]
    exact hnxt.2.2.2
  have hfactor:
      (3:k)*((p-1:ℕ):k)*
        (A.coeff (p-1)*
            ((3:k)*((2*p-1:ℕ):k)*A.coeff p*Fce.coeff 0+
              (2:k)*((p-1:ℕ):k)*B.coeff D^2*d.coeff V)+
          (2:k)*Z0+
          (2:k)*((p:ℕ):k)*A.coeff p*
            (B.coeff D^2*d.coeff (V-1)+
              (2:k)*B.coeff D*B.coeff (D-1)*d.coeff V))=0:=by
    linear_combination hred'
  exact (mul_eq_zero.mp hfactor).resolve_left
    (mul_ne_zero (by norm_num) hpk)

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_jet_reduction68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetReduction68

end Max11DegreeRoutes
