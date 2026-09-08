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

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainder68
end Max11DegreeRoutes
