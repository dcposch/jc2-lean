import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderPart01Scratch

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

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainder68
end Max11DegreeRoutes
