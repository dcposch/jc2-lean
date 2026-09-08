import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderPart05Scratch

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

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainder68
end Max11DegreeRoutes
