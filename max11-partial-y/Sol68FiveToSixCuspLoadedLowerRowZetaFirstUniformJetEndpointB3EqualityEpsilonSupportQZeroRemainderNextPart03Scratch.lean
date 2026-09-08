import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderNextPart02Scratch

/-! # The second companion's literal remainders on `q=0`

At the next source coefficients, the clean remainders have two exceptional
charts, `(N,S)=(7,9)` and `(14,18)`.  Their contributions cancel in the
second companion; from `N ≥ 21` they vanish separately.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The complete literal-remainder contribution to the second companion
cancels, including both exceptional charts. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_next_cancel68
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
    ((p-2:ℕ):k)*A.coeff (p-1)*W2.coeff (p-2)+
      (6:k)*((p-2:ℕ):k)*W0.coeff (2*p-3)+
      ((p:ℕ):k)*A.coeff p*W2.coeff (p-3)=0:=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hold:=fiveToSix_zetaFirst_B3_equality_support_qZero_source_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hnext:=fiveToSix_zetaFirst_B3_equality_support_qZero_clean_next_split68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have htransport:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_next_transport68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hold hnext htransport ⊢
  rcases hnext with hsmall|hmiddle|hlarge
  · rcases hsmall with ⟨hN,hS,hW0c,hW2c⟩
    rcases hold with hold|hold
    · rcases hold with ⟨hN',hS',hW0old,hW2old⟩
      subst N;subst S
      norm_num at hW2old hW0c hW2c htransport ⊢
      rw [hW2old,htransport.1,hW0c,htransport.2,hW2c]
      ring
    · omega
  · rcases hmiddle with ⟨hN,hS,hW0c,hW2c⟩
    rcases hold with hold|hold
    · omega
    · rcases hold with ⟨hNlarge,hW0old,hW2old⟩
      subst N;subst S
      norm_num at hW2old hW0c hW2c htransport ⊢
      rw [hW2old,htransport.1,hW0c,htransport.2,hW2c]
      ring
  · rcases hlarge with ⟨hNlarge,hW0c,hW2c⟩
    rcases hold with hold|hold
    · omega
    · rcases hold with ⟨hN14,hW0old,hW2old⟩
      rw [show 2*(2*N)-3=4*N-3 by omega]
      rw [hW2old,htransport.1,hW0c,htransport.2,hW2c]
      ring

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderNext68
end Max11DegreeRoutes
