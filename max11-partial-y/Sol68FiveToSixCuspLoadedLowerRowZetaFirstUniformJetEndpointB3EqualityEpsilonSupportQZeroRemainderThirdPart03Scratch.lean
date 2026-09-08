import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderThirdPart02Scratch

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

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroRemainderThird68
end Max11DegreeRoutes
