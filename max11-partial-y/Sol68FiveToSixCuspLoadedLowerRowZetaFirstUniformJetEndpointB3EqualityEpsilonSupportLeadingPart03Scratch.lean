import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeadingPart02Scratch

/-! # The same-witness leading edge scalar after the support row

The retained `J` degree drop kills its actual top coefficient.  Together
with the cusp equation this is exactly `4*A_top*B_top^3+27*d_top*e_top=0`.
On the positive compensated-I4 branch, the row-one packet then gives the
additional division-free scalar `4*B_top^2*c_top+9*d_top^2=0`.  The
coefficient-zero coincidence `q=0` is kept verbatim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeading68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Same-witness source packet: the leading scalar is unconditional, while
the positive compensated-I4 branch carries the extra cusp resultant. -/
theorem fiveToSix_zetaFirst_B3_equality_support_leading_packet68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S):
    let q:=9*N-7*S
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    (4*A.coeff (2*N)*B.coeff D^3+27*d.coeff V*e.coeff E=0) ∧
      (q=0 ∨ (0<q ∧
        A.coeff (2*N)*B.coeff D^2*d.coeff V-
          (3:k)*B.coeff D*c.coeff Cc*e.coeff E=0 ∧
        B.coeff D*e.coeff E+c.coeff Cc*d.coeff V=0 ∧
        4*B.coeff D^2*c.coeff Cc+9*d.coeff V^2=0)):=by
  let q:=9*N-7*S
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  have hlead:=fiveToSix_zetaFirst_B3_equality_support_leading_scalar68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs
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
  rcases hcusp with ⟨hBtop,hctop,hdtop,hetop,hcuspEq⟩
  have hctop':c.coeff Cc≠0:=by simpa [Cc,hGS] using hctop
  have hcuspEq':A.coeff (2*N)*B.coeff D^2+
      (3:k)*c.coeff Cc^2=0:=by simpa [D,Cc,hGS] using hcuspEq
  have hsplit:=hs.2.2.2
  dsimp only [q,D,Cc,V,E] at hsplit hlead ⊢
  refine ⟨hlead,?_⟩
  rcases hsplit with hq0|hqpos
  · exact Or.inl hq0
  · right
    rcases hqpos with ⟨hq,hrel,hsum⟩
    exact ⟨hq,hrel,hsum,
      fiveToSix_zetaFirst_B3_equality_support_leading_algebra68
        (A.coeff (2*N)) (B.coeff D) (c.coeff Cc) (d.coeff V)
          (e.coeff E) hctop' hcuspEq' hsum hlead⟩

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeading68
end Max11DegreeRoutes
