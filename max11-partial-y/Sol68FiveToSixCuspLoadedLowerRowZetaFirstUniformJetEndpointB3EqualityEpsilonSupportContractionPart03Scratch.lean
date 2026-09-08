import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportContractionPart02Scratch

/-! # Exact contraction of the post-epsilon support wall

This contracts only the six literal top-support products retained by the
support-wall module.  The sole algebraic reduction used on those products is
the cusp relation `A_top * B_top^2 + 3*c_top^2 = 0`.  In particular the
coincident wall `D=T` (where the compensated `Fce` edge is constant) is kept.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportContraction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Source-facing contraction of the retained support-loaded packet. -/
theorem fiveToSix_zetaFirst_B3_equality_supportLoaded_contracted68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S):
    FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68
      gamma epsilon A B c d e N S:=by
  rcases hs with ⟨hsupport,hrows⟩
  rcases hsupport with ⟨hstop,hTD⟩
  rcases hstop with ⟨hcur,ht,hstate,hclass,hraw0,hraw2⟩
  let D:=3*N-2*S
  let w:=2*D
  let T:=S-w
  let t:=min D T
  have htT:t=T:=by dsimp only [t];exact Nat.min_eq_right hTD
  rcases hcur with ⟨hbase,hbaseDrop⟩
  rcases hbase with ⟨hterminal,hJold,hrowOld0,hrowOld2⟩
  rcases hterminal with ⟨hgamma,hY⟩
  rcases hgamma with ⟨hgammaStop,hcontract⟩
  rcases hgammaStop with ⟨hnext,ha,hjet,hgammaRow0,hgammaRow2⟩
  rcases hnext.1 with ⟨hGS,hcell,hprev⟩
  have hsource:=hcell.1.1.1.1
  have hp:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS,hSR,hd,he,hp,hrest⟩
  rcases hp with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hstate':=hstate
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68] at hstate'
  have hfidx:3*N-2*S-(t-1)-1=9*N-7*S:=by
    dsimp only [D,w,T] at htT
    omega
  have hjidx:5*N-2*S-(t-1)-1=11*N-7*S:=by
    dsimp only [D,w,T] at htT
    omega
  rw [hfidx,hjidx] at hstate'
  rcases hcusp with ⟨hBtop,hctop,hdtop,hetop,hCusp⟩
  rw [hGS] at hgt hle hCusp hB hc hd he
  have hgt':5*N<4*S:=by omega
  have hle':4*S≤6*N:=by omega
  have hd':d.natDegree≤5*N-3*S:=by omega
  have he':e.natDegree≤6*N-3*S:=by omega
  apply fiveToSix_zetaFirst_B3_equality_support_contracted_scalar68
    gamma epsilon A B c d e N S hN hS
      hgt' hle'
      (by omega) (by dsimp only [D,w,T] at hTD;omega)
      hA hB hc hd' he' hCusp hstate' hrows

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportContraction68
end Max11DegreeRoutes
