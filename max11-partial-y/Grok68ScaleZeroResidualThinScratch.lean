import Grok68ScaleZeroExclusionAssemblyScratch
import Grok68B3EqualityWallPacketsFalseScratch
import Grok68OffWallSupportFalseScratch
import Grok68GammaActiveRowTwoScratch

/-! # Thin the normalized `(6,8)` scale-zero open residual

Untracked working note. No tracked file was edited.

This file is pure glue.  It does not re-prove any local identity, Newton
face, I4 tie, or endgame.  Five of the six endpoint disjuncts of
`FiveToSixCuspZetaFirstEndpointOpenResidual68` are already `False` in
tracked green files; the assembly residual is rewritten as the three
packets those closures leave behind.

## Closed endpoint disjuncts (cited, not re-proved)

* Gamma-active `4N-G≤S`
  (`Grok68GammaActiveRowTwoScratch`):
  `fiveToSix_zetaFirst_gammaActive_false68`.
* NextPacket wall `4N-3S=1`
  (`Grok68B3EqualityWallPacketsFalseScratch`):
  `fiveToSix_zetaFirst_B3_equality_next_wall_false68`.
* NextTwo gamma-d wall `4N-3S=2`
  (`Grok68B3EqualityWallPacketsFalseScratch`):
  `fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_false68`.
* Constant-`Fce` wall `D<T`
  (`Grok68B3EqualityWallPacketsFalseScratch`):
  `fiveToSix_zetaFirst_B3_equality_constantFce_wall_false68`.
* Support-loaded off-wall `0<q`
  (`Grok68OffWallSupportFalseScratch`):
  `fiveToSix_zetaFirst_B3_equality_support_offWall_false68`.

## Surviving packets

* Terminal-zero packet `FiveToSixTerminalZeroPacket68`.
* Support-loaded `q=0` vanishing-A charged-integral residual
  `FiveToSixCuspZetaFirstSupportQZeroVanishingAOpenResidual68`.
* Large terminal all-nonzero cusp
  `FiveToSixLargeTerminalAllNonzeroCuspResidual68`.

Exact gain: `IntegratedPolynomialLowerSystem68OpenResidual` reduces to
`IntegratedPolynomialLowerSystem68ThinResidual`.
Next unused row: branchwise (`A_(2N-4)` vanishing-A; terminal-zero
beyond-wall; large terminal cusp).
Residual: `IntegratedPolynomialLowerSystem68ThinResidual`.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section ScaleZeroResidualThin68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Named three-packet residual -/

/-- Exact remaining packet of an integrated `(6,8)` scale-zero lower
system after deleting the five closed endpoint disjuncts.  Binders and
the two outer packets match
`IntegratedPolynomialLowerSystem68OpenResidual`. -/
def IntegratedPolynomialLowerSystem68ThinResidual
    (alpha gamma epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) : Prop :=
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  FiveToSixTerminalZeroPacket68 zeta d ee n g ∨
    (∃ N G S, n = 60 * N ∧ g = 60 * G ∧
      FiveToSixCuspZetaFirstSupportQZeroVanishingAOpenResidual68 alpha
        gamma epsilon zeta eta terminal A B
        (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E) N G S) ∨
    FiveToSixLargeTerminalAllNonzeroCuspResidual68 zeta Ae Be ce d ee n g

/-- Exclusion of the three surviving packets. -/
def IntegratedPolynomialLowerSystem68ThinResidualExclusion : Prop :=
  ∀ (alpha gamma epsilon zeta eta terminal : k)
      (A B C0 D E : k[X]),
    IntegratedPolynomialLowerSystem68ThinResidual alpha gamma epsilon zeta
      eta terminal A B C0 D E → False

/-! ## Endpoint residual after the five closed disjuncts -/

/-- The six-disjunct endpoint residual is exactly the vanishing-A
packet, once the five closed chambers are deleted. -/
theorem fiveToSix_zetaFirst_endpoint_open_residual68_thin
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (h : FiveToSixCuspZetaFirstEndpointOpenResidual68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstSupportQZeroVanishingAOpenResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S := by
  dsimp only [FiveToSixCuspZetaFirstEndpointOpenResidual68] at h
  rcases h with hGamma | hNext | hNextTwo | hConst | hOff | hVan
  · exact False.elim
      (fiveToSix_zetaFirst_gammaActive_false68 alpha gamma epsilon zeta
        eta terminal A B c d e N G S hGamma)
  · exact False.elim
      (fiveToSix_zetaFirst_B3_equality_next_wall_false68 alpha gamma
        epsilon zeta eta terminal A B c d e N G S hNext)
  · exact False.elim
      (fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_false68 alpha
        gamma epsilon zeta eta terminal A B c d e N G S hNextTwo)
  · exact False.elim
      (fiveToSix_zetaFirst_B3_equality_constantFce_wall_false68 alpha
        gamma epsilon zeta eta terminal A B c d e N G S hConst)
  · dsimp only [FiveToSixCuspZetaFirstSupportOffWallOpenResidual68] at hOff
    exact False.elim
      (fiveToSix_zetaFirst_B3_equality_support_offWall_false68 alpha gamma
        epsilon zeta eta terminal A B c d e N G S hOff.1 hOff.2)
  · exact hVan

/-! ## Source-facing lower-system residual -/

/-- Every open residual lands in the three surviving packets. -/
theorem integratedPolynomialLowerSystem68OpenResidual_thin
    (alpha gamma epsilon zeta eta terminal : k)
    (A B C0 D E : k[X])
    (h : IntegratedPolynomialLowerSystem68OpenResidual alpha gamma epsilon
      zeta eta terminal A B C0 D E) :
    IntegratedPolynomialLowerSystem68ThinResidual alpha gamma epsilon zeta
      eta terminal A B C0 D E := by
  dsimp only [IntegratedPolynomialLowerSystem68OpenResidual] at h
  dsimp only [IntegratedPolynomialLowerSystem68ThinResidual]
  rcases h with hzero | hearlier | hterm
  · exact Or.inl hzero
  · obtain ⟨N, G, S, hn, hg, hendpoint⟩ := hearlier
    refine Or.inr (Or.inl ⟨N, G, S, hn, hg, ?_⟩)
    exact fiveToSix_zetaFirst_endpoint_open_residual68_thin alpha gamma
      epsilon zeta eta terminal A B (cubicCDefectPolynomial68 A C0)
      (secondaryDDefectPolynomial68 A B D)
      (cubicEDefectPolynomial68 A C0 E) N G S hendpoint
  · exact Or.inr (Or.inr hterm)

/-- Exclusion of the three-packet residual implies exclusion of the
assembly residual. -/
theorem integratedPolynomialLowerSystem68OpenResidualExclusion_of_thinResidualExclusion
    (hres : IntegratedPolynomialLowerSystem68ThinResidualExclusion
      (k := k)) :
    IntegratedPolynomialLowerSystem68OpenResidualExclusion (k := k) := by
  intro alpha gamma epsilon zeta eta terminal A B C0 D E hopen
  exact hres alpha gamma epsilon zeta eta terminal A B C0 D E
    (integratedPolynomialLowerSystem68OpenResidual_thin alpha gamma
      epsilon zeta eta terminal A B C0 D E hopen)

/-- Complete normalized low-scale `(6,8)` route from the three-packet
scale-zero residual and the unresolved scale-two route. -/
theorem planeKellerNormalized68LowScaleRoute_of_thinResidualExclusion_scaleTwo
    (hres : IntegratedPolynomialLowerSystem68ThinResidualExclusion
      (k := k))
    (hscaleTwo : PlaneKellerNormalized68ScaleTwoRoute (k := k)) :
    PlaneKellerNormalized68LowScaleRoute (K := k) :=
  planeKellerNormalized68LowScaleRoute_of_openResidualExclusion_scaleTwo
    (integratedPolynomialLowerSystem68OpenResidualExclusion_of_thinResidualExclusion
      hres)
    hscaleTwo

end ScaleZeroResidualThin68

#print axioms fiveToSix_zetaFirst_endpoint_open_residual68_thin
#print axioms integratedPolynomialLowerSystem68OpenResidual_thin
#print axioms integratedPolynomialLowerSystem68OpenResidualExclusion_of_thinResidualExclusion
#print axioms planeKellerNormalized68LowScaleRoute_of_thinResidualExclusion_scaleTwo
#print axioms fiveToSix_zetaFirst_gammaActive_false68
#print axioms fiveToSix_zetaFirst_B3_equality_next_wall_false68
#print axioms fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_false68
#print axioms fiveToSix_zetaFirst_B3_equality_constantFce_wall_false68
#print axioms fiveToSix_zetaFirst_B3_equality_support_offWall_false68

end Max11DegreeRoutes
