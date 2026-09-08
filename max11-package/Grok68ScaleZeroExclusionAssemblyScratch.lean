import Grok68NextTwoAndConstantFceWallsScratch
import Grok68OffWallSupportScratch
import Grok68VanishingAChargedIntegralScratch

/-! # Interface composition for the normalized `(6,8)` scale-zero exclusion

Untracked working note. No tracked file was edited.

This file only composes existing tracked and committed scratch bridges.  It
does not re-prove any local identity, Newton face, I4 tie, or endgame.

The committed source adapter
`planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_scaleTwo`
isolates `IntegratedPolynomialLowerSystem68Exclusion` as the scale-zero
premise.  The later-deep and five-to-six towers already force every
integrated system into the five-to-six window; this file records that
reduction after the closed chambers below, and pins the exact remaining
packet as one named Prop.

## Closed chambers (cited, not re-proved)

* Load wall `n=30`, `g=90` (`Grok68LoadWallScratch`):
  `maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_impossible68`.
* Mixed-delta face `2g=5n` (`Grok68MixedDeltaFaceScratch`):
  `maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalEndgame68`.
* Whole interior `3n<2g<5n` (`Grok68ResidualPacketsScratch`):
  `maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_impossible68`.
* `Fce`-zero terminal on `q=0`:
  `fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_impossible68`.
* Strict B3 cells `G<2S`: `fiveToSix_zetaFirst_B3_strict_false68`.
* Sparse endpoint: `fiveToSix_zetaFirst_sparse_endpoint_false68`.
* NextTwo epsilon-B wall `3N-2S=1`:
  `fiveToSix_zetaFirst_B3_equality_nextTwo_epsilonWall_false68`.
* Vanishing-A Case I (`B` divides `2c+C(3γ)`):
  `fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_caseI_empty68`.

## Residual sharpenings (not `False`)

* NextPacket wall `4N-3S=1`:
  `FiveToSixCuspZetaFirstB3EqualityNextPacketWallPacket68`.
* NextTwo gamma-d wall `4N-3S=2`:
  `FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallPacket68`.
* Constant-`Fce` wall `D<T`:
  `FiveToSixCuspZetaFirstB3EqualityConstantFceWallPacket68`.
* Support off-wall `0<q`:
  `FiveToSixCuspZetaFirstB3EqualitySupportOffWallResidual68`.
* Support `q=0` vanishing-A charged integral:
  `FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAChargedIntegralResidual68`.

## Exact open residual

The single named Prop `IntegratedPolynomialLowerSystem68OpenResidual` is
the remaining packet.  Its endpoint disjunct is
`FiveToSixCuspZetaFirstEndpointOpenResidual68`.  The still-open Props are
exactly:

* gamma-active `4N-G≤S`, retaining the endpoint-cell residual
* NextPacket wall packet
* NextTwo gamma-d wall packet
* constant-`Fce` wall packet
* support-loaded off-wall `0<q`
* support-loaded `q=0` vanishing-A charged-integral residual
* terminal-zero packet
* large terminal all-nonzero cusp

Exact gain: `IntegratedPolynomialLowerSystem68Exclusion` reduces to
exclusion of `IntegratedPolynomialLowerSystem68OpenResidual`.
Next unused row: branchwise (gamma pair; row one at `S+1` / `S+2` /
`S+3D`; `A_(2N-1)` off-wall; `A_(2N-4)` vanishing-A; terminal-zero
beyond-wall; large terminal cusp).
Residual: `IntegratedPolynomialLowerSystem68OpenResidual`.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section ScaleZeroExclusionAssembly68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Named residual packets -/

/-- Gamma-active endpoint cell, retained by every `*_or_residual68`. -/
def FiveToSixCuspZetaFirstGammaActiveResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  FiveToSixCuspZetaFirstEndpointCellsResidual68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧
    4 * N - G ≤ S

/-- Support-loaded off-wall `0<q` after the exact-degree identities. -/
def FiveToSixCuspZetaFirstSupportOffWallOpenResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S ∧
    FiveToSixCuspZetaFirstB3EqualitySupportOffWallResidual68
      gamma epsilon A B c d e N S

/-- Support-loaded `q=0` vanishing-A chamber after Case I and `(S)`. -/
def FiveToSixCuspZetaFirstSupportQZeroVanishingAOpenResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  FiveToSixCuspZetaFirstB3EqualitySupportLoadedPacket68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S ∧
    9 * N - 7 * S = 0 ∧
      FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingAChargedIntegralResidual68
        gamma epsilon A B c d e N S

/-- Exact endpoint residual after every committed closed B3 chamber. -/
def FiveToSixCuspZetaFirstEndpointOpenResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  FiveToSixCuspZetaFirstGammaActiveResidual68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∨
    FiveToSixCuspZetaFirstB3EqualityNextPacketWallPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S ∨
    FiveToSixCuspZetaFirstB3EqualityNextTwoGammaWallPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S ∨
    FiveToSixCuspZetaFirstB3EqualityConstantFceWallPacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S ∨
    FiveToSixCuspZetaFirstSupportOffWallOpenResidual68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S ∨
    FiveToSixCuspZetaFirstSupportQZeroVanishingAOpenResidual68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S

/-- Large-radius terminal all-nonzero cusp, unchanged by the endpoint
chambers. -/
def FiveToSixLargeTerminalAllNonzeroCuspResidual68
    (zeta : k) (A B c d e : k[X]) (n g : ℕ) : Prop :=
  120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧
    d.natDegree ≤ g - 2 * n ∧ e.natDegree ≤ g - n ∧ zeta = 0 ∧
    FiveToSixCuspEdge68 A B c d e n g (7 * n - 2 * g)

/-- Exact remaining packet of an integrated `(6,8)` scale-zero lower
system.  This is the single named residual of
`IntegratedPolynomialLowerSystem68Exclusion`. -/
def IntegratedPolynomialLowerSystem68OpenResidual
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
      FiveToSixCuspZetaFirstEndpointOpenResidual68 alpha gamma epsilon zeta
        eta terminal A B (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E) N G S) ∨
    FiveToSixLargeTerminalAllNonzeroCuspResidual68 zeta Ae Be ce d ee n g

/-- Exclusion of the exact remaining packet. -/
def IntegratedPolynomialLowerSystem68OpenResidualExclusion : Prop :=
  ∀ (alpha gamma epsilon zeta eta terminal : k)
      (A B C0 D E : k[X]),
    IntegratedPolynomialLowerSystem68OpenResidual alpha gamma epsilon zeta
      eta terminal A B C0 D E → False

/-! ## Zeta-first support from the earlier-cusp finite-stop assembly -/

/-- The simultaneous loaded wall is already `False`, so the earlier-cusp
finite-stop assembly is exactly the zeta-first support packet. -/
theorem fiveToSix_contractedEarlier_zetaFirst_support68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ)
    (hfinite : FiveToSixContractedEarlierFiniteStopAssembly68 alpha gamma
      epsilon zeta eta terminal A B c d e Ae Be ce de ee n g) :
    ∃ N G S, n = 60 * N ∧ g = 60 * G ∧
      FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
        terminal A B c d e N G S := by
  rcases hfinite.1 with
    ⟨_s, N, G, S, hn, hg, _hs, _hN, hS, hSR, hdSharp, heSharp, hpacket,
      _hsecond⟩
  have hfactor := fiveToSix_contractedCusp_firstLoad_convolution68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hpacket
    hS hSR hdSharp heSharp
  have hwall := fiveToSix_cuspLoadedWall_classify68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hpacket hfactor
  have hlower := fiveToSix_cuspLoadedLowerRow_classify68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hpacket
    hS hSR hdSharp heSharp hwall
  exact ⟨N, G, S, hn, hg,
    fiveToSix_cuspLoadedLowerRow_zetaFirst_support68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hpacket
      hS hSR hdSharp heSharp hlower⟩

/-! ## Support packet to endpoint cells -/

/-- Landed zeta-first tower: support packet through uniform jet
contraction to the endpoint-cell residual. -/
theorem fiveToSix_zetaFirst_support_to_endpoint_cells68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstEndpointCellsResidual68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S := by
  have h1 := fiveToSix_zetaFirst_next_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs
  have h2 := fiveToSix_zetaFirst_depthTwo_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h1
  have h3 := fiveToSix_zetaFirst_depthThree_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h2
  have h4 := fiveToSix_zetaFirst_depthFour_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h3
  have h5 := fiveToSix_zetaFirst_depthFive_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h4
  have h6 := fiveToSix_zetaFirst_finiteStopping_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h5
  have h7 := fiveToSix_zetaFirst_finiteLoaded_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h6
  have h8 := fiveToSix_zetaFirst_finiteLoaded_rowZero_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h7
  have h9 := fiveToSix_zetaFirst_finiteLoaded_rowOne_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h8
  have h10 := fiveToSix_zetaFirst_finiteLoaded_rowTwo_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h9
  have h11 := fiveToSix_zetaFirst_finiteLoaded_next_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h10
  have h12 := fiveToSix_zetaFirst_finiteLoaded_next_rowZero_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h11
  have h13 := fiveToSix_zetaFirst_finiteLoaded_next_rowOne_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h12
  have h14 := fiveToSix_zetaFirst_finiteLoaded_next_rowTwo_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h13
  have h15 := fiveToSix_zetaFirst_finiteLoaded_next_two_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h14
  have h16 := fiveToSix_zetaFirst_uniform_finite_recurrence_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h15
  have h17 := fiveToSix_zetaFirst_uniform_jet_contraction_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h16
  exact fiveToSix_zetaFirst_endpoint_cells_residual68
    alpha gamma epsilon zeta eta terminal A B c d e N G S h17

/-! ## Endpoint cells to the open residual -/

/-- Endpoint residual after deleting every committed `False` B3 chamber
and attaching the residual sharpenings. -/
theorem fiveToSix_zetaFirst_endpoint_open_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hj : FiveToSixCuspZetaFirstEndpointCellsResidual68 alpha gamma epsilon
      zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstEndpointOpenResidual68 alpha gamma epsilon zeta
      eta terminal A B c d e N G S := by
  rcases fiveToSix_zetaFirst_endpoint_B3_equality_after_qZero_Fce_zero_closure68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hj with
    hGamma | hwallOne | hsmall | hconstant | hsupport
  · exact Or.inl ⟨hj, hGamma⟩
  · exact Or.inr (Or.inl
      (fiveToSix_zetaFirst_B3_equality_next_wall_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        hwallOne.1 hwallOne.2))
  · rcases hsmall with ⟨hnextTwo, hwalls⟩
    rcases hwalls with hgamma | heps
    · exact Or.inr (Or.inr (Or.inl
        (fiveToSix_zetaFirst_B3_equality_nextTwo_gamma_wall_packet68
          alpha gamma epsilon zeta eta terminal A B c d e N G S
          hnextTwo hgamma)))
    · exact False.elim
        (fiveToSix_zetaFirst_B3_equality_nextTwo_epsilonWall_false68
          alpha gamma epsilon zeta eta terminal A B c d e N G S
          hnextTwo heps)
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (fiveToSix_zetaFirst_B3_equality_constantFce_wall_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        hconstant))))
  · rcases hsupport with ⟨hloaded, _⟩
    have hrow :=
      fiveToSix_zetaFirst_B3_equality_support_rowOne_packet68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded
    have hsplit := hrow.2.2.2
    rcases hsplit with hq0 | hpos
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hloaded, hq0,
        fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_charged_integral68
          alpha gamma epsilon zeta eta terminal A B c d e N G S
          hterminal hrow hq0⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hloaded,
        fiveToSix_zetaFirst_B3_equality_supportLoaded_offWall68
          alpha gamma epsilon zeta eta terminal A B c d e N G S
          hloaded hpos.1⟩))))

/-! ## Source-facing lower-system residual -/

/-- Every integrated lower system lands in the exact remaining packet. -/
theorem integratedPolynomialLowerSystem68_openResidual
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    IntegratedPolynomialLowerSystem68OpenResidual alpha gamma epsilon zeta
      eta terminal A B C0 D E := by
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
  let c0 := cubicCDefectPolynomial68 A C0
  let d0 := secondaryDDefectPolynomial68 A B D
  let e0 := cubicEDefectPolynomial68 A C0 E
  have hbase :=
    integratedPolynomialLowerSystem68_fiveToSix_finiteStop_assembly68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change FiveToSixTerminalZeroPacket68 zeta d ee n g ∨
      FiveToSixContractedEarlierFiniteStopAssembly68 alpha gamma epsilon
        zeta eta terminal A B c0 d0 e0 Ae Be ce d ee n g ∨
      FiveToSixLargeTerminalAllNonzeroCuspResidual68 zeta Ae Be ce d ee
        n g at hbase
  change IntegratedPolynomialLowerSystem68OpenResidual alpha gamma epsilon
    zeta eta terminal A B C0 D E
  dsimp only [IntegratedPolynomialLowerSystem68OpenResidual]
  rcases hbase with hzero | hearlier | hterm
  · exact Or.inl hzero
  · right; left
    obtain ⟨N, G, S, hn, hg, hsupport⟩ :=
      fiveToSix_contractedEarlier_zetaFirst_support68
        alpha gamma epsilon zeta eta terminal A B c0 d0 e0 Ae Be ce d ee
        n g hearlier
    refine ⟨N, G, S, hn, hg, ?_⟩
    exact fiveToSix_zetaFirst_endpoint_open_residual68
      alpha gamma epsilon zeta eta terminal A B c0 d0 e0 N G S hterminal
      (fiveToSix_zetaFirst_support_to_endpoint_cells68
        alpha gamma epsilon zeta eta terminal A B c0 d0 e0 N G S
        hsupport)
  · exact Or.inr (Or.inr hterm)

/-- The scale-zero polynomial lower-system exclusion reduces exactly to
exclusion of `IntegratedPolynomialLowerSystem68OpenResidual`. -/
theorem integratedPolynomialLowerSystem68Exclusion_of_openResidualExclusion
    (hres : IntegratedPolynomialLowerSystem68OpenResidualExclusion
      (k := k)) :
    IntegratedPolynomialLowerSystem68Exclusion (k := k) := by
  intro l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  exact hres alpha gamma epsilon zeta eta terminal A B C0 D E
    (integratedPolynomialLowerSystem68_openResidual
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys)

/-- Source exclusion from the residual packet exclusion. -/
theorem normalized68ScaleZero_impossible_of_openResidualExclusion
    (hres : IntegratedPolynomialLowerSystem68OpenResidualExclusion
      (k := k))
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 0) : False :=
  normalized68ScaleZero_impossible_of_lowerSystem_exclusion
    (integratedPolynomialLowerSystem68Exclusion_of_openResidualExclusion
      hres)
    hsource

/-- Complete normalized low-scale `(6,8)` route from the residual
scale-zero packet and the unresolved scale-two route. -/
theorem planeKellerNormalized68LowScaleRoute_of_openResidualExclusion_scaleTwo
    (hres : IntegratedPolynomialLowerSystem68OpenResidualExclusion
      (k := k))
    (hscaleTwo : PlaneKellerNormalized68ScaleTwoRoute (k := k)) :
    PlaneKellerNormalized68LowScaleRoute (K := k) :=
  planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_scaleTwo
    (integratedPolynomialLowerSystem68Exclusion_of_openResidualExclusion
      hres)
    hscaleTwo

end ScaleZeroExclusionAssembly68

#print axioms fiveToSix_contractedEarlier_zetaFirst_support68
#print axioms fiveToSix_zetaFirst_support_to_endpoint_cells68
#print axioms fiveToSix_zetaFirst_endpoint_open_residual68
#print axioms integratedPolynomialLowerSystem68_openResidual
#print axioms integratedPolynomialLowerSystem68Exclusion_of_openResidualExclusion
#print axioms normalized68ScaleZero_impossible_of_openResidualExclusion
#print axioms planeKellerNormalized68LowScaleRoute_of_openResidualExclusion_scaleTwo
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalEndgame68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_impossible68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_impossible68
#print axioms fiveToSix_zetaFirst_B3_strict_false68
#print axioms fiveToSix_zetaFirst_sparse_endpoint_false68
#print axioms fiveToSix_zetaFirst_B3_equality_nextTwo_epsilonWall_false68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_caseI_empty68

end Max11DegreeRoutes
