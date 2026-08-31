import Max11Assembly
import Grok410ScaleTwoAlignedFaceClosureScratch
import Grok68ScaleTwoInterfaceCompositionScratch

/-! # Max-eleven with the closed `(4,10)` leaf discharged

Untracked working note.  No tracked file was edited.

This file only composes existing closed interfaces.  It does not re-prove any
local identity, Newton face, valuation kill, or classical route.

The committed `(4,10)` leaf
`proved_planeKellerNormalized410LowScaleRoute` (from
`Grok410ScaleTwoAlignedFaceClosureScratch`) discharges the `h410`
premise of `Max11PlaneKellerGenerationWithFiveNormalizedLowScaleRoutes`.
The four remaining normalized low-scale leaves, together with the two
published classical interfaces, stay explicit.

The documentation corollary restates that four-route headline after the
committed `(6,8)` composition
`planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_square_quadraticPacket`.
-/

noncomputable section

open MvPolynomial

namespace Max11DegreeRoutes

/-- Max-11 after discharging the complete normalized `(4,10)` low-scale
route.  Same statement as
`Max11PlaneKellerGenerationWithFiveNormalizedLowScaleRoutes`, with the
`h410` premise removed. -/
theorem Max11PlaneKellerGenerationWithFourNormalizedLowScaleRoutes
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K))
    (h46 : PlaneKellerNormalized46LowScaleRoute (K := K))
    (h68 : PlaneKellerNormalized68LowScaleRoute (K := K))
    (h610 : PlaneKellerNormalized610LowScaleRoute (K := K))
    (h810 : PlaneKellerNormalized810LowScaleRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithFiveNormalizedLowScaleRoutes
    hprime hendpoint
    h46
    proved_planeKellerNormalized410LowScaleRoute
    h68 h610 h810

/-- Documentation restatement of the four-route headline after the committed
`(6,8)` composition.  The residual `(6,8)` premise is the three-hypothesis
form: scale-zero polynomial lower-system exclusion, aligned square
zero-septic local-root exclusion, and aligned nonsquare quadratic-field
packet. -/
theorem Max11PlaneKellerGenerationWithFourNormalizedLowScaleRoutes_of_68scaleZeroExclusion_square_quadraticPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K))
    (h46 : PlaneKellerNormalized46LowScaleRoute (K := K))
    (hexclude : IntegratedPolynomialLowerSystem68Exclusion (k := K))
    (hsquare : PlaneKeller68AlignedSquareLocalRootExclusion (k := K))
    (hpacket : PlaneKeller68AlignedNonsquareQuadraticPacketExclusion
      (k := K))
    (h610 : PlaneKellerNormalized610LowScaleRoute (K := K))
    (h810 : PlaneKellerNormalized810LowScaleRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithFourNormalizedLowScaleRoutes
    hprime hendpoint h46
    (planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_square_quadraticPacket
      hexclude hsquare hpacket)
    h610 h810

/-- Documentation restatement using the tracked two-hypothesis `(6,8)`
adapter already available in `LowScale68ScaleZeroAssembly`. -/
theorem Max11PlaneKellerGenerationWithFourNormalizedLowScaleRoutes_of_68scaleZeroExclusion_scaleTwo
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K))
    (h46 : PlaneKellerNormalized46LowScaleRoute (K := K))
    (hexclude : IntegratedPolynomialLowerSystem68Exclusion (k := K))
    (h68two : PlaneKellerNormalized68ScaleTwoRoute (k := K))
    (h610 : PlaneKellerNormalized610LowScaleRoute (K := K))
    (h810 : PlaneKellerNormalized810LowScaleRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithFourNormalizedLowScaleRoutes
    hprime hendpoint h46
    (planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_scaleTwo
      hexclude h68two)
    h610 h810

/-- The `(4,6)` leaf is already closed.  Discharging it internally leaves
the three residual normalized low-scale routes `(6,8)`, `(6,10)`, and
`(8,10)`. -/
theorem Max11PlaneKellerGenerationWithThreeNormalizedLowScaleRoutesAfterClosed410
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K))
    (h68 : PlaneKellerNormalized68LowScaleRoute (K := K))
    (h610 : PlaneKellerNormalized610LowScaleRoute (K := K))
    (h810 : PlaneKellerNormalized810LowScaleRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithFourNormalizedLowScaleRoutes
    hprime hendpoint
    proved_planeKellerNormalized46LowScaleRoute
    h68 h610 h810

#print axioms Max11PlaneKellerGenerationWithFourNormalizedLowScaleRoutes
#print axioms Max11PlaneKellerGenerationWithFourNormalizedLowScaleRoutes_of_68scaleZeroExclusion_square_quadraticPacket
#print axioms Max11PlaneKellerGenerationWithFourNormalizedLowScaleRoutes_of_68scaleZeroExclusion_scaleTwo
#print axioms Max11PlaneKellerGenerationWithThreeNormalizedLowScaleRoutesAfterClosed410

end Max11DegreeRoutes
