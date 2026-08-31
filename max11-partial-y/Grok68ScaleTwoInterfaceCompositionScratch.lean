import LowScale68ScaleTwoAlignedNonsquareBridge

/-! # Interface composition for the normalized `(6,8)` scale-two graph

Untracked working note. No tracked file was edited.

This file only composes existing tracked bridges.  It does not re-prove any
local identity, Newton face, quadratic-field residual, or lower-system
exclusion.

## Closed interfaces (not hypotheses)

* `FirstIntegralThreeLocalTopFaceRoute68` is discharged by
  `firstIntegralThreeLocalTopFaceRoute68`.
* The nonzero discriminator face is discharged at source by
  `normalized68ScaleTwo_nonzeroFace_impossible`, which uses
  `SquareConstantLIntegratedLocalRootData68.scaleTwo68_impossible`.
  The stricter local-root Prop
  `PlaneKeller68NonalignedLocalRootExclusion` is therefore unused by the
  source exclusion; it is not claimed here.

## Reduced interfaces (discharged by the residual hypotheses)

* `PlaneKeller68AlignedNonsquareExclusion` by
  `planeKeller68AlignedNonsquareExclusion_of_quadraticPacket`.
* `PlaneKeller68AlignedScaleTwoExclusion` by
  `planeKeller68AlignedScaleTwoExclusion_of_square_nonsquare`.
* `PlaneKellerNormalized68ScaleTwoRoute` by
  `planeKellerNormalized68ScaleTwoRoute_of_alignedExclusion`.

## Residual open interfaces, stated as hypotheses

* `PlaneKeller68AlignedSquareLocalRootExclusion`
* `PlaneKeller68AlignedNonsquareQuadraticPacketExclusion`
* `IntegratedPolynomialLowerSystem68Exclusion` (scale-zero premise; needed
  only for the full low-scale route)
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section ScaleTwoInterfaceComposition68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The aligned scale-two source chamber reduces exactly to the square
zero-septic local-root exclusion and the nonsquare quadratic-field packet. -/
theorem planeKeller68AlignedScaleTwoExclusion_of_square_quadraticPacket
    (hsquare : PlaneKeller68AlignedSquareLocalRootExclusion (k := k))
    (hpacket : PlaneKeller68AlignedNonsquareQuadraticPacketExclusion
      (k := k)) :
    PlaneKeller68AlignedScaleTwoExclusion (k := k) :=
  planeKeller68AlignedScaleTwoExclusion_of_square_nonsquare hsquare
    (planeKeller68AlignedNonsquareExclusion_of_quadraticPacket hpacket)

/-- Full normalized `(6,8)` scale-two source exclusion from the two residual
aligned chambers.  The nonzero discriminator face is already closed. -/
theorem normalized68ScaleTwo_impossible_of_square_quadraticPacket
    (hsquare : PlaneKeller68AlignedSquareLocalRootExclusion (k := k))
    (hpacket : PlaneKeller68AlignedNonsquareQuadraticPacketExclusion
      (k := k))
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2) : False :=
  normalized68ScaleTwo_impossible_of_alignedExclusion
    (planeKeller68AlignedScaleTwoExclusion_of_square_quadraticPacket
      hsquare hpacket)
    hsource

/-- Scale-two route handoff from the same residual pair. -/
theorem planeKellerNormalized68ScaleTwoRoute_of_square_quadraticPacket
    (hsquare : PlaneKeller68AlignedSquareLocalRootExclusion (k := k))
    (hpacket : PlaneKeller68AlignedNonsquareQuadraticPacketExclusion
      (k := k)) :
    PlaneKellerNormalized68ScaleTwoRoute (k := k) :=
  planeKellerNormalized68ScaleTwoRoute_of_alignedExclusion
    (planeKeller68AlignedScaleTwoExclusion_of_square_quadraticPacket
      hsquare hpacket)

/-- The complete normalized low-scale `(6,8)` route from the scale-zero
polynomial lower-system exclusion and the two residual scale-two chambers. -/
theorem planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_square_quadraticPacket
    (hexclude : IntegratedPolynomialLowerSystem68Exclusion (k := k))
    (hsquare : PlaneKeller68AlignedSquareLocalRootExclusion (k := k))
    (hpacket : PlaneKeller68AlignedNonsquareQuadraticPacketExclusion
      (k := k)) :
    PlaneKellerNormalized68LowScaleRoute (K := k) :=
  planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_scaleTwo
    hexclude
    (planeKellerNormalized68ScaleTwoRoute_of_square_quadraticPacket
      hsquare hpacket)

end ScaleTwoInterfaceComposition68

#print axioms firstIntegralThreeLocalTopFaceRoute68
#print axioms normalized68ScaleTwo_nonzeroFace_impossible
#print axioms planeKeller68AlignedNonsquareExclusion_of_quadraticPacket
#print axioms planeKeller68AlignedScaleTwoExclusion_of_square_nonsquare
#print axioms normalized68ScaleTwo_impossible_of_alignedExclusion
#print axioms planeKellerNormalized68ScaleTwoRoute_of_alignedExclusion
#print axioms planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_scaleTwo
#print axioms planeKeller68AlignedScaleTwoExclusion_of_square_quadraticPacket
#print axioms normalized68ScaleTwo_impossible_of_square_quadraticPacket
#print axioms planeKellerNormalized68ScaleTwoRoute_of_square_quadraticPacket
#print axioms planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_square_quadraticPacket

end Max11DegreeRoutes
