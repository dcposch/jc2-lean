import Sol410ScaleTwoAlignedSquareClosureScratch
import Sol410ScaleTwoNonzeroSquareExclusionScratch

/-! # Closure of the normalized `(4,10)` route

The aligned and nonzero square-core exclusions now discharge the two exact
source faces left by the scale-zero and aligned-nonsquare reductions.
-/

noncomputable section

namespace Max11DegreeRoutes

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- The fully closed normalized low-scale `(4,10)` route. -/
theorem proved_planeKellerNormalized410LowScaleRoute :
    PlaneKellerNormalized410LowScaleRoute (K := K) :=
  planeKellerNormalized410LowScaleRoute_of_squareExclusions
    planeKeller410AlignedSquareExclusion_closed
    planeKeller410_nonzeroSquareExclusion

#print axioms proved_planeKellerNormalized410LowScaleRoute

end Max11DegreeRoutes
