import Grok810AlignedNonsquareDegreeZeroPrimitiveScratch
import Grok810AlignedSquareChamberClosureScratch
import Grok810NonzeroFaceSplitAssemblyScratch
import Grok810ScaleZeroQuarticAssembly2Scratch

/-! # Leaf closure: the normalized `(8,10)` low-scale route

Scale zero: `planeKeller810ScaleZeroExclusion_closed7`.
Nonzero face: `planeKeller810NonzeroFaceExclusion_closed`.
Aligned square chamber: `planeKeller810AlignedSquareExclusion_closed`.
Aligned nonsquare chamber: `planeKeller810AlignedNonsquareExclusion_closed`.
Coordinator glue, no new mathematics. -/

noncomputable section

namespace Max11DegreeRoutes

section RouteClosure810

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **LEAF CLOSED.** The normalized `(8,10)` low-scale route. -/
theorem proved_planeKellerNormalized810LowScaleRoute :
    PlaneKellerNormalized810LowScaleRoute (K := K) :=
  planeKellerNormalized810LowScaleRoute_of_chamberExclusions
    planeKeller810ScaleZeroExclusion_closed7
    planeKeller810NonzeroFaceExclusion_closed
    planeKeller810AlignedSquareExclusion_closed
    planeKeller810AlignedNonsquareExclusion_closed

end RouteClosure810

#print axioms proved_planeKellerNormalized810LowScaleRoute

end Max11DegreeRoutes
