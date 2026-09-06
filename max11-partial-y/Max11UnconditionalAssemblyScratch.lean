import Max11Assembly
import Grok410ChainPromotionScratch
import Grok68TerminalZeroMeetingCellScratch
import Grok610ScaleZeroCubicLoadWallsScratch
import Grok810RouteClosureScratch

/-! # Max-11 headline modulo the two classical citations

Every normalized low-scale leaf is closed internally; only the two classical
inputs (`PlaneKellerPrimeTotalDegreeGCDRoute`, Nagata 1989 Thm 7.3, and
`PlaneKellerStandardEndpointGCDObstruction`, GGV Cor 7.9) remain as
hypotheses. Coordinator glue, no new mathematics. -/

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section UnconditionalAssembly

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **MAX-11.** Every plane Keller pair of partial `y`-degrees at most `11`
generates, given the two classical citations. -/
theorem Max11PlaneKellerGenerationWithClassicalInterfaces
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q :=
  Max11PlaneKellerGenerationWithFiveNormalizedLowScaleRoutes
    hprime hendpoint
    proved_planeKellerNormalized46LowScaleRoute
    (planeKellerNormalized410LowScaleRoute_proved (k := K))
    proved_planeKellerNormalized68LowScaleRoute
    proved_planeKellerNormalized610LowScaleRoute
    proved_planeKellerNormalized810LowScaleRoute

end UnconditionalAssembly

#print axioms Max11PlaneKellerGenerationWithClassicalInterfaces

end Max11DegreeRoutes
