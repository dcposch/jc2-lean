import Max11Assembly
import Sol410NormalizedRouteClosureScratch

/-! # Max-eleven with exactly three normalized low-scale leaves

This composition backwires the complete `(4,6)` and `(4,10)` low-scale
closures into the source-facing Max-11 theorem.  Its only nonclassical local
inputs are now the normalized `(6,8)`, `(6,10)`, and `(8,10)` low-scale
routes; the two standard published global inputs remain explicit.
-/

noncomputable section

open MvPolynomial

namespace Max11DegreeRoutes

/-- Max-11 after discharging the complete normalized `(4,6)` and `(4,10)`
low-scale routes. -/
theorem Max11PlaneKellerGenerationWithThreeRemainingNormalizedLowScaleRoutes
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K))
    (h68 : PlaneKellerNormalized68LowScaleRoute (K := K))
    (h610 : PlaneKellerNormalized610LowScaleRoute (K := K))
    (h810 : PlaneKellerNormalized810LowScaleRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithFiveNormalizedLowScaleRoutes
    hprime hendpoint
    proved_planeKellerNormalized46LowScaleRoute
    proved_planeKellerNormalized410LowScaleRoute
    h68 h610 h810

#print axioms Max11PlaneKellerGenerationWithThreeRemainingNormalizedLowScaleRoutes

end Max11DegreeRoutes
