import LowScale410ScaleZeroGammaFinalConeElimination

/-! # Scale-zero route adapter for the normalized `(4,10)` leaf

The complete unconditional scale-zero closure
`normalized410ScaleZero_impossible` is already proved.  This module
isolates the remaining scale-two source as an explicit route interface
and upgrades it to the full normalized low-scale `(4,10)` handoff used
by the Max-11 assembly.  No scale-two exclusion is claimed.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section SourceScaleZeroAssembly410

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The only remaining normalized `(4,10)` low-scale input is now scale two. -/
def PlaneKellerNormalized410ScaleTwoRoute : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) k) (H : k[X]),
    Normalized410LeadingCoreSource P Q H 2 → PlanePairGenerates P Q

/-- Scale-zero exclusion upgrades any scale-two route to the full normalized
`(4,10)` low-scale interface used by the Max-11 assembly. -/
theorem planeKellerNormalized410LowScaleRoute_of_scaleTwo
    (hscaleTwo : PlaneKellerNormalized410ScaleTwoRoute (k := k)) :
    PlaneKellerNormalized410LowScaleRoute (K := k) := by
  intro P Q H n hn hsource
  rcases hn with rfl | rfl
  · exact (normalized410ScaleZero_impossible hsource).elim
  · exact hscaleTwo P Q H hsource

end SourceScaleZeroAssembly410

#print axioms planeKellerNormalized410LowScaleRoute_of_scaleTwo

end Max11DegreeRoutes
