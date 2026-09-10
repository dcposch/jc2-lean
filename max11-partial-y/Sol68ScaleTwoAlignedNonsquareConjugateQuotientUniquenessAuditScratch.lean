import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIIConjugateStableAssemblyScratch

/-! # Canonical quotient-witness uniqueness audit

This compact packet records exactly which source equations suffice to
identify independently selected coordinate quotients.  It also makes the API
boundary explicit: an exported packet that omits the `p5 = H*g`, `g = H*r`
provenance cannot use this reconciliation theorem merely from its displayed
`X/Y` equations.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section ConjugateQuotientUniquenessAudit68

variable {k : Type*} [Field k] [CharZero k]

/-- Cancellation identifies any quotient whose literal numerator equation is
retained. -/
theorem coreQuotient_unique_68 (H P u v : k[X]) (hH : H ≠ 0)
    (hu : P = H * u) (hv : P = H * v) : u = v := by
  apply mul_left_cancel₀ hH
  rw [← hu, ← hv]

/-- The full canonical coordinate prefix is unique once both selections retain
the source `p5` quotient chain and the literal `p4`, `X`, and `Yd` equations. -/
theorem alignedNonsquareCanonicalCoordinatePrefix_unique_68
    (H p5 p4 p3 g₁ r₁ t₁ X₁ Y₁ g₂ r₂ t₂ X₂ Y₂ : k[X])
    (hH : H ≠ 0)
    (hg₁ : p5 = H * g₁) (hr₁ : g₁ = H * r₁)
    (ht₁ : p4 = H * t₁)
    (hX₁ : (3 : k[X]) * t₁ - r₁ ^ 2 = H * X₁)
    (hY₁ : (27 : k[X]) * p3 - r₁ ^ 3 = H * Y₁)
    (hg₂ : p5 = H * g₂) (hr₂ : g₂ = H * r₂)
    (ht₂ : p4 = H * t₂)
    (hX₂ : (3 : k[X]) * t₂ - r₂ ^ 2 = H * X₂)
    (hY₂ : (27 : k[X]) * p3 - r₂ ^ 3 = H * Y₂) :
    g₁ = g₂ ∧ r₁ = r₂ ∧ t₁ = t₂ ∧ X₁ = X₂ ∧ Y₁ = Y₂ := by
  have hg : g₁ = g₂ := coreQuotient_unique_68 H p5 g₁ g₂ hH hg₁ hg₂
  have hr : r₁ = r₂ := by
    apply mul_left_cancel₀ hH
    rw [← hr₁, ← hr₂, hg]
  have ht : t₁ = t₂ := coreQuotient_unique_68 H p4 t₁ t₂ hH ht₁ ht₂
  have hX : X₁ = X₂ := by
    apply mul_left_cancel₀ hH
    rw [← hX₁, ← hX₂, ht, hr]
  have hY : Y₁ = Y₂ := by
    apply mul_left_cancel₀ hH
    rw [← hY₁, ← hY₂, hr]
  exact ⟨hg, hr, ht, hX, hY⟩

/-- Once the common numerator itself is retained, every later single-core
quotient (such as `b₂`, `d₂`, `w₂`, `phi₁`, or `k₁`) is unique by
the same cancellation. -/
theorem alignedNonsquareNamedNumeratorQuotient_unique_68
    (H numerator u v : k[X]) (hH : H ≠ 0)
    (hu : numerator = H * u) (hv : numerator = H * v) : u = v :=
  coreQuotient_unique_68 H numerator u v hH hu hv

end ConjugateQuotientUniquenessAudit68

end Max11DegreeRoutes
