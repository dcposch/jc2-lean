import Sol610ScaleTwoNonzeroFourteenthMergedJetDefinitionsDiagScratch

/-! Diagnostic leaf isolating the first merged-jet homogeneity factor. -/

noncomputable section

namespace Max11DegreeRoutes.DefinitionDiag610

variable {R : Type*} [CommRing R]

theorem nuBarAHigh610_factored_diag
    (h A B C0 E P Q R0 T : R) :
    nuBarAHigh610 (h ^ 9 * A) (h ^ 14 * B) (h ^ 18 * C0)
        (h ^ 28 * E) (h ^ 9 * P) (h ^ 14 * Q) (h ^ 18 * R0)
        (h ^ 27 * T) =
      h ^ 63 * nuJetAHigh610 h A B C0 E P Q R0 T := by
  simp only [nuBarAHigh610, nuJetAHigh610]
  ring

end Max11DegreeRoutes.DefinitionDiag610
