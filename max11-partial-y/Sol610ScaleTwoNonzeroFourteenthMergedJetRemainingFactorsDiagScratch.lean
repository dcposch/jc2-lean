import Sol610ScaleTwoNonzeroFourteenthMergedJetDefinitionsDiagScratch

/-! Diagnostic leaf isolating the remaining four bar homogeneity factors. -/

noncomputable section

namespace Max11DegreeRoutes.DefinitionDiag610

variable {R : Type*} [CommRing R]

theorem nuBarAMid610_factored_diag
    (h A B C0 D E P Q R0 S T U V : R) :
    nuBarAMid610 (h ^ 9 * A) (h ^ 14 * B) (h ^ 18 * C0)
        (h ^ 23 * D) (h ^ 28 * E) (h ^ 9 * P) (h ^ 14 * Q)
        (h ^ 18 * R0) (h ^ 23 * S) (h ^ 27 * T) (h ^ 32 * U)
        (h ^ 37 * V) =
      h ^ 63 * nuJetAMid610 h A B C0 D E P Q R0 S T U V := by
  simp only [nuBarAMid610, nuJetAMid610]
  ring

theorem nuBarALow610_factored_diag
    (h A B C0 D E P Q R0 S T U V W : R) :
    nuBarALow610 (h ^ 9 * A) (h ^ 14 * B) (h ^ 18 * C0)
        (h ^ 23 * D) (h ^ 28 * E) (h ^ 9 * P) (h ^ 14 * Q)
        (h ^ 18 * R0) (h ^ 23 * S) (h ^ 27 * T) (h ^ 32 * U)
        (h ^ 37 * V) (h ^ 42 * W) =
      h ^ 63 * nuJetALow610 h A B C0 D E P Q R0 S T U V W := by
  simp only [nuBarALow610, nuJetALow610]
  ring

theorem nuBarAZero610_factored_diag
    (h B C0 D E P Q R0 S T U V W : R) :
    nuBarAZero610 (h ^ 14 * B) (h ^ 18 * C0) (h ^ 23 * D)
        (h ^ 28 * E) (h ^ 9 * P) (h ^ 14 * Q) (h ^ 18 * R0)
        (h ^ 23 * S) (h ^ 27 * T) (h ^ 32 * U) (h ^ 37 * V)
        (h ^ 42 * W) =
      h ^ 63 * nuJetAZero610 h B C0 D E P Q R0 S T U V W := by
  simp only [nuBarAZero610, nuJetAZero610]
  ring

theorem nuBarLambda610_factored_diag
    (h A B C0 D E lambda : R) :
    nuBarLambda610 (h ^ 9 * A) (h ^ 14 * B) (h ^ 18 * C0)
        (h ^ 23 * D) (h ^ 28 * E) (h ^ 5 * lambda) =
      h ^ 63 * nuJetLambda610 h A B C0 D E lambda := by
  simp only [nuBarLambda610, nuJetLambda610]
  ring

end Max11DegreeRoutes.DefinitionDiag610
