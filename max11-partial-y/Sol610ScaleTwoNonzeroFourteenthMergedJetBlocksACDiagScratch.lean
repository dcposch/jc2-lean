import Sol610ScaleTwoNonzeroFourteenthMergedJetDefinitionsDiagScratch

/-! Diagnostic leaf certifying the exact five-block regrouping by AC only. -/

noncomputable section

namespace Max11DegreeRoutes.DefinitionDiag610

variable {R : Type*} [CommRing R]

theorem nonzeroClearedFourteenthResidual610_blocks_ac_diag
    (A B C0 D E P Q R0 S T U V W lambda : R) :
    nonzeroClearedFourteenthResidual610 A B C0 D E P Q R0 S T U V W
        lambda =
      nuBarAHigh610 A B C0 E P Q R0 T +
      nuBarAMid610 A B C0 D E P Q R0 S T U V +
      nuBarALow610 A B C0 D E P Q R0 S T U V W +
      nuBarAZero610 B C0 D E P Q R0 S T U V W +
      nuBarLambda610 A B C0 D E lambda := by
  simp only [nonzeroClearedFourteenthResidual610,
    clearedFourteenthResidual610, nuBarAHigh610, nuBarAMid610,
    nuBarALow610, nuBarAZero610, nuBarLambda610, sub_eq_add_neg,
    neg_mul, add_assoc]

end Max11DegreeRoutes.DefinitionDiag610
