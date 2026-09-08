import Sol610ScaleTwoNonzeroFourteenthMergedJetBlocksACDiagScratch
import Sol610ScaleTwoNonzeroFourteenthMergedJetHighFactorDiagScratch
import Sol610ScaleTwoNonzeroFourteenthMergedJetRemainingFactorsDiagScratch

/-! Quarter-prefix diagnostic through the merged-bar factorization. -/

noncomputable section

namespace Max11DegreeRoutes.PrefixQuarterDiag610

open Max11DegreeRoutes.DefinitionDiag610

variable {R : Type*} [CommRing R]

def nonzeroFourteenthMergedBarQuotient610
    (h A B C0 D E P Q R0 S T U V W lambda : R) : R :=
  nuJetAHigh610 h A B C0 E P Q R0 T +
    nuJetAMid610 h A B C0 D E P Q R0 S T U V +
    nuJetALow610 h A B C0 D E P Q R0 S T U V W +
    nuJetAZero610 h B C0 D E P Q R0 S T U V W +
    nuJetLambda610 h A B C0 D E lambda

theorem nonzeroClearedFourteenthResidual610_mergedBar_factored
    (h A B C0 D E P Q R0 S T U V W lambda : R) :
    nonzeroClearedFourteenthResidual610
        (h ^ 9 * A) (h ^ 14 * B) (h ^ 18 * C0) (h ^ 23 * D)
        (h ^ 28 * E) (h ^ 9 * P) (h ^ 14 * Q) (h ^ 18 * R0)
        (h ^ 23 * S) (h ^ 27 * T) (h ^ 32 * U) (h ^ 37 * V)
        (h ^ 42 * W) (h ^ 5 * lambda) =
      h ^ 63 * nonzeroFourteenthMergedBarQuotient610 h A B C0 D E P Q R0 S
        T U V W lambda := by
  rw [nonzeroClearedFourteenthResidual610_blocks_ac_diag]
  rw [nuBarAHigh610_factored_diag, nuBarAMid610_factored_diag,
    nuBarALow610_factored_diag, nuBarAZero610_factored_diag,
    nuBarLambda610_factored_diag]
  simp only [nonzeroFourteenthMergedBarQuotient610]
  ring

end Max11DegreeRoutes.PrefixQuarterDiag610
