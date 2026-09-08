import Sol610ScaleTwoNonzeroFourteenthMergedJetRawSourceFactorsDiagScratch

/-! Compact source `h^63` bridge using named raw bars and scale lemmas. -/

noncomputable section

namespace Max11DegreeRoutes.FastSourceFactorDiag610

open Max11DegreeRoutes.PrefixQuarterDiag610
open Max11DegreeRoutes.SourceDefsDiag610
open Max11DegreeRoutes.RawSourceDefsDiag610
open Max11DegreeRoutes.RawSourceFactorsDiag610

variable {R : Type*} [CommRing R]

theorem nonzeroLocalClearedFourteenthDefect610_mergedJet_factored
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 lambda : R) :
    nonzeroLocalClearedFourteenthDefect610 h (h ^ 5 * w1)
        (h ^ 3 * a41) (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1)
        (h ^ 6 * u2) (h ^ 4 * b62) (h ^ 3 * q53) (h * q41)
        q3 q2 q1 lambda =
      h ^ 63 * nonzeroFourteenthMergedJetQuotient610 h w1 a41 p32 s1 u2
        b62 q53 p2 p1 p0 q41 q3 q2 q1 lambda := by
  rw [nonzeroLocalClearedFourteenthDefect610_eq_rawBars]
  rw [rawNuA610_factored, rawNuB610_factored, rawNuC610_factored,
    rawNuD610_factored, rawNuE610_factored, rawNuP610_factored,
    rawNuQ610_factored, rawNuR610_factored, rawNuS610_factored,
    rawNuT610_factored, rawNuU610_factored, rawNuV610_factored,
    rawNuW610_factored]
  rw [mul_comm lambda (h ^ 5)]
  simpa only [
      Max11DegreeRoutes.SourceDefsDiag610.nonzeroFourteenthMergedJetQuotient610] using
    (Max11DegreeRoutes.PrefixQuarterDiag610.nonzeroClearedFourteenthResidual610_mergedBar_factored h
        (mergedNuA610 h w1 a41) (mergedNuB610 h w1 a41 p32)
        (mergedNuC610 h w1 a41 p32 p2)
        (mergedNuD610 h w1 a41 p32 p2 p1)
        (mergedNuE610 h w1 a41 p32 p2 p1 p0)
        (mergedNuP610 h w1 s1 lambda) (mergedNuQ610 h w1 s1 u2 lambda)
        (mergedNuR610 h w1 s1 u2 b62 lambda)
        (mergedNuS610 h w1 s1 u2 b62 q53 lambda)
        (mergedNuT610 h w1 s1 u2 b62 q53 q41 lambda)
        (mergedNuU610 h w1 s1 u2 b62 q53 q41 q3 lambda)
        (mergedNuV610 h w1 s1 u2 b62 q53 q41 q3 q2 lambda)
        (mergedNuW610 h w1 s1 u2 b62 q53 q41 q3 q2 q1 lambda) lambda)

end Max11DegreeRoutes.FastSourceFactorDiag610
