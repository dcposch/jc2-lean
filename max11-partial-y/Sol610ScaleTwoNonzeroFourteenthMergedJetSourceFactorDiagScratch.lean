import Sol610ScaleTwoNonzeroFourteenthMergedJetSourceDefsDiagScratch

/-! Theorem-only diagnostic for the aggregate source `h^63` bridge. -/

noncomputable section

namespace Max11DegreeRoutes.SourceFactorDiag610

open Max11DegreeRoutes.PrefixQuarterDiag610
open Max11DegreeRoutes.SourceDefsDiag610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 800000000 in
theorem nonzeroLocalClearedFourteenthDefect610_mergedJet_factored
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 lambda : R) :
    nonzeroLocalClearedFourteenthDefect610 h (h ^ 5 * w1)
        (h ^ 3 * a41) (h ^ 2 * p32) p2 p1 p0 (h ^ 7 * s1)
        (h ^ 6 * u2) (h ^ 4 * b62) (h ^ 3 * q53) (h * q41)
        q3 q2 q1 lambda =
      h ^ 63 * nonzeroFourteenthMergedJetQuotient610 h w1 a41 p32 s1 u2
        b62 q53 p2 p1 p0 q41 q3 q2 q1 lambda := by
  simp only [nonzeroLocalClearedFourteenthDefect610]
  have hA : 12 * (h ^ 3 * a41) * h ^ 6 - 5 * (h ^ 5 * w1) ^ 2 =
      h ^ 9 * mergedNuA610 h w1 a41 := by simp [mergedNuA610]; ring
  have hB : 54 * (h ^ 2 * p32) * h ^ 12 - 36 * (h ^ 3 * a41) *
          (h ^ 5 * w1) * h ^ 6 + 10 * (h ^ 5 * w1) ^ 3 =
      h ^ 14 * mergedNuB610 h w1 a41 p32 := by simp [mergedNuB610]; ring
  have hC : 144 * p2 * h ^ 18 - 72 * (h ^ 2 * p32) * (h ^ 5 * w1) * h ^ 12 +
          24 * (h ^ 3 * a41) * (h ^ 5 * w1) ^ 2 * h ^ 6 - 5 * (h ^ 5 * w1) ^ 4 =
      h ^ 18 * mergedNuC610 h w1 a41 p32 p2 := by simp [mergedNuC610]; ring
  have hD : 324 * p1 * h ^ 24 - 108 * p2 * (h ^ 5 * w1) * h ^ 18 +
          27 * (h ^ 2 * p32) * (h ^ 5 * w1) ^ 2 * h ^ 12 -
          6 * (h ^ 3 * a41) * (h ^ 5 * w1) ^ 3 * h ^ 6 + (h ^ 5 * w1) ^ 5 =
      h ^ 23 * mergedNuD610 h w1 a41 p32 p2 p1 := by simp [mergedNuD610]; ring
  have hE : 46656 * p0 * h ^ 30 - 7776 * p1 * (h ^ 5 * w1) * h ^ 24 +
          1296 * p2 * (h ^ 5 * w1) ^ 2 * h ^ 18 -
          216 * (h ^ 2 * p32) * (h ^ 5 * w1) ^ 3 * h ^ 12 +
          36 * (h ^ 3 * a41) * (h ^ 5 * w1) ^ 4 * h ^ 6 - 5 * (h ^ 5 * w1) ^ 6 =
      h ^ 28 * mergedNuE610 h w1 a41 p32 p2 p1 p0 := by simp [mergedNuE610]; ring
  have hP : -5 * (h ^ 5 * w1) ^ 2 + 2 * lambda * (h ^ 5 * w1) * h ^ 5 +
          4 * (h ^ 7 * s1) * h ^ 2 = h ^ 9 * mergedNuP610 h w1 s1 lambda := by
    simp [mergedNuP610]; ring
  have hQ : 10 * (h ^ 5 * w1) ^ 3 - 3 * lambda * (h ^ 5 * w1) ^ 2 * h ^ 5 -
          12 * (h ^ 5 * w1) * (h ^ 7 * s1) * h ^ 2 + 9 * (h ^ 6 * u2) * h ^ 8 =
      h ^ 14 * mergedNuQ610 h w1 s1 u2 lambda := by simp [mergedNuQ610]; ring
  have hR : -210 * (h ^ 5 * w1) ^ 4 + 56 * lambda * (h ^ 5 * w1) ^ 3 * h ^ 5 +
          336 * (h ^ 5 * w1) ^ 2 * (h ^ 7 * s1) * h ^ 2 -
          504 * (h ^ 5 * w1) * (h ^ 6 * u2) * h ^ 8 + 432 * (h ^ 4 * b62) * h ^ 14 =
      h ^ 18 * mergedNuR610 h w1 s1 u2 b62 lambda := by simp [mergedNuR610]; ring
  have hS : 28 * (h ^ 5 * w1) ^ 5 - 7 * lambda * (h ^ 5 * w1) ^ 4 * h ^ 5 -
          56 * (h ^ 5 * w1) ^ 3 * (h ^ 7 * s1) * h ^ 2 +
          126 * (h ^ 5 * w1) ^ 2 * (h ^ 6 * u2) * h ^ 8 -
          216 * (h ^ 5 * w1) * (h ^ 4 * b62) * h ^ 14 + 216 * (h ^ 3 * q53) * h ^ 20 =
      h ^ 23 * mergedNuS610 h w1 s1 u2 b62 q53 lambda := by simp [mergedNuS610]; ring
  have hT : -175 * (h ^ 5 * w1) ^ 6 + 42 * lambda * (h ^ 5 * w1) ^ 5 * h ^ 5 +
          420 * (h ^ 5 * w1) ^ 4 * (h ^ 7 * s1) * h ^ 2 -
          1260 * (h ^ 5 * w1) ^ 3 * (h ^ 6 * u2) * h ^ 8 +
          3240 * (h ^ 5 * w1) ^ 2 * (h ^ 4 * b62) * h ^ 14 -
          6480 * (h ^ 5 * w1) * (h ^ 3 * q53) * h ^ 20 + 7776 * (h * q41) * h ^ 26 =
      h ^ 27 * mergedNuT610 h w1 s1 u2 b62 q53 q41 lambda := by simp [mergedNuT610]; ring
  have hU : 30 * (h ^ 5 * w1) ^ 7 - 7 * lambda * (h ^ 5 * w1) ^ 6 * h ^ 5 -
          84 * (h ^ 5 * w1) ^ 5 * (h ^ 7 * s1) * h ^ 2 +
          315 * (h ^ 5 * w1) ^ 4 * (h ^ 6 * u2) * h ^ 8 -
          1080 * (h ^ 5 * w1) ^ 3 * (h ^ 4 * b62) * h ^ 14 +
          3240 * (h ^ 5 * w1) ^ 2 * (h ^ 3 * q53) * h ^ 20 -
          7776 * (h ^ 5 * w1) * (h * q41) * h ^ 26 + 11664 * q3 * h ^ 32 =
      h ^ 32 * mergedNuU610 h w1 s1 u2 b62 q53 q41 q3 lambda := by simp [mergedNuU610]; ring
  have hV : -35 * (h ^ 5 * w1) ^ 8 + 8 * lambda * (h ^ 5 * w1) ^ 7 * h ^ 5 +
          112 * (h ^ 5 * w1) ^ 6 * (h ^ 7 * s1) * h ^ 2 -
          504 * (h ^ 5 * w1) ^ 5 * (h ^ 6 * u2) * h ^ 8 +
          2160 * (h ^ 5 * w1) ^ 4 * (h ^ 4 * b62) * h ^ 14 -
          8640 * (h ^ 5 * w1) ^ 3 * (h ^ 3 * q53) * h ^ 20 +
          31104 * (h ^ 5 * w1) ^ 2 * (h * q41) * h ^ 26 -
          93312 * (h ^ 5 * w1) * q3 * h ^ 32 + 186624 * q2 * h ^ 38 =
      h ^ 37 * mergedNuV610 h w1 s1 u2 b62 q53 q41 q3 q2 lambda := by simp [mergedNuV610]; ring
  have hW : 40 * (h ^ 5 * w1) ^ 9 - 9 * lambda * (h ^ 5 * w1) ^ 8 * h ^ 5 -
          144 * (h ^ 5 * w1) ^ 7 * (h ^ 7 * s1) * h ^ 2 +
          756 * (h ^ 5 * w1) ^ 6 * (h ^ 6 * u2) * h ^ 8 -
          3888 * (h ^ 5 * w1) ^ 5 * (h ^ 4 * b62) * h ^ 14 +
          19440 * (h ^ 5 * w1) ^ 4 * (h ^ 3 * q53) * h ^ 20 -
          93312 * (h ^ 5 * w1) ^ 3 * (h * q41) * h ^ 26 +
          419904 * (h ^ 5 * w1) ^ 2 * q3 * h ^ 32 -
          1679616 * (h ^ 5 * w1) * q2 * h ^ 38 + 5038848 * q1 * h ^ 44 =
      h ^ 42 * mergedNuW610 h w1 s1 u2 b62 q53 q41 q3 q2 q1 lambda := by simp [mergedNuW610]; ring
  rw [hA, hB, hC, hD, hE, hP, hQ, hR, hS, hT, hU, hV, hW]
  unfold nonzeroFourteenthMergedJetQuotient610
  apply nonzeroClearedFourteenthResidual610_mergedBar_factored


end Max11DegreeRoutes.SourceFactorDiag610

