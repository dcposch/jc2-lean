import Sol610ScaleTwoNonzeroFourteenthMergedJetRawSourceDefsDiagScratch

/-! Separate scale certificates for all thirteen named raw source bars. -/

noncomputable section

namespace Max11DegreeRoutes.RawSourceFactorsDiag610

open Max11DegreeRoutes.RawSourceDefsDiag610
open Max11DegreeRoutes.SourceDefsDiag610

variable {R : Type*} [CommRing R]

theorem rawNuA610_factored (h w1 a41 : R) :
    rawNuA610 h (h ^ 5 * w1) (h ^ 3 * a41) =
      h ^ 9 * mergedNuA610 h w1 a41 := by
  simp [rawNuA610, mergedNuA610]; ring

theorem rawNuB610_factored (h w1 a41 p32 : R) :
    rawNuB610 h (h ^ 5 * w1) (h ^ 3 * a41) (h ^ 2 * p32) =
      h ^ 14 * mergedNuB610 h w1 a41 p32 := by
  simp [rawNuB610, mergedNuB610]; ring

theorem rawNuC610_factored (h w1 a41 p32 p2 : R) :
    rawNuC610 h (h ^ 5 * w1) (h ^ 3 * a41) (h ^ 2 * p32) p2 =
      h ^ 18 * mergedNuC610 h w1 a41 p32 p2 := by
  simp [rawNuC610, mergedNuC610]; ring

theorem rawNuD610_factored (h w1 a41 p32 p2 p1 : R) :
    rawNuD610 h (h ^ 5 * w1) (h ^ 3 * a41) (h ^ 2 * p32) p2 p1 =
      h ^ 23 * mergedNuD610 h w1 a41 p32 p2 p1 := by
  simp [rawNuD610, mergedNuD610]; ring

theorem rawNuE610_factored (h w1 a41 p32 p2 p1 p0 : R) :
    rawNuE610 h (h ^ 5 * w1) (h ^ 3 * a41) (h ^ 2 * p32) p2 p1 p0 =
      h ^ 28 * mergedNuE610 h w1 a41 p32 p2 p1 p0 := by
  simp [rawNuE610, mergedNuE610]; ring

theorem rawNuP610_factored (h w1 s1 lambda : R) :
    rawNuP610 h (h ^ 5 * w1) (h ^ 7 * s1) lambda =
      h ^ 9 * mergedNuP610 h w1 s1 lambda := by
  simp [rawNuP610, mergedNuP610]; ring

theorem rawNuQ610_factored (h w1 s1 u2 lambda : R) :
    rawNuQ610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2) lambda =
      h ^ 14 * mergedNuQ610 h w1 s1 u2 lambda := by
  simp [rawNuQ610, mergedNuQ610]; ring

theorem rawNuR610_factored (h w1 s1 u2 b62 lambda : R) :
    rawNuR610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) lambda =
      h ^ 18 * mergedNuR610 h w1 s1 u2 b62 lambda := by
  simp [rawNuR610, mergedNuR610]; ring

theorem rawNuS610_factored (h w1 s1 u2 b62 q53 lambda : R) :
    rawNuS610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) (h ^ 3 * q53) lambda =
      h ^ 23 * mergedNuS610 h w1 s1 u2 b62 q53 lambda := by
  simp [rawNuS610, mergedNuS610]; ring

theorem rawNuT610_factored (h w1 s1 u2 b62 q53 q41 lambda : R) :
    rawNuT610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) (h ^ 3 * q53) (h * q41) lambda =
      h ^ 27 * mergedNuT610 h w1 s1 u2 b62 q53 q41 lambda := by
  simp [rawNuT610, mergedNuT610]; ring

theorem rawNuU610_factored (h w1 s1 u2 b62 q53 q41 q3 lambda : R) :
    rawNuU610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) (h ^ 3 * q53) (h * q41) q3 lambda =
      h ^ 32 * mergedNuU610 h w1 s1 u2 b62 q53 q41 q3 lambda := by
  simp [rawNuU610, mergedNuU610]; ring

theorem rawNuV610_factored (h w1 s1 u2 b62 q53 q41 q3 q2 lambda : R) :
    rawNuV610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) (h ^ 3 * q53) (h * q41) q3 q2 lambda =
      h ^ 37 * mergedNuV610 h w1 s1 u2 b62 q53 q41 q3 q2 lambda := by
  simp [rawNuV610, mergedNuV610]; ring

theorem rawNuW610_factored
    (h w1 s1 u2 b62 q53 q41 q3 q2 q1 lambda : R) :
    rawNuW610 h (h ^ 5 * w1) (h ^ 7 * s1) (h ^ 6 * u2)
        (h ^ 4 * b62) (h ^ 3 * q53) (h * q41) q3 q2 q1 lambda =
      h ^ 42 * mergedNuW610 h w1 s1 u2 b62 q53 q41 q3 q2 q1 lambda := by
  simp [rawNuW610, mergedNuW610]; ring

end Max11DegreeRoutes.RawSourceFactorsDiag610
