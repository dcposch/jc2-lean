import Sol610ScaleTwoNonzeroFourteenthMergedJetBlocksACDiagScratch
import Sol610ScaleTwoNonzeroFourteenthMergedJetHighFactorDiagScratch
import Sol610ScaleTwoNonzeroFourteenthMergedJetRemainingFactorsDiagScratch

/-! Half-prefix diagnostic through the exact source `h^63` factorization. -/

noncomputable section

namespace Max11DegreeRoutes.PrefixHalfDiag610

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
      h ^ 63 *
        nonzeroFourteenthMergedBarQuotient610 h A B C0 D E P Q R0 S T U
          V W lambda := by
  rw [nonzeroClearedFourteenthResidual610_blocks_ac_diag]
  rw [nuBarAHigh610_factored_diag, nuBarAMid610_factored_diag,
    nuBarALow610_factored_diag, nuBarAZero610_factored_diag,
    nuBarLambda610_factored_diag]
  simp only [nonzeroFourteenthMergedBarQuotient610]
  ring

def mergedNuA610 (h w1 a41 : R) : R := 12 * a41 - 5 * h * w1 ^ 2
def mergedNuB610 (h w1 a41 p32 : R) : R :=
  54 * p32 - 36 * a41 * w1 + 10 * h * w1 ^ 3
def mergedNuC610 (h w1 a41 p32 p2 : R) : R :=
  144 * p2 + 24 * a41 * h * w1 ^ 2 - 72 * h * p32 * w1 -
    5 * h ^ 2 * w1 ^ 4
def mergedNuD610 (h w1 a41 p32 p2 p1 : R) : R :=
  -108 * p2 * w1 + h * (-6 * a41 * w1 ^ 3 + 324 * p1 +
    27 * p32 * w1 ^ 2) + h ^ 2 * w1 ^ 5
def mergedNuE610 (h w1 a41 p32 p2 p1 p0 : R) : R :=
  1296 * p2 * w1 ^ 2 + h * (36 * a41 * w1 ^ 4 - 7776 * p1 * w1 -
    216 * p32 * w1 ^ 3) + h ^ 2 * (46656 * p0 - 5 * w1 ^ 6)
def mergedNuP610 (h w1 s1 lambda : R) : R :=
  4 * s1 + h * (2 * lambda * w1 - 5 * w1 ^ 2)
def mergedNuQ610 (h w1 s1 u2 lambda : R) : R :=
  -12 * s1 * w1 + 9 * u2 + h * (-3 * lambda * w1 ^ 2 + 10 * w1 ^ 3)
def mergedNuR610 (h w1 s1 u2 b62 lambda : R) : R :=
  432 * b62 + h * (336 * s1 * w1 ^ 2 - 504 * u2 * w1) +
    h ^ 2 * (56 * lambda * w1 ^ 3 - 210 * w1 ^ 4)
def mergedNuS610 (h w1 s1 u2 b62 q53 lambda : R) : R :=
  -216 * b62 * w1 + 216 * q53 +
    h * (-56 * s1 * w1 ^ 3 + 126 * u2 * w1 ^ 2) +
    h ^ 2 * (-7 * lambda * w1 ^ 4 + 28 * w1 ^ 5)
def mergedNuT610 (h w1 s1 u2 b62 q53 q41 lambda : R) : R :=
  7776 * q41 + h * (3240 * b62 * w1 ^ 2 - 6480 * q53 * w1) +
    h ^ 2 * (420 * s1 * w1 ^ 4 - 1260 * u2 * w1 ^ 3) +
    h ^ 3 * (42 * lambda * w1 ^ 5 - 175 * w1 ^ 6)
def mergedNuU610 (h w1 s1 u2 b62 q53 q41 q3 lambda : R) : R :=
  11664 * q3 - 7776 * q41 * w1 +
    h * (-1080 * b62 * w1 ^ 3 + 3240 * q53 * w1 ^ 2) +
    h ^ 2 * (-84 * s1 * w1 ^ 5 + 315 * u2 * w1 ^ 4) +
    h ^ 3 * (-7 * lambda * w1 ^ 6 + 30 * w1 ^ 7)
def mergedNuV610 (h w1 s1 u2 b62 q53 q41 q3 q2 lambda : R) : R :=
  -93312 * q3 * w1 + 31104 * q41 * w1 ^ 2 +
    h * (2160 * b62 * w1 ^ 4 + 186624 * q2 - 8640 * q53 * w1 ^ 3) +
    h ^ 2 * (112 * s1 * w1 ^ 6 - 504 * u2 * w1 ^ 5) +
    h ^ 3 * (8 * lambda * w1 ^ 7 - 35 * w1 ^ 8)
def mergedNuW610
    (h w1 s1 u2 b62 q53 q41 q3 q2 q1 lambda : R) : R :=
  419904 * q3 * w1 ^ 2 - 93312 * q41 * w1 ^ 3 +
    h * (-3888 * b62 * w1 ^ 5 - 1679616 * q2 * w1 +
      19440 * q53 * w1 ^ 4) +
    h ^ 2 * (5038848 * q1 - 144 * s1 * w1 ^ 7 + 756 * u2 * w1 ^ 6) +
    h ^ 3 * (-9 * lambda * w1 ^ 8 + 40 * w1 ^ 9)

def nonzeroFourteenthMergedJetQuotient610
    (h w1 a41 p32 s1 u2 b62 q53 p2 p1 p0 q41 q3 q2 q1 lambda : R) : R :=
  nonzeroFourteenthMergedBarQuotient610 h
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
    (mergedNuW610 h w1 s1 u2 b62 q53 q41 q3 q2 q1 lambda) lambda

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

end Max11DegreeRoutes.PrefixHalfDiag610
