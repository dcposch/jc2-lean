import Sol610ScaleTwoNonzeroFourteenthMergedJetQuarterPrefixDiagScratch

/-! Definition-only source-bar prefix for the merged `(6,10)` ν jet. -/

noncomputable section

namespace Max11DegreeRoutes.SourceDefsDiag610

open Max11DegreeRoutes.PrefixQuarterDiag610

variable {R : Type*} [CommRing R]

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

end Max11DegreeRoutes.SourceDefsDiag610
