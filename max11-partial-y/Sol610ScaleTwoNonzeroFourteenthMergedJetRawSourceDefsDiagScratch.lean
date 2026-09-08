import Sol610ScaleTwoNonzeroFourteenthMergedJetSourceDefsDiagScratch

/-! Named raw source bars for a bounded source-to-merged factorization. -/

noncomputable section

namespace Max11DegreeRoutes.RawSourceDefsDiag610

variable {R : Type*} [CommRing R]

def rawNuA610 (h a5 a4 : R) : R := 12 * a4 * h ^ 6 - 5 * a5 ^ 2
def rawNuB610 (h a5 a4 a3 : R) : R :=
  54 * a3 * h ^ 12 - 36 * a4 * a5 * h ^ 6 + 10 * a5 ^ 3
def rawNuC610 (h a5 a4 a3 a2 : R) : R :=
  144 * a2 * h ^ 18 - 72 * a3 * a5 * h ^ 12 +
    24 * a4 * a5 ^ 2 * h ^ 6 - 5 * a5 ^ 4
def rawNuD610 (h a5 a4 a3 a2 a1 : R) : R :=
  324 * a1 * h ^ 24 - 108 * a2 * a5 * h ^ 18 +
    27 * a3 * a5 ^ 2 * h ^ 12 - 6 * a4 * a5 ^ 3 * h ^ 6 + a5 ^ 5
def rawNuE610 (h a5 a4 a3 a2 a1 a0 : R) : R :=
  46656 * a0 * h ^ 30 - 7776 * a1 * a5 * h ^ 24 +
    1296 * a2 * a5 ^ 2 * h ^ 18 - 216 * a3 * a5 ^ 3 * h ^ 12 +
    36 * a4 * a5 ^ 4 * h ^ 6 - 5 * a5 ^ 6
def rawNuP610 (h a5 b8 lambda : R) : R :=
  -5 * a5 ^ 2 + 2 * lambda * a5 * h ^ 5 + 4 * b8 * h ^ 2
def rawNuQ610 (h a5 b8 b7 lambda : R) : R :=
  10 * a5 ^ 3 - 3 * lambda * a5 ^ 2 * h ^ 5 -
    12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8
def rawNuR610 (h a5 b8 b7 b6 lambda : R) : R :=
  -210 * a5 ^ 4 + 56 * lambda * a5 ^ 3 * h ^ 5 +
    336 * a5 ^ 2 * b8 * h ^ 2 - 504 * a5 * b7 * h ^ 8 +
    432 * b6 * h ^ 14
def rawNuS610 (h a5 b8 b7 b6 b5 lambda : R) : R :=
  28 * a5 ^ 5 - 7 * lambda * a5 ^ 4 * h ^ 5 -
    56 * a5 ^ 3 * b8 * h ^ 2 + 126 * a5 ^ 2 * b7 * h ^ 8 -
    216 * a5 * b6 * h ^ 14 + 216 * b5 * h ^ 20
def rawNuT610 (h a5 b8 b7 b6 b5 b4 lambda : R) : R :=
  -175 * a5 ^ 6 + 42 * lambda * a5 ^ 5 * h ^ 5 +
    420 * a5 ^ 4 * b8 * h ^ 2 - 1260 * a5 ^ 3 * b7 * h ^ 8 +
    3240 * a5 ^ 2 * b6 * h ^ 14 - 6480 * a5 * b5 * h ^ 20 +
    7776 * b4 * h ^ 26
def rawNuU610 (h a5 b8 b7 b6 b5 b4 b3 lambda : R) : R :=
  30 * a5 ^ 7 - 7 * lambda * a5 ^ 6 * h ^ 5 -
    84 * a5 ^ 5 * b8 * h ^ 2 + 315 * a5 ^ 4 * b7 * h ^ 8 -
    1080 * a5 ^ 3 * b6 * h ^ 14 + 3240 * a5 ^ 2 * b5 * h ^ 20 -
    7776 * a5 * b4 * h ^ 26 + 11664 * b3 * h ^ 32
def rawNuV610 (h a5 b8 b7 b6 b5 b4 b3 b2 lambda : R) : R :=
  -35 * a5 ^ 8 + 8 * lambda * a5 ^ 7 * h ^ 5 +
    112 * a5 ^ 6 * b8 * h ^ 2 - 504 * a5 ^ 5 * b7 * h ^ 8 +
    2160 * a5 ^ 4 * b6 * h ^ 14 - 8640 * a5 ^ 3 * b5 * h ^ 20 +
    31104 * a5 ^ 2 * b4 * h ^ 26 - 93312 * a5 * b3 * h ^ 32 +
    186624 * b2 * h ^ 38
def rawNuW610 (h a5 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
  40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
    144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
    3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
    93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
    1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44

theorem nonzeroLocalClearedFourteenthDefect610_eq_rawBars
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    nonzeroLocalClearedFourteenthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6
        b5 b4 b3 b2 b1 lambda =
      nonzeroClearedFourteenthResidual610
        (rawNuA610 h a5 a4) (rawNuB610 h a5 a4 a3)
        (rawNuC610 h a5 a4 a3 a2) (rawNuD610 h a5 a4 a3 a2 a1)
        (rawNuE610 h a5 a4 a3 a2 a1 a0) (rawNuP610 h a5 b8 lambda)
        (rawNuQ610 h a5 b8 b7 lambda) (rawNuR610 h a5 b8 b7 b6 lambda)
        (rawNuS610 h a5 b8 b7 b6 b5 lambda)
        (rawNuT610 h a5 b8 b7 b6 b5 b4 lambda)
        (rawNuU610 h a5 b8 b7 b6 b5 b4 b3 lambda)
        (rawNuV610 h a5 b8 b7 b6 b5 b4 b3 b2 lambda)
        (rawNuW610 h a5 b8 b7 b6 b5 b4 b3 b2 b1 lambda)
        (lambda * h ^ 5) := by
  rfl

end Max11DegreeRoutes.RawSourceDefsDiag610
