import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch
import Fable610ScaleZeroTwelfthDefectSpeedTPart03Scratch
import Sol610ScaleTwoDegreeZeroLocalPoleScratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareBars610

variable {F : Type*} [Field F] [CharZero F]

/-- Polynomial numerator of `12 h¹⁰ A` after the MixedPair peel. -/
def alignedSquareABar610 (h w1 e1 : F) : F :=
  (4 : F) * e1 * h ^ 9 - h ^ 8 * w1 ^ 2

end AlignedSquareBars610

end Max11DegreeRoutes
