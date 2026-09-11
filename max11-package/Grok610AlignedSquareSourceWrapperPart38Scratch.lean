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

theorem alignedSquareL_eq_zero610
    (h a5 b9 : F) (hh : h ≠ 0)
    (hN : (5 : F) * a5 * h ^ 4 - (3 : F) * b9 = 0) :
    depressedL610 h (sexticDepressionR610 h a5) b9 = 0 := by
  have hL := depressedL610_eq_of_ninthPower h a5 b9 (0 : F) hh
    (by simpa using hN)
  simpa using hL

end AlignedSquareBars610

end Max11DegreeRoutes
