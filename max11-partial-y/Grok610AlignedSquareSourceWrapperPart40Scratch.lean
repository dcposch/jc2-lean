import LowScale68ScaleTwoAlignedNonsquareDivisibility
import Grok810SpeedValLibScratch
import Sol610ScaleTwoDegreeZeroLocalPoleScratch
import Sol610ScaleTwoDegreeZeroPrimitivePart09Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section AlignedSquareSourcePrimitive610

variable {F : Type*} [Field F] [CharZero F]

/-- The weight-fifteen primitive on the sextic-decic depression of a
literal aligned `(6,10)` source.  The ninth-power scalar is specialised
to `λ = 0`, so `L` is definitionally the depressed `z⁹` coefficient of
the aligned face. -/
def alignedSquareSourcePrimitive610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 : F) : F :=
  degreeZeroPrimitive610
    (depressedL610 h (sexticDepressionR610 h a5) b9)
    (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
    (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
    (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
    (depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1)
    (depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 a0)
    (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
    (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7)
    (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6)
    (depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5)
    (depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4)
    (depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3)
    (depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3 b2)
    (depressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3 b2
      b1)
    0

end AlignedSquareSourcePrimitive610

end Max11DegreeRoutes
