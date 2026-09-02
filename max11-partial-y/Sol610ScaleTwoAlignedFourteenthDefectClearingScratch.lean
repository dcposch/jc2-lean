import Sol610ScaleTwoAlignedFourteenthResidualConstantBridgeScratch

/-! # Same-source polynomial descent for the aligned `(6,10)` ν defect

This successor applies the verified weight-seventy clearing identity to the
same supplied square-core witness and uses the RatFunc constant-field theorem
to descend the normalized fourth-tail integral to `k[X]`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section FourteenthSourceClearing610

variable {F : Type*} [Field F] [CharZero F]

/-- Exact source-polynomial numerator of the aligned weight-seventy residual. -/
def localClearedFourteenthDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) : F[X] :=
  alignedClearedFourteenthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
    b3 b2 b1

set_option maxHeartbeats 800000000 in
/-- Clearing `19042491875328 h⁷⁰ ν` on the aligned ninth-power face. -/
theorem fourteenthDefect_eq_clearedNu610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0) (hN : 5 * a5 * h ^ 4 - 3 * b9 = 0) :
    (19042491875328 : F) * h ^ 70 *
        fourteenthResidual610
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
          (depressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3 b2 b1) =
      alignedClearedFourteenthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5
        b4 b3 b2 b1 := by
  have hL : depressedL610 h (sexticDepressionR610 h a5) b9 = 0 := by
    have h := depressedL610_eq_of_ninthPower h a5 b9 0 hh (by simpa using hN)
    simpa using h
  have hA := depressedA610_eq_cleared h a5 a4 hh
  have hB := depressedB610_eq_cleared h a5 a4 a3 hh
  have hC := depressedC610_eq_cleared h a5 a4 a3 a2 hh
  have hD := depressedD610_eq_cleared h a5 a4 a3 a2 a1 hh
  have hE := depressedE610_eq_cleared h a5 a4 a3 a2 a1 a0 hh
  have hP := depressedP610_eq_cleared_ninthPower h a5 b9 b8 0 hh
    (by simpa using hN)
  have hQ := depressedQ610_eq_cleared h a5 b9 b8 b7 0 hh
    (by simpa using hN)
  have hR := depressedR610_eq_cleared h a5 b9 b8 b7 b6 0 hh
    (by simpa using hN)
  have hS := depressedS610_eq_cleared h a5 b9 b8 b7 b6 b5 0 hh
    (by simpa using hN)
  have hT := depressedT610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 0 hh
    (by simpa using hN)
  have hU := depressedU610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 0 hh
    (by simpa using hN)
  have hV := depressedV610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 0 hh
    (by simpa using hN)
  have hW := depressedW610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1
    0 hh (by simpa using hN)
  rw [hL, hA, hB, hC, hD, hE, hP, hQ, hR, hS, hT, hU, hV, hW]
  simp only [zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  unfold alignedClearedFourteenthDefect610
  apply fourteenthResidual610_eq_cleared_aligned
  exact hh

end FourteenthSourceClearing610

end Max11DegreeRoutes
