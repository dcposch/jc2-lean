import Grok610AlignedSquareTowerOrders61to68Part212Scratch
import Grok610AlignedSquareTowerOrders61to68Part20Scratch
import Grok610AlignedSquareTowerOrders61to68Part69Scratch

noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 100000000
set_option maxHeartbeats 1600000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

section AlignedSquareTowerHeads610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 1600000000 in
/-- Frozen `w₁ = 0`: the same pole-`14` obstruction forces the frozen
order-`61` head to vanish at `a`. -/
theorem alignedSquareW1ZeroOrder61610_zero_of_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder61610 (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a) = 0 := by
  let Q61 : k[X] :=
    alignedSquareW1ZeroOrder61610 e1 e3 a2 b8
      + h0 * alignedSquareW1ZeroOrder62610 e1 e3 a2 a1 b8 b7
      + h0 ^ 2 * alignedSquareW1ZeroOrder63610 e1 e3 a2 a1 b8 b7
      + h0 ^ 3 * alignedSquareW1ZeroOrder64610 e1 e3 a2 a1 a0 b8 b7 b6
      + h0 ^ 4 * alignedSquareW1ZeroOrder65610 e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1ZeroOrder66610 e1 e3 a2 a1 a0 b7 b6 b5
      + h0 ^ 6 * alignedSquareW1ZeroOrder67610 e1 e3 a2 a1 a0 b6 b5 b4
      + h0 ^ 7 * alignedSquareW1ZeroOrder68610 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
      + h0 ^ 8 * alignedSquareW1ZeroOrder68Plus610 h0 e1 e3 a2 a1 a0 b4 b3 b2 b1
  have hscale := alignedSquareJetQuotient610_w1Zero_scale h0 e1 e3 a2 a1
    a0 b8 b7 b6 b5 b4 b3 b2 b1
  have hjet : alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1 = h0 ^ 7 * Q61 := by
    simpa [Q61] using hscale
  have hclear14 :
      algebraMap k[X] (RatFunc k) Q61 =
        (algebraMap k[X] (RatFunc k) h0) ^
            alignedSquareW1ZeroRemainingPole610 * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q61 rho 7 14 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  have hQ0 : Q61.eval a = 0 :=
    alignedSquare_poleFourteen_head_eval_zero610 a j h0 Q61 rho hdegree
      hroot hclear14 hderiv
  let Head : k[X] := alignedSquareW1ZeroOrder61610 e1 e3 a2 b8
  let Rest : k[X] :=
    alignedSquareW1ZeroOrder62610 e1 e3 a2 a1 b8 b7
      + h0 * alignedSquareW1ZeroOrder63610 e1 e3 a2 a1 b8 b7
      + h0 ^ 2 * alignedSquareW1ZeroOrder64610 e1 e3 a2 a1 a0 b8 b7 b6
      + h0 ^ 3 * alignedSquareW1ZeroOrder65610 e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 4 * alignedSquareW1ZeroOrder66610 e1 e3 a2 a1 a0 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1ZeroOrder67610 e1 e3 a2 a1 a0 b6 b5 b4
      + h0 ^ 6 * alignedSquareW1ZeroOrder68610 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
      + h0 ^ 7 * alignedSquareW1ZeroOrder68Plus610 h0 e1 e3 a2 a1 a0 b4 b3 b2 b1
  have hshape : Q61 = Head + h0 * Rest := by
    simp only [Q61, Head, Rest]
    ring
  have hO : Q61.eval a =
      alignedSquareW1ZeroOrder61610 (e1.eval a) (e3.eval a) (a2.eval a)
        (b8.eval a) := by
    rw [hshape,
      alignedSquare_eval_head_of_linear_factor610 h0 Head Rest a hroot]
    simp only [Head, alignedSquareW1ZeroOrder61610_eval]
  exact hO.symm.trans hQ0

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
