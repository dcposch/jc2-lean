import Grok610AlignedSquareTowerOrders61to68Part174Scratch
import Grok610AlignedSquareTowerOrders61to68Part176Scratch

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
/-- Complement peel: orders `61`–`63` vanish identically, then remaining
numerators of orders `64` through `68` peel.  Same terminal
`h₀^{15}`-divisibility. -/
theorem alignedSquareW1Complement_orders64to68_remaining_dvd
    (h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b)
            (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q64 Q65 Q66 Q67 Q68 : k[X],
      alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b)
          (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 10 * Q64 ∧ Q64.eval a = 0 ∧
      Q64 = h0 * Q65 ∧ Q65.eval a = 0 ∧
      Q65 = h0 * Q66 ∧ Q66.eval a = 0 ∧
      Q66 = h0 * Q67 ∧ Q67.eval a = 0 ∧
      Q67 = h0 * Q68 ∧ Q68.eval a = 0 ∧
      h0 ∣ Q68 := by
  obtain ⟨Q64, hjet, h64z, hdvd64⟩ :=
    alignedSquareW1Complement_order64_remaining_dvd h0 w1n e1b e3b a2b a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear hderiv
  have hclear11 :
      algebraMap k[X] (RatFunc k) Q64 =
        (algebraMap k[X] (RatFunc k) h0) ^ (10 + 1) * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q64 rho 10 11 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 10 + 11 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  obtain ⟨Q65, h65f, hclear10, h65z, _hdvd65⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q64 rho j a 10
      (by decide) hh0 hdegree hroot h64z hclear11 hderiv
  obtain ⟨Q66, h66f, hclear9, h66z, _hdvd66⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q65 rho j a 9
      (by decide) hh0 hdegree hroot h65z hclear10 hderiv
  obtain ⟨Q67, h67f, hclear8, h67z, _hdvd67⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q66 rho j a 8
      (by decide) hh0 hdegree hroot h66z hclear9 hderiv
  obtain ⟨Q68, h68f, _hclear7, h68z, hdvd68⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q67 rho j a 7
      (by decide) hh0 hdegree hroot h67z hclear8 hderiv
  exact ⟨Q64, Q65, Q66, Q67, Q68, hjet, h64z, h65f, h65z, h66f, h66z,
    h67f, h67z, h68f, h68z, hdvd68⟩

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
