import Grok610AlignedSquareTowerOrders61to68Part172Scratch
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
/-- On `w₁ = h₀ w₁n`, cancel the polynomial `h₀⁷` and peel remaining
numerators of orders `61` through `68`.  Each step applies the
remaining-pole obstruction (the same lemma as
`alignedSquare_poleTwentyOne_head_eval_zero610`) and records one more
`h₀` factor.  After order `68` the jet is `h₀^{15}` times a pole-`6`
numerator.  This is not a closure. -/
theorem alignedSquareW1Peel_orders61to68_remaining_dvd
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q61 Q62 Q63 Q64 Q65 Q66 Q67 Q68 : k[X],
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 7 * Q61 ∧ Q61.eval a = 0 ∧
      Q61 = h0 * Q62 ∧ Q62.eval a = 0 ∧
      Q62 = h0 * Q63 ∧ Q63.eval a = 0 ∧
      Q63 = h0 * Q64 ∧ Q64.eval a = 0 ∧
      Q64 = h0 * Q65 ∧ Q65.eval a = 0 ∧
      Q65 = h0 * Q66 ∧ Q66.eval a = 0 ∧
      Q66 = h0 * Q67 ∧ Q67.eval a = 0 ∧
      Q67 = h0 * Q68 ∧ Q68.eval a = 0 ∧
      h0 ∣ Q68 := by
  obtain ⟨Q61, hjet, h61z, hdvd61⟩ :=
    alignedSquareW1Peel_order61_remaining_dvd h0 w1n e1 e3 a2 a1 a0 b8
      b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear hderiv
  have hclear14 :
      algebraMap k[X] (RatFunc k) Q61 =
        (algebraMap k[X] (RatFunc k) h0) ^ (13 + 1) * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q61 rho 7 14 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  obtain ⟨Q62, h62f, hclear13, h62z, _hdvd62⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q61 rho j a 13
      (by decide) hh0 hdegree hroot h61z hclear14 hderiv
  obtain ⟨Q63, h63f, hclear12, h63z, _hdvd63⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q62 rho j a 12
      (by decide) hh0 hdegree hroot h62z hclear13 hderiv
  obtain ⟨Q64, h64f, hclear11, h64z, _hdvd64⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q63 rho j a 11
      (by decide) hh0 hdegree hroot h63z hclear12 hderiv
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
  exact ⟨Q61, Q62, Q63, Q64, Q65, Q66, Q67, Q68, hjet, h61z, h62f, h62z,
    h63f, h63z, h64f, h64z, h65f, h65z, h66f, h66z, h67f, h67z, h68f,
    h68z, hdvd68⟩

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
