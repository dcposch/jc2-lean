import Grok610AlignedSquareSourceWrapperPart06Scratch
import Grok610AlignedSquareTowerOrders61to68Part176Scratch
import Grok610AlignedSquareTowerOrders61to68Part169Scratch

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
/-- `μ = 0` after the `q₈` peel: the specialised jet is `h₀` times
`alignedSquareMuZeroQ8QuotOne610`.  Cancelling that factor leaves a
pole-`20` numerator; remaining-numerator peels then run through the
order-`68` remaining numerator.  Named mixed coefficients of orders
`61`–`68` are the `h^{k-61}` terms of the order-`61` tower; their
vanishing as frozen heads is the mixin of previous quotients, recorded
conditionally below. -/
theorem alignedSquareMuZeroQ8_orders55to68_remaining_dvd
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q55 Q56 Q57 Q58 Q59 Q60 Q61 Q62 Q63 Q64 Q65 Q66 Q67 Q68 : k[X],
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 * Q55 ∧ Q55.eval a = 0 ∧
      Q55 = h0 * Q56 ∧ Q56.eval a = 0 ∧
      Q56 = h0 * Q57 ∧ Q57.eval a = 0 ∧
      Q57 = h0 * Q58 ∧ Q58.eval a = 0 ∧
      Q58 = h0 * Q59 ∧ Q59.eval a = 0 ∧
      Q59 = h0 * Q60 ∧ Q60.eval a = 0 ∧
      Q60 = h0 * Q61 ∧ Q61.eval a = 0 ∧
      Q61 = h0 * Q62 ∧ Q62.eval a = 0 ∧
      Q62 = h0 * Q63 ∧ Q63.eval a = 0 ∧
      Q63 = h0 * Q64 ∧ Q64.eval a = 0 ∧
      Q64 = h0 * Q65 ∧ Q65.eval a = 0 ∧
      Q65 = h0 * Q66 ∧ Q66.eval a = 0 ∧
      Q66 = h0 * Q67 ∧ Q67.eval a = 0 ∧
      Q67 = h0 * Q68 ∧ Q68.eval a = 0 ∧
      h0 ∣ Q68 := by
  let Q55 : k[X] :=
    alignedSquareMuZeroQ8QuotOne610 h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5
      b4 b3 b2 b1
  have hjet :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 * Q55 := by
    simpa [Q55] using
      alignedSquareJetQuotient610_muZeroQ8_factor_one h0 w1 e1n e3 a2 a1
        a0 b8n b7 b6 b5 b4 b3 b2 b1
  have hclear20 :
      algebraMap k[X] (RatFunc k) Q55 =
        (algebraMap k[X] (RatFunc k) h0) ^ (19 + 1) * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q55 rho 1 20 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 1 + 20 := rfl
        rw [hpow] at hclear
        have hjet1 :
            alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
                (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
              h0 ^ 1 * Q55 := by
          simpa [pow_one] using hjet
        simpa [hjet1] using hclear)
  have h55z : Q55.eval a = 0 :=
    alignedSquare_localLinearPole_head_eval_zero610 20 (by decide) a j
      h0 Q55 rho hdegree hroot hclear20 hderiv
  obtain ⟨Q56, h56f, hclear19, h56z, _hdvd56⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q55 rho j a 19
      (by decide) hh0 hdegree hroot h55z hclear20 hderiv
  obtain ⟨Q57, h57f, hclear18, h57z, _hdvd57⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q56 rho j a 18
      (by decide) hh0 hdegree hroot h56z hclear19 hderiv
  obtain ⟨Q58, h58f, hclear17, h58z, _hdvd58⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q57 rho j a 17
      (by decide) hh0 hdegree hroot h57z hclear18 hderiv
  obtain ⟨Q59, h59f, hclear16, h59z, _hdvd59⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q58 rho j a 16
      (by decide) hh0 hdegree hroot h58z hclear17 hderiv
  obtain ⟨Q60, h60f, hclear15, h60z, _hdvd60⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q59 rho j a 15
      (by decide) hh0 hdegree hroot h59z hclear16 hderiv
  obtain ⟨Q61, h61f, hclear14, h61z, _hdvd61⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q60 rho j a 14
      (by decide) hh0 hdegree hroot h60z hclear15 hderiv
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
  exact ⟨Q55, Q56, Q57, Q58, Q59, Q60, Q61, Q62, Q63, Q64, Q65, Q66, Q67,
    Q68, hjet, h55z, h56f, h56z, h57f, h57z, h58f, h58z, h59f, h59z,
    h60f, h60z, h61f, h61z, h62f, h62z, h63f, h63z, h64f, h64z, h65f,
    h65z, h66f, h66z, h67f, h67z, h68f, h68z, hdvd68⟩

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
