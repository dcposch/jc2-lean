import Sol68FiveToSixCuspSimultaneousTerminalSplitPart1Scratch

/-! # SPEED: theorems of `Sol68FiveToSixCuspSimultaneousTerminalScratch`, part 3 of 6, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000

section FiveToSixCuspSimultaneousTerminal68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The simultaneous first wall is impossible. -/
theorem fiveToSix_cusp_simultaneous_false68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hS : 0 < S)
    (hsim : S = 7 * N - 2 * G - S)
    (hdSharp : d.natDegree ≤ 5 * N - G - S)
    (heSharp : e.natDegree ≤ 6 * N - G - S) : False := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
  have hrow := fiveToSix_cusp_simultaneous_rowOne_scalar68
    alpha gamma epsilon zeta eta terminal A B c d e N G S
    ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
    hS hsim hdSharp heSharp
  have hface := fiveToSix_contractedCusp_firstJet68
    alpha gamma epsilon zeta eta terminal A B c d e N G S
    ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
    hS (by omega) hdSharp heSharp
  have hsq : B.coeff (3 * N - G) ^ 2 *
      e.coeff (6 * N - G - S) ^ 2 =
      c.coeff (4 * N - G) ^ 2 *
        d.coeff (5 * N - G - S) ^ 2 := by
    linear_combination
      (B.coeff (3 * N - G) * e.coeff (6 * N - G - S) -
        c.coeff (4 * N - G) * d.coeff (5 * N - G - S)) * hface.1.four
  have hW : 2 * (6 * N - G - S) = 5 * N := by omega
  have htemp :
      (6 * ((6 * N - G - S : ℕ) : k) + 15 * (N : k)) *
        c.coeff (4 * N - G) ^ 2 *
          d.coeff (5 * N - G - S) ^ 2 = 0 := by
    linear_combination
      -B.coeff (3 * N - G) ^ 2 * hrow +
      5 * (N : k) * d.coeff (5 * N - G - S) ^ 2 * hface.2 -
      6 * ((6 * N - G - S : ℕ) : k) * hsq
  have hWcast : 2 * ((6 * N - G - S : ℕ) : k) = 5 * (N : k) := by
    exact_mod_cast hW
  have hzero : (N : k) * c.coeff (4 * N - G) ^ 2 *
      d.coeff (5 * N - G - S) ^ 2 = 0 := by
    linear_combination (1 / 30 : k) * htemp -
      (1 / 10 : k) * c.coeff (4 * N - G) ^ 2 *
        d.coeff (5 * N - G - S) ^ 2 * hWcast
  have hNcast : (N : k) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  exact (mul_ne_zero (mul_ne_zero hNcast (pow_ne_zero 2 hc0))
    (pow_ne_zero 2 hds)) hzero


end FiveToSixCuspSimultaneousTerminal68

end Max11DegreeRoutes

end
