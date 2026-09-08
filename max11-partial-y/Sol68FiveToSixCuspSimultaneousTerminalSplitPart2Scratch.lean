import Sol68FiveToSixCuspSimultaneousTerminalSplitPart1Scratch

/-! # SPEED: theorems of `Sol68FiveToSixCuspSimultaneousTerminalScratch`, part 2 of 3, so that no single
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

theorem fiveToSix_terminal_directLowerRow68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G)) :
    FiveToSixTerminalDirectLowerRow68
      alpha gamma epsilon zeta eta terminal A B c d e N G := by
  rcases hpacket with
    ⟨hN, _hgt5, _hle6, _hA, _hB, _hc, _hd, _he, _ha, _hcusp,
      i4, i3, _hi4, _hi3, hrow0, _hrow1, _hrow2, _hpos, _hiff⟩
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * N - 2)) hrow0
  have hidx : 6 * N - 2 ≠ 0 := by omega
  simpa only [FiveToSixTerminalDirectLowerRow68, coeff_C, if_neg hidx]
    using hcoeff

#print axioms fiveToSix_cusp_simultaneous_i3_face_coeff68
#print axioms fiveToSix_cusp_simultaneous_rowOne_scalar68
#print axioms fiveToSix_cusp_simultaneous_false68
#print axioms fiveToSix_terminal_directLowerRow68

end FiveToSixCuspSimultaneousTerminal68

end Max11DegreeRoutes

end
