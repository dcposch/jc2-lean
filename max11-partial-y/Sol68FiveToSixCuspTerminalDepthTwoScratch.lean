import Sol68FiveToSixCuspTerminalLowerRowScratch

/-! # The apparent depth-two terminal walls are arithmetically empty

The next literal source coefficients are I4 coefficient `2N-2` and
row-zero coefficient `6N-3`.  They are extracted here without replacing
the constant source right-hand sides by polynomial zero.  In the large
contracted chamber, however, both prospective loads are already excluded:
`2G ≤ 6N` gives `7N-2G ≥ N ≥ 3`, while `5N < 2G` and `2 < N` give
`3G-7N ≥ 3`.  Thus I4 says the second face-sum jet is zero and row zero is
dependent at this depth.  The first genuinely loaded successor is depth
three, at I4 coefficient `2N-3` / row-zero coefficient `6N-4`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspTerminalDepthTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The next I4 coefficient, directly extracted from its literal constant
source right-hand side. -/
def FiveToSixTerminalDirectI4Two68
    (gamma epsilon zeta : k) (A B c d e : k[X]) (N : ℕ) : Prop :=
  (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (2 * N - 2) = 0

theorem fiveToSix_terminal_directI4Two68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G)) :
    FiveToSixTerminalDirectI4Two68 gamma epsilon zeta A B c d e N := by
  rcases hpacket with
    ⟨_hN, _hgt5, _hle6, _hA, _hB, _hc, _hd, _he, _ha, _hcusp,
      i4, _i3, hi4, _hi3, _hrow0, _hrow1, _hrow2, _hpos, _hiff⟩
  have hcoeff := congrArg (fun p : k[X] => p.coeff (2 * N - 2)) hi4
  have hidx : 2 * N - 2 ≠ 0 := by omega
  simpa only [FiveToSixTerminalDirectI4Two68, coeff_C, if_neg hidx]
    using hcoeff

/-- The next row-zero coefficient, also taken directly from the literal
constant source right-hand side. -/
def FiveToSixTerminalDirectLowerRowTwo68
    (alpha gamma epsilon zeta eta : k)
    (A B c d e : k[X]) (N : ℕ) : Prop :=
  (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * N - 3) = 0

theorem fiveToSix_terminal_directLowerRowTwo68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G)) :
    FiveToSixTerminalDirectLowerRowTwo68
      alpha gamma epsilon zeta eta A B c d e N := by
  rcases hpacket with
    ⟨_hN, _hgt5, _hle6, _hA, _hB, _hc, _hd, _he, _ha, _hcusp,
      _i4, _i3, _hi4, _hi3, hrow0, _hrow1, _hrow2, _hpos, _hiff⟩
  have hcoeff := congrArg (fun p : k[X] => p.coeff (6 * N - 3)) hrow0
  have hidx : 6 * N - 3 ≠ 0 := by omega
  simpa only [FiveToSixTerminalDirectLowerRowTwo68, coeff_C, if_neg hidx]
    using hcoeff

/-- Exact classification of the two prospective depth-two loads.  Both
walls are empty in the retained large chamber; no coefficient equation or
strict/equality incompatibility is used. -/
theorem fiveToSix_terminal_depth_two_walls_empty68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G)) :
    7 * N - 2 * G ≠ 2 ∧ 3 * G - 7 * N ≠ 2 ∧
      3 ≤ 7 * N - 2 * G ∧ 3 ≤ 3 * G - 7 * N := by
  rcases hpacket with ⟨_hN, hgt5, hle6, _rest⟩
  omega

/-- With the empty depth-two walls removed, the exact I4 coefficient is
the vanishing second jet of `B*e+c*d`. -/
theorem fiveToSix_terminal_i4_faceSum_two_zero68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N)
    (hzeta : zeta = 0) :
    (B * e + c * d).coeff (2 * N - 2) = 0 := by
  have hdepth := fiveToSix_terminal_depth_two_walls_empty68
    alpha gamma epsilon zeta eta terminal A B c d e N G hNbig hpacket
  rcases hpacket with
    ⟨_hN, hgt5, hle6, _hA, hB, _hc, _hd, _he, _ha, _hcusp,
      i4, _i3, hi4, _hi3, _hrow0, _hrow1, _hrow2, _hpos, _hiff⟩
  have hidx : 0 < 2 * N - 2 := by omega
  have hB3low : (B ^ 3).natDegree < 2 * N - 2 := by
    compute_degree
    omega
  have hBlow : B.natDegree < 2 * N - 2 := by omega
  have hdlow : d.natDegree < 2 * N - 2 := by omega
  have hcoeff := congrArg (fun p : k[X] => p.coeff (2 * N - 2)) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    hzeta] at hcoeff
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt hidx, if_false,
    coeff_eq_zero_of_natDegree_lt hB3low,
    coeff_eq_zero_of_natDegree_lt hBlow,
    coeff_eq_zero_of_natDegree_lt hdlow, zero_mul, add_zero] at hcoeff
  rw [coeff_add]
  linear_combination (3 / 8 : k) * hcoeff

/-- Honest terminal successor carrying both newly extracted literal source
coefficients and the strengthened arithmetic depths. -/
def FiveToSixTerminalCuspDepthThreeResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ) : Prop :=
  FiveToSixTerminalCuspDepthResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G ∧
    3 ≤ 7 * N - 2 * G ∧ 3 ≤ 3 * G - 7 * N ∧
    FiveToSixTerminalDirectI4Two68 gamma epsilon zeta A B c d e N ∧
    FiveToSixTerminalDirectLowerRowTwo68
      alpha gamma epsilon zeta eta A B c d e N

theorem fiveToSix_terminal_cusp_depth_three_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hres : FiveToSixTerminalCuspDepthResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G) :
    FiveToSixTerminalCuspDepthThreeResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G := by
  rcases hres with
    ⟨hNbig, hdTerminal, heTerminal, hzeta, hR2, hL2, hpacket, hrowOne⟩
  have hdepth := fiveToSix_terminal_depth_two_walls_empty68
    alpha gamma epsilon zeta eta terminal A B c d e N G hNbig hpacket
  exact ⟨⟨hNbig, hdTerminal, heTerminal, hzeta, hR2, hL2, hpacket,
      hrowOne⟩, hdepth.2.2.1, hdepth.2.2.2,
    fiveToSix_terminal_directI4Two68
      alpha gamma epsilon zeta eta terminal A B c d e N G hNbig hpacket,
    fiveToSix_terminal_directLowerRowTwo68
      alpha gamma epsilon zeta eta terminal A B c d e N G hNbig hpacket⟩

#print axioms fiveToSix_terminal_directI4Two68
#print axioms fiveToSix_terminal_directLowerRowTwo68
#print axioms fiveToSix_terminal_depth_two_walls_empty68
#print axioms fiveToSix_terminal_i4_faceSum_two_zero68
#print axioms fiveToSix_terminal_cusp_depth_three_residual68

end FiveToSixCuspTerminalDepthTwo68

end Max11DegreeRoutes
