import Sol68FiveToSixCuspSimultaneousTerminalSplitBaseScratch

/-! # SPEED: theorems of `Sol68FiveToSixCuspSimultaneousTerminalScratch`, part 0 of 6, so that no single
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

/-- On the simultaneous wall, I3 fixes the first coefficient of its face
sum. -/
theorem fiveToSix_cusp_simultaneous_i3_face_coeff68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hS : 0 < S)
    (hsim : S = 7 * N - 2 * G - S)
    (hdSharp : d.natDegree ≤ 5 * N - G - S)
    (heSharp : e.natDegree ≤ 6 * N - G - S)
    (hq : q ≤ S) :
    (-(A * B * d) + (3 : k) • (c * e)).coeff
        (10 * N - 2 * G - S - q) =
      if q = S then
        (-3 / 2 : k) * d.coeff (5 * N - G - S) ^ 2
      else 0 := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, _ha, _hcusp,
      i4, i3, _hi4, hi3, _hrow0, _hrow1, _hrow2, _hrow0pos, _hiff⟩
  have hidx : 0 < 10 * N - 2 * G - S - q := by omega
  have hABd := coeff_mul_mul_at_bounds68 A B d
    (2 * N) (3 * N - G) (5 * N - G - S) hA hB hdSharp
  rw [show 2 * N + (3 * N - G) + (5 * N - G - S) =
    10 * N - 2 * G - S from by omega] at hABd
  have hce := coeff_mul_at_bounds68 c e
    (4 * N - G) (6 * N - G - S) hc heSharp
  rw [show (4 * N - G) + (6 * N - G - S) =
    10 * N - 2 * G - S from by omega] at hce
  have hB2c : (B ^ 2 * c).natDegree <
      10 * N - 2 * G - S - q := by compute_degree; omega
  have hBload : B.natDegree < 10 * N - 2 * G - S - q := by omega
  have hcload : c.natDegree < 10 * N - 2 * G - S - q := by omega
  have heload : e.natDegree < 10 * N - 2 * G - S - q := by omega
  have hB2load : (B ^ 2).natDegree <
      10 * N - 2 * G - S - q := by compute_degree; omega
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (10 * N - 2 * G - S - q)) hi3
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates]
    at hcoeff
  by_cases hqS : q = S
  · have hidxd : 10 * N - 2 * G - S - q =
        2 * (5 * N - G - S) := by omega
    have hd2 := coeff_pow_at_bound68 d (5 * N - G - S) 2 hdSharp
    rw [show 2 * (5 * N - G - S) =
      2 * (5 * N - G - S) from rfl] at hd2
    rw [hidxd] at hcoeff hB2c hBload hcload heload hB2load
    rw [if_pos hqS, hidxd]
    simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
      coeff_sub, coeff_neg, coeff_smul, smul_eq_mul, coeff_C,
      show (2 * (5 * N - G - S) : ℕ) ≠ 0 by omega, if_false,
      coeff_eq_zero_of_natDegree_lt hB2c,
      coeff_eq_zero_of_natDegree_lt hBload,
      coeff_eq_zero_of_natDegree_lt hcload,
      coeff_eq_zero_of_natDegree_lt heload,
      coeff_eq_zero_of_natDegree_lt hB2load,
      hd2, mul_zero, add_zero, sub_zero] at hcoeff
    simp only [coeff_add, coeff_neg, coeff_smul, smul_eq_mul]
    linear_combination (9 / 8 : k) * hcoeff
  · have hd2low : (d ^ 2).natDegree <
        10 * N - 2 * G - S - q := by compute_degree; omega
    rw [if_neg hqS]
    simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
      coeff_sub, coeff_neg, coeff_smul, smul_eq_mul, coeff_C,
      Nat.ne_of_gt hidx, if_false,
      coeff_eq_zero_of_natDegree_lt hB2c,
      coeff_eq_zero_of_natDegree_lt hd2low,
      coeff_eq_zero_of_natDegree_lt hBload,
      coeff_eq_zero_of_natDegree_lt hcload,
      coeff_eq_zero_of_natDegree_lt heload,
      coeff_eq_zero_of_natDegree_lt hB2load,
      mul_zero, add_zero, sub_zero] at hcoeff
    simp only [coeff_add, coeff_neg, coeff_smul, smul_eq_mul]
    linear_combination (9 / 8 : k) * hcoeff


end FiveToSixCuspSimultaneousTerminal68

end Max11DegreeRoutes

end
