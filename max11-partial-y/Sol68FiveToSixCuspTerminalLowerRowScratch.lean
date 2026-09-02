import Sol68FiveToSixCuspSimultaneousTerminalScratch

/-! # First direct lower row on the terminal all-nonzero cusp

The terminal zero consumer does not apply here: both terminal edge
coefficients are nonzero.  At direct row-zero coefficient `6N-2`, the
only possible new homogeneous loads are `A'*d*e` when
`7N-2G=1`, and the first `B^3` jet in I4 when `3G-7N=1`.
Each arithmetic wall contradicts the all-nonzero cusp.  Away from both
walls this coefficient is exactly dependent, so the honest successor has
both depths at least two.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspTerminalLowerRow68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact first terminal I4 jet.  The only competing term is `B^3` on
the arithmetic wall `3G-7N=1`. -/
theorem fiveToSix_terminal_i4_faceSum_one68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N)
    (hzeta : zeta = 0) :
    (B * e + c * d).coeff (2 * N - 1) =
      if 3 * G - 7 * N = 1 then
        (1 / 9 : k) * B.coeff (3 * N - G) ^ 3
      else 0 := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, _ha, _hcusp,
      i4, i3, hi4, _hi3, _hrow0, _hrow1, _hrow2, _hpos, _hiff⟩
  have hgap : 0 < 3 * G - 7 * N := by omega
  have hidx : 0 < 2 * N - 1 := by omega
  have hBload : B.natDegree < 2 * N - 1 := by omega
  have hdload : d.natDegree < 2 * N - 1 := by omega
  have hcoeff := congrArg (fun p : k[X] => p.coeff (2 * N - 1)) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    hzeta] at hcoeff
  by_cases hwall : 3 * G - 7 * N = 1
  · have hB3deg : (B ^ 3).natDegree ≤ 2 * N - 1 := by
      compute_degree
      omega
    have hB3 := coeff_pow_at_bound68 B (3 * N - G) 3 hB
    rw [show 3 * (3 * N - G) = 2 * N - 1 from by omega] at hB3
    rw [if_pos hwall]
    simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
      coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt hidx, if_false,
      hB3, coeff_eq_zero_of_natDegree_lt hBload,
      coeff_eq_zero_of_natDegree_lt hdload, zero_mul, add_zero] at hcoeff
    rw [coeff_add]
    linear_combination (3 / 8 : k) * hcoeff
  · have hB3low : (B ^ 3).natDegree < 2 * N - 1 := by
      compute_degree
      omega
    rw [if_neg hwall]
    simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
      coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt hidx, if_false,
      coeff_eq_zero_of_natDegree_lt hB3low,
      coeff_eq_zero_of_natDegree_lt hBload,
      coeff_eq_zero_of_natDegree_lt hdload, zero_mul, add_zero] at hcoeff
    rw [coeff_add]
    linear_combination (3 / 8 : k) * hcoeff

/-- The direct coefficient `6N-2` closes both first-depth terminal walls.
No strict/equality pair is assumed. -/
theorem fiveToSix_terminal_cusp_depths_ge_two68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N)
    (hzeta : zeta = 0) :
    2 ≤ 7 * N - 2 * G ∧ 2 ≤ 3 * G - 7 * N := by
  have hface := fiveToSix_contractedCusp_terminalFace68
    alpha gamma epsilon zeta eta terminal A B c d e N G hpacket
    hdTerminal heTerminal hzeta
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
  let R := 7 * N - 2 * G
  let L := 3 * G - 7 * N
  let F := B * e + c * d
  have hR : 0 < R := by
    have hdidx : 5 * N - G - R = G - 2 * N := by dsimp only [R]; omega
    dsimp only [R]
    omega
  have hL : 0 < L := by dsimp only [L]; omega
  have hFdeg : F.natDegree ≤ 2 * N := by
    dsimp only [F]
    compute_degree
    omega
  have hderA : (derivative A).natDegree ≤ 2 * N - 1 := by
    compute_degree
    omega
  have hFtop : F.coeff (2 * N) = 0 := by
    have hBe := coeff_mul_at_bounds68 B e (3 * N - G) (G - N) hB heTerminal
    rw [show (3 * N - G) + (G - N) = 2 * N from by omega] at hBe
    have hcd := coeff_mul_at_bounds68 c d (4 * N - G) (G - 2 * N)
      hc hdTerminal
    rw [show (4 * N - G) + (G - 2 * N) = 2 * N from by omega] at hcd
    simp only [F, coeff_add, hBe, hcd]
    exact hface.four
  have hdsTerminal : d.coeff (G - 2 * N) ≠ 0 := by
    simpa only [show 5 * N - G - (7 * N - 2 * G) = G - 2 * N by
      omega] using hds
  have hesTerminal : e.coeff (G - N) ≠ 0 := by
    simpa only [show 6 * N - G - (7 * N - 2 * G) = G - N by
      omega] using hes
  have hFone : F.coeff (2 * N - 1) =
      if L = 1 then (1 / 9 : k) * B.coeff (3 * N - G) ^ 3 else 0 := by
    simpa only [F, L] using fiveToSix_terminal_i4_faceSum_one68
      alpha gamma epsilon zeta eta terminal A B c d e N G hNbig
      ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
        ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
      hdTerminal heTerminal hzeta
  have hAAFraw := coeff_mul_mul_at_reflect_one68
    A (derivative A) F (2 * N) (2 * N - 1) (2 * N)
    hA hderA hFdeg (by omega)
  have hAAF : (A * derivative A * F).coeff (6 * N - 2) =
      A.coeff (2 * N) ^ 2 * (((2 * N : ℕ) : k)) *
        (if L = 1 then (1 / 9 : k) * B.coeff (3 * N - G) ^ 3 else 0) := by
    rw [show 2 * N + (2 * N - 1) + 2 * N - 1 = 6 * N - 2 from by omega]
      at hAAFraw
    norm_num [coeff_reflect, coeff_derivative, hFtop] at hAAFraw
    rw [revAt_le (by omega : 1 ≤ 2 * N), hFone,
      show 2 * N - 1 + 1 = 2 * N by omega] at hAAFraw
    have hcast : (((2 * N - 1 : ℕ) : k) + 1) = ((2 * N : ℕ) : k) := by
      exact_mod_cast (show 2 * N - 1 + 1 = 2 * N by omega)
    rw [hcast] at hAAFraw
    simpa only [pow_two, mul_assoc] using hAAFraw
  have hrowDirect := fiveToSix_terminal_directLowerRow68
    alpha gamma epsilon zeta eta terminal A B c d e N G
    ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
      ⟨hb, hc0, hds, hes, hcusp⟩, hadapter⟩
  change (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * N - 2) = 0
    at hrowDirect
  have hlow1 : (A * B ^ 2 * derivative d).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hlow3 : (derivative A * B * c ^ 2).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hlow4 : (B * c * derivative e).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hlow5 : (B * d * derivative d).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hlow6 : (derivative B * d ^ 2).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hlow7 : (c * derivative c * d).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hload1 : (B * derivative A * c).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hload2 : (B * derivative e).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hload3 : (A * B * derivative A).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hload4 : (A * derivative A * d).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hload5 : (d * derivative c).natDegree < 6 * N - 2 := by
    compute_degree; omega
  have hload6 : (d * derivative A).natDegree < 6 * N - 2 := by
    compute_degree; omega
  rw [coeff_add, cubicLoadRowZeroPolynomial68_uniform_pinned_eq68, hzeta]
    at hrowDirect
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add, coeff_sub,
    coeff_neg, coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hload1,
    coeff_eq_zero_of_natDegree_lt hload2,
    coeff_eq_zero_of_natDegree_lt hload3,
    coeff_eq_zero_of_natDegree_lt hload4,
    coeff_eq_zero_of_natDegree_lt hload5,
    coeff_eq_zero_of_natDegree_lt hload6,
    coeff_smul, smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero] at hrowDirect
  have hcombine :
      (A * derivative A * B * e).coeff (6 * N - 2) +
        (A * derivative A * c * d).coeff (6 * N - 2) =
        (A * derivative A * F).coeff (6 * N - 2) := by
    dsimp only [F]
    rw [mul_add, coeff_add]
    ring
  have hcore : (-4 / 27 : k) *
      (A * derivative A * F).coeff (6 * N - 2) -
      (4 / 9 : k) * (derivative A * d * e).coeff (6 * N - 2) = 0 := by
    linear_combination hrowDirect + (4 / 27 : k) * hcombine
  constructor
  · by_contra hR2
    have hR1 : R = 1 := by omega
    have hLne : L ≠ 1 := by
      intro hL1
      dsimp only [R, L] at hR1 hL1
      omega
    rw [hAAF, if_neg hLne] at hcore
    simp only [mul_zero] at hcore
    have hde := coeff_mul_mul_derivative_at_bounds68 d e A
      (G - 2 * N) (G - N) (2 * N) (by omega)
      hdTerminal heTerminal hA
    rw [show (G - 2 * N) + (G - N) + 2 * N - 1 = 6 * N - 2 from by
      dsimp only [R] at hR1; omega] at hde
    have hde' : (derivative A * d * e).coeff (6 * N - 2) =
        A.coeff (2 * N) * d.coeff (G - 2 * N) * e.coeff (G - N) *
          (((2 * N : ℕ) : k)) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hde
    rw [hde'] at hcore
    have hcast : (((2 * N : ℕ) : k)) ≠ 0 := by
      exact_mod_cast (show (2 * N : ℕ) ≠ 0 by omega)
    have hprod : (((2 * N : ℕ) : k)) * A.coeff (2 * N) *
        d.coeff (G - 2 * N) * e.coeff (G - N) = 0 := by
      linear_combination (-9 / 4 : k) * hcore
    exact (mul_ne_zero
      (mul_ne_zero (mul_ne_zero hcast ha) hdsTerminal) hesTerminal) hprod
  · by_contra hL2
    have hL1 : L = 1 := by omega
    have hRne : R ≠ 1 := by
      intro hR1
      dsimp only [R, L] at hR1 hL1
      omega
    have hdeLow : (derivative A * d * e).natDegree < 6 * N - 2 := by
      compute_degree
      dsimp only [R] at hRne
      omega
    rw [hAAF, if_pos hL1, coeff_eq_zero_of_natDegree_lt hdeLow] at hcore
    have hcast : (((2 * N : ℕ) : k)) ≠ 0 := by
      exact_mod_cast (show (2 * N : ℕ) ≠ 0 by omega)
    have hprod : (((2 * N : ℕ) : k)) * A.coeff (2 * N) ^ 2 *
        B.coeff (3 * N - G) ^ 3 = 0 := by
      linear_combination (-243 / 4 : k) * hcore
    exact (mul_ne_zero (mul_ne_zero hcast (pow_ne_zero 2 ha))
      (pow_ne_zero 3 hb)) hprod

/-- Honest terminal successor after consuming the first direct lower row. -/
def FiveToSixTerminalCuspDepthResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ) : Prop :=
  2 < N ∧ d.natDegree ≤ G - 2 * N ∧ e.natDegree ≤ G - N ∧
    zeta = 0 ∧ 2 ≤ 7 * N - 2 * G ∧ 2 ≤ 3 * G - 7 * N ∧
    FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G (7 * N - 2 * G) ∧
    FiveToSixTerminalDirectLowerRow68 alpha gamma epsilon zeta eta terminal
      A B c d e N G

theorem fiveToSix_terminal_cusp_depth_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hNbig : 2 < N)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N)
    (hzeta : zeta = 0) :
    FiveToSixTerminalCuspDepthResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G := by
  have hdepth := fiveToSix_terminal_cusp_depths_ge_two68
    alpha gamma epsilon zeta eta terminal A B c d e N G hNbig hpacket
    hdTerminal heTerminal hzeta
  exact ⟨hNbig, hdTerminal, heTerminal, hzeta, hdepth.1, hdepth.2,
    hpacket, fiveToSix_terminal_directLowerRow68
      alpha gamma epsilon zeta eta terminal A B c d e N G hpacket⟩

#print axioms fiveToSix_terminal_i4_faceSum_one68
#print axioms fiveToSix_terminal_cusp_depths_ge_two68
#print axioms fiveToSix_terminal_cusp_depth_residual68

end FiveToSixCuspTerminalLowerRow68

end Max11DegreeRoutes
