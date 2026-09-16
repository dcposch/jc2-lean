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
/-! # SPEED: theorems of `Sol68FiveToSixCuspSimultaneousTerminalScratch`, part 1 of 6, so that no single
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
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8000000

section FiveToSixCuspSimultaneousTerminal68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Exact row-one scalar on the simultaneous wall. -/
theorem fiveToSix_cusp_simultaneous_rowOne_scalar68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hS : 0 < S)
    (hsim : S = 7 * N - 2 * G - S)
    (hdSharp : d.natDegree ≤ 5 * N - G - S)
    (heSharp : e.natDegree ≤ 6 * N - G - S) :
    5 * (N : k) * A.coeff (2 * N) * d.coeff (5 * N - G - S) ^ 2 -
      6 * ((6 * N - G - S : ℕ) : k) *
        e.coeff (6 * N - G - S) ^ 2 = 0 := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, ha,
      hcusp, i4, i3, hi4, hi3, hrow0, hrow1, hrow2, hrow0pos, hiff⟩
  rcases hcusp with ⟨hb, hc0, hds, hes, hcusp0⟩
  let H : k[X] := -(A * B * d) + (3 : k) • (c * e)
  let P := 10 * N - 2 * G - S
  let V := 5 * N - G - S
  let W := 6 * N - G - S
  let K := 12 * N - 2 * G - 2 * S - 1
  -- Compute primitive degree bounds once; compose inequalities below.
  have hAder := (natDegree_derivative_le A).trans (Nat.sub_le_sub_right hA 1)
  have hBder := (natDegree_derivative_le B).trans (Nat.sub_le_sub_right hB 1)
  have hcder := (natDegree_derivative_le c).trans (Nat.sub_le_sub_right hc 1)
  have hdder := (natDegree_derivative_le d).trans (Nat.sub_le_sub_right hdSharp 1)
  have heder := (natDegree_derivative_le e).trans (Nat.sub_le_sub_right heSharp 1)
  have hBsq := natDegree_pow_le_of_le 2 hB
  have hcsq := natDegree_pow_le_of_le 2 hc
  have hHbound : H.natDegree ≤ P := by
    have hABd := natDegree_mul_le_of_le (natDegree_mul_le_of_le hA hB) hdSharp
    have hce := natDegree_mul_le_of_le hc heSharp
    dsimp only [H, P]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · rw [natDegree_neg]
      exact hABd.trans (by clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    · exact (natDegree_smul_le _ _).trans (hce.trans (by clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega))
  have hlow1 : (derivative A * B ^ 2 * c).natDegree < K := by
    exact (natDegree_mul_le_of_le (natDegree_mul_le_of_le hAder hBsq) hc).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
  have hlow2 : (B ^ 2 * derivative e).natDegree < K := by
    exact (natDegree_mul_le_of_le hBsq heder).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
  have hlow3 : (B * c * derivative d).natDegree < K := by
    exact (natDegree_mul_le_of_le (natDegree_mul_le_of_le hB hc) hdder).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
  have hlow4 : (B * derivative c * d).natDegree < K := by
    exact (natDegree_mul_le_of_le (natDegree_mul_le_of_le hB hcder) hdSharp).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
  have hlow5 : (derivative B * c * d).natDegree < K := by
    exact (natDegree_mul_le_of_le (natDegree_mul_le_of_le hBder hc) hdSharp).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
  have hlow6 : (c ^ 2 * derivative c).natDegree < K := by
    exact (natDegree_mul_le_of_le hcsq hcder).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
  have hloadDeg :
      (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).natDegree < K := by
    rw [cubicLoadRowOnePolynomial68_uniform_pinned_eq68]
    have hsmul (a : k) (p : k[X]) (hp : p.natDegree < K) :
        (a • p).natDegree < K := (natDegree_smul_le a p).trans_lt hp
    have hload1 : (A * derivative e).natDegree < K :=
      (natDegree_mul_le_of_le hA heder).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    have hload2 : (c * derivative c).natDegree < K :=
      (natDegree_mul_le_of_le hc hcder).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    have hload3 : (derivative A * B ^ 2).natDegree < K :=
      (natDegree_mul_le_of_le hAder hBsq).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    have hload4 : (B * derivative d).natDegree < K :=
      (natDegree_mul_le_of_le hB hdder).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    have hload5 : (d * derivative B).natDegree < K :=
      (natDegree_mul_le_of_le hdSharp hBder).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    have hload6 : (A * derivative c).natDegree < K :=
      (natDegree_mul_le_of_le hA hcder).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    have hload7 : (derivative e).natDegree < K :=
      (heder).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    have hload8 : (derivative A * B).natDegree < K :=
      (natDegree_mul_le_of_le hAder hB).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    have hload9 : (A * derivative B).natDegree < K :=
      (natDegree_mul_le_of_le hA hBder).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    have hload10 : (derivative d).natDegree < K :=
      (hdder).trans_lt (by dsimp only [K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    exact (natDegree_add_le _ _).trans_lt
        (max_lt ((natDegree_add_le _ _).trans_lt
          (max_lt ((natDegree_add_le _ _).trans_lt
            (max_lt ((natDegree_add_le _ _).trans_lt
              (max_lt ((natDegree_add_le _ _).trans_lt
                (max_lt ((natDegree_sub_le _ _).trans_lt
                  (max_lt ((natDegree_add_le _ _).trans_lt
                    (max_lt ((natDegree_add_le _ _).trans_lt
                      (max_lt ((natDegree_sub_le _ _).trans_lt
                        (max_lt (hsmul _ _ hload1) (hsmul _ _ hload2))) (hsmul _ _ hload3))) (hsmul _ _ hload4))) (hsmul _ _ hload5))) (hsmul _ _ hload6))) (hsmul _ _ hload7))) (hsmul _ _ hload8))) (hsmul _ _ hload9))) (hsmul _ _ hload10))
  have hPS : P - S = 3 * N := by dsimp only [P]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega
  have hW : 2 * W = 5 * N := by dsimp only [W]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega
  have hHcoeff (q : ℕ) (hq : q ≤ S) :
      H.coeff (P - q) =
        if q = S then (-3 / 2 : k) * d.coeff V ^ 2 else 0 := by
    simpa only [H, P, V] using
      fiveToSix_cusp_simultaneous_i3_face_coeff68
        alpha gamma epsilon zeta eta terminal A B c d e N G S q
        ⟨hN, hgt5, hle6, hA, hB, hc, by clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega, by clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega, ha,
          ⟨hb, hc0, hds, hes, hcusp0⟩,
          ⟨i4, i3, hi4, hi3, hrow0, hrow1, hrow2, hrow0pos, hiff⟩⟩
        hS hsim hdSharp heSharp hq
  have hHdeg : H.natDegree ≤ P - S := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    by_cases hjP : P < j
    · exact coeff_eq_zero_of_natDegree_lt (hHbound.trans_lt hjP)
    · let q := P - j
      have hq : q < S := by dsimp only [q]; clear * - hj hjP; omega
      have hz := hHcoeff q (le_of_lt hq)
      rw [if_neg (Nat.ne_of_lt hq)] at hz
      rw [show P - q = j from by
        dsimp only [q]
        exact Nat.sub_sub_self (Nat.le_of_not_gt hjP)] at hz
      exact hz
  have hHS : H.coeff (P - S) = (-3 / 2 : k) * d.coeff V ^ 2 := by
    have hz := hHcoeff S (le_refl S)
    rw [if_pos rfl] at hz
    exact hz
  have hAH := coeff_mul_derivative_at_bounds68 A H (2 * N) (P - S)
    (by clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega) hA hHdeg
  rw [show 2 * N + (P - S) - 1 = K from by
    dsimp only [P, K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega, hHS] at hAH
  have hAH' : (A * derivative H).coeff K =
      A.coeff (2 * N) * ((-3 / 2 : k) * d.coeff V ^ 2) *
        (((P - S : ℕ) : k)) := hAH
  have hAd2 := coeff_mul_mul_derivative_at_bounds68 d d A
    V V (2 * N) (by clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega) hdSharp hdSharp hA
  rw [show V + V + 2 * N - 1 = K from by
    dsimp only [V, K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega] at hAd2
  have hAd2' : (derivative A * d ^ 2).coeff K =
      A.coeff (2 * N) * d.coeff V ^ 2 * (((2 * N : ℕ) : k)) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hAd2
  have hee := coeff_mul_derivative_at_bounds68 e e W W (by clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega)
    heSharp heSharp
  rw [show W + W - 1 = K from by dsimp only [W, K]; clear * - hN hgt5 hle6 hS hsim hA hB hc hdSharp heSharp; omega] at hee
  have hrow := congrArg (fun p : k[X] => p.coeff K) hrow1
  simp only [coeff_zero, coeff_add] at hrow
  have hmainPoly :
      (2 : k) • (A ^ 2 * B * derivative d) +
          (2 : k) • (A ^ 2 * derivative B * d) +
          (2 : k) • (A * derivative A * B * d) -
          (6 : k) • (A * c * derivative e) -
          (6 : k) • (A * derivative c * e) =
        (-2 : k) • (A * derivative H) := by
    dsimp only [H]
    simp only [derivative_add, derivative_neg, derivative_mul,
      derivative_smul, derivative_C, derivative_ofNat, zero_mul, add_zero,
      neg_mul, mul_neg,
      pow_two,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_neg,
      map_ofNat, map_zero]
    ring
  have hmain := congrArg (fun p : k[X] => p.coeff K) hmainPoly
  simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul] at hmain
  have hrowCore : (-4 / 27 : k) *
      (-2 * (A * derivative H).coeff K +
        3 * (derivative A * d ^ 2).coeff K -
        18 * (e * derivative e).coeff K) = 0 := by
    rw [coeff_eq_zero_of_natDegree_lt hloadDeg] at hrow
    simp only [secondaryResidualRowOnePolynomial68, coeff_smul, coeff_add,
      coeff_sub, smul_eq_mul,
      coeff_eq_zero_of_natDegree_lt hlow1,
      coeff_eq_zero_of_natDegree_lt hlow2,
      coeff_eq_zero_of_natDegree_lt hlow3,
      coeff_eq_zero_of_natDegree_lt hlow4,
      coeff_eq_zero_of_natDegree_lt hlow5,
      coeff_eq_zero_of_natDegree_lt hlow6,
      mul_zero, add_zero, sub_zero] at hrow
    -- Substitute the compact coefficient identity before clearing scalars.
    rw [hmain] at hrow
    exact hrow
  rw [hAH', hAd2', hee] at hrowCore
  rw [hPS] at hrowCore
  push_cast at hrowCore
  -- The scalar certificate only sees five field atoms, never polynomials.
  have hscalar (n a dd ee w : k)
      (h : (-4 / 27 : k) *
        (-2 * (a * ((-3 / 2 : k) * dd ^ 2) * (3 * n)) +
          3 * (a * dd ^ 2 * (2 * n)) - 18 * (ee * ee * w)) = 0) :
      5 * n * a * dd ^ 2 - 6 * w * ee ^ 2 = 0 := by
    linear_combination (-9 / 4 : k) * h
  exact hscalar (N : k) (A.coeff (2 * N)) (d.coeff V) (e.coeff W)
    (W : k) hrowCore


end FiveToSixCuspSimultaneousTerminal68

#print axioms fiveToSix_cusp_simultaneous_rowOne_scalar68

end Max11DegreeRoutes

end
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
/-! # SPEED: theorems of `Sol68FiveToSixCuspSimultaneousTerminalScratch`, part 4 of 6, so that no single
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
