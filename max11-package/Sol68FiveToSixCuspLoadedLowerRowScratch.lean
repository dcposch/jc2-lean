import Sol68FiveToSixCuspLoadedWallScratch

/-! # The first lower row on the loaded cusp wall

At the first loaded reflected depth, the quartic first integral controls the
first coefficient of `B*e+c*d`.  In the positive row-zero coefficient all
other terms are still below the cutoff.  Thus the only new terms are
`A'*d*e` on the `d^2` wall and `zeta*A^2*A'` on the opposite wall.

The resulting exact split closes the `d^2`-first branch, forces `zeta=0`
on the `zeta*A`-first branch, and retains one scalar on the simultaneous
wall.  The terminal all-nonzero cusp is kept separate: its first row is at
the terminal load itself and is not covered by this positive interior
coefficient.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRow68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The quartic first integral determines the first possibly loaded
coefficient of `B*e+c*d`. -/
theorem fiveToSix_cusp_i4_faceSum_coeff_before_firstLoad68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hS : 0 < S) (hSR : S < 7 * N - 2 * G)
    (hdSharp : d.natDegree ≤ 5 * N - G - S)
    (heSharp : e.natDegree ≤ 6 * N - G - S)
    (hqS : q ≤ S) (hqZ : q ≤ 7 * N - 2 * G - S) :
    (B * e + c * d).coeff (9 * N - 2 * G - S - q) =
      if q = 7 * N - 2 * G - S then
        (-3 / 8 : k) * zeta * A.coeff (2 * N)
      else 0 := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, _ha, _hcusp,
      i4, i3, hi4, _hi3, _hrow0, _hrow1, _hrow2, _hrow0pos, _hiff⟩
  have hqsmall : q < 4 * N - G := by omega
  have hidx : 0 < 9 * N - 2 * G - S - q := by omega
  have hB3 : (B ^ 3).natDegree < 9 * N - 2 * G - S - q := by
    compute_degree
    omega
  have hBload : B.natDegree < 9 * N - 2 * G - S - q := by omega
  have hdload : d.natDegree < 9 * N - 2 * G - S - q := by omega
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (9 * N - 2 * G - S - q)) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
    at hcoeff
  by_cases hq : q = 7 * N - 2 * G - S
  · have hidxA : 9 * N - 2 * G - S - q = 2 * N := by omega
    rw [hidxA] at hcoeff hB3 hBload hdload
    rw [if_pos hq, hidxA]
    simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
      coeff_smul, smul_eq_mul, coeff_C, show (2 * N : ℕ) ≠ 0 by omega,
      if_false,
      coeff_eq_zero_of_natDegree_lt hB3,
      coeff_eq_zero_of_natDegree_lt hBload,
      coeff_eq_zero_of_natDegree_lt hdload,
      mul_zero, add_zero] at hcoeff
    rw [coeff_add]
    linear_combination (3 / 8 : k) * hcoeff
  · have hAload : A.natDegree < 9 * N - 2 * G - S - q := by omega
    rw [if_neg hq]
    simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
      coeff_smul, smul_eq_mul, coeff_C, Nat.ne_of_gt hidx, if_false,
      coeff_eq_zero_of_natDegree_lt hB3,
      coeff_eq_zero_of_natDegree_lt hAload,
      coeff_eq_zero_of_natDegree_lt hBload,
      coeff_eq_zero_of_natDegree_lt hdload,
      mul_zero, add_zero] at hcoeff
    rw [coeff_add]
    linear_combination (3 / 8 : k) * hcoeff

/-- At every depth no later than the first load, the positive row-zero
coefficient reduces exactly to its face-sum term and the two possible wall
loads. -/
theorem fiveToSix_cusp_rowZero_firstLoad_core68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hS : 0 < S) (hSR : S < 7 * N - 2 * G)
    (hdSharp : d.natDegree ≤ 5 * N - G - S)
    (heSharp : e.natDegree ≤ 6 * N - G - S)
    (hqS : q ≤ S) (hqZ : q ≤ 7 * N - 2 * G - S) :
    (-4 / 27 : k) *
        (A * derivative A * (B * e + c * d)).coeff
          (13 * N - 2 * G - S - q - 1) -
      (4 / 9 : k) * (derivative A * d * e).coeff
          (13 * N - 2 * G - S - q - 1) +
      (1 / 9 : k) * zeta * (A ^ 2 * derivative A).coeff
          (13 * N - 2 * G - S - q - 1) = 0 := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, _ha, _hcusp,
      i4, i3, _hi4, _hi3, hrow0, _hrow1, _hrow2, hrow0pos, _hiff⟩
  have hqsmall : q < 4 * N - G := by omega
  have hidx : 0 < 13 * N - 2 * G - S - q - 1 := by omega
  have hrow := hrow0pos (13 * N - 2 * G - S - q - 1) hidx
  have hlow1 : (A * B ^ 2 * derivative d).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hlow3 : (derivative A * B * c ^ 2).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hlow4 : (B * c * derivative e).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hlow5 : (B * d * derivative d).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hlow6 : (derivative B * d ^ 2).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hlow7 : (c * derivative c * d).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hload1 : (B * derivative A * c).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hload2 : (B * derivative e).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hload3 : (A * B * derivative A).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hload4 : (A * derivative A * d).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hload5 : (d * derivative c).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hload6 : (d * derivative A).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hload7 : (derivative A * c).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hload8 : (A * derivative c).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  have hload9 : (derivative e).natDegree <
      13 * N - 2 * G - S - q - 1 := by compute_degree; omega
  rw [coeff_add, cubicLoadRowZeroPolynomial68_uniform_pinned_eq68] at hrow
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, coeff_neg, coeff_eq_zero_of_natDegree_lt hlow1,
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
    coeff_eq_zero_of_natDegree_lt hload7,
    coeff_eq_zero_of_natDegree_lt hload8,
    coeff_eq_zero_of_natDegree_lt hload9,
    coeff_smul, smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero] at hrow
  have hcombine :
      (A * derivative A * B * e).coeff
          (13 * N - 2 * G - S - q - 1) +
        (A * derivative A * c * d).coeff
          (13 * N - 2 * G - S - q - 1) =
        (A * derivative A * (B * e + c * d)).coeff
          (13 * N - 2 * G - S - q - 1) := by
    rw [mul_add, coeff_add]
    ring
  linear_combination hrow + (4 / 27 : k) * hcombine

/-- Exact independent lower-row consequence at the first loaded rung.
The three conclusions correspond to `d^2` first, `zeta*A` first, and the
simultaneous wall. -/
theorem fiveToSix_contractedCusp_loadedLowerRow68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hS : 0 < S) (hSR : S < 7 * N - 2 * G)
    (hdSharp : d.natDegree ≤ 5 * N - G - S)
    (heSharp : e.natDegree ≤ 6 * N - G - S) :
    (S < 7 * N - 2 * G - S → False) ∧
      (7 * N - 2 * G - S < S → zeta = 0) ∧
      (S = 7 * N - 2 * G - S →
        3 * zeta * A.coeff (2 * N) ^ 2 =
          8 * d.coeff (5 * N - G - S) *
            e.coeff (6 * N - G - S)) := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, ha,
      hcusp, hadapter⟩
  rcases hcusp with ⟨hb, hc0, hds, hes, hcusp0⟩
  have hcast : (((2 * N : ℕ) : k)) ≠ 0 := by
    exact_mod_cast (show (2 * N : ℕ) ≠ 0 by omega)
  let P := 9 * N - 2 * G - S
  let T := 13 * N - 2 * G - S - 1
  let F := B * e + c * d
  have hFdeg : F.natDegree ≤ P := by
    dsimp only [F, P]
    compute_degree
    omega
  have hAAdeg : (A * derivative A).natDegree ≤ 4 * N - 1 := by
    compute_degree
    omega
  have hAAtop : (A * derivative A).coeff (4 * N - 1) =
      A.coeff (2 * N) ^ 2 * (((2 * N : ℕ) : k)) := by
    have h := coeff_mul_derivative_at_bounds68 A A (2 * N) (2 * N)
      (by omega) hA hA
    rw [show 2 * N + 2 * N - 1 = 4 * N - 1 from by omega] at h
    simpa only [pow_two, mul_assoc] using h
  have hAAF (q : ℕ) (hqS : q ≤ S)
      (hqZ : q ≤ 7 * N - 2 * G - S) :
      (A * derivative A * F).coeff (T - q) =
        (if q = 7 * N - 2 * G - S then
          (-3 / 8 : k) * zeta * A.coeff (2 * N) else 0) *
          (A.coeff (2 * N) ^ 2 * (((2 * N : ℕ) : k))) := by
    have hFcoeff := fiveToSix_cusp_i4_faceSum_coeff_before_firstLoad68
      alpha gamma epsilon zeta eta terminal A B c d e N G S q
      ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
        ⟨hb, hc0, hds, hes, hcusp0⟩, hadapter⟩
      hS hSR hdSharp heSharp hqS hqZ
    have hzero : ∀ j, j < q → (F.reflect P).coeff j = 0 := by
      intro j hj
      have hjcoeff := fiveToSix_cusp_i4_faceSum_coeff_before_firstLoad68
        alpha gamma epsilon zeta eta terminal A B c d e N G S j
        ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
          ⟨hb, hc0, hds, hes, hcusp0⟩, hadapter⟩
        hS hSR hdSharp heSharp (by omega) (by omega)
      rw [if_neg (by omega)] at hjcoeff
      dsimp only [F, P]
      rw [coeff_reflect, revAt_le (by omega)]
      exact hjcoeff
    have href := coeff_mul_at_reflect_of_left_lower_zero68
      F (A * derivative A) P (4 * N - 1) q hFdeg hAAdeg
      (by omega) hzero
    have hFwall : (F.reflect P).coeff q =
        if q = 7 * N - 2 * G - S then
          (-3 / 8 : k) * zeta * A.coeff (2 * N) else 0 := by
      dsimp only [F, P]
      rw [coeff_reflect, revAt_le (by omega)]
      exact hFcoeff
    have hAAr : ((A * derivative A).reflect (4 * N - 1)).coeff 0 =
        A.coeff (2 * N) ^ 2 * (((2 * N : ℕ) : k)) := by
      simpa only [coeff_reflect, revAt_zero] using hAAtop
    rw [hFwall, hAAr] at href
    rw [show P + (4 * N - 1) - q = T - q from by
      dsimp only [P, T]; omega] at href
    simpa only [F, mul_assoc, mul_comm, mul_left_comm] using href
  constructor
  · intro hdFirst
    have hF := hAAF S (le_refl S) (by omega)
    rw [if_neg (by omega)] at hF
    simp only [zero_mul] at hF
    have hde := coeff_mul_mul_derivative_at_bounds68 d e A
      (5 * N - G - S) (6 * N - G - S) (2 * N) (by omega)
      hdSharp heSharp hA
    rw [show (5 * N - G - S) + (6 * N - G - S) + 2 * N - 1 =
      T - S from by dsimp only [T]; omega] at hde
    have hde' : (derivative A * d * e).coeff (T - S) =
        d.coeff (5 * N - G - S) * e.coeff (6 * N - G - S) *
          A.coeff (2 * N) * (((2 * N : ℕ) : k)) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hde
    have hzetaLow : (A ^ 2 * derivative A).natDegree < T - S := by
      dsimp only [T]
      compute_degree
      omega
    have hrow := fiveToSix_cusp_rowZero_firstLoad_core68
      alpha gamma epsilon zeta eta terminal A B c d e N G S S
      ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
        ⟨hb, hc0, hds, hes, hcusp0⟩, hadapter⟩
      hS hSR hdSharp heSharp (le_refl S) (by omega)
    rw [show 13 * N - 2 * G - S - S - 1 = T - S from by
      dsimp only [T]; omega,
      hF, hde', coeff_eq_zero_of_natDegree_lt hzetaLow] at hrow
    have hprod : (((2 * N : ℕ) : k)) * A.coeff (2 * N) *
        d.coeff (5 * N - G - S) * e.coeff (6 * N - G - S) = 0 := by
      linear_combination (-9 / 4 : k) * hrow
    exact (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero hcast ha) hds) hes) hprod
  · constructor
    · intro hzFirst
      have hF := hAAF (7 * N - 2 * G - S) (by omega) (le_refl _)
      rw [if_pos rfl] at hF
      have hdeLow : (derivative A * d * e).natDegree <
          T - (7 * N - 2 * G - S) := by
        dsimp only [T]
        compute_degree
        omega
      have hzTop := coeff_mul_mul_derivative_at_bounds68 A A A
        (2 * N) (2 * N) (2 * N) (by omega) hA hA hA
      rw [show 2 * N + 2 * N + 2 * N - 1 =
        T - (7 * N - 2 * G - S) from by dsimp only [T]; omega] at hzTop
      have hzTop' : (A ^ 2 * derivative A).coeff
          (T - (7 * N - 2 * G - S)) =
          A.coeff (2 * N) ^ 3 * (((2 * N : ℕ) : k)) := by
        calc
          _ = A.coeff (2 * N) * A.coeff (2 * N) *
                A.coeff (2 * N) * (((2 * N : ℕ) : k)) := by
              simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm]
                using hzTop
          _ = _ := by ring
      have hrow := fiveToSix_cusp_rowZero_firstLoad_core68
        alpha gamma epsilon zeta eta terminal A B c d e N G S
        (7 * N - 2 * G - S)
        ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
          ⟨hb, hc0, hds, hes, hcusp0⟩, hadapter⟩
        hS hSR hdSharp heSharp (by omega) (le_refl _)
      rw [show 13 * N - 2 * G - S - (7 * N - 2 * G - S) - 1 =
          T - (7 * N - 2 * G - S) from by dsimp only [T]; omega,
        hF, coeff_eq_zero_of_natDegree_lt hdeLow, hzTop'] at hrow
      have hzprod : (((2 * N : ℕ) : k)) * zeta *
          A.coeff (2 * N) ^ 3 = 0 := by
        linear_combination 6 * hrow
      have hza3 : zeta * A.coeff (2 * N) ^ 3 = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left hcast
        simpa only [mul_assoc] using hzprod
      have ha3 : A.coeff (2 * N) ^ 3 ≠ 0 := pow_ne_zero 3 ha
      exact (mul_eq_zero.mp hza3).resolve_right ha3
    · intro heq
      have hF := hAAF S (le_refl S) (by omega)
      rw [if_pos heq] at hF
      have hde := coeff_mul_mul_derivative_at_bounds68 d e A
        (5 * N - G - S) (6 * N - G - S) (2 * N) (by omega)
        hdSharp heSharp hA
      rw [show (5 * N - G - S) + (6 * N - G - S) + 2 * N - 1 =
        T - S from by dsimp only [T]; omega] at hde
      have hde' : (derivative A * d * e).coeff (T - S) =
          d.coeff (5 * N - G - S) * e.coeff (6 * N - G - S) *
            A.coeff (2 * N) * (((2 * N : ℕ) : k)) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hde
      have hzTop := coeff_mul_mul_derivative_at_bounds68 A A A
        (2 * N) (2 * N) (2 * N) (by omega) hA hA hA
      rw [show 2 * N + 2 * N + 2 * N - 1 = T - S from by
        dsimp only [T]; omega] at hzTop
      have hzTop' : (A ^ 2 * derivative A).coeff (T - S) =
          A.coeff (2 * N) ^ 3 * (((2 * N : ℕ) : k)) := by
        calc
          _ = A.coeff (2 * N) * A.coeff (2 * N) *
                A.coeff (2 * N) * (((2 * N : ℕ) : k)) := by
              simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm]
                using hzTop
          _ = _ := by ring
      have hrow := fiveToSix_cusp_rowZero_firstLoad_core68
        alpha gamma epsilon zeta eta terminal A B c d e N G S S
        ⟨hN, hgt5, hle6, hA, hB, hc, by omega, by omega, ha,
          ⟨hb, hc0, hds, hes, hcusp0⟩, hadapter⟩
        hS hSR hdSharp heSharp (le_refl S) (by omega)
      rw [show 13 * N - 2 * G - S - S - 1 = T - S from by
        dsimp only [T]; omega, hF, hde', hzTop'] at hrow
      have hscalar : (((2 * N : ℕ) : k)) * A.coeff (2 * N) *
          (3 * zeta * A.coeff (2 * N) ^ 2 -
            8 * d.coeff (5 * N - G - S) *
              e.coeff (6 * N - G - S)) = 0 := by
        linear_combination 18 * hrow
      have hnonzero : (((2 * N : ℕ) : k)) * A.coeff (2 * N) ≠ 0 :=
        mul_ne_zero hcast ha
      have hz := (mul_eq_zero.mp hscalar).resolve_left hnonzero
      linear_combination hz

/-- The loaded-wall packet after consuming the first independent lower row.
Only the `zeta*A`-first zero branch and the simultaneous scalar survive. -/
def FiveToSixCuspLoadedLowerRowClassification68
    (zeta : k) (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  let R := 7 * N - 2 * G
  let mu := min S (R - S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8 * N - 2 * G
  let V := 5 * N - G - S
  let W := 6 * N - G - S
  let a := A.coeff (2 * N)
  let b := B.coeff (3 * N - G)
  let c0 := c.coeff (4 * N - G)
  let ds := d.coeff V
  let es := e.coeff W
  let deltaMu := (Delta.reflect U).coeff mu
  (∀ q, q < mu → (Delta.reflect U).coeff q = 0) ∧
    ((R - S < S ∧ mu = R - S ∧ zeta = 0 ∧ deltaMu = 0) ∨
      (S = R - S ∧ mu = S ∧ mu = R - S ∧
        deltaMu * ds + (9 / 8 : k) * zeta * a * c0 -
            (3 / 2 : k) * b * ds ^ 2 = 0 ∧
        3 * zeta * a ^ 2 = 8 * ds * es ∧
        (deltaMu = 0 ↔ 4 * b * ds ^ 2 = 3 * zeta * a * c0)))

theorem fiveToSix_cuspLoadedLowerRow_classify68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hS : 0 < S) (hSR : S < 7 * N - 2 * G)
    (hdSharp : d.natDegree ≤ 5 * N - G - S)
    (heSharp : e.natDegree ≤ 6 * N - G - S)
    (hwall : FiveToSixCuspLoadedWallClassification68 zeta A B c d N G S) :
    FiveToSixCuspLoadedLowerRowClassification68 zeta A B c d e N G S := by
  have hlower := fiveToSix_contractedCusp_loadedLowerRow68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hpacket
    hS hSR hdSharp heSharp
  change _ ∧ _ at hwall
  change _ ∧ _
  refine ⟨hwall.1, ?_⟩
  rcases hwall.2 with hdFirst | hzFirst | hboth
  · exact (hlower.1 hdFirst.1).elim
  · left
    have hzeta := hlower.2.1 hzFirst.1
    exact ⟨hzFirst.1, hzFirst.2.1, hzeta,
      hzFirst.2.2.2.mpr hzeta⟩
  · right
    exact ⟨hboth.1, hboth.2.1, hboth.2.2.1, hboth.2.2.2.1,
      hlower.2.2 hboth.1, hboth.2.2.2.2⟩

/-- Source-facing split.  The terminal all-nonzero cusp remains exactly the
same separate residual; no terminal positive coefficient has been asserted. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_loadedLowerRow_assembly68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    FiveToSixTerminalZeroPacket68 zeta d ee n g ∨
      (∃ N G S, n = 60 * N ∧ g = 60 * G ∧
        FiveToSixCuspLoadedLowerRowClassification68 zeta
          A B (cubicCDefectPolynomial68 A C0)
          (secondaryDDefectPolynomial68 A B D)
          (cubicEDefectPolynomial68 A C0 E) N G S) ∨
      (120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧
        d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n ∧ zeta = 0 ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g)) := by
  dsimp only
  rcases integratedPolynomialLowerSystem68_fiveToSix_finiteStop_assembly68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys with hzero | hearlier | hterminalCusp
  · exact Or.inl hzero
  · right; left
    rcases hearlier.1 with
      ⟨_s, N, G, S, hn, hg, _hs, _hN, hS, hSR,
        hdSharp, heSharp, hpacket, _hsecond⟩
    have hfactor := fiveToSix_contractedCusp_firstLoad_convolution68
      alpha gamma epsilon zeta eta terminal
      A B (cubicCDefectPolynomial68 A C0)
      (secondaryDDefectPolynomial68 A B D)
      (cubicEDefectPolynomial68 A C0 E) N G S hpacket
      hS hSR hdSharp heSharp
    have hwall := fiveToSix_cuspLoadedWall_classify68
      alpha gamma epsilon zeta eta terminal
      A B (cubicCDefectPolynomial68 A C0)
      (secondaryDDefectPolynomial68 A B D)
      (cubicEDefectPolynomial68 A C0 E) N G S hpacket hfactor
    exact ⟨N, G, S, hn, hg,
      fiveToSix_cuspLoadedLowerRow_classify68
        alpha gamma epsilon zeta eta terminal
        A B (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E) N G S hpacket
        hS hSR hdSharp heSharp hwall⟩
  · exact Or.inr (Or.inr hterminalCusp)

#print axioms fiveToSix_cusp_i4_faceSum_coeff_before_firstLoad68
#print axioms fiveToSix_cusp_rowZero_firstLoad_core68
#print axioms fiveToSix_contractedCusp_loadedLowerRow68
#print axioms fiveToSix_cuspLoadedLowerRow_classify68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_loadedLowerRow_assembly68

end FiveToSixCuspLoadedLowerRow68

end Max11DegreeRoutes
