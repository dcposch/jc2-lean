import Sol68FiveToSixCuspConvolutionPart01Scratch

/-! # Finite discriminant convolution at an arbitrary cusp depth

The exact first-integral combination from the third-jet file works at every
contracted depth.  Reflection turns its leading term `Delta*d` into an
ordinary coefficient convolution.  Since the edge coefficient of `d` is
nonzero, strong induction kills every `Delta` jet strictly before the first
load `mu = min(S, 7N-2G-S)`.  At `mu` the same convolution leaves exactly
the `d^2`, `zeta*A`, or simultaneous loaded scalar.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspConvolution68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

private structure Leaf68Bound (p : k[X]) (u : ℕ) : Prop where
  le : p.natDegree ≤ u

private theorem leaf68_bd_of_le {p : k[X]} {u : ℕ} (h : p.natDegree ≤ u) :
    Leaf68Bound p u := ⟨h⟩

private theorem leaf68_bd_C (a : k) : Leaf68Bound (C a) 0 :=
  ⟨(natDegree_C a).le⟩

private theorem leaf68_bd_smul (r : k) {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (r • p) u :=
  ⟨(natDegree_smul_le r p).trans hp.le⟩

private theorem leaf68_bd_neg {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (-p) u :=
  ⟨(natDegree_neg p).le.trans hp.le⟩

private theorem leaf68_bd_add {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p + q) (max u v) :=
  ⟨(natDegree_add_le p q).trans (max_le_max hp.le hq.le)⟩

private theorem leaf68_bd_sub {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p - q) (max u v) :=
  ⟨(natDegree_sub_le p q).trans (max_le_max hp.le hq.le)⟩

private theorem leaf68_bd_mul {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p * q) (u + v) :=
  ⟨natDegree_mul_le.trans (Nat.add_le_add hp.le hq.le)⟩

private theorem leaf68_bd_pow {p : k[X]} {u : ℕ} (m : ℕ)
    (hp : Leaf68Bound p u) : Leaf68Bound (p ^ m) (m * u) :=
  ⟨natDegree_pow_le.trans (Nat.mul_le_mul (le_refl m) hp.le)⟩

private theorem leaf68_bd_deriv {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (derivative p) (u - 1) :=
  ⟨(natDegree_derivative_le p).trans (Nat.sub_le_sub_right hp.le 1)⟩

private theorem leaf68_lt_of_bd {p : k[X]} {u b : ℕ}
    (hp : Leaf68Bound p u) (h : u < b) : p.natDegree < b :=
  lt_of_le_of_lt hp.le h

private theorem leaf68_le_of_bd {p : k[X]} {u b : ℕ}
    (hp : Leaf68Bound p u) (h : u ≤ b) : p.natDegree ≤ b :=
  hp.le.trans h


set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 30000000 in
theorem fiveToSix_contractedCusp_firstLoad_convolution68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hS : 0 < S) (hSR : S < 7 * N - 2 * G)
    (hdSharp : d.natDegree ≤ 5 * N - G - S)
    (heSharp : e.natDegree ≤ 6 * N - G - S) :
    FiveToSixCuspFirstLoadFactor68 zeta A B c d N G S := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, _ha, hcusp, hadapter⟩
  rcases hcusp with ⟨_hb, _hc0, hds, _hes, hcusp0⟩
  rcases hadapter with
    ⟨i4, i3, hi4, hi3, _hrow0, _hrow1, _hrow2, _hrow0pos, _hiff⟩
  let R := 7 * N - 2 * G
  let mu := min S (R - S)
  let U := 8 * N - 2 * G
  let V := 5 * N - G - S
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  have hmuS : mu ≤ S := Nat.min_le_left _ _
  have hmuZ : mu ≤ R - S := Nat.min_le_right _ _
  have hstop := fiveToSix_cuspJet_finiteStop_arithmetic68
    N G S hN ⟨hgt5, hle6⟩ hS hSR
  change 0 < mu ∧ _ ∧ _ ∧ _ at hstop
  have hmuPos := hstop.1
  have hwallCases := hstop.2.2.2
  have hRG : R < G := by omega
  have hmuGamma : mu < 4 * N - G := by
    rcases le_total S (R - S) with hleft | hright
    · have htwice : 2 * S ≤ R := by omega
      omega
    · have htwice : 2 * (R - S) ≤ R := by omega
      omega
  have hDelta : Delta.natDegree ≤ U := by
    dsimp only [Delta, U, fiveToSixCuspDiscriminantPolynomial68]
    first
    | with_reducible apply leaf68_lt_of_bd
    | with_reducible apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hdSharp
      | with_reducible exact leaf68_bd_of_le heSharp
      | with_reducible exact leaf68_bd_of_le hDelta
      | exact leaf68_bd_of_le (by assumption)
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hB2 : (B ^ 2).natDegree ≤ 6 * N - 2 * G := by
    first
    | with_reducible apply leaf68_lt_of_bd
    | with_reducible apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hdSharp
      | with_reducible exact leaf68_bd_of_le heSharp
      | with_reducible exact leaf68_bd_of_le hDelta
      | exact leaf68_bd_of_le (by assumption)
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hB2top := coeff_mul_at_bounds68 B B (3 * N - G) (3 * N - G)
    hB hB
  rw [← pow_two, show (3 * N - G) + (3 * N - G) = 6 * N - 2 * G
    from by omega] at hB2top
  have hAB2top := coeff_mul_at_bounds68 A (B ^ 2)
    (2 * N) (6 * N - 2 * G) hA hB2
  rw [show 2 * N + (6 * N - 2 * G) = U from by omega, hB2top]
    at hAB2top
  have hc2top := coeff_mul_at_bounds68 c c (4 * N - G) (4 * N - G)
    hc hc
  rw [← pow_two, show (4 * N - G) + (4 * N - G) = U from by omega]
    at hc2top
  have hDeltaTop : Delta.coeff U = 0 := by
    dsimp only [Delta, fiveToSixCuspDiscriminantPolynomial68]
    rw [coeff_add, coeff_smul, smul_eq_mul, hAB2top, hc2top]
    linear_combination hcusp0
  have hDelta0 : (Delta.reflect U).coeff 0 = 0 := by
    simpa only [coeff_reflect, revAt_zero] using hDeltaTop
  have hdsR : (d.reflect V).coeff 0 ≠ 0 := by
    simpa only [coeff_reflect, revAt_zero, V] using hds
  have hidentity := fiveToSix_firstIntegrals_cuspCombination68
    gamma epsilon zeta A B c d e

  have hcombination_coeff (q : ℕ) (hq : q ≤ mu) :
      (Delta * d).coeff (U + V - q) +
        (9 / 8 * zeta : k) * (A * c).coeff (U + V - q) -
        (3 / 2 : k) * (B * d ^ 2).coeff (U + V - q) = 0 := by
    have hidx : U + V - q = 13 * N - 3 * G - S - q := by omega
    have hBzero : B.coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      omega
    have hczero : c.coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      omega
    have hB3czero : (B ^ 3 * c).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      first
      | with_reducible apply leaf68_lt_of_bd
      | with_reducible apply leaf68_le_of_bd
      repeat'
        first
        | with_reducible exact leaf68_bd_of_le hdSharp
        | with_reducible exact leaf68_bd_of_le heSharp
        | with_reducible exact leaf68_bd_of_le hDelta
        | exact leaf68_bd_of_le (by assumption)
        | with_reducible apply leaf68_bd_smul
        | with_reducible apply leaf68_bd_neg
        | with_reducible apply leaf68_bd_sub
        | with_reducible apply leaf68_bd_add
        | with_reducible apply leaf68_bd_pow
        | with_reducible apply leaf68_bd_deriv
        | with_reducible apply leaf68_bd_mul
        | with_reducible apply leaf68_bd_C
        | omega
    have hB2zero : (B ^ 2).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      first
      | with_reducible apply leaf68_lt_of_bd
      | with_reducible apply leaf68_le_of_bd
      repeat'
        first
        | with_reducible exact leaf68_bd_of_le hdSharp
        | with_reducible exact leaf68_bd_of_le heSharp
        | with_reducible exact leaf68_bd_of_le hDelta
        | exact leaf68_bd_of_le (by assumption)
        | with_reducible apply leaf68_bd_smul
        | with_reducible apply leaf68_bd_neg
        | with_reducible apply leaf68_bd_sub
        | with_reducible apply leaf68_bd_add
        | with_reducible apply leaf68_bd_pow
        | with_reducible apply leaf68_bd_deriv
        | with_reducible apply leaf68_bd_mul
        | with_reducible apply leaf68_bd_C
        | omega
    have hcdzero : (c * d).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      first
      | with_reducible apply leaf68_lt_of_bd
      | with_reducible apply leaf68_le_of_bd
      repeat'
        first
        | with_reducible exact leaf68_bd_of_le hdSharp
        | with_reducible exact leaf68_bd_of_le heSharp
        | with_reducible exact leaf68_bd_of_le hDelta
        | exact leaf68_bd_of_le (by assumption)
        | with_reducible apply leaf68_bd_smul
        | with_reducible apply leaf68_bd_neg
        | with_reducible apply leaf68_bd_sub
        | with_reducible apply leaf68_bd_add
        | with_reducible apply leaf68_bd_pow
        | with_reducible apply leaf68_bd_deriv
        | with_reducible apply leaf68_bd_mul
        | with_reducible apply leaf68_bd_C
        | omega
    have hBezero : (B * e).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      first
      | with_reducible apply leaf68_lt_of_bd
      | with_reducible apply leaf68_le_of_bd
      repeat'
        first
        | with_reducible exact leaf68_bd_of_le hdSharp
        | with_reducible exact leaf68_bd_of_le heSharp
        | with_reducible exact leaf68_bd_of_le hDelta
        | exact leaf68_bd_of_le (by assumption)
        | with_reducible apply leaf68_bd_smul
        | with_reducible apply leaf68_bd_neg
        | with_reducible apply leaf68_bd_sub
        | with_reducible apply leaf68_bd_add
        | with_reducible apply leaf68_bd_pow
        | with_reducible apply leaf68_bd_deriv
        | with_reducible apply leaf68_bd_mul
        | with_reducible apply leaf68_bd_C
        | omega
    have hB3zero : (B ^ 3).coeff (U + V - q) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      first
      | with_reducible apply leaf68_lt_of_bd
      | with_reducible apply leaf68_le_of_bd
      repeat'
        first
        | with_reducible exact leaf68_bd_of_le hdSharp
        | with_reducible exact leaf68_bd_of_le heSharp
        | with_reducible exact leaf68_bd_of_le hDelta
        | exact leaf68_bd_of_le (by assumption)
        | with_reducible apply leaf68_bd_smul
        | with_reducible apply leaf68_bd_neg
        | with_reducible apply leaf68_bd_sub
        | with_reducible apply leaf68_bd_add
        | with_reducible apply leaf68_bd_pow
        | with_reducible apply leaf68_bd_deriv
        | with_reducible apply leaf68_bd_mul
        | with_reducible apply leaf68_bd_C
        | omega
    have hz := congrArg (fun p : k[X] => p.coeff (U + V - q)) hidentity
    rw [hi3, hi4] at hz
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul,
      coeff_mul_C, hBzero, hczero, hB3czero, hB2zero, hcdzero, hBezero,
      hB3zero, zero_mul, mul_zero, add_zero, sub_zero] at hz
    change 0 = (Delta * d).coeff (U + V - q) -
      (3 / 2 : k) * (B * d ^ 2).coeff (U + V - q) +
      (9 / 8 : k) * zeta * (A * c).coeff (U + V - q) at hz
    linear_combination -hz

  have hvanish : ∀ q, q < mu → (Delta.reflect U).coeff q = 0 := by
    have hall := fiveToSix_cuspJet_zero_before_firstLoad68 mu
      (fun q => (Delta.reflect U).coeff q) hDelta0
      (by
        intro q hq hprev
        let t := q + 1
        have htmu : t < mu := hq
        have htS : t < S := lt_of_lt_of_le htmu hmuS
        have htZ : t < R - S := lt_of_lt_of_le htmu hmuZ
        have hAc : (A * c).coeff (U + V - t) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          compute_degree
          omega
        have hBd : (B * d ^ 2).coeff (U + V - t) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          compute_degree
          omega
        have hprodRaw := hcombination_coeff t (Nat.le_of_lt htmu)
        have hprod : (Delta * d).coeff (U + V - t) = 0 := by
          rw [hAc, hBd] at hprodRaw
          linear_combination hprodRaw
        have href := coeff_mul_at_reflect_of_left_lower_zero68
          Delta d U V t hDelta hdSharp (by omega)
          (by
            intro j hj
            exact hprev j (by omega))
        rw [href] at hprod
        exact (mul_eq_zero.mp hprod).resolve_right hdsR)
    intro q hq
    exact hall q hq q (by omega)

  have hwallRaw := hcombination_coeff mu (le_refl mu)
  have hrefWall := coeff_mul_at_reflect_of_left_lower_zero68
    Delta d U V mu hDelta hdSharp (by omega) hvanish
  rw [hrefWall] at hwallRaw
  have hds0 : (d.reflect V).coeff 0 = d.coeff V := by
    simp only [coeff_reflect, revAt_zero]
  rw [hds0] at hwallRaw
  have hActop := coeff_mul_at_bounds68 A c (2 * N) (4 * N - G) hA hc
  have hd2bound : (d ^ 2).natDegree ≤ 2 * V := by
    dsimp only [V]
    first
    | with_reducible apply leaf68_lt_of_bd
    | with_reducible apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hdSharp
      | with_reducible exact leaf68_bd_of_le heSharp
      | with_reducible exact leaf68_bd_of_le hDelta
      | exact leaf68_bd_of_le (by assumption)
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hd2top := coeff_mul_at_bounds68 d d V V hdSharp hdSharp
  rw [← pow_two] at hd2top
  have hd2top' : (d ^ 2).coeff (2 * V) = d.coeff V ^ 2 := by
    rw [show 2 * V = V + V from by omega, hd2top]
    ring
  have hBdtop := coeff_mul_at_bounds68 B (d ^ 2)
    (3 * N - G) (2 * V) hB hd2bound
  rw [hd2top'] at hBdtop
  have hAc_before (hq : mu < R - S) :
      (A * c).coeff (U + V - mu) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    first
    | with_reducible apply leaf68_lt_of_bd
    | with_reducible apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hdSharp
      | with_reducible exact leaf68_bd_of_le heSharp
      | with_reducible exact leaf68_bd_of_le hDelta
      | exact leaf68_bd_of_le (by assumption)
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hAc_wall (hq : mu = R - S) :
      (A * c).coeff (U + V - mu) =
        A.coeff (2 * N) * c.coeff (4 * N - G) := by
    rw [show U + V - mu = 2 * N + (4 * N - G) from by omega]
    exact hActop
  have hBd_before (hq : mu < S) :
      (B * d ^ 2).coeff (U + V - mu) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    first
    | with_reducible apply leaf68_lt_of_bd
    | with_reducible apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hdSharp
      | with_reducible exact leaf68_bd_of_le heSharp
      | with_reducible exact leaf68_bd_of_le hDelta
      | exact leaf68_bd_of_le (by assumption)
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hBd_wall (hq : mu = S) :
      (B * d ^ 2).coeff (U + V - mu) =
        B.coeff (3 * N - G) * d.coeff V ^ 2 := by
    rw [show U + V - mu = (3 * N - G) + 2 * V from by omega]
    exact hBdtop
  change (∀ q, q < mu → (Delta.reflect U).coeff q = 0) ∧ _
  refine ⟨hvanish, ?_⟩
  rcases hwallCases with ⟨hlt, hmuS'⟩ | ⟨hlt, hmuZ'⟩ |
      ⟨heq, hmuS', hmuZ'⟩
  · left
    refine ⟨hlt, hmuS', ?_⟩
    rw [hAc_before (by omega), hBd_wall hmuS', mul_zero] at hwallRaw
    linear_combination hwallRaw
  · right; left
    refine ⟨hlt, hmuZ', ?_⟩
    rw [hAc_wall hmuZ', hBd_before (by omega), mul_zero, sub_zero] at hwallRaw
    linear_combination hwallRaw
  · right; right
    refine ⟨heq, hmuS', hmuZ', ?_⟩
    rw [hAc_wall hmuZ', hBd_wall hmuS'] at hwallRaw
    linear_combination hwallRaw

end FiveToSixCuspConvolution68
end Max11DegreeRoutes
