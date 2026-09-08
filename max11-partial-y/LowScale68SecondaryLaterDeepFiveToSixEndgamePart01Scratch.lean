import LowScale68SecondaryLaterDeepSevenBoundaryEndgame

/-! # The remaining later-deep five-to-six window

The two invariant faces are already available.  Here the terminal lower row
is shown to retain its ordinary first-secondary scalar throughout
`5n < 2g ≤ 6n`, despite the deeper load chamber.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSix68

variable {k : Type*} [Field k] [CharZero k]

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


set_option maxHeartbeats 14000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem fiveToSix_loadRowZero_eq68
    (alpha gamma epsilon zeta eta : k) (A B c D e E0 Ur W : k[X])
    (hE0 : E0 = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hUr : Ur = (2 / 3 * gamma : k) • B + C zeta)
    (hW : W = (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
      (1 / 3 * epsilon : k) • A + C eta) :
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c D e = Ur * derivative E0 - D * derivative W := by
  have hUl : cubicLoadUPolynomial68 0 alpha 0 gamma 0 zeta
      A B c D e = alpha • D + Ur := by
    simp [hUr, cubicLoadUPolynomial68]
    module
  have hVl : cubicLoadVPolynomial68 0 alpha 0 gamma 0 epsilon eta
      A B c D e = alpha • E0 + W := by
    simp only [hE0, hW, cubicLoadVPolynomial68, zero_mul, zero_smul,
      smul_zero, zero_add, add_zero]
    module
  rw [cubicLoadRowZeroPolynomial68, hUl, hVl, ← hE0]
  simp only [derivative_add]
  simp only [derivative_smul]
  simp only [Polynomial.smul_eq_C_mul]
  ring

private theorem fiveToSix_coreRowZero_coeff68
    (A B c D e : k[X]) (n g j : ℕ) (hj : j = 13 * n - 2 * g - 1)
    (hn : 0 < n) (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (firstSecondaryCoreRowZeroPolynomial68 A B c D e).coeff j =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hD
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 : (A ^ 2 * B * c * derivative A).coeff j =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) *
          ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 (A ^ 2) B c A
      (4 * n) (3 * n - g) (4 * n - g) (2 * n) (by omega)
      hA2deg hB hc hA
    have hi : 4 * n + (3 * n - g) + (4 * n - g) + 2 * n - 1 = j := by
      omega
    rw [hi, hA2] at h
    exact h
  have h2 : (A * D * c * derivative A).coeff j =
      A.coeff (2 * n) * D.coeff (5 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) *
          ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 A D c A
      (2 * n) (5 * n - g) (4 * n - g) (2 * n) (by omega)
      hA hD hc hA
    have hi : 2 * n + (5 * n - g) + (4 * n - g) + 2 * n - 1 = j := by
      omega
    simpa only [hi] using h
  have h3 : (D * e * derivative A).coeff j =
      D.coeff (5 * n - g) * e.coeff (6 * n - g) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 D e A
      (5 * n - g) (6 * n - g) (2 * n) (by omega) hD he hA
    have hi : (5 * n - g) + (6 * n - g) + 2 * n - 1 = j := by
      omega
    simpa only [hi] using h
  simp only [firstSecondaryCoreRowZeroPolynomial68, coeff_smul, coeff_sub,
    h1, h2, h3, smul_eq_mul]
  push_cast
  simp only [firstSecondaryZero68]
  ring

/-- The terminal lower row gives the ordinary scalar `F₀=0` throughout
`5n < 2g ≤ 6n` after `l=beta=delta=0`. -/
theorem lowerRowZeroPolynomial68_fiveToSix_forces_firstSecondaryZero
    (alpha gamma epsilon zeta eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hrowCoeff :
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B
          ((1 / 3 : k) • A ^ 2 + c) D
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A B
          ((1 / 3 : k) • A ^ 2 + c) D
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
        D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (13 * n - 2 * g - 1) = 0) :
    firstSecondaryZero68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
  let j := 13 * n - 2 * g - 1
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ur : k[X] := (2 / 3 * gamma : k) • B + C zeta
  let W : k[X] :=
    (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
      (1 / 3 * epsilon : k) • A + C eta
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon zeta eta A B c D e
  have hu := hcoords.u_eq
  have hv := hcoords.v_eq
  change integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B
      ((1 / 3 : k) • A ^ 2 + c) D E0 = _ at hu
  change integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A B
      ((1 / 3 : k) • A ^ 2 + c) D E0 = _ at hv
  change (lowerRowZeroPolynomial68 _ _ D E0).coeff j = 0 at hrowCoeff
  rw [hu, hv, cubicRowZeroPolynomial68_split,
    cubicHomogeneousRowZeroPolynomial68_eq_expanded,
    cubicHomogeneousRowZeroExpandedPolynomial68, coeff_add, coeff_add]
      at hrowCoeff
  have hcore :
      (firstSecondaryCoreRowZeroPolynomial68 A B c D e).coeff j =
        (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
          firstSecondaryZero68
            (A.coeff (2 * n)) (B.coeff (3 * n - g))
            (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
            (e.coeff (6 * n - g)) :=
    fiveToSix_coreRowZero_coeff68 A B c D e n g j rfl hn hwindow hA hB hc hD he
  have hremdeg : (cubicRemainderRowZeroPolynomial68 A B c D e).natDegree <
      j := by
    simp only [cubicRemainderRowZeroPolynomial68]
    dsimp only [j]
    apply leaf68_lt_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hD
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hloadEq :
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c D e = Ur * derivative E0 - D * derivative W :=
    fiveToSix_loadRowZero_eq68 alpha gamma epsilon zeta eta A B c D e E0 Ur W
      rfl rfl rfl
  have hEdeg : E0.natDegree ≤ 6 * n := by
    simp only [E0]
    apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hD
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible exact leaf68_bd_of_le hEdeg
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hUrdeg : Ur.natDegree ≤ 3 * n - g := by
    simp only [Ur]
    apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hD
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible exact leaf68_bd_of_le hEdeg
      | with_reducible exact leaf68_bd_of_le hUrdeg
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  have hWdeg : W.natDegree ≤ 4 * n := by
    simp only [W]
    apply leaf68_le_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hD
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible exact leaf68_bd_of_le hEdeg
      | with_reducible exact leaf68_bd_of_le hUrdeg
      | with_reducible exact leaf68_bd_of_le hWdeg
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  clear_value E0 Ur W
  have hloaddeg :
      (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c D e).natDegree < j := by
    rw [hloadEq]
    dsimp only [j]
    apply leaf68_lt_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hD
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible exact leaf68_bd_of_le hEdeg
      | with_reducible exact leaf68_bd_of_le hUrdeg
      | with_reducible exact leaf68_bd_of_le hWdeg
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  rw [hcore, coeff_eq_zero_of_natDegree_lt hremdeg,
    coeff_eq_zero_of_natDegree_lt hloaddeg] at hrowCoeff
  simp only [add_zero] at hrowCoeff
  have hnCast : (n : k) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact (mul_eq_zero.mp hrowCoeff).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) hnCast) ha)

end LaterDeepFiveToSix68
end Max11DegreeRoutes
