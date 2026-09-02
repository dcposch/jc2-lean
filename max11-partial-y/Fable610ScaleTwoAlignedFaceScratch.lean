import LowScale610ScaleTwoSourceFace
import LowScale68ScaleTwoAlignedNonsquareDegreeTen

/-! # Aligned scale-two discriminator face for the normalized `(6,10)` leaf

Untracked working note.  No tracked file was edited.

`LowScale610ScaleTwoSourceFace` proves the exact first-face dichotomy for
every normalized scale-two `(6,10)` source: the discriminator
`N = 5 p₅ H² - 3 q₉` vanishes, or `N² = κ H⁹` with `κ ≠ 0`.  The nonzero
ninth-power face carries its own chain; this file opens the previously
untouched aligned face `N = 0` and depends on the source face only — no
theorem of the `(6,10)` nonzero-root chain is used, and the degree-`13`
Keller row is re-derived here directly from the literal Keller bracket.

On the aligned face the degree-`15` Jacobian coefficient is the trivial
leading weighted-Wronskian row and the degree-`14` coefficient is spent:
it is the weighted derivative of `N`, and `N = 0`.  The first genuinely
independent Keller row is therefore the degree-`13` coefficient.  On
`N = 0` that row is the weighted derivative `H M' - 5 M H' = 0` of the
cleared weight-five defect

`M = 9 q₈ H - 15 p₄ H³ - 5 p₅²`,

so `M = κ H⁵` is a polynomial first integral.  Clearing gives the
strongest literal source normal form available on the aligned face:

* `q₉ = (5/3) p₅ H²` — the face itself, solved;
* `5 p₅² = H (9 q₈ - 15 p₄ H² - κ H⁴)` — the consumed row, solved;

in particular every root of `H` kills `p₅` and `q₉`.  Unlike the `(6,8)`
aligned defect, the cleared row is quadratic in `p₅` with only one
visible factor of `H`, so the divisibility upgrade honestly splits on
whether the quadratic core is a polynomial square:

* square chamber `H = h₀²`: `h₀² ∣ p₅²`, hence `p₅ = h₀ g`,
  `q₉ = (5/3) g h₀⁵`, and `9 q₈ = 5 g² + 15 p₄ h₀⁴ + κ h₀⁸`;
* nonsquare chamber (`H` a degree-two nonsquare, hence with simple
  roots): `H ∣ p₅`, so `p₅ = H g`, `q₉ = (5/3) g H³`, and
  `9 q₈ = H (5 g² + 15 p₄ H + κ H³)`, in particular `H ∣ q₈`.

The square/nonsquare hypotheses transfer from the mature `(6,8)` aligned
architecture, and exactly three of its generic lemmas are reused:
`nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`, and
`dvd_of_sq_dvd_sq_poly` (plus the numeral helper `C_ofNat_poly`).  They
are generic in the degree pair; no `(6,8)`-specific source theorem is
invoked.

No closure is claimed.  Both chambers remain open: the packet solves
`q₉`, constrains `p₅` and `q₈`, and preserves the constant `κ` of the
weight-five integral without clearing it.  The zero branches of the
chamber data (`g = 0`, `κ = 0`) are not excluded.  The next unused
Keller row on the aligned face is the degree-`12` Jacobian coefficient,
the first row that sees `p₃` and `q₇`.  No total-degree or twice-prime
theorem is used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient on the aligned face -/

/-- The second row below the leading weighted-Wronskian row for outer
degrees `(6,10)`: the degree-`13` Jacobian coefficient.  It is re-derived
here directly from the Keller bracket so that the aligned face depends
only on the source face and not on the nonzero-root chain. -/
theorem alignedSecondCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 5).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 4).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 8).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 9).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 13) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (13 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 13 :
      Finset (ℕ × ℕ)) =
      ({(0, 13), (1, 12), (2, 11), (3, 10), (4, 9), (5, 8), (6, 7),
        (7, 6), (8, 5), (9, 4), (10, 3), (11, 2), (12, 1),
        (13, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  rw [hC8, hC9, hC10, hC6, hC5, hC4]
  linear_combination hcoeff

/-! ## Aligned cleared defect -/

/-- Cleared weight-five defect of the aligned `(6,10)` face:
`M = 9 q₈ H - 15 p₄ H³ - 5 p₅²`.  On the aligned face it is an actual
polynomial first integral, with no square root of `H` required. -/
def alignedSecondDefect610 {K : Type*} [CommRing K]
    (H a4 a5 b8 : K[X]) : K[X] :=
  (9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 - (5 : K[X]) * a5 ^ 2

set_option maxHeartbeats 8000000 in
/-- Exact combination of the degree-`13` Jacobian expression with the
weighted derivative of `M`.  The right-hand side vanishes on `N = 0`. -/
theorem alignedSecondDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K] (H a4 a5 b8 b9 : K[X]) :
    (2 : K[X]) * H *
        (H * (alignedSecondDefect610 H a4 a5 b8).derivative -
          (5 : K[X]) * alignedSecondDefect610 H a4 a5 b8 * H.derivative) +
      (3 : K[X]) *
        ((H ^ 3).derivative * (b8 * (8 : K[X])) +
          a5.derivative * (b9 * (9 : K[X])) +
          a4.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 3 * (6 : K[X])) * b8.derivative +
          (a5 * (5 : K[X])) * b9.derivative +
          (a4 * (4 : K[X])) * (H ^ 5).derivative)) =
      (5 : K[X]) * a5 *
          ((5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9).derivative -
        (9 : K[X]) * a5.derivative *
          ((5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9) := by
  simp only [alignedSecondDefect610, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_ofNat, nsmul_eq_mul, zero_mul, zero_add]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

/-- On the aligned face `N = 0`, the degree-`13` row is the weighted
derivative `H M' - 5 M H' = 0`. -/
theorem alignedSecondDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    H * (alignedSecondDefect610 H (p.coeff 4) (p.coeff 5)
          (q.coeff 8)).derivative -
      (5 : K[X]) *
        alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) *
          H.derivative = 0 := by
  have hrow := alignedSecondCoefficientJacobianRow_610 hp hq hjac
  rw [hp6, hq10] at hrow
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  rw [hC8, hC9, hC10, hC6, hC5, hC4] at hrow
  have hid := alignedSecondDefect_weightedDerivative_identity_610
    H (p.coeff 4) (p.coeff 5) (q.coeff 8) (q.coeff 9)
  rw [haligned, hrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, add_zero,
    sub_zero] at hid
  have h2H : (2 : K[X]) * H ≠ 0 := by
    refine mul_ne_zero ?_ hH
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  exact (mul_eq_zero.mp hid).resolve_left h2H

/-- Polynomial first integral of the aligned `(6,10)` second defect. -/
theorem alignedSecondDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    ∃ κ : K,
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
        Polynomial.C κ * H ^ 5 := by
  let M : K[X] :=
    alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8)
  have hrow : H * M.derivative - (5 : K[X]) * M * H.derivative = 0 := by
    simpa only [M] using
      alignedSecondDefectRow_eq_zero_610 hp hq hjac hH hp6 hq10 haligned
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian M (H ^ 5) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      M * (Polynomial.C (5 : K) * H ^ (5 - 1) * H.derivative) -
          M.derivative * H ^ 5 =
          H ^ 4 *
            (Polynomial.C (5 : K) * M * H.derivative -
              H * M.derivative) := by ring
      _ = 0 := by
        rw [hC5]
        have hfac :
            (5 : K[X]) * M * H.derivative - H * M.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 5 hH) hW

/-- Cleared literal form of the weight-five integral:
`5 p₅² = H (9 q₈ - 15 p₄ H² - κ H⁴)`. -/
theorem alignedSecondDefect_clearing_610 {K : Type*} [CommRing K]
    {H a4 a5 b8 : K[X]} {κ : K}
    (hM : alignedSecondDefect610 H a4 a5 b8 = Polynomial.C κ * H ^ 5) :
    (5 : K[X]) * a5 ^ 2 =
      H * ((9 : K[X]) * b8 - (15 : K[X]) * a4 * H ^ 2 -
        Polynomial.C κ * H ^ 4) := by
  have hM' :
      (9 : K[X]) * b8 * H - (15 : K[X]) * a4 * H ^ 3 -
          (5 : K[X]) * a5 ^ 2 = Polynomial.C κ * H ^ 5 := by
    simpa only [alignedSecondDefect610] using hM
  linear_combination -hM'

/-- Every root of the common core kills `p₅` on the aligned face. -/
theorem alignedSecondDefect_eval_p5_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {H a4 a5 b8 : K[X]} {κ : K}
    (hM : alignedSecondDefect610 H a4 a5 b8 = Polynomial.C κ * H ^ 5)
    {a : K} (ha : H.eval a = 0) : a5.eval a = 0 := by
  have hclear := alignedSecondDefect_clearing_610 hM
  have hc := congrArg (fun f : K[X] => f.eval a) hclear
  simp only [Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, ha, zero_mul] at hc
  have h5 : (5 : K) ≠ 0 := by norm_num
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hc).resolve_left h5)

/-- The aligned face itself in solved form: `q₉ = (5/3) p₅ H²`. -/
theorem aligned_q9_solved_610 {K : Type*} [Field K] [CharZero K]
    {H a5 b9 : K[X]}
    (haligned : (5 : K[X]) * a5 * H ^ 2 - (3 : K[X]) * b9 = 0) :
    b9 = Polynomial.C (5 / 3 : K) * a5 * H ^ 2 := by
  have h3ne : (3 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have h3scale : (3 : K[X]) * Polynomial.C (5 / 3 : K) = (5 : K[X]) := by
    rw [← C_ofNat_poly (n := 3), ← C_ofNat_poly (n := 5),
      ← Polynomial.C_mul]
    norm_num
  apply mul_left_cancel₀ h3ne
  calc
    (3 : K[X]) * b9 = (5 : K[X]) * a5 * H ^ 2 := by
      linear_combination -haligned
    _ = ((3 : K[X]) * Polynomial.C (5 / 3 : K)) * a5 * H ^ 2 := by
      rw [h3scale]
    _ = (3 : K[X]) * (Polynomial.C (5 / 3 : K) * a5 * H ^ 2) := by
      ring

/-! ## Square chamber -/

/-- In the square chamber the core square root divides `p₅`.  This is the
exact transfer of the `(6,8)` aligned square-divisibility step; here it
needs the square hypothesis because the cleared row carries only one
visible factor of `H`. -/
theorem alignedSquare_dvd_p5_610 {K : Type*} [Field K] [CharZero K]
    {H h0 a4 a5 b8 : K[X]} {κ : K} (hHsq : H = h0 ^ 2)
    (hM : alignedSecondDefect610 H a4 a5 b8 = Polynomial.C κ * H ^ 5) :
    h0 ∣ a5 := by
  have hclear := alignedSecondDefect_clearing_610 hM
  rw [hHsq] at hclear
  have h5ne : (5 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have h5inv : (5 : K[X]) * Polynomial.C (5⁻¹ : K) = 1 := by
    rw [← C_ofNat_poly, ← Polynomial.C_mul]
    norm_num
  have hcancel :
      a5 ^ 2 =
        h0 ^ 2 *
          (Polynomial.C (5⁻¹ : K) *
            ((9 : K[X]) * b8 - (15 : K[X]) * a4 * (h0 ^ 2) ^ 2 -
              Polynomial.C κ * (h0 ^ 2) ^ 4)) := by
    apply mul_left_cancel₀ h5ne
    calc
      (5 : K[X]) * a5 ^ 2 =
          h0 ^ 2 *
            ((9 : K[X]) * b8 - (15 : K[X]) * a4 * (h0 ^ 2) ^ 2 -
              Polynomial.C κ * (h0 ^ 2) ^ 4) := hclear
      _ = ((5 : K[X]) * Polynomial.C (5⁻¹ : K)) *
            (h0 ^ 2 *
              ((9 : K[X]) * b8 - (15 : K[X]) * a4 * (h0 ^ 2) ^ 2 -
                Polynomial.C κ * (h0 ^ 2) ^ 4)) := by
          rw [h5inv, one_mul]
      _ = (5 : K[X]) *
            (h0 ^ 2 *
              (Polynomial.C (5⁻¹ : K) *
                ((9 : K[X]) * b8 - (15 : K[X]) * a4 * (h0 ^ 2) ^ 2 -
                  Polynomial.C κ * (h0 ^ 2) ^ 4))) := by ring
  exact dvd_of_sq_dvd_sq_poly ⟨_, hcancel⟩

/-- In the square chamber the octic coefficient is fully solved:
`9 q₈ = 5 g² + 15 p₄ h₀⁴ + κ h₀⁸`. -/
theorem alignedSquare_q8_solved_610 {K : Type*} [Field K] [CharZero K]
    {H h0 g a4 a5 b8 : K[X]} {κ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a5 = h0 * g)
    (hM : alignedSecondDefect610 H a4 a5 b8 = Polynomial.C κ * H ^ 5) :
    (9 : K[X]) * b8 =
      (5 : K[X]) * g ^ 2 + (15 : K[X]) * a4 * h0 ^ 4 +
        Polynomial.C κ * h0 ^ 8 := by
  have hclear := alignedSecondDefect_clearing_610 hM
  rw [hHsq, hg] at hclear
  apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
  linear_combination -hclear

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the full quadratic core divides `p₅`: a
degree-two nonsquare has simple roots, and every root of `H` kills `p₅`.
The simple-root and divisibility lemmas transfer from the `(6,8)` aligned
nonsquare architecture. -/
theorem alignedNonsquare_dvd_p5_610 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a4 a5 b8 : k[X]} {κ : k} (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hM : alignedSecondDefect610 H a4 a5 b8 = Polynomial.C κ * H ^ 5) :
    H ∣ a5 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  exact dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    (fun a ha => alignedSecondDefect_eval_p5_eq_zero_610 hM ha)

/-- In the nonsquare chamber the octic coefficient gains a full core
factor: `9 q₈ = H (5 g² + 15 p₄ H + κ H³)`, in particular `H ∣ q₈`. -/
theorem alignedNonsquare_q8_solved_610 {K : Type*} [Field K] [CharZero K]
    {H g a4 a5 b8 : K[X]} {κ : K}
    (hH : H ≠ 0) (hg : a5 = H * g)
    (hM : alignedSecondDefect610 H a4 a5 b8 = Polynomial.C κ * H ^ 5) :
    (9 : K[X]) * b8 =
      H * ((5 : K[X]) * g ^ 2 + (15 : K[X]) * a4 * H +
        Polynomial.C κ * H ^ 3) := by
  have hclear := alignedSecondDefect_clearing_610 hM
  rw [hg] at hclear
  apply mul_left_cancel₀ hH
  linear_combination -hclear

/-! ## Source-facing aligned packets -/

/-- Source-facing weight-five integral and literal normal form of a
normalized aligned scale-two `(6,10)` source: the face solves `q₉`, and
the consumed degree-`13` row solves `5 p₅²` against `q₈`. -/
theorem normalized610ScaleTwo_alignedFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ : K,
      q.coeff 9 = Polynomial.C (5 / 3 : K) * p.coeff 5 * H ^ 2 ∧
        alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        (5 : K[X]) * p.coeff 5 ^ 2 =
          H * ((9 : K[X]) * q.coeff 8 -
            (15 : K[X]) * p.coeff 4 * H ^ 2 -
            Polynomial.C κ * H ^ 4) := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨κ, hM⟩ := alignedSecondDefectPowerRelation_610 hp hq hjac hH
    (by simpa only [p] using hp6) (by simpa only [q] using hq10) haligned
  exact ⟨κ, aligned_q9_solved_610 haligned, hM,
    alignedSecondDefect_clearing_610 hM⟩

/-- Exact square-chamber packet of a normalized aligned scale-two
`(6,10)` source: `p₅ = h₀ g`, `q₉ = (5/3) g h₀⁵`, and
`9 q₈ = 5 g² + 15 p₄ h₀⁴ + κ h₀⁸`. -/
theorem normalized610ScaleTwo_alignedFace_squareChamber_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ : K) (g : K[X]),
      p.coeff 5 = h0 * g ∧
        q.coeff 9 = Polynomial.C (5 / 3 : K) * g * h0 ^ 5 ∧
        (9 : K[X]) * q.coeff 8 =
          (5 : K[X]) * g ^ 2 + (15 : K[X]) * p.coeff 4 * h0 ^ 4 +
            Polynomial.C κ * h0 ^ 8 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨κ, hM⟩ := alignedSecondDefectPowerRelation_610 hp hq hjac hH
    (by simpa only [p] using hp6) (by simpa only [q] using hq10) haligned
  obtain ⟨g, hg⟩ := alignedSquare_dvd_p5_610 hHsq hM
  have hq9 : q.coeff 9 = Polynomial.C (5 / 3 : K) * p.coeff 5 * H ^ 2 :=
    aligned_q9_solved_610 haligned
  refine ⟨κ, g, hg, ?_, alignedSquare_q8_solved_610 hh0 hHsq hg hM⟩
  rw [hq9, hg, hHsq]
  ring

/-- Exact nonsquare-chamber packet of a normalized aligned scale-two
`(6,10)` source: `p₅ = H g`, `q₉ = (5/3) g H³`, and
`9 q₈ = H (5 g² + 15 p₄ H + κ H³)`. -/
theorem normalized610ScaleTwo_alignedFace_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ : K) (g : K[X]),
      p.coeff 5 = H * g ∧
        q.coeff 9 = Polynomial.C (5 / 3 : K) * g * H ^ 3 ∧
        (9 : K[X]) * q.coeff 8 =
          H * ((5 : K[X]) * g ^ 2 + (15 : K[X]) * p.coeff 4 * H +
            Polynomial.C κ * H ^ 3) := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨κ, hM⟩ := alignedSecondDefectPowerRelation_610 hp hq hjac hH
    (by simpa only [p] using hp6) (by simpa only [q] using hq10) haligned
  obtain ⟨g, hg⟩ := alignedNonsquare_dvd_p5_610 hHdegree hnsq hM
  have hq9 : q.coeff 9 = Polynomial.C (5 / 3 : K) * p.coeff 5 * H ^ 2 :=
    aligned_q9_solved_610 haligned
  refine ⟨κ, g, hg, ?_, alignedNonsquare_q8_solved_610 hH hg hM⟩
  rw [hq9, hg]
  ring

/-- Honest square/nonsquare chamber split of the aligned `(6,10)` face,
mirroring the `(6,8)` aligned architecture.  Neither chamber is excluded
and no closure is claimed. -/
theorem normalized610ScaleTwo_alignedFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (κ : K) (g : K[X]),
        p.coeff 5 = h0 * g ∧
          q.coeff 9 = Polynomial.C (5 / 3 : K) * g * h0 ^ 5 ∧
          (9 : K[X]) * q.coeff 8 =
            (5 : K[X]) * g ^ 2 + (15 : K[X]) * p.coeff 4 * h0 ^ 4 +
              Polynomial.C κ * h0 ^ 8) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g : K[X]),
        p.coeff 5 = H * g ∧
          q.coeff 9 = Polynomial.C (5 / 3 : K) * g * H ^ 3 ∧
          (9 : K[X]) * q.coeff 8 =
            H * ((5 : K[X]) * g ^ 2 + (15 : K[X]) * p.coeff 4 * H +
              Polynomial.C κ * H ^ 3)) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    exact Or.inl ⟨h0, hh0, hHsq,
      normalized610ScaleTwo_alignedFace_squareChamber_packet
        hsource hh0 hHsq haligned⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    exact Or.inr ⟨hnsq,
      normalized610ScaleTwo_alignedFace_nonsquareChamber_packet
        hsource hnsq haligned⟩

/-- At scale two the common core has a root, and on the aligned face the
jet `p₅, q₉` vanishes there.  This is the chamber-independent root jet of
the consumed degree-`13` row. -/
theorem normalized610ScaleTwo_alignedFace_rootJet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ a : K, H.eval a = 0 ∧ (p.coeff 5).eval a = 0 ∧
      (q.coeff 9).eval a = 0 := by
  dsimp only at haligned ⊢
  have hH : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  have hdeg : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hHdegree]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdeg
  have hroot : H.eval a = 0 := ha
  obtain ⟨κ, hq9, hM, _hclear⟩ :=
    normalized610ScaleTwo_alignedFace_packet hsource haligned
  have hp5 :
      (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 5).eval
        a = 0 :=
    alignedSecondDefect_eval_p5_eq_zero_610 hM hroot
  refine ⟨a, hroot, hp5, ?_⟩
  simp [hq9, hroot]

#print axioms alignedSecondCoefficientJacobianRow_610
#print axioms alignedSecondDefectRow_eq_zero_610
#print axioms alignedSecondDefectPowerRelation_610
#print axioms alignedSecondDefect_clearing_610
#print axioms alignedSecondDefect_eval_p5_eq_zero_610
#print axioms aligned_q9_solved_610
#print axioms alignedSquare_dvd_p5_610
#print axioms alignedSquare_q8_solved_610
#print axioms alignedNonsquare_dvd_p5_610
#print axioms alignedNonsquare_q8_solved_610
#print axioms normalized610ScaleTwo_alignedFace_packet
#print axioms normalized610ScaleTwo_alignedFace_squareChamber_packet
#print axioms normalized610ScaleTwo_alignedFace_nonsquareChamber_packet
#print axioms normalized610ScaleTwo_alignedFace_chamberDichotomy
#print axioms normalized610ScaleTwo_alignedFace_rootJet

end Max11DegreeRoutes
