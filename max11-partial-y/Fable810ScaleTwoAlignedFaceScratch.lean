import LowScale810ScaleTwoSourceFace
import LowScale68ScaleTwoAlignedNonsquareDegreeTen

/-! # Aligned scale-two discriminator face for the normalized `(8,10)` leaf

Untracked working note.  No tracked file was edited.

`LowScale810ScaleTwoSourceFace` proves the exact first-face dichotomy for
every normalized scale-two `(8,10)` source: the discriminator
`N = 5 p₇ H - 4 q₉` vanishes, or `N² = κ H⁹` with `κ ≠ 0`.  The nonzero
ninth-power face carries its own chain; this file opens the previously
untouched aligned face `N = 0` and depends on the source face only — no
theorem of the `(8,10)` nonzero-root chain is imported or used, and the
degree-`15` Keller row is re-derived here directly from the literal
Keller bracket.

On the aligned face the degree-`17` Jacobian coefficient is the trivial
leading weighted-Wronskian row and the degree-`16` coefficient is spent:
it is the weighted derivative of `N`, and `N = 0`.  The first genuinely
independent Keller row is therefore the degree-`15` coefficient.  On
`N = 0` that row is the weighted derivative `H M' - 7 M H' = 0` of the
cleared weight-fourteen defect

`M = 32 q₈ H³ - 40 p₆ H⁴ - 5 p₇²`,

so `M = κ H⁷` is a polynomial first integral.  Clearing gives the
strongest literal source normal form available on the aligned face:

* `q₉ = (5/4) p₇ H` — the face itself, solved;
* `5 p₇² = H³ (32 q₈ - 40 p₆ H - κ H⁴)` — the consumed row, solved;

in particular every root of `H` kills `p₇` and `q₉`.  Unlike the
`(6,10)` aligned defect, the cleared row carries three visible factors
of `H`, so the honest square/nonsquare split of the quadratic core is
correspondingly deeper:

* square chamber `H = h₀²`: `h₀⁶ ∣ p₇²`, hence `p₇ = h₀³ g`,
  `q₉ = (5/4) g h₀⁵`, and `32 q₈ = 5 g² + 40 p₆ h₀² + κ h₀⁸`;
* nonsquare chamber (`H` a degree-two nonsquare, hence with simple
  roots): a two-step descent `H ∣ p₇`, then `H ∣ p₇ / H`, gives
  `p₇ = H² g₂`, `q₉ = (5/4) g₂ H³`, and
  `32 q₈ = H (5 g₂² + 40 p₆ + κ H³)`, in particular `H ∣ q₈`.

The square/nonsquare hypotheses transfer from the mature `(6,8)` aligned
architecture, and exactly three of its generic lemmas are reused:
`nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`, and
`dvd_of_sq_dvd_sq_poly` (plus the numeral helper `C_ofNat_poly`).  They
are generic in the degree pair; no `(6,8)`-specific source theorem is
invoked.

No closure is claimed.  Both chambers remain open: the packet solves
`q₉`, constrains `p₇` and `q₈`, and preserves the constant `κ` of the
weight-fourteen integral without clearing it.  The zero branches of the
chamber data (`g = 0`, `g₂ = 0`, `κ = 0`) are not excluded, and no
individual vanishing of `p₆`, `p₇`, `q₈` is claimed.  The next unused
Keller row on the aligned face is the degree-`14` Jacobian coefficient,
the first row that sees `p₅` and `q₇`.  No total-degree or twice-prime
theorem is used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient on the aligned face -/

/-- The second row below the leading weighted-Wronskian row for outer
degrees `(8,10)`: the degree-`15` Jacobian coefficient.  It is re-derived
here directly from the Keller bracket so that the aligned face depends
only on the source face and not on the nonzero-root chain. -/
theorem alignedSecondCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 7).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 6).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 8).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 9).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 15) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (15 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 15 :
      Finset (ℕ × ℕ)) =
      ({(0, 15), (1, 14), (2, 13), (3, 12), (4, 11), (5, 10), (6, 9),
        (7, 8), (8, 7), (9, 6), (10, 5), (11, 4), (12, 3), (13, 2),
        (14, 1), (15, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  rw [hC8, hC9, hC10, hC7, hC6]
  linear_combination hcoeff

/-! ## Aligned cleared defect -/

/-- Cleared weight-fourteen defect of the aligned `(8,10)` face:
`M = 32 q₈ H³ - 40 p₆ H⁴ - 5 p₇²`.  On the aligned face it is an actual
polynomial first integral, with no square root of `H` required. -/
def alignedSecondDefect810 {K : Type*} [CommRing K]
    (H a6 a7 b8 : K[X]) : K[X] :=
  (32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
    (5 : K[X]) * a7 ^ 2

set_option maxHeartbeats 8000000 in
/-- Exact combination of the degree-`15` Jacobian expression with the
weighted derivative of `M`.  The right-hand side vanishes on `N = 0`. -/
theorem alignedSecondDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K] (H a6 a7 b8 b9 : K[X]) :
    (H * (alignedSecondDefect810 H a6 a7 b8).derivative -
        (7 : K[X]) * alignedSecondDefect810 H a6 a7 b8 * H.derivative) +
      (4 : K[X]) *
        ((H ^ 4).derivative * (b8 * (8 : K[X])) +
          a7.derivative * (b9 * (9 : K[X])) +
          a6.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 4 * (8 : K[X])) * b8.derivative +
          (a7 * (7 : K[X])) * b9.derivative +
          (a6 * (6 : K[X])) * (H ^ 5).derivative)) =
      (7 : K[X]) * a7 *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9).derivative -
        (9 : K[X]) * a7.derivative *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9) := by
  simp only [alignedSecondDefect810, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_ofNat, nsmul_eq_mul, zero_mul, zero_add]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

/-- On the aligned face `N = 0`, the degree-`15` row is the weighted
derivative `H M' - 7 M H' = 0`. -/
theorem alignedSecondDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    H * (alignedSecondDefect810 H (p.coeff 6) (p.coeff 7)
          (q.coeff 8)).derivative -
      (7 : K[X]) *
        alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) *
          H.derivative = 0 := by
  have hrow := alignedSecondCoefficientJacobianRow_810 hp hq hjac
  rw [hp8, hq10] at hrow
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  rw [hC8, hC9, hC10, hC7, hC6] at hrow
  have hid := alignedSecondDefect_weightedDerivative_identity_810
    H (p.coeff 6) (p.coeff 7) (q.coeff 8) (q.coeff 9)
  rw [haligned, hrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, add_zero,
    sub_zero] at hid
  exact hid

/-- Polynomial first integral of the aligned `(8,10)` second defect. -/
theorem alignedSecondDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    ∃ κ : K,
      alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
        Polynomial.C κ * H ^ 7 := by
  let M : K[X] :=
    alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8)
  have hrow : H * M.derivative - (7 : K[X]) * M * H.derivative = 0 := by
    simpa only [M] using
      alignedSecondDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian M (H ^ 7) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      M * (Polynomial.C (7 : K) * H ^ (7 - 1) * H.derivative) -
          M.derivative * H ^ 7 =
          H ^ 6 *
            (Polynomial.C (7 : K) * M * H.derivative -
              H * M.derivative) := by ring
      _ = 0 := by
        rw [hC7]
        have hfac :
            (7 : K[X]) * M * H.derivative - H * M.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 7 hH) hW

/-- Cleared literal form of the weight-fourteen integral:
`5 p₇² = H³ (32 q₈ - 40 p₆ H - κ H⁴)`. -/
theorem alignedSecondDefect_clearing_810 {K : Type*} [CommRing K]
    {H a6 a7 b8 : K[X]} {κ : K}
    (hM : alignedSecondDefect810 H a6 a7 b8 = Polynomial.C κ * H ^ 7) :
    (5 : K[X]) * a7 ^ 2 =
      H ^ 3 * ((32 : K[X]) * b8 - (40 : K[X]) * a6 * H -
        Polynomial.C κ * H ^ 4) := by
  have hM' :
      (32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
          (5 : K[X]) * a7 ^ 2 = Polynomial.C κ * H ^ 7 := by
    simpa only [alignedSecondDefect810] using hM
  linear_combination -hM'

/-- Every root of the common core kills `p₇` on the aligned face. -/
theorem alignedSecondDefect_eval_p7_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {H a6 a7 b8 : K[X]} {κ : K}
    (hM : alignedSecondDefect810 H a6 a7 b8 = Polynomial.C κ * H ^ 7)
    {a : K} (ha : H.eval a = 0) : a7.eval a = 0 := by
  have hclear := alignedSecondDefect_clearing_810 hM
  have hc := congrArg (fun f : K[X] => f.eval a) hclear
  simp only [Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, ha] at hc
  rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul] at hc
  have h5 : (5 : K) ≠ 0 := by norm_num
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hc).resolve_left h5)

/-- The aligned face itself in solved form: `q₉ = (5/4) p₇ H`. -/
theorem aligned_q9_solved_810 {K : Type*} [Field K] [CharZero K]
    {H a7 b9 : K[X]}
    (haligned : (5 : K[X]) * a7 * H - (4 : K[X]) * b9 = 0) :
    b9 = Polynomial.C (5 / 4 : K) * a7 * H := by
  have h4ne : (4 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have h4scale : (4 : K[X]) * Polynomial.C (5 / 4 : K) = (5 : K[X]) := by
    rw [← C_ofNat_poly (n := 4), ← C_ofNat_poly (n := 5),
      ← Polynomial.C_mul]
    norm_num
  apply mul_left_cancel₀ h4ne
  calc
    (4 : K[X]) * b9 = (5 : K[X]) * a7 * H := by
      linear_combination -haligned
    _ = ((4 : K[X]) * Polynomial.C (5 / 4 : K)) * a7 * H := by
      rw [h4scale]
    _ = (4 : K[X]) * (Polynomial.C (5 / 4 : K) * a7 * H) := by
      ring

/-! ## Square chamber -/

/-- In the square chamber the cube of the core square root divides `p₇`:
the cleared row carries three visible factors of `H = h₀²`, so
`h₀⁶ ∣ p₇²` and the generic square-divisibility lemma applies to
`d = h₀³`. -/
theorem alignedSquare_dvd_p7_810 {K : Type*} [Field K] [CharZero K]
    {H h0 a6 a7 b8 : K[X]} {κ : K} (hHsq : H = h0 ^ 2)
    (hM : alignedSecondDefect810 H a6 a7 b8 = Polynomial.C κ * H ^ 7) :
    h0 ^ 3 ∣ a7 := by
  have hclear := alignedSecondDefect_clearing_810 hM
  rw [hHsq] at hclear
  have h5ne : (5 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have h5inv : (5 : K[X]) * Polynomial.C (5⁻¹ : K) = 1 := by
    rw [← C_ofNat_poly, ← Polynomial.C_mul]
    norm_num
  have hcancel :
      a7 ^ 2 =
        (h0 ^ 3) ^ 2 *
          (Polynomial.C (5⁻¹ : K) *
            ((32 : K[X]) * b8 - (40 : K[X]) * a6 * h0 ^ 2 -
              Polynomial.C κ * (h0 ^ 2) ^ 4)) := by
    apply mul_left_cancel₀ h5ne
    calc
      (5 : K[X]) * a7 ^ 2 =
          (h0 ^ 2) ^ 3 *
            ((32 : K[X]) * b8 - (40 : K[X]) * a6 * h0 ^ 2 -
              Polynomial.C κ * (h0 ^ 2) ^ 4) := hclear
      _ = ((5 : K[X]) * Polynomial.C (5⁻¹ : K)) *
            ((h0 ^ 2) ^ 3 *
              ((32 : K[X]) * b8 - (40 : K[X]) * a6 * h0 ^ 2 -
                Polynomial.C κ * (h0 ^ 2) ^ 4)) := by
          rw [h5inv, one_mul]
      _ = (5 : K[X]) *
            ((h0 ^ 3) ^ 2 *
              (Polynomial.C (5⁻¹ : K) *
                ((32 : K[X]) * b8 - (40 : K[X]) * a6 * h0 ^ 2 -
                  Polynomial.C κ * (h0 ^ 2) ^ 4))) := by ring
  exact dvd_of_sq_dvd_sq_poly ⟨_, hcancel⟩

/-- In the square chamber the octic coefficient is fully solved:
`32 q₈ = 5 g² + 40 p₆ h₀² + κ h₀⁸`. -/
theorem alignedSquare_q8_solved_810 {K : Type*} [Field K] [CharZero K]
    {H h0 g a6 a7 b8 : K[X]} {κ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 3 * g)
    (hM : alignedSecondDefect810 H a6 a7 b8 = Polynomial.C κ * H ^ 7) :
    (32 : K[X]) * b8 =
      (5 : K[X]) * g ^ 2 + (40 : K[X]) * a6 * h0 ^ 2 +
        Polynomial.C κ * h0 ^ 8 := by
  have hclear := alignedSecondDefect_clearing_810 hM
  rw [hHsq, hg] at hclear
  apply mul_left_cancel₀ (pow_ne_zero 6 hh0)
  linear_combination -hclear

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the full quadratic core divides `p₇`: a
degree-two nonsquare has simple roots, and every root of `H` kills `p₇`.
The simple-root and divisibility lemmas transfer from the `(6,8)` aligned
nonsquare architecture. -/
theorem alignedNonsquare_dvd_p7_810 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    {H a6 a7 b8 : K[X]} {κ : K} (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hM : alignedSecondDefect810 H a6 a7 b8 = Polynomial.C κ * H ^ 7) :
    H ∣ a7 := by
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  exact dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    (fun a ha => alignedSecondDefect_eval_p7_eq_zero_810 hM ha)

/-- After the first descent `p₇ = H g`, one factor of the core cancels
and the quotient still satisfies a cleared quadratic row:
`5 g² = H (32 q₈ - 40 p₆ H - κ H⁴)`. -/
theorem alignedNonsquare_g_clearing_810 {K : Type*} [Field K] [CharZero K]
    {H g a6 a7 b8 : K[X]} {κ : K}
    (hH : H ≠ 0) (hg : a7 = H * g)
    (hM : alignedSecondDefect810 H a6 a7 b8 = Polynomial.C κ * H ^ 7) :
    (5 : K[X]) * g ^ 2 =
      H * ((32 : K[X]) * b8 - (40 : K[X]) * a6 * H -
        Polynomial.C κ * H ^ 4) := by
  have hclear := alignedSecondDefect_clearing_810 hM
  rw [hg] at hclear
  apply mul_left_cancel₀ (pow_ne_zero 2 hH)
  linear_combination hclear

/-- Second descent in the nonsquare chamber: the cleared quotient row
still kills `g` at every (simple) root of the core, so `H ∣ g`. -/
theorem alignedNonsquare_dvd_g_810 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    {H g a6 a7 b8 : K[X]} {κ : K} (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hH : H ≠ 0) (hg : a7 = H * g)
    (hM : alignedSecondDefect810 H a6 a7 b8 = Polynomial.C κ * H ^ 7) :
    H ∣ g := by
  have hgclear := alignedNonsquare_g_clearing_810 hH hg hM
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  refine dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    (fun a ha => ?_)
  have hc := congrArg (fun f : K[X] => f.eval a) hgclear
  simp only [Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, ha, zero_mul] at hc
  have h5 : (5 : K) ≠ 0 := by norm_num
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hc).resolve_left h5)

/-- In the nonsquare chamber the octic coefficient gains a full core
factor: `32 q₈ = H (5 g₂² + 40 p₆ + κ H³)`, in particular `H ∣ q₈`. -/
theorem alignedNonsquare_q8_solved_810 {K : Type*} [Field K] [CharZero K]
    {H g2 a6 a7 b8 : K[X]} {κ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hM : alignedSecondDefect810 H a6 a7 b8 = Polynomial.C κ * H ^ 7) :
    (32 : K[X]) * b8 =
      H * ((5 : K[X]) * g2 ^ 2 + (40 : K[X]) * a6 +
        Polynomial.C κ * H ^ 3) := by
  have hclear := alignedSecondDefect_clearing_810 hM
  rw [hg2] at hclear
  apply mul_left_cancel₀ (pow_ne_zero 3 hH)
  linear_combination -hclear

/-! ## Source-facing aligned packets -/

/-- Source-facing weight-fourteen integral and literal normal form of a
normalized aligned scale-two `(8,10)` source: the face solves `q₉`, and
the consumed degree-`15` row solves `5 p₇²` against `q₈`. -/
theorem normalized810ScaleTwo_alignedFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ : K,
      q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H ∧
        alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
          Polynomial.C κ * H ^ 7 ∧
        (5 : K[X]) * p.coeff 7 ^ 2 =
          H ^ 3 * ((32 : K[X]) * q.coeff 8 -
            (40 : K[X]) * p.coeff 6 * H -
            Polynomial.C κ * H ^ 4) := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨κ, hM⟩ := alignedSecondDefectPowerRelation_810 hp hq hjac hH
    (by simpa only [p] using hp8) (by simpa only [q] using hq10) haligned
  exact ⟨κ, aligned_q9_solved_810 haligned, hM,
    alignedSecondDefect_clearing_810 hM⟩

/-- Exact square-chamber packet of a normalized aligned scale-two
`(8,10)` source: `p₇ = h₀³ g`, `q₉ = (5/4) g h₀⁵`, and
`32 q₈ = 5 g² + 40 p₆ h₀² + κ h₀⁸`. -/
theorem normalized810ScaleTwo_alignedFace_squareChamber_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ : K) (g : K[X]),
      p.coeff 7 = h0 ^ 3 * g ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g * h0 ^ 5 ∧
        (32 : K[X]) * q.coeff 8 =
          (5 : K[X]) * g ^ 2 + (40 : K[X]) * p.coeff 6 * h0 ^ 2 +
            Polynomial.C κ * h0 ^ 8 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨κ, hM⟩ := alignedSecondDefectPowerRelation_810 hp hq hjac hH
    (by simpa only [p] using hp8) (by simpa only [q] using hq10) haligned
  obtain ⟨g, hg⟩ := alignedSquare_dvd_p7_810 hHsq hM
  have hq9 : q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H :=
    aligned_q9_solved_810 haligned
  refine ⟨κ, g, hg, ?_, alignedSquare_q8_solved_810 hh0 hHsq hg hM⟩
  rw [hq9, hg, hHsq]
  ring

/-- Exact nonsquare-chamber packet of a normalized aligned scale-two
`(8,10)` source, after the two-step descent: `p₇ = H² g₂`,
`q₉ = (5/4) g₂ H³`, and `32 q₈ = H (5 g₂² + 40 p₆ + κ H³)`. -/
theorem normalized810ScaleTwo_alignedFace_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ : K) (g2 : K[X]),
      p.coeff 7 = H ^ 2 * g2 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
        (32 : K[X]) * q.coeff 8 =
          H * ((5 : K[X]) * g2 ^ 2 + (40 : K[X]) * p.coeff 6 +
            Polynomial.C κ * H ^ 3) := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨κ, hM⟩ := alignedSecondDefectPowerRelation_810 hp hq hjac hH
    (by simpa only [p] using hp8) (by simpa only [q] using hq10) haligned
  obtain ⟨g, hg⟩ := alignedNonsquare_dvd_p7_810 hHdegree hnsq hM
  obtain ⟨g2, hg2'⟩ := alignedNonsquare_dvd_g_810 hHdegree hnsq hH hg hM
  have hg2 : p.coeff 7 = H ^ 2 * g2 := by
    rw [hg, hg2']
    ring
  have hq9 : q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H :=
    aligned_q9_solved_810 haligned
  refine ⟨κ, g2, hg2, ?_, alignedNonsquare_q8_solved_810 hH hg2 hM⟩
  rw [hq9, hg2]
  ring

/-- Honest square/nonsquare chamber split of the aligned `(8,10)` face,
mirroring the `(6,8)` aligned architecture.  Neither chamber is excluded
and no closure is claimed. -/
theorem normalized810ScaleTwo_alignedFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (κ : K) (g : K[X]),
        p.coeff 7 = h0 ^ 3 * g ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g * h0 ^ 5 ∧
          (32 : K[X]) * q.coeff 8 =
            (5 : K[X]) * g ^ 2 + (40 : K[X]) * p.coeff 6 * h0 ^ 2 +
              Polynomial.C κ * h0 ^ 8) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (32 : K[X]) * q.coeff 8 =
            H * ((5 : K[X]) * g2 ^ 2 + (40 : K[X]) * p.coeff 6 +
              Polynomial.C κ * H ^ 3)) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    exact Or.inl ⟨h0, hh0, hHsq,
      normalized810ScaleTwo_alignedFace_squareChamber_packet
        hsource hh0 hHsq haligned⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    exact Or.inr ⟨hnsq,
      normalized810ScaleTwo_alignedFace_nonsquareChamber_packet
        hsource hnsq haligned⟩

/-- At scale two the common core has a root, and on the aligned face the
jet `p₇, q₉` vanishes there.  This is the chamber-independent root jet of
the consumed degree-`15` row. -/
theorem normalized810ScaleTwo_alignedFace_rootJet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ a : K, H.eval a = 0 ∧ (p.coeff 7).eval a = 0 ∧
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
    normalized810ScaleTwo_alignedFace_packet hsource haligned
  have hp7 :
      (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 7).eval
        a = 0 :=
    alignedSecondDefect_eval_p7_eq_zero_810 hM hroot
  refine ⟨a, hroot, hp7, ?_⟩
  simp [hq9, hroot]

#print axioms alignedSecondCoefficientJacobianRow_810
#print axioms alignedSecondDefect_weightedDerivative_identity_810
#print axioms alignedSecondDefectRow_eq_zero_810
#print axioms alignedSecondDefectPowerRelation_810
#print axioms alignedSecondDefect_clearing_810
#print axioms alignedSecondDefect_eval_p7_eq_zero_810
#print axioms aligned_q9_solved_810
#print axioms alignedSquare_dvd_p7_810
#print axioms alignedSquare_q8_solved_810
#print axioms alignedNonsquare_dvd_p7_810
#print axioms alignedNonsquare_g_clearing_810
#print axioms alignedNonsquare_dvd_g_810
#print axioms alignedNonsquare_q8_solved_810
#print axioms normalized810ScaleTwo_alignedFace_packet
#print axioms normalized810ScaleTwo_alignedFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedFace_rootJet

end Max11DegreeRoutes
