import LowScale410ScaleTwoSourceFace
import LowScale68ScaleTwoAlignedNonsquareDegreeTen

/-! # Aligned scale-two discriminator face for the normalized `(4,10)` leaf

Untracked working note.  No tracked file was edited.

`LowScale410ScaleTwoSourceFace` proves the exact first-face dichotomy for
every normalized scale-two `(4,10)` source: the discriminator
`N = 5 p₃ H³ - 2 q₉` vanishes, or `N² = κ H⁹` with `κ ≠ 0`.  The nonzero
ninth-power face carries its own iota chain; this file opens the
previously untouched aligned face `N = 0` and depends on the source face
only — no theorem of the `(4,10)` nonzero-face iota tower is used, and
the degree-`11` Keller row is derived here directly from the literal
Keller bracket.

On the aligned face the degree-`13` Jacobian coefficient is the trivial
leading weighted-Wronskian row and the degree-`12` coefficient is spent:
it is the weighted derivative of `N`, and `N = 0`.  The first genuinely
independent Keller row is therefore the degree-`11` coefficient.  The
exact combination proved here is

`H (H M' - 4 M H') + 2 · row₁₁[p₄ = H², q₁₀ = H⁵] = 3 p₃ N' - 9 p₃' N`

for the weight-four defect

`M = 8 q₈ - 20 p₂ H³ - 15 p₃² H`,

so on `N = 0` the row is the weighted derivative `H M' - 4 M H' = 0` and
`M = κ H⁴` is a polynomial first integral — one full weight lower than
the `(6,10)` aligned analogue (`M₆₁₀ = κ H⁵`).  Clearing gives the
strongest literal source normal form available on the aligned face:

* `q₉ = (5/2) p₃ H³` — the face itself, solved;
* `8 q₈ = H (15 p₃² + 20 p₂ H² + κ H³)` — the consumed row, solved;

in particular `H ∣ q₈` and every root of `H` kills `q₈` and `q₉`,
chamber-free.  This is the honest structural difference from the
`(6,10)` aligned face: there the cleared row `5 p₅² = H (…)` was
quadratic in the jet with only one visible factor of `H`, so the
square/nonsquare dichotomy gated a genuine divisibility upgrade.  Here
the quadratic core term `15 p₃² H` carries its own visible factor of
`H`, the divisibility all lands on `q₈`, and no chamber split is needed
for it.  The square/nonsquare split still carries exact content, but it
lives one derivative deeper, in the vanishing order of the solved `q₈`
at core roots, through the chamber-free root-derivative tie

`8 q₈'(a) = 15 p₃(a)² H'(a)`  at every root `a` of `H`:

* square chamber `H = h₀²`: every core root is a double root of `H`,
  so `H'(a) = 0` and `q₈` vanishes doubly (`q₈(a) = q₈'(a) = 0`;
  `h₀² ∣ q₈` is visible in the solved form
  `8 q₈ = h₀² (15 p₃² + 20 p₂ h₀⁴ + κ h₀⁶)`);
* nonsquare chamber (`H` a degree-two nonsquare, hence with simple
  roots): `H'(a) ≠ 0` and `q₈'(a) = 0 ↔ p₃(a) = 0` — second-order
  vanishing of `q₈` exactly detects the `p₃` jet at each core root.

Exactly one generic lemma of the mature `(6,8)` aligned architecture is
reused, `nonsquare_natDegree_two_derivative_ne_zero` (plus the numeral
helper `C_ofNat_poly`); it is generic in the degree pair, and no
`(6,8)`-specific source theorem is invoked.

No closure is claimed.  Both chambers remain open: the packet solves
`q₉` and `q₈`, preserves the constant `κ` of the weight-four integral
without clearing it, and constrains `p₂, p₃` only through the solved
forms.  The zero branches (`p₃ = 0` at a root, `κ = 0`) are not
excluded.  The next unused Keller row on the aligned face is the
degree-`10` Jacobian coefficient, the first row that sees `p₁` and
`q₇`.  No total-degree or twice-prime theorem is used, and no
finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient on the aligned face -/

/-- The second row below the leading weighted-Wronskian row for outer
degrees `(4,10)`: the degree-`11` Jacobian coefficient.  It is derived
here directly from the Keller bracket so that the aligned face depends
only on the source face and not on the nonzero-face iota chain. -/
theorem alignedSecondCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 8).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 9).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 11) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (11 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 11 :
      Finset (ℕ × ℕ)) =
      ({(0, 11), (1, 10), (2, 9), (3, 8), (4, 7), (5, 6), (6, 5),
        (7, 4), (8, 3), (9, 2), (10, 1), (11, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC8, hC9, hC10, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Aligned cleared defect -/

/-- Cleared weight-four defect of the aligned `(4,10)` face:
`M = 8 q₈ - 20 p₂ H³ - 15 p₃² H`.  On the aligned face it is an actual
polynomial first integral, one full weight below the `(6,10)` aligned
defect. -/
def alignedSecondDefect410 {K : Type*} [CommRing K]
    (H a2 a3 b8 : K[X]) : K[X] :=
  (8 : K[X]) * b8 - (20 : K[X]) * a2 * H ^ 3 - (15 : K[X]) * a3 ^ 2 * H

set_option maxHeartbeats 8000000 in
/-- Exact combination of the degree-`11` Jacobian expression with the
weighted derivative of `M`.  The right-hand side vanishes on `N = 0`. -/
theorem alignedSecondDefect_weightedDerivative_identity_410 {K : Type*}
    [Field K] [CharZero K] (H a2 a3 b8 b9 : K[X]) :
    H * (H * (alignedSecondDefect410 H a2 a3 b8).derivative -
          (4 : K[X]) * alignedSecondDefect410 H a2 a3 b8 * H.derivative) +
      (2 : K[X]) *
        ((H ^ 2).derivative * (b8 * (8 : K[X])) +
          a3.derivative * (b9 * (9 : K[X])) +
          a2.derivative * (H ^ 5 * (10 : K[X])) -
        ((H ^ 2 * (4 : K[X])) * b8.derivative +
          (a3 * (3 : K[X])) * b9.derivative +
          (a2 * (2 : K[X])) * (H ^ 5).derivative)) =
      (3 : K[X]) * a3 *
          ((5 : K[X]) * a3 * H ^ 3 - (2 : K[X]) * b9).derivative -
        (9 : K[X]) * a3.derivative *
          ((5 : K[X]) * a3 * H ^ 3 - (2 : K[X]) * b9) := by
  simp only [alignedSecondDefect410, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_ofNat, nsmul_eq_mul, zero_mul, zero_add]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

/-- On the aligned face `N = 0`, the degree-`11` row is the weighted
derivative `H M' - 4 M H' = 0`. -/
theorem alignedSecondDefectRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    H * (alignedSecondDefect410 H (p.coeff 2) (p.coeff 3)
          (q.coeff 8)).derivative -
      (4 : K[X]) *
        alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) *
          H.derivative = 0 := by
  have hrow := alignedSecondCoefficientJacobianRow_410 hp hq hjac
  rw [hp4, hq10] at hrow
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  rw [hC8, hC9, hC10, hC4, hC3, hC2] at hrow
  have hid := alignedSecondDefect_weightedDerivative_identity_410
    H (p.coeff 2) (p.coeff 3) (q.coeff 8) (q.coeff 9)
  rw [haligned, hrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, add_zero,
    sub_zero] at hid
  exact (mul_eq_zero.mp hid).resolve_left hH

/-- Polynomial first integral of the aligned `(4,10)` second defect. -/
theorem alignedSecondDefectPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    ∃ κ : K,
      alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
        Polynomial.C κ * H ^ 4 := by
  let M : K[X] :=
    alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8)
  have hrow : H * M.derivative - (4 : K[X]) * M * H.derivative = 0 := by
    simpa only [M] using
      alignedSecondDefectRow_eq_zero_410 hp hq hjac hH hp4 hq10 haligned
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian M (H ^ 4) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow]
    calc
      M * (Polynomial.C (4 : K) * H ^ (4 - 1) * H.derivative) -
          M.derivative * H ^ 4 =
          H ^ 3 *
            (Polynomial.C (4 : K) * M * H.derivative -
              H * M.derivative) := by ring
      _ = 0 := by
        rw [hC4]
        have hfac :
            (4 : K[X]) * M * H.derivative - H * M.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 4 hH) hW

/-- Cleared literal form of the weight-four integral:
`8 q₈ = H (15 p₃² + 20 p₂ H² + κ H³)`.  Unlike the `(6,10)` aligned
row, the full common core divides the solved coefficient chamber-free. -/
theorem alignedSecondDefect_clearing_410 {K : Type*} [CommRing K]
    {H a2 a3 b8 : K[X]} {κ : K}
    (hM : alignedSecondDefect410 H a2 a3 b8 = Polynomial.C κ * H ^ 4) :
    (8 : K[X]) * b8 =
      H * ((15 : K[X]) * a3 ^ 2 + (20 : K[X]) * a2 * H ^ 2 +
        Polynomial.C κ * H ^ 3) := by
  have hM' :
      (8 : K[X]) * b8 - (20 : K[X]) * a2 * H ^ 3 -
          (15 : K[X]) * a3 ^ 2 * H = Polynomial.C κ * H ^ 4 := by
    simpa only [alignedSecondDefect410] using hM
  linear_combination hM'

/-- The aligned face itself in solved form: `q₉ = (5/2) p₃ H³`. -/
theorem aligned_q9_solved_410 {K : Type*} [Field K] [CharZero K]
    {H a3 b9 : K[X]}
    (haligned : (5 : K[X]) * a3 * H ^ 3 - (2 : K[X]) * b9 = 0) :
    b9 = Polynomial.C (5 / 2 : K) * a3 * H ^ 3 := by
  have h2ne : (2 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have h2scale : (2 : K[X]) * Polynomial.C (5 / 2 : K) = (5 : K[X]) := by
    rw [← C_ofNat_poly (n := 2), ← C_ofNat_poly (n := 5),
      ← Polynomial.C_mul]
    norm_num
  apply mul_left_cancel₀ h2ne
  calc
    (2 : K[X]) * b9 = (5 : K[X]) * a3 * H ^ 3 := by
      linear_combination -haligned
    _ = ((2 : K[X]) * Polynomial.C (5 / 2 : K)) * a3 * H ^ 3 := by
      rw [h2scale]
    _ = (2 : K[X]) * (Polynomial.C (5 / 2 : K) * a3 * H ^ 3) := by
      ring

/-- Every root of the common core kills `q₈` on the aligned face,
chamber-free. -/
theorem alignedSecondDefect_eval_q8_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {H a2 a3 b8 : K[X]} {κ : K}
    (hM : alignedSecondDefect410 H a2 a3 b8 = Polynomial.C κ * H ^ 4)
    {a : K} (ha : H.eval a = 0) : b8.eval a = 0 := by
  have hclear := alignedSecondDefect_clearing_410 hM
  have hc := congrArg (fun f : K[X] => f.eval a) hclear
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, ha,
    zero_mul] at hc
  have h8 : (8 : K) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hc).resolve_left h8

/-- Chamber-free root-derivative tie of the consumed degree-`11` row:
at every root of the common core, `8 q₈'(a) = 15 p₃(a)² H'(a)`. -/
theorem alignedSecondDefect_rootDerivativeTie_410 {K : Type*}
    [Field K] [CharZero K] {H a2 a3 b8 : K[X]} {κ : K}
    (hM : alignedSecondDefect410 H a2 a3 b8 = Polynomial.C κ * H ^ 4)
    {a : K} (ha : H.eval a = 0) :
    (8 : K) * b8.derivative.eval a =
      (15 : K) * a3.eval a ^ 2 * H.derivative.eval a := by
  have hM' :
      (8 : K[X]) * b8 - (20 : K[X]) * a2 * H ^ 3 -
          (15 : K[X]) * a3 ^ 2 * H = Polynomial.C κ * H ^ 4 := by
    simpa only [alignedSecondDefect410] using hM
  have hd := congrArg (fun f : K[X] => f.derivative.eval a) hM'
  simp only [Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_ofNat,
    Polynomial.derivative_C, nsmul_eq_mul,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat, zero_mul, add_zero, zero_add] at hd
  rw [ha] at hd
  linear_combination hd

/-- The full common core divides `q₈` on the aligned face,
chamber-free. -/
theorem aligned_dvd_q8_410 {K : Type*} [Field K] [CharZero K]
    {H a2 a3 b8 : K[X]} {κ : K}
    (hM : alignedSecondDefect410 H a2 a3 b8 = Polynomial.C κ * H ^ 4) :
    H ∣ b8 := by
  refine ⟨Polynomial.C (8⁻¹ : K) *
    ((15 : K[X]) * a3 ^ 2 + (20 : K[X]) * a2 * H ^ 2 +
      Polynomial.C κ * H ^ 3), ?_⟩
  have hclear := alignedSecondDefect_clearing_410 hM
  have h8ne : (8 : K[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have h8scale : (8 : K[X]) * Polynomial.C (8⁻¹ : K) = 1 := by
    rw [← C_ofNat_poly, ← Polynomial.C_mul]
    norm_num
  apply mul_left_cancel₀ h8ne
  calc
    (8 : K[X]) * b8 =
        H * ((15 : K[X]) * a3 ^ 2 + (20 : K[X]) * a2 * H ^ 2 +
          Polynomial.C κ * H ^ 3) := hclear
    _ = ((8 : K[X]) * Polynomial.C (8⁻¹ : K)) *
          (H * ((15 : K[X]) * a3 ^ 2 + (20 : K[X]) * a2 * H ^ 2 +
            Polynomial.C κ * H ^ 3)) := by rw [h8scale, one_mul]
    _ = (8 : K[X]) *
          (H * (Polynomial.C (8⁻¹ : K) *
            ((15 : K[X]) * a3 ^ 2 + (20 : K[X]) * a2 * H ^ 2 +
              Polynomial.C κ * H ^ 3))) := by ring

/-! ## Square chamber -/

/-- In the square chamber the solved octic coefficient carries the
visible square of the core root:
`8 q₈ = h₀² (15 p₃² + 20 p₂ h₀⁴ + κ h₀⁶)`. -/
theorem alignedSquare_q8_solved_410 {K : Type*} [Field K] [CharZero K]
    {H h0 a2 a3 b8 : K[X]} {κ : K} (hHsq : H = h0 ^ 2)
    (hM : alignedSecondDefect410 H a2 a3 b8 = Polynomial.C κ * H ^ 4) :
    (8 : K[X]) * b8 =
      h0 ^ 2 * ((15 : K[X]) * a3 ^ 2 + (20 : K[X]) * a2 * h0 ^ 4 +
        Polynomial.C κ * h0 ^ 6) := by
  have hclear := alignedSecondDefect_clearing_410 hM
  rw [hHsq] at hclear
  linear_combination hclear

/-- In the square chamber every core root is a double root of `H`, so
the solved `q₈` vanishes doubly there: `q₈(a) = q₈'(a) = 0`. -/
theorem alignedSquare_q8_doubleRootKill_410 {K : Type*}
    [Field K] [CharZero K] {H h0 a2 a3 b8 : K[X]} {κ : K}
    (hHsq : H = h0 ^ 2)
    (hM : alignedSecondDefect410 H a2 a3 b8 = Polynomial.C κ * H ^ 4)
    {a : K} (ha : H.eval a = 0) :
    b8.eval a = 0 ∧ b8.derivative.eval a = 0 := by
  have ha' := ha
  rw [hHsq] at ha'
  have hh0a : h0.eval a = 0 := by
    have h2 : h0.eval a ^ 2 = 0 := by
      simpa only [Polynomial.eval_pow] using ha'
    exact sq_eq_zero_iff.mp h2
  have hH'a : H.derivative.eval a = 0 := by
    rw [hHsq]
    simp [Polynomial.derivative_pow, hh0a]
  have htie := alignedSecondDefect_rootDerivativeTie_410 hM ha
  rw [hH'a, mul_zero] at htie
  have h8 : (8 : K) ≠ 0 := by norm_num
  exact ⟨alignedSecondDefect_eval_q8_eq_zero_410 hM ha,
    (mul_eq_zero.mp htie).resolve_left h8⟩

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the core has simple roots, and the
root-derivative tie becomes an exact detection: `q₈` vanishes to second
order at a core root exactly when the `p₃` jet vanishes there.  The
simple-root lemma transfers from the `(6,8)` aligned nonsquare
architecture. -/
theorem alignedNonsquare_q8_derivativeDetects_p3_410 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a2 a3 b8 : k[X]} {κ : k} (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hM : alignedSecondDefect410 H a2 a3 b8 = Polynomial.C κ * H ^ 4)
    {a : k} (ha : H.eval a = 0) :
    H.derivative.eval a ≠ 0 ∧
      (b8.derivative.eval a = 0 ↔ a3.eval a = 0) := by
  have hH' : H.derivative.eval a ≠ 0 :=
    nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have htie := alignedSecondDefect_rootDerivativeTie_410 hM ha
  refine ⟨hH', ?_, ?_⟩
  · intro hb
    rw [hb, mul_zero] at htie
    have hzero := htie.symm
    have h15 : (15 : k) ≠ 0 := by norm_num
    have hcore :=
      ((mul_eq_zero.mp hzero).resolve_right hH')
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hcore).resolve_left h15)
  · intro ha3
    have h8 : (8 : k) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h8
    rw [htie, ha3, mul_zero]
    ring

/-! ## Source-facing aligned packets -/

/-- Source-facing weight-four integral and literal normal form of a
normalized aligned scale-two `(4,10)` source: the face solves `q₉`, and
the consumed degree-`11` row solves `8 q₈` with a full visible factor of
the common core. -/
theorem normalized410ScaleTwo_alignedFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ : K,
      q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * H ^ 3 ∧
        alignedSecondDefect410 H (p.coeff 2) (p.coeff 3) (q.coeff 8) =
          Polynomial.C κ * H ^ 4 ∧
        (8 : K[X]) * q.coeff 8 =
          H * ((15 : K[X]) * p.coeff 3 ^ 2 +
            (20 : K[X]) * p.coeff 2 * H ^ 2 +
            Polynomial.C κ * H ^ 3) := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨κ, hM⟩ := alignedSecondDefectPowerRelation_410 hp hq hjac hH
    (by simpa only [p] using hp4) (by simpa only [q] using hq10) haligned
  exact ⟨κ, aligned_q9_solved_410 haligned, hM,
    alignedSecondDefect_clearing_410 hM⟩

/-- Exact square-chamber packet of a normalized aligned scale-two
`(4,10)` source: `q₉ = (5/2) p₃ h₀⁶`,
`8 q₈ = h₀² (15 p₃² + 20 p₂ h₀⁴ + κ h₀⁶)`, and `q₈` vanishes doubly at
every core root. -/
theorem normalized410ScaleTwo_alignedFace_squareChamber_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ : K,
      q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * h0 ^ 6 ∧
        (8 : K[X]) * q.coeff 8 =
          h0 ^ 2 * ((15 : K[X]) * p.coeff 3 ^ 2 +
            (20 : K[X]) * p.coeff 2 * h0 ^ 4 +
            Polynomial.C κ * h0 ^ 6) ∧
        ∀ a : K, H.eval a = 0 →
          (q.coeff 8).eval a = 0 ∧
            (q.coeff 8).derivative.eval a = 0 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨κ, hM⟩ := alignedSecondDefectPowerRelation_410 hp hq hjac hH
    (by simpa only [p] using hp4) (by simpa only [q] using hq10) haligned
  have hq9 : q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * H ^ 3 :=
    aligned_q9_solved_410 haligned
  refine ⟨κ, ?_, alignedSquare_q8_solved_410 hHsq hM,
    fun a ha => alignedSquare_q8_doubleRootKill_410 hHsq hM ha⟩
  rw [hq9, hHsq]
  ring

/-- Exact nonsquare-chamber packet of a normalized aligned scale-two
`(4,10)` source: `q₉ = (5/2) p₃ H³`,
`8 q₈ = H (15 p₃² + 20 p₂ H² + κ H³)`, and at every (simple) core root
the second-order vanishing of `q₈` exactly detects the `p₃` jet. -/
theorem normalized410ScaleTwo_alignedFace_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ : K,
      q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * H ^ 3 ∧
        (8 : K[X]) * q.coeff 8 =
          H * ((15 : K[X]) * p.coeff 3 ^ 2 +
            (20 : K[X]) * p.coeff 2 * H ^ 2 +
            Polynomial.C κ * H ^ 3) ∧
        ∀ a : K, H.eval a = 0 →
          H.derivative.eval a ≠ 0 ∧
            ((q.coeff 8).derivative.eval a = 0 ↔
              (p.coeff 3).eval a = 0) := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨κ, hM⟩ := alignedSecondDefectPowerRelation_410 hp hq hjac hH
    (by simpa only [p] using hp4) (by simpa only [q] using hq10) haligned
  exact ⟨κ, aligned_q9_solved_410 haligned,
    alignedSecondDefect_clearing_410 hM,
    fun a ha =>
      alignedNonsquare_q8_derivativeDetects_p3_410 hHdegree hnsq hM ha⟩

/-- Honest square/nonsquare chamber split of the aligned `(4,10)` face.
The divisibility `H ∣ q₈` is chamber-free; the chambers differ only in
the vanishing order of the solved `q₈` at core roots.  Neither chamber
is excluded and no closure is claimed. -/
theorem normalized410ScaleTwo_alignedFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ κ : K,
        q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * h0 ^ 6 ∧
          (8 : K[X]) * q.coeff 8 =
            h0 ^ 2 * ((15 : K[X]) * p.coeff 3 ^ 2 +
              (20 : K[X]) * p.coeff 2 * h0 ^ 4 +
              Polynomial.C κ * h0 ^ 6) ∧
          ∀ a : K, H.eval a = 0 →
            (q.coeff 8).eval a = 0 ∧
              (q.coeff 8).derivative.eval a = 0) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ κ : K,
        q.coeff 9 = Polynomial.C (5 / 2 : K) * p.coeff 3 * H ^ 3 ∧
          (8 : K[X]) * q.coeff 8 =
            H * ((15 : K[X]) * p.coeff 3 ^ 2 +
              (20 : K[X]) * p.coeff 2 * H ^ 2 +
              Polynomial.C κ * H ^ 3) ∧
          ∀ a : K, H.eval a = 0 →
            H.derivative.eval a ≠ 0 ∧
              ((q.coeff 8).derivative.eval a = 0 ↔
                (p.coeff 3).eval a = 0)) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    exact Or.inl ⟨h0, hh0, hHsq,
      normalized410ScaleTwo_alignedFace_squareChamber_packet
        hsource hHsq haligned⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    exact Or.inr ⟨hnsq,
      normalized410ScaleTwo_alignedFace_nonsquareChamber_packet
        hsource hnsq haligned⟩

/-- At scale two the common core has a root, and on the aligned face the
solved coefficients `q₉, q₈` vanish there while the row leaves the exact
derivative tie `8 q₈'(a) = 15 p₃(a)² H'(a)`.  This is the
chamber-independent root jet of the consumed degree-`11` row; unlike the
`(6,10)` aligned face, the `p₃` jet itself is not forced to vanish. -/
theorem normalized410ScaleTwo_alignedFace_rootJet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ a : K, H.eval a = 0 ∧ (q.coeff 9).eval a = 0 ∧
      (q.coeff 8).eval a = 0 ∧
      (8 : K) * (q.coeff 8).derivative.eval a =
        (15 : K) * (p.coeff 3).eval a ^ 2 * H.derivative.eval a := by
  dsimp only at haligned ⊢
  have hH : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  have hdeg : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hHdegree]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdeg
  have hroot : H.eval a = 0 := ha
  obtain ⟨κ, hq9, hM, _hclear⟩ :=
    normalized410ScaleTwo_alignedFace_packet hsource haligned
  refine ⟨a, hroot, ?_,
    alignedSecondDefect_eval_q8_eq_zero_410 hM hroot,
    alignedSecondDefect_rootDerivativeTie_410 hM hroot⟩
  simp [hq9, hroot]

#print axioms alignedSecondCoefficientJacobianRow_410
#print axioms alignedSecondDefect_weightedDerivative_identity_410
#print axioms alignedSecondDefectRow_eq_zero_410
#print axioms alignedSecondDefectPowerRelation_410
#print axioms alignedSecondDefect_clearing_410
#print axioms aligned_q9_solved_410
#print axioms alignedSecondDefect_eval_q8_eq_zero_410
#print axioms alignedSecondDefect_rootDerivativeTie_410
#print axioms aligned_dvd_q8_410
#print axioms alignedSquare_q8_solved_410
#print axioms alignedSquare_q8_doubleRootKill_410
#print axioms alignedNonsquare_q8_derivativeDetects_p3_410
#print axioms normalized410ScaleTwo_alignedFace_packet
#print axioms normalized410ScaleTwo_alignedFace_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedFace_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedFace_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedFace_rootJet

end Max11DegreeRoutes
