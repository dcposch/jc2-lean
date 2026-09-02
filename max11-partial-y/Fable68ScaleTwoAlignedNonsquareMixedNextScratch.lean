import Fable68ScaleTwoAlignedNonsquareMixedThirdRowScratch

/-! # Fourth row of the preserved transverse two-root allocation

After the third-row collapse (`k₁(a) = 0` at the `r`-root), the first
genuinely unused row of the mixed branch is the transported lower-zero
one-form itself, freed of its single automatic core factor.  With
`b₁ = H b₂`, `d₁ = H d₂` one core power splits off the cleared row
term-by-term; the quotient row is again exactly zero, and its first two
Taylor coefficients at each core root are the genuinely new faces.

At any core root `z` the quotient's first coefficient is
`(1/2) Φ₁ (H')² (A₀ b₂ - 5 d₂)`, and `A₀(z) = -(1/12) r(z)²` from the
descended coordinate `3t - r² = HX`.  At the `r`-root both `A₀` and `b₂`
vanish, so `d₂(a) = 0` outright, the retained `I₄` face then forces
`b₂'(a) = 0`, and the quotient's second coefficient forces `d₂'(a) = 0`;
the third-row lower-zero kill upgrades the scalar split to the definite
`k₁(a) = 0` exactly as before.  At the complementary `Φ₁`-root the second
coefficient factors as
`(A₀ b₂ - 3 d₂)(Φ₁' + 2 A₀ w₂ H')`, i.e. in coordinate form
`(r² b₂ + 36 d₂)(6 Φ₁' - r² w₂ H') = 0`, and the terminal derivative
numerator is pinned by `15552 Ė(b) = H'(b) r(b)⁶`, a unit.

The surviving trichotomy at the `Φ₁`-root globalizes exactly as in the
third row and then refines: the `k₁(b) = 0` face is preserved verbatim;
the `b₂(b) = 0` face gains the cross-root transfer `H ∣ d₂` and its two
reduced rows; in the transverse residual the new face kills `w₂(b) = 0`
(as `A₀(b) ≠ 0` there), the retained terminal face then yields
`d₂'(b) = 0`, the double transfer gives `d₂ = H² e₂` globally, both rows
descend one and two core powers, and the reduced terminal row's first
coefficient at `b` ties `b₂(b) w₂'(b) Ė(b) = H'(b) e₂(b) k₁(b)`.  No
honest contradiction is available at this depth: the residual is
returned.  The `H ∣ r` and `H ∣ Φ₁` branches pass through untouched. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section MixedFourthRowAlgebra68

variable {k : Type*} [Field k] [CharZero k]

def mixedLowerZeroSOne68 (H A b2 d2 : k[X]) (alpha : k) : k[X] :=
  C (4 / 3 : k) * d2 + C (4 / 9 : k) * A * b2 + C alpha * H * b2

def mixedLowerZeroUOne68
    (H A b2 C0 d2 : k[X]) (alpha gamma : k) : k[X] :=
  C (4 / 9 : k) * b2 * C0 + C (4 / 9 : k) * A * d2 -
    C (4 / 27 : k) * A ^ 2 * b2 + C alpha * H * d2 +
    C (2 / 3 * gamma : k) * H ^ 2 * b2

def mixedLowerZeroDDOne68 (H d2 : k[X]) : k[X] :=
  (C 2 - C 3) * H.derivative * d2 + C 2 * H * d2.derivative

def mixedLowerZeroUDOne68 (H U : k[X]) : k[X] :=
  (C 2 - C 5) * H.derivative * U + C 2 * H * U.derivative

/-- The quotient of the transported lower-zero row after removing the
single automatic core factor carried by `b₁ = H b₂`, `d₁ = H d₂`. -/
def mixedLowerZeroOne68
    (H A b2 C0 d2 E : k[X]) (alpha gamma epsilon eta : k) : k[X] :=
  let S1 := mixedLowerZeroSOne68 H A b2 d2 alpha
  let T0 := terminalLowerOneTNumerator68 H A (H * b2) C0 E
    alpha gamma epsilon
  let U1 := mixedLowerZeroUOne68 H A b2 C0 d2 alpha gamma
  let V0 := terminalVNumerator68 H A (H * b2) C0 (H * d2) E
    alpha gamma epsilon eta
  U1 * terminalLowerZeroCDot68 H C0 +
    T0 * mixedLowerZeroDDOne68 H d2 +
    C 3 * S1 * terminalEDerivativeNumerator68 H E -
    C 3 * b2 * terminalVDerivativeNumerator68 H V0 -
    C0 * mixedLowerZeroUDOne68 H U1 -
    d2 * terminalLowerZeroTDot68 H T0

theorem mixedLowerZero_factor_one_68
    (H A b C0 d E b2 d2 : k[X]) (alpha gamma epsilon eta : k)
    (hb : b = H * b2) (hd : d = H * d2) :
    terminalLowerZeroCleared68 H A b C0 d E alpha gamma epsilon eta =
      H * mixedLowerZeroOne68 H A b2 C0 d2 E alpha gamma epsilon eta := by
  rw [hb, hd]
  have hS : terminalLowerZeroSNumerator68 H A (H * b2) (H * d2) alpha =
      H * mixedLowerZeroSOne68 H A b2 d2 alpha := by
    simp only [terminalLowerZeroSNumerator68, mixedLowerZeroSOne68]
    ring
  have hU : terminalLowerOneUNumerator68 H A (H * b2) C0 (H * d2)
      alpha gamma = H * mixedLowerZeroUOne68 H A b2 C0 d2 alpha gamma := by
    simp only [terminalLowerOneUNumerator68, mixedLowerZeroUOne68]
    ring
  have hDD : terminalLowerOneDTwoDot68 H (H * d2) =
      H * mixedLowerZeroDDOne68 H d2 := by
    simp only [terminalLowerOneDTwoDot68, mixedLowerZeroDDOne68,
      derivative_mul]
    ring
  have hUD : terminalLowerOneUTwoDot68 H
      (terminalLowerOneUNumerator68 H A (H * b2) C0 (H * d2)
        alpha gamma) = H * mixedLowerZeroUDOne68 H
          (mixedLowerZeroUOne68 H A b2 C0 d2 alpha gamma) := by
    rw [hU]
    simp only [terminalLowerOneUTwoDot68, mixedLowerZeroUDOne68,
      derivative_mul]
    ring
  simp only [terminalLowerZeroCleared68, mixedLowerZeroOne68]
  rw [hS, hDD, hUD, hU]
  ring

/-- First coefficient of the once-reduced lower-zero row at a core root:
`(1/2) Φ₁ (H')² (A b₂ - 5 d₂)`. -/
theorem mixedLowerZeroOne_derivative_factor_68
    (H A b2 d2 phi w : k[X]) (alpha gamma epsilon eta : k) (z : k)
    (hz : H.eval z = 0) :
    let C0 := C (1 / 3 : k) * A ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
    let E := C (1 / 27 : k) * A ^ 3 + C (3 / 8 : k) * H * phi +
      H ^ 2 * (C (3 / 2 : k) * A * w - C (1 / 2 * gamma : k) * A) -
      C (3 / 4 * epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * (H * b2)) ^ 2
    (mixedLowerZeroOne68 H A b2 C0 d2 E
      alpha gamma epsilon eta).derivative.eval z =
        (1 / 2 : k) * phi.eval z * H.derivative.eval z ^ 2 *
          (A.eval z * b2.eval z - 5 * d2.eval z) := by
  dsimp only
  simp only [mixedLowerZeroOne68, mixedLowerZeroSOne68,
    mixedLowerZeroUOne68, mixedLowerZeroDDOne68, mixedLowerZeroUDOne68,
    terminalLowerZeroCDot68, terminalLowerZeroTDot68,
    terminalLowerOneTNumerator68, terminalEDerivativeNumerator68,
    terminalVDerivativeNumerator68, terminalVNumerator68,
    derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly,
    eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat,
    eval_zero, hz, zero_mul, mul_zero, zero_add, add_zero, zero_pow]
  ring

set_option maxHeartbeats 16000000 in
/-- Second coefficient of the once-reduced lower-zero row at a core root
carrying simultaneous zeros of `b₂` and `d₂`:
`Φ₁ (H')² (A b₂' - 3 d₂')`. -/
theorem mixedLowerZeroOne_secondDerivative_rRoot_68
    (H A b2 d2 phi w : k[X]) (alpha gamma epsilon eta : k) (z : k)
    (hz : H.eval z = 0) (hb2 : b2.eval z = 0) (hd2 : d2.eval z = 0) :
    let C0 := C (1 / 3 : k) * A ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
    let E := C (1 / 27 : k) * A ^ 3 + C (3 / 8 : k) * H * phi +
      H ^ 2 * (C (3 / 2 : k) * A * w - C (1 / 2 * gamma : k) * A) -
      C (3 / 4 * epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * (H * b2)) ^ 2
    (mixedLowerZeroOne68 H A b2 C0 d2 E
      alpha gamma epsilon eta).derivative.derivative.eval z =
        phi.eval z * H.derivative.eval z ^ 2 *
          (A.eval z * b2.derivative.eval z -
            3 * d2.derivative.eval z) := by
  dsimp only
  simp only [mixedLowerZeroOne68, mixedLowerZeroSOne68,
    mixedLowerZeroUOne68, mixedLowerZeroDDOne68, mixedLowerZeroUDOne68,
    terminalLowerZeroCDot68, terminalLowerZeroTDot68,
    terminalLowerOneTNumerator68, terminalEDerivativeNumerator68,
    terminalVDerivativeNumerator68, terminalVNumerator68,
    derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly,
    eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat,
    eval_zero, hz, hb2, hd2, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow]
  ring

set_option maxHeartbeats 16000000 in
/-- Second coefficient of the once-reduced lower-zero row at a core root
of `Φ₁`; it factors as `(H')² (A b₂ - 3 d₂)(Φ₁' + 2 A w₂ H')`. -/
theorem mixedLowerZeroOne_secondDerivative_phiRoot_68
    (H A b2 d2 phi w : k[X]) (alpha gamma epsilon eta : k) (z : k)
    (hz : H.eval z = 0) (hphi : phi.eval z = 0) :
    let C0 := C (1 / 3 : k) * A ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w - C (3 / 2 * gamma : k))
    let E := C (1 / 27 : k) * A ^ 3 + C (3 / 8 : k) * H * phi +
      H ^ 2 * (C (3 / 2 : k) * A * w - C (1 / 2 * gamma : k) * A) -
      C (3 / 4 * epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * (H * b2)) ^ 2
    (mixedLowerZeroOne68 H A b2 C0 d2 E
      alpha gamma epsilon eta).derivative.derivative.eval z =
        H.derivative.eval z ^ 2 *
          ((A.eval z * b2.eval z - 3 * d2.eval z) *
            (phi.derivative.eval z +
              2 * A.eval z * w.eval z * H.derivative.eval z)) := by
  dsimp only
  simp only [mixedLowerZeroOne68, mixedLowerZeroSOne68,
    mixedLowerZeroUOne68, mixedLowerZeroDDOne68, mixedLowerZeroUDOne68,
    terminalLowerZeroCDot68, terminalLowerZeroTDot68,
    terminalLowerOneTNumerator68, terminalEDerivativeNumerator68,
    terminalVDerivativeNumerator68, terminalVNumerator68,
    derivative_add, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, derivative_C, derivative_ofNat, C_ofNat_poly,
    eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_ofNat,
    eval_zero, hz, hphi, zero_mul, mul_zero, zero_add, add_zero,
    zero_pow]
  ring

end MixedFourthRowAlgebra68

section MixedFourthRowSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Fourth-row refinement of the preserved transverse two-root allocation.
The once-reduced lower-zero row is exactly zero; its first two Taylor
coefficients at the `r`-root force `d₂(a) = 0`, `b₂'(a) = 0`, `d₂'(a) = 0`
outright (with `k₁(a) = 0` preserved), while at the `Φ₁`-root they produce
the new face `(r² b₂ + 36 d₂)(6 Φ₁' - r² w₂ H') = 0` together with the
unit pin `15552 Ė(b) = H'(b) r(b)⁶`.  The trichotomy globalizes exactly:
the `k₁` face is preserved verbatim, the `b₂` face gains `H ∣ d₂` with
both reduced rows, and the transverse residual sharpens to `w₂(b) = 0`,
`d₂'(b) = 0`, `d₂ = H² e₂` with the twice-descended rows and the exact
first coefficient `b₂(b) w₂'(b) Ė(b) = H'(b) e₂(b) k₁(b)`. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneMixedFourthRowPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r t X Yd phi1 k1 b2 d2 w2 : k[X]),
      p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      b2 * phi1 + (6 : k[X]) * H * w2 * d2 = 0 ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4) ∧
      (H ∣ r ∨ H ∣ phi1 ∨
        (let A0 := cubicANumerator68 t r
         let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
         let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
           (p.coeff 3) t r
         let eDot := terminalEDerivativeNumerator68 H E0
         ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
           r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
           r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
           b2.eval a = 0 ∧ k1.eval a = 0 ∧ d2.eval a = 0 ∧
           b2.derivative.eval a = 0 ∧ d2.derivative.eval a = 0 ∧
           b2.eval b * phi1.derivative.eval b +
             6 * H.derivative.eval b * w2.eval b * d2.eval b = 0 ∧
           H.derivative.eval b * b2.eval b * w2.eval b * eDot.eval b -
             (d2.derivative.eval b * k1.eval b +
               d2.eval b * k1.derivative.eval b) = 0 ∧
           (r.eval b ^ 2 * b2.eval b + 36 * d2.eval b) *
             (6 * phi1.derivative.eval b -
               r.eval b ^ 2 * w2.eval b * H.derivative.eval b) = 0 ∧
           15552 * eDot.eval b = H.derivative.eval b * r.eval b ^ 6 ∧
           ((k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
               b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) ∨
            (d2.eval b = 0 ∧ b2.eval b = 0 ∧ ∃ b3 e1 : k[X],
               b2 = H * b3 ∧ d2 = H * e1 ∧
               b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0 ∧
               e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3) ∨
            (d2.eval b = 0 ∧ k1.eval b ≠ 0 ∧ b2.eval b ≠ 0 ∧
               phi1.derivative.eval b = 0 ∧ w2.eval b = 0 ∧
               d2.derivative.eval b = 0 ∧
               ∃ e2 : k[X], d2 = H ^ 2 * e2 ∧
                 b2 * phi1 + (6 : k[X]) * H ^ 3 * w2 * e2 = 0 ∧
                 b2 * w2 * eDot - H * e2 * k1 = C j * H ^ 3 ∧
                 b2.eval b * w2.derivative.eval b * eDot.eval b =
                   H.derivative.eval b * e2.eval b * k1.eval b)))) := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
      hg, hgr, ht, hX, hY, hb1n, hd1n, hw1n, hphin, hb1b2, hd1d2, hw1w2,
      hI4, hrow, hroots, _hpure⟩ :=
    S.terminalAfterLowerOneDoubleZeroPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac hj
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hrow' : H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4 := by
    simpa only [A0, C0, E0, eDot] using hrow
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  -- Exact core shapes of the retained cubic coordinates.
  have hW1 : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
    dsimp only [A0, C0, terminalScaledW68]
    rw [← hw1n]
    simp only [cubicWNumerator68]
  have hW2 : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w2 := by
    rw [hW1, hw1w2]
    ring
  have hCshape : C0 = C (1 / 3 : k) * A0 ^ 2 +
      H ^ 2 * (C (9 / 4 : k) * w2 - C (3 / 2 * S.gamma : k)) := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hm := congrArg (algebraMap k[X] (RatFunc k)) hW2
    dsimp only [terminalScaledW68] at hm
    simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_one] at hm ⊢
    linear_combination (9 / 4 : RatFunc k) * hm
  have hPhi : terminalScaledPhi68 H A0 b1 C0 E0 S.gamma S.epsilon =
      H * phi1 := by
    dsimp only [A0, C0, E0, terminalScaledPhi68]
    rw [← hphin, ← hb1n]
    simp only [cubicPhiNumerator68]
  have hEshape : E0 = C (1 / 27 : k) * A0 ^ 3 +
      C (3 / 8 : k) * H * phi1 +
      H ^ 2 * (C (3 / 2 : k) * A0 * w2 -
        C (1 / 2 * S.gamma : k) * A0) -
      C (3 / 4 * S.epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * b1) ^ 2 := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    have hPm := congrArg (algebraMap k[X] (RatFunc k)) hPhi
    have hCm := congrArg (algebraMap k[X] (RatFunc k)) hCshape
    dsimp only [terminalScaledPhi68] at hPm
    simp only [map_add, map_sub, map_neg, map_mul, map_pow,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one] at hPm hCm ⊢
    linear_combination (3 / 8 : RatFunc k) * hPm +
      (2 / 3 * algebraMap k[X] (RatFunc k) A0) * hCm
  have htransport := S.terminalLowerZeroClearedTransport_source (H := H)
    hp hp6 hg hgr ht hX hY
  obtain ⟨hAred, hBred, hCred, hDred, hEred⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
  have hbred : terminalGReducedB68 r X Yd = b1 := by
    apply mul_left_cancel₀ hH
    rw [← hBred, ← hb1n]
  have hdred : terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2) =
      d1 := by
    apply mul_left_cancel₀ hH
    rw [← hDred, ← hd1n]
  have hlower : terminalLowerZeroCleared68 H A0 b1 C0 d1 E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    simpa only [A0, C0, E0, ← hAred, hbred, ← hCred, hdred, ← hEred]
      using htransport
  -- The once-reduced lower-zero row is exactly zero.
  have hEshape2 : E0 = C (1 / 27 : k) * A0 ^ 3 +
      C (3 / 8 : k) * H * phi1 +
      H ^ 2 * (C (3 / 2 : k) * A0 * w2 -
        C (1 / 2 * S.gamma : k) * A0) -
      C (3 / 4 * S.epsilon : k) * H ^ 3 +
      C (1 / 9 : k) * (H * (H * b2)) ^ 2 := by
    rw [← hb1b2]
    exact hEshape
  have hfactorOne := mixedLowerZero_factor_one_68 H A0 b1 C0 d1 E0 b2 d2
    S.alpha S.gamma S.epsilon S.eta hb1b2 hd1d2
  have hRone : mixedLowerZeroOne68 H A0 b2 C0 d2 E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    have hz : H * mixedLowerZeroOne68 H A0 b2 C0 d2 E0
        S.alpha S.gamma S.epsilon S.eta = 0 := by
      rw [← hfactorOne]
      exact hlower
    exact (mul_eq_zero.mp hz).resolve_left hH
  -- Every core root pins the cubic apex to the descended coordinate.
  have hA0root : ∀ z : k, H.eval z = 0 →
      A0.eval z = -(1 / 12 : k) * r.eval z ^ 2 := by
    intro z hz
    have hXe := congrArg (fun P : k[X] => P.eval z) hX
    simp only [eval_mul, eval_sub, eval_pow, eval_ofNat, hz, zero_mul]
      at hXe
    dsimp only [A0, cubicANumerator68]
    simp only [eval_sub, eval_mul, eval_pow, eval_C]
    linear_combination (1 / 3 : k) * hXe
  -- The lower-zero row deletes any core root carrying units `Φ₁`, `k₁`
  -- and simultaneous double zeros of `b₂`, `d₂`.
  have hlocalKill : ∀ x : k, H.eval x = 0 → phi1.eval x ≠ 0 →
      k1.eval x ≠ 0 → b2.eval x = 0 → b2.derivative.eval x = 0 →
      d2.eval x = 0 → d2.derivative.eval x = 0 → False := by
    intro x hx hpx hkx hbx hbdx hdx hddx
    have hboot := terminalAfterLowerOne_mixedRoot_bootstrap_68
      H b2 phi1 w2 d2 eDot k1 j x hx hpx hkx hbx hbdx hdx hddx hI4 hrow'
    let L : k[X] := Polynomial.X - C x
    have hLH : L ∣ H := by
      dsimp only [L]
      rw [dvd_iff_isRoot]
      exact hx
    obtain ⟨M, hHM⟩ := hLH
    have hMval : M.eval x = H.derivative.eval x := by
      have hder := congrArg (fun P : k[X] => P.derivative.eval x) hHM
      dsimp only [L] at hder
      simp only [derivative_mul, derivative_sub, derivative_X,
        derivative_C, eval_add, eval_mul, eval_sub, eval_one, eval_X,
        eval_C, sub_self, zero_mul, one_mul, add_zero] at hder
      simpa using hder.symm
    have hMne : M.eval x ≠ 0 := by
      rw [hMval]
      exact hsimple x hx
    obtain ⟨B, hB⟩ := hboot.1
    obtain ⟨D, hD⟩ := hboot.2
    have hL : L ≠ 0 := by
      dsimp only [L]
      exact X_sub_C_ne_zero x
    have hrowQ : L ^ 2 * M * B * w2 * eDot - D * k1 = C j * M ^ 4 := by
      apply mul_left_cancel₀ (pow_ne_zero 4 hL)
      rw [hHM, hB, hD] at hrow'
      linear_combination hrow'
    have hDprod : D.eval x * k1.eval x = -j * (M.eval x) ^ 4 := by
      have he := congrArg (fun P : k[X] => P.eval x) hrowQ
      dsimp only [L] at he
      simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C,
        eval_X, sub_self, zero_pow, zero_mul] at he
      linear_combination -he
    have hDne : D.eval x ≠ 0 := by
      intro hDz
      rw [hDz, zero_mul] at hDprod
      exact (mul_ne_zero (neg_ne_zero.mpr hj) (pow_ne_zero 4 hMne))
        hDprod.symm
    have hbLocal : b1 = L ^ 6 * (M * B) := by
      rw [hb1b2, hB, hHM]
      ring
    have hdLocal : d1 = L ^ 5 * (M * D) := by
      rw [hd1d2, hD, hHM]
      ring
    have hClocal : C0 = C (1 / 3 : k) * A0 ^ 2 +
        (L * M) ^ 2 *
          (C (9 / 4 : k) * w2 - C (3 / 2 * S.gamma : k)) := by
      rw [← hHM]
      exact hCshape
    have hElocal : E0 = C (1 / 27 : k) * A0 ^ 3 +
        C (3 / 8 : k) * (L * M) * phi1 +
        (L * M) ^ 2 * (C (3 / 2 : k) * A0 * w2 -
          C (1 / 2 * S.gamma : k) * A0) -
        C (3 / 4 * S.epsilon : k) * (L * M) ^ 3 +
        C (1 / 9 : k) * ((L * M) * (L ^ 6 * (M * B))) ^ 2 := by
      rw [← hHM, ← hbLocal]
      exact hEshape
    have hlowerLocal : terminalLowerZeroCleared68 (L * M)
        A0 b1 C0 d1 E0 S.alpha S.gamma S.epsilon S.eta = 0 := by
      rw [← hHM]
      exact hlower
    exact terminalLowerZero_mixedLocal_impossible_68
      M A0 b1 C0 d1 E0 (M * B) (M * D) phi1 w2
      S.alpha S.gamma S.epsilon S.eta x hMne
      (by simp only [eval_mul]; exact mul_ne_zero hMne hDne) hpx
      (by simpa only [L] using hbLocal)
      (by simpa only [L] using hdLocal)
      (by simpa only [L] using hClocal)
      (by simpa only [L] using hElocal)
      (by simpa only [L] using hlowerLocal)
  -- Every core root lies on the coordinate divisor.
  have hrootCoordinate : ∀ x : k, H.eval x = 0 →
      (r * phi1).eval x = 0 := by
    intro x hx
    by_contra hrphi
    have hrne : r.eval x ≠ 0 := by
      intro hr0
      exact hrphi (by simp [eval_mul, hr0])
    have hpne : phi1.eval x ≠ 0 := by
      intro hp0
      exact hrphi (by simp [eval_mul, hp0])
    rcases hroots x hx with hr0 | hp0 | hdz
    · exact hrne hr0
    · exact hpne hp0
    · exact hlocalKill x hx hpne hdz.2.2.2.2 hdz.1 hdz.2.1 hdz.2.2.1
        hdz.2.2.2.1
  have hdvd : H ∣ r * phi1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      hrootCoordinate
  have hsplitTri := simpleQuadratic_dvd_product_coordinate_split_68
    H r phi1 hdeg hsimple hdvd
  rcases hsplitTri with hcase | hcase | hmix
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inl hcase⟩
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inr (Or.inl hcase)⟩
  · obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb⟩ := hmix
    have hrf := terminalAfterLowerOne_rRoot_faces_68
      H b2 phi1 w2 d2 eDot k1 j a ha hpa hI4 hrow'
    have hpf := terminalAfterLowerOne_phiRoot_faces_68
      H b2 phi1 w2 d2 eDot k1 j b hb hpb (hsimple b hb) hI4 hrow'
    have hb2a : b2.eval a = 0 := hrf.1
    -- Fourth-row order-0 face at the `r`-root: `d₂(a) = 0` outright.
    have hRoneDa : (mixedLowerZeroOne68 H A0 b2 C0 d2 E0
        S.alpha S.gamma S.epsilon S.eta).derivative.eval a = 0 := by
      rw [hRone, derivative_zero, eval_zero]
    rw [hCshape, hEshape2, mixedLowerZeroOne_derivative_factor_68
      H A0 b2 d2 phi1 w2 S.alpha S.gamma S.epsilon S.eta a ha] at hRoneDa
    have hd2a : d2.eval a = 0 := by
      have h5 : phi1.eval a * H.derivative.eval a ^ 2 * d2.eval a = 0 := by
        linear_combination (-2 / 5 : k) * hRoneDa +
          (1 / 5 : k) * phi1.eval a * H.derivative.eval a ^ 2 *
            A0.eval a * hb2a
      rcases mul_eq_zero.mp h5 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hpa
        · exact absurd h' (pow_ne_zero 2 (hsimple a ha))
      · exact h
    have hb2da : b2.derivative.eval a = 0 := by
      have hz : b2.derivative.eval a * phi1.eval a = 0 := by
        linear_combination hrf.2.1 -
          6 * H.derivative.eval a * w2.eval a * hd2a
      exact (mul_eq_zero.mp hz).resolve_right hpa
    -- Fourth-row order-1 face at the `r`-root: `d₂'(a) = 0`.
    have hRoneDDa : (mixedLowerZeroOne68 H A0 b2 C0 d2 E0
        S.alpha S.gamma S.epsilon
          S.eta).derivative.derivative.eval a = 0 := by
      rw [hRone, derivative_zero, derivative_zero, eval_zero]
    rw [hCshape, hEshape2, mixedLowerZeroOne_secondDerivative_rRoot_68
      H A0 b2 d2 phi1 w2 S.alpha S.gamma S.epsilon S.eta a ha hb2a hd2a]
      at hRoneDDa
    have hd2da : d2.derivative.eval a = 0 := by
      have h3 : phi1.eval a * H.derivative.eval a ^ 2 *
          d2.derivative.eval a = 0 := by
        linear_combination (-1 / 3 : k) * hRoneDDa +
          (1 / 3 : k) * phi1.eval a * H.derivative.eval a ^ 2 *
            A0.eval a * hb2da
      rcases mul_eq_zero.mp h3 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hpa
        · exact absurd h' (pow_ne_zero 2 (hsimple a ha))
      · exact h
    -- The third-row lower-zero kill still collapses the scalar split.
    have hk1a : k1.eval a = 0 := by
      by_contra hk1ne
      exact hlocalKill a ha hpa hk1ne hb2a hb2da hd2a hd2da
    -- Fourth-row order-1 face at the `Φ₁`-root, in coordinate form.
    have hRoneDDb : (mixedLowerZeroOne68 H A0 b2 C0 d2 E0
        S.alpha S.gamma S.epsilon
          S.eta).derivative.derivative.eval b = 0 := by
      rw [hRone, derivative_zero, derivative_zero, eval_zero]
    rw [hCshape, hEshape2, mixedLowerZeroOne_secondDerivative_phiRoot_68
      H A0 b2 d2 phi1 w2 S.alpha S.gamma S.epsilon S.eta b hb hpb]
      at hRoneDDb
    have hXY := (mul_eq_zero.mp hRoneDDb).resolve_left
      (pow_ne_zero 2 (hsimple b hb))
    rw [hA0root b hb] at hXY
    have hfaceB : (r.eval b ^ 2 * b2.eval b + 36 * d2.eval b) *
        (6 * phi1.derivative.eval b -
          r.eval b ^ 2 * w2.eval b * H.derivative.eval b) = 0 := by
      linear_combination (-72 : k) * hXY
    -- The terminal derivative numerator is a unit multiple of `r⁶` at `b`.
    have hE0b : E0.eval b = (1 / 27 : k) * A0.eval b ^ 3 := by
      have hEe := congrArg (fun P : k[X] => P.eval b) hEshape2
      simpa only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, hb,
        zero_mul, mul_zero, zero_pow, zero_add, add_zero, sub_zero,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using hEe
    have heDotPin : 15552 * eDot.eval b =
        H.derivative.eval b * r.eval b ^ 6 := by
      have he1 : eDot.eval b =
          -(3 : k) * (H.derivative.eval b * E0.eval b) := by
        dsimp only [eDot, terminalEDerivativeNumerator68]
        simp only [eval_sub, eval_mul, eval_C, hb, zero_mul]
        ring
      rw [he1, hE0b, hA0root b hb]
      ring
    -- Exact globalization of the surviving split at the `Φ₁`-root.
    have htrichB :
        (k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
            b2 * w2 * eDot - d2 * k2 = C j * H ^ 3) ∨
        (d2.eval b = 0 ∧ b2.eval b = 0 ∧ ∃ b3 e1 : k[X],
            b2 = H * b3 ∧ d2 = H * e1 ∧
            b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0 ∧
            e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3) ∨
        (d2.eval b = 0 ∧ k1.eval b ≠ 0 ∧ b2.eval b ≠ 0 ∧
            phi1.derivative.eval b = 0 ∧ w2.eval b = 0 ∧
            d2.derivative.eval b = 0 ∧
            ∃ e2 : k[X], d2 = H ^ 2 * e2 ∧
              b2 * phi1 + (6 : k[X]) * H ^ 3 * w2 * e2 = 0 ∧
              b2 * w2 * eDot - H * e2 * k1 = C j * H ^ 3 ∧
              b2.eval b * w2.derivative.eval b * eDot.eval b =
                H.derivative.eval b * e2.eval b * k1.eval b) := by
      by_cases hk1b : k1.eval b = 0
      · left
        refine ⟨hk1b, ?_⟩
        obtain ⟨k2, hk2⟩ := dvd_of_two_simple_root_evals_68 H k1 hdeg
          hsimple a b hab ha hb hk1a hk1b
        refine ⟨k2, hk2, ?_⟩
        apply mul_left_cancel₀ hH
        have hrowc := hrow'
        rw [hk2] at hrowc
        linear_combination hrowc
      · have hd2b : d2.eval b = 0 := hpf.2.2.resolve_right hk1b
        by_cases hb2b : b2.eval b = 0
        · right
          left
          refine ⟨hd2b, hb2b, ?_⟩
          obtain ⟨b3, hb3⟩ := dvd_of_two_simple_root_evals_68 H b2 hdeg
            hsimple a b hab ha hb hb2a hb2b
          obtain ⟨e1, he1d⟩ := dvd_of_two_simple_root_evals_68 H d2 hdeg
            hsimple a b hab ha hb hd2a hd2b
          refine ⟨b3, e1, hb3, he1d, ?_, ?_⟩
          · apply mul_left_cancel₀ hH
            have hI4c := hI4
            rw [hb3, he1d] at hI4c
            linear_combination hI4c
          · apply mul_left_cancel₀ hH
            have hrowc := hrow'
            rw [hb3, he1d] at hrowc
            linear_combination -hrowc
        · right
          right
          have hphi1db : phi1.derivative.eval b = 0 := by
            have hz : b2.eval b * phi1.derivative.eval b = 0 := by
              linear_combination hpf.1 -
                6 * H.derivative.eval b * w2.eval b * hd2b
            exact (mul_eq_zero.mp hz).resolve_left hb2b
          -- The fourth-row face kills `w₂(b)`.
          have hw2b : w2.eval b = 0 := by
            have h6 : r.eval b ^ 4 * b2.eval b * H.derivative.eval b *
                w2.eval b = 0 := by
              linear_combination (-1 : k) * hfaceB +
                (6 * r.eval b ^ 2 * b2.eval b + 216 * d2.eval b) *
                  hphi1db +
                (-36 : k) * r.eval b ^ 2 * w2.eval b *
                  H.derivative.eval b * hd2b
            rcases mul_eq_zero.mp h6 with h | h
            · rcases mul_eq_zero.mp h with h' | h'
              · rcases mul_eq_zero.mp h' with h'' | h''
                · exact absurd h'' (pow_ne_zero 4 hrb)
                · exact absurd h'' hb2b
              · exact absurd h' (hsimple b hb)
            · exact h
          have hd2db : d2.derivative.eval b = 0 := by
            have hz : d2.derivative.eval b * k1.eval b = 0 := by
              linear_combination (-1 : k) * hpf.2.1 +
                H.derivative.eval b * b2.eval b * eDot.eval b * hw2b +
                (-1 : k) * k1.derivative.eval b * hd2b
            exact (mul_eq_zero.mp hz).resolve_right hk1b
          -- Cross-root double transfer: `d₂ = H² e₂` globally.
          obtain ⟨e, he⟩ := dvd_of_two_simple_root_evals_68 H d2 hdeg
            hsimple a b hab ha hb hd2a hd2b
          have heRoot : ∀ z : k, H.eval z = 0 →
              d2.derivative.eval z =
                H.derivative.eval z * e.eval z := by
            intro z hz
            have hder := congrArg (fun P : k[X] => P.derivative.eval z) he
            simpa only [derivative_mul, eval_add, eval_mul, hz, zero_mul,
              add_zero] using hder
          have hea : e.eval a = 0 := by
            have hval := heRoot a ha
            rw [hd2da] at hval
            exact (mul_eq_zero.mp hval.symm).resolve_left (hsimple a ha)
          have heb : e.eval b = 0 := by
            have hval := heRoot b hb
            rw [hd2db] at hval
            exact (mul_eq_zero.mp hval.symm).resolve_left (hsimple b hb)
          obtain ⟨e2, he2⟩ := dvd_of_two_simple_root_evals_68 H e hdeg
            hsimple a b hab ha hb hea heb
          have hd2sq : d2 = H ^ 2 * e2 := by
            rw [he, he2]
            ring
          have hI4red : b2 * phi1 +
              (6 : k[X]) * H ^ 3 * w2 * e2 = 0 := by
            have hI4c := hI4
            rw [hd2sq] at hI4c
            linear_combination hI4c
          have hrowRed : b2 * w2 * eDot - H * e2 * k1 = C j * H ^ 3 := by
            apply mul_left_cancel₀ hH
            have hrowc := hrow'
            rw [hd2sq] at hrowc
            linear_combination hrowc
          -- First coefficient of the reduced terminal row at `b`.
          have hface3 : b2.eval b * w2.derivative.eval b * eDot.eval b =
              H.derivative.eval b * e2.eval b * k1.eval b := by
            have hder := congrArg
              (fun P : k[X] => P.derivative.eval b) hrowRed
            simp only [derivative_sub, derivative_mul, derivative_pow,
              derivative_C, eval_sub, eval_add, eval_mul, eval_pow,
              eval_C, eval_ofNat, hb, hw2b, zero_mul, mul_zero, zero_add,
              add_zero, sub_zero, zero_sub, zero_pow] at hder
            linear_combination hder
          exact ⟨hd2b, hk1b, hb2b, hphi1db, hw2b, hd2db, e2, hd2sq,
            hI4red, hrowRed, hface3⟩
    exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inr (Or.inr
        ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hb2a, hk1a, hd2a,
         hb2da, hd2da, hpf.1, hpf.2.1, hfaceB, heDotPin, htrichB⟩)⟩

end MixedFourthRowSource68

end Max11DegreeRoutes
