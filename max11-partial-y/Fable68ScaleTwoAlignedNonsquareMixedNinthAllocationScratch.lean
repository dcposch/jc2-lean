import Fable68ScaleTwoAlignedNonsquareMixedNinthScratch

/-! # Allocation packet for the ninth-row transverse two-root split

The ninth-row packet leaves the `b₂ = H b₃` limb of the preserved
transverse allocation with an exclusive `e₁'(a) = 0` / `k₁'(a) = 0`
dichotomy whose `e₁'(a) = 0` branch carries the exact root dichotomy
`b₃'''(a) = 0 ↔ w₂(a) = 0` together with unit pins, while the `b`-side
sub-split `e₁(b) = 0 ∨ k₁(b) = 0` sits as an independent conjunct.
This file takes **no** further Taylor row.  It exploits only the new
iff, the retained unit pins, the existing root zeros at `a` and `b`,
and the retained global divisibilities `b₂ = H b₃`, `d₂ = H e₁`,
`e₁ = H e₂`, `k₁ = H k₂` and `d₂ = H² e₂`, `Φ₁ = (x - b)⁴ ψ₄` to
allocate roots and merge the limb-local data into the source
coordinates.

Concretely, in the `b₂ = H b₃` limb the divisibilities lift the whole
dichotomy onto the coordinate jets: branch-free one obtains
`d₂''(a) = 2 H'(a) e₁'(a)`, `b₂'''(a) = 3 H'(a) b₃''(a)`, the
coordinate reading `d₂''(a) = 0 ↔ e₁'(a) = 0` of the exclusive
dichotomy, and the branch-free coordinate face
`b₂'''(a) Φ₁(a) + 18 H'(a) w₂(a) d₂''(a) = 0`.  On the `e₁'(a) = 0`
branch the deepened jets give the exact unit order pin
`d₂'''(a) = 3 H'(a) e₁''(a) ≠ 0`, its `j`-loaded transport
`d₂'''(a) k₁'(a) + 6 j H'(a)⁴ = 0`, the fourth-order lift
`b₂''''(a) = 4 H'(a) b₃'''(a)`, the lifted face
`b₂''''(a) Φ₁(a) + 24 H'(a) w₂(a) d₂'''(a) = 0`, the lifted `j`-face
`b₂''''(a) Φ₁(a) k₁'(a) = 144 j H'(a)⁵ w₂(a)`, the transported iff
`b₂''''(a) = 0 ↔ w₂(a) = 0`, and the explicit root allocation
`(w₂(a) = 0 ∧ b₃'''(a) = 0 ∧ b₂''''(a) = 0) ∨ (all three ≠ 0)`.  The
`b`-side sub-split is merged into the dichotomy and sharpened per
cell: with `e₁ = H e₂` the `e₁'(a) = 0` branch forces `e₂(a) = 0`,
`e₁''(a) = 2 H'(a) e₂'(a)`, the unit `e₂'(a) ≠ 0` and the peeled pin
`e₂'(a) k₁'(a) + j H'(a)² = 0`, while the `k₁'(a) = 0` branch forces
the unit `e₂(a) ≠ 0`; with `k₁ = H k₂` the `e₁'(a) = 0` branch forces
the unit `k₂(a) ≠ 0` and the peeled pin
`e₁''(a) k₂(a) + 2 j H'(a)² = 0`, while the `k₁'(a) = 0` branch forces
`k₂(a) = 0`, `k₁''(a) = 2 H'(a) k₂'(a)` and the peeled `j`-loaded pin
`e₁'(a) (k₂'(a) Φ₁(a) + 6 H'(a) w₂(a)² Ė(a)) + j H'(a)² Φ₁(a) = 0`.
The other two limbs are touched only through their existing global
factors: in the `k₁ = H k₂` limb the order-one transports
`k₁'(a) = H'(a) k₂(a)`, `k₁'(b) = H'(b) k₂(b)` allocate the retained
face onto the coordinate jet, `d₂''(a) k₁'(a) = 0`; in the transverse
residual the retained factorisations give `d₂''(b) = 2 H'(b)² e₂(b)`
and `Φ₁''''(b) = 24 ψ₄(b)`.  No cell closes — every transported pin
is satisfiable — so the sharpened children are returned and the
`H ∣ r`, `H ∣ Φ₁` siblings pass through untouched. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

section MixedNinthAllocationAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- First-order transport through a retained divisibility at a core
root: the derivative of the product reads the quotient. -/
theorem productDerivativeEval_68
    (H Q P : k[X]) (a : k) (ha : H.eval a = 0) (hPQ : P = H * Q) :
    P.derivative.eval a = H.derivative.eval a * Q.eval a := by
  have hd := congrArg (fun R : k[X] => R.derivative.eval a) hPQ
  simp only [derivative_mul, eval_add, eval_mul, ha, zero_mul,
    mul_zero, add_zero, zero_add] at hd
  first
    | exact hd
    | linear_combination hd

/-- Second-order transport through a retained divisibility at a core
root: on a simple zero of the quotient the second derivative of the
product reads the quotient derivative. -/
theorem productSecondDerivativeEval_68
    (H Q P : k[X]) (a : k) (ha : H.eval a = 0) (hQa : Q.eval a = 0)
    (hPQ : P = H * Q) :
    P.derivative.derivative.eval a =
      2 * H.derivative.eval a * Q.derivative.eval a := by
  have hdd := congrArg
    (fun R : k[X] => R.derivative.derivative.eval a) hPQ
  simp only [derivative_mul, derivative_add, eval_add, eval_mul, ha,
    hQa, zero_mul, mul_zero, add_zero, zero_add] at hdd
  first
    | exact hdd
    | linear_combination hdd

/-- Third-order transport through a retained divisibility at a core
root: on a double zero of the quotient the third derivative of the
product reads the quotient second derivative. -/
theorem productThirdDerivativeEval_68
    (H Q P : k[X]) (a : k) (ha : H.eval a = 0) (hQa : Q.eval a = 0)
    (hQda : Q.derivative.eval a = 0) (hPQ : P = H * Q) :
    P.derivative.derivative.derivative.eval a =
      3 * H.derivative.eval a * Q.derivative.derivative.eval a := by
  have hddd := congrArg
    (fun R : k[X] => R.derivative.derivative.derivative.eval a) hPQ
  simp only [derivative_mul, derivative_add, eval_add, eval_mul, ha,
    hQa, hQda, zero_mul, mul_zero, add_zero, zero_add] at hddd
  first
    | exact hddd
    | linear_combination hddd

/-- Fourth-order transport through a retained divisibility at a core
root: on a triple zero of the quotient the fourth derivative of the
product reads the quotient third derivative. -/
theorem productFourthDerivativeEval_68
    (H Q P : k[X]) (a : k) (ha : H.eval a = 0) (hQa : Q.eval a = 0)
    (hQda : Q.derivative.eval a = 0)
    (hQdda : Q.derivative.derivative.eval a = 0) (hPQ : P = H * Q) :
    P.derivative.derivative.derivative.derivative.eval a =
      4 * H.derivative.eval a *
        Q.derivative.derivative.derivative.eval a := by
  have hdddd := congrArg
    (fun R : k[X] =>
      R.derivative.derivative.derivative.derivative.eval a) hPQ
  simp only [derivative_mul, derivative_add, eval_add, eval_mul, ha,
    hQa, hQda, hQdda, zero_mul, mul_zero, add_zero, zero_add] at hdddd
  first
    | exact hdddd
    | linear_combination hdddd

/-- Fourth-order transport through the retained quartic factorisation
of `Φ₁` at its root: for a monic simple factor the fourth derivative
reads the cofactor, `Φ₁''''(b) = 24 ψ₄(b)`. -/
theorem quarticCofactorFourthDerivativeEval_68
    (N psi4 phi1 : k[X]) (b : k) (hNb : N.eval b = 0)
    (hNd : N.derivative.eval b = 1)
    (hquart : phi1 = N ^ 4 * psi4) :
    phi1.derivative.derivative.derivative.derivative.eval b =
      24 * psi4.eval b := by
  have hphi : phi1 = N * (N * (N * (N * psi4))) := by rw [hquart]; ring
  have hS0 : (N * psi4).eval b = 0 := by rw [eval_mul, hNb, zero_mul]
  have hSd : (N * psi4).derivative.eval b = psi4.eval b := by
    rw [productDerivativeEval_68 N psi4 (N * psi4) b hNb rfl, hNd,
      one_mul]
  have hR0 : (N * (N * psi4)).eval b = 0 := by
    rw [eval_mul, hNb, zero_mul]
  have hRd : (N * (N * psi4)).derivative.eval b = 0 := by
    rw [productDerivativeEval_68 N (N * psi4) (N * (N * psi4)) b hNb
      rfl, hS0, mul_zero]
  have hRdd : (N * (N * psi4)).derivative.derivative.eval b =
      2 * psi4.eval b := by
    rw [productSecondDerivativeEval_68 N (N * psi4) (N * (N * psi4)) b
      hNb hS0 rfl, hNd, hSd]
    ring
  have hQ0 : (N * (N * (N * psi4))).eval b = 0 := by
    rw [eval_mul, hNb, zero_mul]
  have hQd : (N * (N * (N * psi4))).derivative.eval b = 0 := by
    rw [productDerivativeEval_68 N (N * (N * psi4))
      (N * (N * (N * psi4))) b hNb rfl, hR0, mul_zero]
  have hQdd :
      (N * (N * (N * psi4))).derivative.derivative.eval b = 0 := by
    rw [productSecondDerivativeEval_68 N (N * (N * psi4))
      (N * (N * (N * psi4))) b hNb hR0 rfl, hRd, mul_zero]
  have hQddd :
      (N * (N * (N * psi4))).derivative.derivative.derivative.eval b =
        6 * psi4.eval b := by
    rw [productThirdDerivativeEval_68 N (N * (N * psi4))
      (N * (N * (N * psi4))) b hNb hR0 hRd rfl, hNd, hRdd]
    ring
  rw [productFourthDerivativeEval_68 N (N * (N * (N * psi4))) phi1 b
    hNb hQ0 hQd hQdd hphi, hNd, hQddd]
  ring

/-- Peeled transport of the `k₁'(a) = 0` branch pin through the
retained factorisation `k₁ = H k₂`: substituting the transported jet
`k₁''(a) = 2 H'(a) k₂'(a)` and cancelling the unit `2 H'(a)` peels the
retained `j`-loaded pin to
`e₁'(a) (k₂'(a) Φ₁(a) + 6 H'(a) w₂(a)² Ė(a)) + j H'(a)² Φ₁(a) = 0`. -/
theorem mixedNinthKTwoDeepPinTransport_68
    {Hda e1d k1dd k2d phia w2a eDa j : k} (hHda : Hda ≠ 0)
    (hk1ddEq : k1dd = 2 * Hda * k2d)
    (hpin2 : e1d * (k1dd * phia + 12 * Hda ^ 2 * w2a ^ 2 * eDa) +
      2 * j * Hda ^ 3 * phia = 0) :
    e1d * (k2d * phia + 6 * Hda * w2a ^ 2 * eDa) +
      j * Hda ^ 2 * phia = 0 := by
  have h2H : (2 : k) * Hda ≠ 0 := mul_ne_zero (by norm_num) hHda
  have hz : 2 * Hda *
      (e1d * (k2d * phia + 6 * Hda * w2a ^ 2 * eDa) +
        j * Hda ^ 2 * phia) = 0 := by
    linear_combination hpin2 - e1d * phia * hk1ddEq
  exact (mul_eq_zero.mp hz).resolve_left h2H

end MixedNinthAllocationAlgebra68

section MixedNinthAllocationSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Allocation refinement of the ninth-row transverse two-root packet.
No new Taylor row is taken.  The `b₂ = H b₃` limb is sharpened by pure
transport through the retained divisibilities: branch-free coordinate
reads `d₂''(a) = 2 H'(a) e₁'(a)`, `b₂'''(a) = 3 H'(a) b₃''(a)`, the
coordinate dichotomy `d₂''(a) = 0 ↔ e₁'(a) = 0` and the coordinate
face `b₂'''(a) Φ₁(a) + 18 H'(a) w₂(a) d₂''(a) = 0`; on `e₁'(a) = 0`
the unit order pin `d₂'''(a) = 3 H'(a) e₁''(a) ≠ 0`, the `j`-loaded
coordinate pin `d₂'''(a) k₁'(a) + 6 j H'(a)⁴ = 0`, the lifts
`b₂''''(a) = 4 H'(a) b₃'''(a)`,
`b₂''''(a) Φ₁(a) + 24 H'(a) w₂(a) d₂'''(a) = 0`,
`b₂''''(a) Φ₁(a) k₁'(a) = 144 j H'(a)⁵ w₂(a)`, the transported iff
`b₂''''(a) = 0 ↔ w₂(a) = 0` and the explicit `w₂(a)` root allocation;
and the `b`-side sub-split is merged into the dichotomy with per-cell
peeled pins (`e₂(a) = 0`, `e₂'(a) ≠ 0`,
`e₂'(a) k₁'(a) + j H'(a)² = 0` / `k₂(a) ≠ 0`,
`e₁''(a) k₂(a) + 2 j H'(a)² = 0` on `e₁'(a) = 0`; `e₂(a) ≠ 0` /
`k₂(a) = 0`, `k₁''(a) = 2 H'(a) k₂'(a)`,
`e₁'(a) (k₂'(a) Φ₁(a) + 6 H'(a) w₂(a)² Ė(a)) + j H'(a)² Φ₁(a) = 0` on
`k₁'(a) = 0`).  The `k₁ = H k₂` limb gains only the factor transports
`k₁'(a) = H'(a) k₂(a)`, `k₁'(b) = H'(b) k₂(b)` and the coordinate
allocation `d₂''(a) k₁'(a) = 0`; the transverse residual gains only
`d₂''(b) = 2 H'(b)² e₂(b)` and `Φ₁''''(b) = 24 ψ₄(b)`.  No cell
closes and the `H ∣ r`, `H ∣ Φ₁` siblings pass through untouched. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneMixedNinthAllocationPacket
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
           b2.derivative.derivative.eval a = 0 ∧
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
               b2 * w2 * eDot - d2 * k2 = C j * H ^ 3 ∧
               b2.derivative.eval b * w2.eval b * eDot.eval b +
                   b2.eval b * w2.derivative.eval b * eDot.eval b +
                   b2.eval b * w2.eval b * eDot.derivative.eval b -
                 (d2.derivative.eval b * k2.eval b +
                   d2.eval b * k2.derivative.eval b) = 0 ∧
               d2.derivative.derivative.eval a * k2.eval a = 0 ∧
               b2.derivative.derivative.derivative.eval a * w2.eval a *
                   eDot.eval a -
                   (d2.derivative.derivative.derivative.eval a *
                       k2.eval a +
                     3 * d2.derivative.derivative.eval a *
                       k2.derivative.eval a) =
                 6 * j * H.derivative.eval a ^ 3 ∧
               b2.derivative.derivative.eval b * w2.eval b *
                     eDot.eval b +
                   2 * b2.derivative.eval b * w2.derivative.eval b *
                     eDot.eval b +
                   2 * b2.derivative.eval b * w2.eval b *
                     eDot.derivative.eval b +
                   b2.eval b * w2.derivative.derivative.eval b *
                     eDot.eval b +
                   2 * b2.eval b * w2.derivative.eval b *
                     eDot.derivative.eval b +
                   b2.eval b * w2.eval b *
                     eDot.derivative.derivative.eval b -
                   (d2.derivative.derivative.eval b * k2.eval b +
                     2 * d2.derivative.eval b *
                       k2.derivative.eval b +
                     d2.eval b * k2.derivative.derivative.eval b)
                     = 0 ∧
               b2.derivative.derivative.derivative.eval b *
                     w2.eval b * eDot.eval b +
                   3 * b2.derivative.derivative.eval b *
                     w2.derivative.eval b * eDot.eval b +
                   3 * b2.derivative.derivative.eval b * w2.eval b *
                     eDot.derivative.eval b +
                   3 * b2.derivative.eval b *
                     w2.derivative.derivative.eval b * eDot.eval b +
                   6 * b2.derivative.eval b * w2.derivative.eval b *
                     eDot.derivative.eval b +
                   3 * b2.derivative.eval b * w2.eval b *
                     eDot.derivative.derivative.eval b +
                   b2.eval b *
                     w2.derivative.derivative.derivative.eval b *
                     eDot.eval b +
                   3 * b2.eval b * w2.derivative.derivative.eval b *
                     eDot.derivative.eval b +
                   3 * b2.eval b * w2.derivative.eval b *
                     eDot.derivative.derivative.eval b +
                   b2.eval b * w2.eval b *
                     eDot.derivative.derivative.derivative.eval b -
                   (d2.derivative.derivative.derivative.eval b *
                       k2.eval b +
                     3 * d2.derivative.derivative.eval b *
                       k2.derivative.eval b +
                     3 * d2.derivative.eval b *
                       k2.derivative.derivative.eval b +
                     d2.eval b *
                       k2.derivative.derivative.derivative.eval b) =
                 6 * j * H.derivative.eval b ^ 3 ∧
               k1.derivative.eval a =
                 H.derivative.eval a * k2.eval a ∧
               k1.derivative.eval b =
                 H.derivative.eval b * k2.eval b ∧
               d2.derivative.derivative.eval a *
                 k1.derivative.eval a = 0) ∨
            (d2.eval b = 0 ∧ b2.eval b = 0 ∧ ∃ b3 e1 : k[X],
               b2 = H * b3 ∧ d2 = H * e1 ∧
               b3 * phi1 + (6 : k[X]) * H * w2 * e1 = 0 ∧
               e1 * k1 = H * b3 * w2 * eDot - C j * H ^ 3 ∧
               b3.eval a = 0 ∧ e1.eval a = 0 ∧
               b3.derivative.eval a = 0 ∧
               e1.derivative.eval a * k1.derivative.eval a = 0 ∧
               d2.derivative.derivative.eval a =
                 2 * H.derivative.eval a * e1.derivative.eval a ∧
               b2.derivative.derivative.derivative.eval a =
                 3 * H.derivative.eval a *
                   b3.derivative.derivative.eval a ∧
               (d2.derivative.derivative.eval a = 0 ↔
                 e1.derivative.eval a = 0) ∧
               b2.derivative.derivative.derivative.eval a *
                   phi1.eval a +
                 18 * H.derivative.eval a * w2.eval a *
                   d2.derivative.derivative.eval a = 0 ∧
               ((e1.derivative.eval a = 0 ∧
                   b3.derivative.derivative.eval a = 0 ∧
                   d2.derivative.derivative.eval a = 0 ∧
                   b2.derivative.derivative.derivative.eval a = 0 ∧
                   k1.derivative.eval a ≠ 0 ∧
                   e1.derivative.derivative.eval a ≠ 0 ∧
                   e1.derivative.derivative.eval a *
                       k1.derivative.eval a +
                     2 * j * H.derivative.eval a ^ 3 = 0 ∧
                   b3.derivative.derivative.derivative.eval a *
                       phi1.eval a +
                     18 * H.derivative.eval a * w2.eval a *
                       e1.derivative.derivative.eval a = 0 ∧
                   b3.derivative.derivative.derivative.eval a *
                       phi1.eval a * k1.derivative.eval a =
                     36 * j * H.derivative.eval a ^ 4 * w2.eval a ∧
                   (b3.derivative.derivative.derivative.eval a = 0 ↔
                     w2.eval a = 0) ∧
                   d2.derivative.derivative.derivative.eval a =
                     3 * H.derivative.eval a *
                       e1.derivative.derivative.eval a ∧
                   d2.derivative.derivative.derivative.eval a ≠ 0 ∧
                   d2.derivative.derivative.derivative.eval a *
                       k1.derivative.eval a +
                     6 * j * H.derivative.eval a ^ 4 = 0 ∧
                   b2.derivative.derivative.derivative.derivative.eval
                       a =
                     4 * H.derivative.eval a *
                       b3.derivative.derivative.derivative.eval a ∧
                   b2.derivative.derivative.derivative.derivative.eval
                         a * phi1.eval a +
                     24 * H.derivative.eval a * w2.eval a *
                       d2.derivative.derivative.derivative.eval a
                       = 0 ∧
                   b2.derivative.derivative.derivative.derivative.eval
                         a * phi1.eval a * k1.derivative.eval a =
                     144 * j * H.derivative.eval a ^ 5 * w2.eval a ∧
                   (b2.derivative.derivative.derivative.derivative.eval
                       a = 0 ↔ w2.eval a = 0) ∧
                   ((w2.eval a = 0 ∧
                       b3.derivative.derivative.derivative.eval a
                         = 0 ∧
                       b2.derivative.derivative.derivative.derivative.eval
                         a = 0) ∨
                     (w2.eval a ≠ 0 ∧
                       b3.derivative.derivative.derivative.eval a
                         ≠ 0 ∧
                       b2.derivative.derivative.derivative.derivative.eval
                         a ≠ 0)) ∧
                   ((e1.eval b = 0 ∧ ∃ e2 : k[X], e1 = H * e2 ∧
                       d2 = H ^ 2 * e2 ∧
                       b3 * phi1 + (6 : k[X]) * H ^ 2 * w2 * e2
                         = 0 ∧
                       e2 * k1 = b3 * w2 * eDot - C j * H ^ 2 ∧
                       e2.eval a = 0 ∧
                       e1.derivative.derivative.eval a =
                         2 * H.derivative.eval a *
                           e2.derivative.eval a ∧
                       e2.derivative.eval a ≠ 0 ∧
                       e2.derivative.eval a * k1.derivative.eval a +
                         j * H.derivative.eval a ^ 2 = 0) ∨
                    (k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
                       e1 * k2 = b3 * w2 * eDot - C j * H ^ 2 ∧
                       k1.derivative.eval a =
                         H.derivative.eval a * k2.eval a ∧
                       k2.eval a ≠ 0 ∧
                       e1.derivative.derivative.eval a * k2.eval a +
                         2 * j * H.derivative.eval a ^ 2 = 0))) ∨
                 (k1.derivative.eval a = 0 ∧
                   e1.derivative.eval a ≠ 0 ∧
                   b3.derivative.derivative.eval a * phi1.eval a +
                     12 * H.derivative.eval a * w2.eval a *
                       e1.derivative.eval a = 0 ∧
                   e1.derivative.eval a *
                       (k1.derivative.derivative.eval a *
                           phi1.eval a +
                         12 * H.derivative.eval a ^ 2 *
                           w2.eval a ^ 2 * eDot.eval a) +
                     2 * j * H.derivative.eval a ^ 3 * phi1.eval a
                       = 0 ∧
                   b3.derivative.derivative.derivative.eval a *
                       phi1.eval a +
                     3 * b3.derivative.derivative.eval a *
                       phi1.derivative.eval a +
                     36 * H.derivative.eval a *
                       w2.derivative.eval a * e1.derivative.eval a +
                     18 * H.derivative.eval a * w2.eval a *
                       e1.derivative.derivative.eval a +
                     18 * H.derivative.derivative.eval a * w2.eval a *
                       e1.derivative.eval a = 0 ∧
                   d2.derivative.derivative.eval a ≠ 0 ∧
                   ((e1.eval b = 0 ∧ ∃ e2 : k[X], e1 = H * e2 ∧
                       d2 = H ^ 2 * e2 ∧
                       b3 * phi1 + (6 : k[X]) * H ^ 2 * w2 * e2
                         = 0 ∧
                       e2 * k1 = b3 * w2 * eDot - C j * H ^ 2 ∧
                       e1.derivative.eval a =
                         H.derivative.eval a * e2.eval a ∧
                       e2.eval a ≠ 0) ∨
                    (k1.eval b = 0 ∧ ∃ k2 : k[X], k1 = H * k2 ∧
                       e1 * k2 = b3 * w2 * eDot - C j * H ^ 2 ∧
                       k2.eval a = 0 ∧
                       k1.derivative.derivative.eval a =
                         2 * H.derivative.eval a *
                           k2.derivative.eval a ∧
                       e1.derivative.eval a *
                           (k2.derivative.eval a * phi1.eval a +
                             6 * H.derivative.eval a *
                               w2.eval a ^ 2 * eDot.eval a) +
                         j * H.derivative.eval a ^ 2 * phi1.eval a
                           = 0))))) ∨
            (d2.eval b = 0 ∧ k1.eval b ≠ 0 ∧ b2.eval b ≠ 0 ∧
               phi1.derivative.eval b = 0 ∧ w2.eval b = 0 ∧
               d2.derivative.eval b = 0 ∧
               phi1.derivative.derivative.eval b = 0 ∧
               phi1.derivative.derivative.derivative.eval b = 0 ∧
               ∃ e2 psi4 : k[X], d2 = H ^ 2 * e2 ∧
                 phi1 = (Polynomial.X - C b) ^ 4 * psi4 ∧
                 b2 * phi1 + (6 : k[X]) * H ^ 3 * w2 * e2 = 0 ∧
                 b2 * w2 * eDot - H * e2 * k1 = C j * H ^ 3 ∧
                 b2.eval b * w2.derivative.eval b * eDot.eval b =
                   H.derivative.eval b * e2.eval b * k1.eval b ∧
                 2 * b2.derivative.eval b * w2.derivative.eval b *
                       eDot.eval b +
                     b2.eval b * w2.derivative.derivative.eval b *
                       eDot.eval b +
                     2 * b2.eval b * w2.derivative.eval b *
                       eDot.derivative.eval b =
                   H.derivative.derivative.eval b * e2.eval b *
                       k1.eval b +
                     2 * H.derivative.eval b * e2.derivative.eval b *
                       k1.eval b +
                     2 * H.derivative.eval b * e2.eval b *
                       k1.derivative.eval b ∧
                 3 * b2.derivative.derivative.eval b *
                       w2.derivative.eval b * eDot.eval b +
                     3 * b2.derivative.eval b *
                       w2.derivative.derivative.eval b *
                       eDot.eval b +
                     b2.eval b *
                       w2.derivative.derivative.derivative.eval b *
                       eDot.eval b +
                     6 * b2.derivative.eval b * w2.derivative.eval b *
                       eDot.derivative.eval b +
                     3 * b2.eval b * w2.derivative.derivative.eval b *
                       eDot.derivative.eval b +
                     3 * b2.eval b * w2.derivative.eval b *
                       eDot.derivative.derivative.eval b =
                   H.derivative.derivative.derivative.eval b *
                       e2.eval b * k1.eval b +
                     3 * H.derivative.derivative.eval b *
                       e2.derivative.eval b * k1.eval b +
                     3 * H.derivative.derivative.eval b * e2.eval b *
                       k1.derivative.eval b +
                     3 * H.derivative.eval b *
                       e2.derivative.derivative.eval b * k1.eval b +
                     6 * H.derivative.eval b * e2.derivative.eval b *
                       k1.derivative.eval b +
                     3 * H.derivative.eval b * e2.eval b *
                       k1.derivative.derivative.eval b +
                     6 * j * H.derivative.eval b ^ 3 ∧
                 4 * b2.derivative.derivative.derivative.eval b *
                       w2.derivative.eval b * eDot.eval b +
                     6 * b2.derivative.derivative.eval b *
                       w2.derivative.derivative.eval b *
                       eDot.eval b +
                     12 * b2.derivative.derivative.eval b *
                       w2.derivative.eval b * eDot.derivative.eval b +
                     4 * b2.derivative.eval b *
                       w2.derivative.derivative.derivative.eval b *
                       eDot.eval b +
                     12 * b2.derivative.eval b *
                       w2.derivative.derivative.eval b *
                       eDot.derivative.eval b +
                     12 * b2.derivative.eval b *
                       w2.derivative.eval b *
                       eDot.derivative.derivative.eval b +
                     b2.eval b *
                       w2.derivative.derivative.derivative.derivative.eval
                         b * eDot.eval b +
                     4 * b2.eval b *
                       w2.derivative.derivative.derivative.eval b *
                       eDot.derivative.eval b +
                     6 * b2.eval b *
                       w2.derivative.derivative.eval b *
                       eDot.derivative.derivative.eval b +
                     4 * b2.eval b * w2.derivative.eval b *
                       eDot.derivative.derivative.derivative.eval b =
                   H.derivative.derivative.derivative.derivative.eval
                       b * e2.eval b * k1.eval b +
                     4 * H.derivative.derivative.derivative.eval b *
                       e2.derivative.eval b * k1.eval b +
                     4 * H.derivative.derivative.derivative.eval b *
                       e2.eval b * k1.derivative.eval b +
                     6 * H.derivative.derivative.eval b *
                       e2.derivative.derivative.eval b * k1.eval b +
                     12 * H.derivative.derivative.eval b *
                       e2.derivative.eval b * k1.derivative.eval b +
                     6 * H.derivative.derivative.eval b * e2.eval b *
                       k1.derivative.derivative.eval b +
                     4 * H.derivative.eval b *
                       e2.derivative.derivative.derivative.eval b *
                       k1.eval b +
                     12 * H.derivative.eval b *
                       e2.derivative.derivative.eval b *
                       k1.derivative.eval b +
                     12 * H.derivative.eval b * e2.derivative.eval b *
                       k1.derivative.derivative.eval b +
                     4 * H.derivative.eval b * e2.eval b *
                       k1.derivative.derivative.derivative.eval b +
                     36 * j * H.derivative.eval b ^ 2 *
                       H.derivative.derivative.eval b ∧
                 d2.derivative.derivative.eval b =
                   2 * H.derivative.eval b ^ 2 * e2.eval b ∧
                 phi1.derivative.derivative.derivative.derivative.eval
                   b = 24 * psi4.eval b)))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, hsplit⟩ :=
    S.terminalAfterLowerOneMixedNinthRowPacket (H := H) hdeg hp hq
      hp6 hq8 haligned hjac hj
  have hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0 :=
    fun x hx => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq hx
  rcases hsplit with hr | hphi | hmix
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inl hr⟩
  · exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, Or.inr (Or.inl hphi)⟩
  · obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hb2a, hk1a, hd2a,
      hb2da, hd2da, hb2dda, hI4faceB, hrowFaceB, hfaceB, hpinB,
      htri⟩ := hmix
    have hHda : H.derivative.eval a ≠ 0 := hsimple a ha
    refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hI4, hrow,
      Or.inr (Or.inr ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb, hb2a,
        hk1a, hd2a, hb2da, hd2da, hb2dda, hI4faceB, hrowFaceB, hfaceB,
        hpinB, ?_⟩)⟩
    rcases htri with
      ⟨hk1b, k2, hk2, hk2row, hk2faceB, hk2facea, hk2jet, hk2tie2,
        hk2tie3⟩ |
      ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red, he1row, hb3a, he1a,
        hb3da, hfaceProd, hdichot, hsub⟩ |
      ⟨hd2b, hk1bne, hb2bne, hphi1db, hw2b, hd2db, hphi1ddb,
        hphi1dddb, e2, psi4, hd2sq, hquart, hI4redR, hrowRed, htie,
        htie2, htie3, htie4⟩
    · -- `k₁ = H k₂` limb: order-one transports through the retained
      -- factorisation allocate the retained `d₂`-face onto the
      -- coordinate jet `k₁'(a)`.
      have htra := productDerivativeEval_68 H k2 k1 a ha hk2
      have htrb := productDerivativeEval_68 H k2 k1 b hb hk2
      have hallock : d2.derivative.derivative.eval a *
          k1.derivative.eval a = 0 := by
        linear_combination H.derivative.eval a * hk2facea +
          d2.derivative.derivative.eval a * htra
      exact Or.inl ⟨hk1b, k2, hk2, hk2row, hk2faceB, hk2facea, hk2jet,
        hk2tie2, hk2tie3, htra, htrb, hallock⟩
    · -- `b₂ = H b₃` limb: branch-free coordinate reads through
      -- `b₂ = H b₃`, `d₂ = H e₁`, then the merged sharpened split.
      have hd2ddEq :=
        productSecondDerivativeEval_68 H e1 d2 a ha he1a hd2e1
      have hb2dddEq :=
        productThirdDerivativeEval_68 H b3 b2 a ha hb3a hb3da hb2b3
      have hd2ddIff : d2.derivative.derivative.eval a = 0 ↔
          e1.derivative.eval a = 0 := by
        rw [hd2ddEq]
        constructor
        · intro h0
          exact (mul_eq_zero.mp h0).resolve_left
            (mul_ne_zero (by norm_num) hHda)
        · intro h0
          rw [h0, mul_zero]
      have hbracket : b3.derivative.derivative.eval a * phi1.eval a +
          12 * H.derivative.eval a * w2.eval a *
            e1.derivative.eval a = 0 := by
        rcases hdichot with ⟨he1d, hb3dd, -⟩ | ⟨-, -, hI4tie, -⟩
        · linear_combination phi1.eval a * hb3dd +
            12 * H.derivative.eval a * w2.eval a * he1d
        · exact hI4tie
      have hcoordFace :
          b2.derivative.derivative.derivative.eval a * phi1.eval a +
            18 * H.derivative.eval a * w2.eval a *
              d2.derivative.derivative.eval a = 0 := by
        linear_combination phi1.eval a * hb2dddEq +
          18 * H.derivative.eval a * w2.eval a * hd2ddEq +
          3 * H.derivative.eval a * hbracket
      refine Or.inr (Or.inl ⟨hd2b, hb2b, b3, e1, hb2b3, hd2e1, hI4red,
        he1row, hb3a, he1a, hb3da, hfaceProd, hd2ddEq, hb2dddEq,
        hd2ddIff, hcoordFace, ?_⟩)
      rcases hdichot with
        ⟨he1d, hb3dd, hd2dd, hb2ddd, hk1dne, he1ddne, hpin, htieA,
          hjface, hiff⟩ |
        ⟨hk1d, he1dne, hI4tie, hpin2, hfull⟩
      · -- `e₁'(a) = 0` branch: unit order pins and the `w₂(a)`
        -- allocation, all by transport — no new rows.
        have hd3Eq :=
          productThirdDerivativeEval_68 H e1 d2 a ha he1a he1d hd2e1
        have hd3ne :
            d2.derivative.derivative.derivative.eval a ≠ 0 := by
          rw [hd3Eq]
          exact mul_ne_zero (mul_ne_zero (by norm_num) hHda) he1ddne
        have hd3pin :
            d2.derivative.derivative.derivative.eval a *
                k1.derivative.eval a +
              6 * j * H.derivative.eval a ^ 4 = 0 := by
          linear_combination k1.derivative.eval a * hd3Eq +
            3 * H.derivative.eval a * hpin
        have hb4Eq := productFourthDerivativeEval_68 H b3 b2 a ha
          hb3a hb3da hb3dd hb2b3
        have hb4face :
            b2.derivative.derivative.derivative.derivative.eval a *
                phi1.eval a +
              24 * H.derivative.eval a * w2.eval a *
                d2.derivative.derivative.derivative.eval a = 0 := by
          linear_combination phi1.eval a * hb4Eq +
            24 * H.derivative.eval a * w2.eval a * hd3Eq +
            4 * H.derivative.eval a * htieA
        have hb4jface :
            b2.derivative.derivative.derivative.derivative.eval a *
                phi1.eval a * k1.derivative.eval a =
              144 * j * H.derivative.eval a ^ 5 * w2.eval a := by
          linear_combination
            phi1.eval a * k1.derivative.eval a * hb4Eq +
            4 * H.derivative.eval a * hjface
        have hb4iff :
            b2.derivative.derivative.derivative.derivative.eval a
                = 0 ↔ w2.eval a = 0 := by
          constructor
          · intro h0
            apply hiff.mp
            have hz : 4 * H.derivative.eval a *
                b3.derivative.derivative.derivative.eval a = 0 := by
              rw [← hb4Eq]; exact h0
            exact (mul_eq_zero.mp hz).resolve_left
              (mul_ne_zero (by norm_num) hHda)
          · intro h0
            rw [hb4Eq, hiff.mpr h0, mul_zero]
        have halloc : (w2.eval a = 0 ∧
              b3.derivative.derivative.derivative.eval a = 0 ∧
              b2.derivative.derivative.derivative.derivative.eval a
                = 0) ∨
            (w2.eval a ≠ 0 ∧
              b3.derivative.derivative.derivative.eval a ≠ 0 ∧
              b2.derivative.derivative.derivative.derivative.eval a
                ≠ 0) := by
          by_cases hw : w2.eval a = 0
          · exact Or.inl ⟨hw, hiff.mpr hw, hb4iff.mpr hw⟩
          · exact Or.inr ⟨hw, fun h0 => hw (hiff.mp h0),
              fun h0 => hw (hb4iff.mp h0)⟩
        refine Or.inl ⟨he1d, hb3dd, hd2dd, hb2ddd, hk1dne, he1ddne,
          hpin, htieA, hjface, hiff, hd3Eq, hd3ne, hd3pin, hb4Eq,
          hb4face, hb4jface, hb4iff, halloc, ?_⟩
        rcases hsub with ⟨he1b, e2, he2, hd2e2, hI4red2, hk1row2⟩ |
          ⟨hk1b2, k2, hk2b, hk2row2⟩
        · -- `e₁ = H e₂` cell: `e₂` inherits an exact simple zero and
          -- the peeled unit pin.
          have he2tr := productDerivativeEval_68 H e2 e1 a ha he2
          have he2a : e2.eval a = 0 := by
            have hz : H.derivative.eval a * e2.eval a = 0 := by
              rw [← he2tr]; exact he1d
            exact (mul_eq_zero.mp hz).resolve_left hHda
          have he2Eq :=
            productSecondDerivativeEval_68 H e2 e1 a ha he2a he2
          have he2dne : e2.derivative.eval a ≠ 0 := by
            intro h0
            exact he1ddne (by rw [he2Eq, h0, mul_zero])
          have he2pin : e2.derivative.eval a * k1.derivative.eval a +
              j * H.derivative.eval a ^ 2 = 0 := by
            have hz : 2 * H.derivative.eval a *
                (e2.derivative.eval a * k1.derivative.eval a +
                  j * H.derivative.eval a ^ 2) = 0 := by
              linear_combination hpin - k1.derivative.eval a * he2Eq
            exact (mul_eq_zero.mp hz).resolve_left
              (mul_ne_zero (by norm_num) hHda)
          exact Or.inl ⟨he1b, e2, he2, hd2e2, hI4red2, hk1row2, he2a,
            he2Eq, he2dne, he2pin⟩
        · -- `k₁ = H k₂` cell: `k₂(a)` is a unit and the pin peels one
          -- power of `H'(a)`.
          have hk2tr := productDerivativeEval_68 H k2 k1 a ha hk2b
          have hk2ane : k2.eval a ≠ 0 := by
            intro h0
            exact hk1dne (by rw [hk2tr, h0, mul_zero])
          have hk2pin : e1.derivative.derivative.eval a * k2.eval a +
              2 * j * H.derivative.eval a ^ 2 = 0 := by
            have hz : H.derivative.eval a *
                (e1.derivative.derivative.eval a * k2.eval a +
                  2 * j * H.derivative.eval a ^ 2) = 0 := by
              linear_combination hpin -
                e1.derivative.derivative.eval a * hk2tr
            exact (mul_eq_zero.mp hz).resolve_left hHda
          exact Or.inr ⟨hk1b2, k2, hk2b, hk2row2, hk2tr, hk2ane,
            hk2pin⟩
      · -- `k₁'(a) = 0` branch: the coordinate `d₂''(a)` is a unit and
        -- the sub-split allocates `k₂(a)` exactly.
        have hd2ddne : d2.derivative.derivative.eval a ≠ 0 := by
          rw [hd2ddEq]
          exact mul_ne_zero (mul_ne_zero (by norm_num) hHda) he1dne
        refine Or.inr ⟨hk1d, he1dne, hI4tie, hpin2, hfull, hd2ddne,
          ?_⟩
        rcases hsub with ⟨he1b, e2, he2, hd2e2, hI4red2, hk1row2⟩ |
          ⟨hk1b2, k2, hk2b, hk2row2⟩
        · have he2tr := productDerivativeEval_68 H e2 e1 a ha he2
          have he2ane : e2.eval a ≠ 0 := by
            intro h0
            exact he1dne (by rw [he2tr, h0, mul_zero])
          exact Or.inl ⟨he1b, e2, he2, hd2e2, hI4red2, hk1row2, he2tr,
            he2ane⟩
        · have hk2tr := productDerivativeEval_68 H k2 k1 a ha hk2b
          have hk2a0 : k2.eval a = 0 := by
            have hz : H.derivative.eval a * k2.eval a = 0 := by
              rw [← hk2tr]; exact hk1d
            exact (mul_eq_zero.mp hz).resolve_left hHda
          have hk1ddEq :=
            productSecondDerivativeEval_68 H k2 k1 a ha hk2a0 hk2b
          have hk2pin2 :=
            mixedNinthKTwoDeepPinTransport_68 hHda hk1ddEq hpin2
          exact Or.inr ⟨hk1b2, k2, hk2b, hk2row2, hk2a0, hk1ddEq,
            hk2pin2⟩
    · -- Transverse residual: coordinate transports through the
      -- retained factorisations `d₂ = H² e₂`, `Φ₁ = (x - b)⁴ ψ₄`.
      have hmul : d2 = H * (H * e2) := by rw [hd2sq]; ring
      have hm0 : (H * e2).eval b = 0 := by rw [eval_mul, hb, zero_mul]
      have hmd := productDerivativeEval_68 H e2 (H * e2) b hb rfl
      have hd2ddbEq : d2.derivative.derivative.eval b =
          2 * H.derivative.eval b ^ 2 * e2.eval b := by
        rw [productSecondDerivativeEval_68 H (H * e2) d2 b hb hm0
          hmul, hmd]
        ring
      have hpsi4Eq := quarticCofactorFourthDerivativeEval_68
        (Polynomial.X - C b) psi4 phi1 b
        (by rw [eval_sub, eval_X, eval_C, sub_self])
        (by rw [derivative_sub, derivative_X, derivative_C, sub_zero,
          eval_one])
        hquart
      exact Or.inr (Or.inr ⟨hd2b, hk1bne, hb2bne, hphi1db, hw2b,
        hd2db, hphi1ddb, hphi1dddb, e2, psi4, hd2sq, hquart, hI4redR,
        hrowRed, htie, htie2, htie3, htie4, hd2ddbEq, hpsi4Eq⟩)

end MixedNinthAllocationSource68

end Max11DegreeRoutes
