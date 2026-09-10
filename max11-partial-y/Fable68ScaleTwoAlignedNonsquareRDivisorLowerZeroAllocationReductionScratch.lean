import Fable68ScaleTwoAlignedNonsquareRDivisorLowerZeroAllocationScratch

/-! # Reduction of the allocated `H ∣ r` lower-zero tree

The Allocation packet split every fresh product divisibility of the
`H ∣ r` lower-zero tree across the two simple core roots and left a
nested nineteen-leaf tree.  Here that finite allocation is reduced with
no new differentiation and no new Taylor rows: only retained faces,
unit pins, order-zero evaluations, the two-root transfer and the exact
cofactor pins `m(root) = −j` (with `j ≠ 0`) are combined.

Reductions performed, merging the `H`-divisible `b₂`, `ψ`, `d`, `w`
and `k` factors into the already-verified coordinate, conjugate-root,
`H`-divisor and lower-zero consumers:

* **Path merges.**  The `d₂ = H²·` deep leaf reached through the
  coordinate `d`-child and then `H ∣ ψ` coincides with the leaf reached
  through the `ψ`-child and then `H ∣ d₃`: both land in the single
  regime `ψ = Hψ₂ ∧ φ₁ = H³ψ₂ ∧ d₂ = H²D ∧ b₂ψ₂ = −6w₂D ∧
  Dk₁ = H²m` with the descended quotient row `Q₃ = 0`.  Likewise the
  `w`-then-`d` and `d`-then-`w` mixed allocations merge into the single
  split regime `w₂ = Hw₃ ∧ d₂ = Hd₃ ∧ w₃d₃ = −(1/6)b₂ψ₂ ∧
  d₃k₁ = H³m` with `H ∣ β`-numerator; the `B1`-path there gains the
  descended quotient `Q₃ = 0` and the `T₃/U₁` root tie outright through
  the standalone factor lemma (no new row is opened).

* **`d/k` tower resolution.**  On the `k₁ = Hk₂` grandchild the two
  retained per-root exclusive unit dichotomies are resolved across the
  root pair.  Joint zeros globalize by the two-root transfer and the
  budget `d₂k₁ = H⁴m` is then exactly exhausted: the tree collapses
  onto the three exact allocations `d₂ = H³d₇ ∧ k₁ = Hk₂ ∧ d₇k₂ = m`,
  `d₂ = H²d₅ ∧ k₁ = H²k₃ ∧ d₅k₃ = m` (reached from BOTH dichotomies —
  they merge), and `d₂ = Hd₃ ∧ k₁ = H³k₄ ∧ d₃k₄ = m`, each carrying the
  source-facing row `quotient·quotient + Cj = H·(b₂w₂ė₃)` and, at every
  core root, the exact unit pins `value·value = −j ≠ 0` next to the
  retained `−jH'²`/`−2jH'²` derivative pins; two mixed transverse
  residuals remain with both orientations pinned.

* **Free `k`-quotient pins.**  Every transverse leaf that globalized
  `H ∣ k₁` with `d₂k₂ = H³m` gains, at order zero, the per-root face
  `d₂(a)k₂(a) = 0` and hence the pin `k₂ = 0` at its `d₂`-unit root;
  the `B2`-side such leaf is re-based into the `d`-child `k₂`-regime
  `d₂ = Hd₃ ∧ d₃k₂ = H²m` with its quotient row `Q₃ = 0` retained.

No allocation closes (no `x`-degree bounds are available and every leaf
is witnessed); the `H ∣ φ₁` and outer transverse siblings are
transported literally.  The residual inventory is the literal flat
twenty-leaf disjunction of the packet below. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section RDivisorLowerZeroAllocationReductionAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- A degree-two core with simple roots has two distinct roots. -/
theorem rDivisorReduction_root_pair_exists_68
    (H : k[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0) :
    ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root H hdegne
  have hx' : H.eval x = 0 := hx
  have hlin : X - C x ∣ H := by
    rw [dvd_iff_isRoot]
    exact hx'
  obtain ⟨H1, hH1⟩ := hlin
  have hH1ne : H1 ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hH1
    exact hH hH1
  have hH1deg : H1.natDegree = 1 := by
    have hmul : H.natDegree =
        (X - C x : k[X]).natDegree + H1.natDegree := by
      rw [hH1]
      exact natDegree_mul (X_sub_C_ne_zero x) hH1ne
    simp only [natDegree_X_sub_C] at hmul
    rw [hdeg] at hmul
    omega
  have hH1degne : H1.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH1ne, hH1deg]
    decide
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root H1 hH1degne
  have hy1 : H1.eval y = 0 := hy
  have hyH : H.eval y = 0 := by
    rw [hH1, eval_mul, hy1, mul_zero]
  refine ⟨x, y, ?_, hx', hyH⟩
  intro hxy
  rw [← hxy] at hy1
  apply hsimple x hx'
  have hd1 : H.derivative = H1 + (X - C x) * H1.derivative := by
    rw [hH1, derivative_mul, derivative_sub, derivative_X, derivative_C]
    ring
  have hev := congrArg (fun P : k[X] => P.eval x) hd1
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self,
    zero_mul, add_zero] at hev
  rw [hev]
  exact hy1

end RDivisorLowerZeroAllocationReductionAlgebra68

section RDivisorLowerZeroAllocationReductionSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Reduction of the allocated `H ∣ r` lower-zero tree: path-duplicate
leaves are merged into single canonical regimes, the two retained
per-root `d/k` unit dichotomies are resolved across the root pair into
three exact fully de-cored allocations of `d₂k₁ = H⁴m` (with per-root
unit pins `= −j`) plus two mixed residuals, the `H ∣ k₁` consumers gain
their free order-zero `k`-quotient root pins, and the descended
quotient-row data is threaded into every merged leaf.  The result is a
literal flat twenty-leaf residual inventory; no leaf closes, and the
`H ∣ φ₁` and outer transverse siblings are transported literally. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneRDivisorLowerZeroAllocationReductionPacket
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
      ((∃ s t1 y1 A1 c2 e3 psi m : k[X],
          r = H * s ∧
          t = H * t1 ∧
          (3 : k[X]) * t1 = H * s ^ 2 + X ∧
          p.coeff 4 = H ^ 2 * t1 ∧
          p.coeff 3 = H * y1 ∧
          (27 : k[X]) * y1 = H ^ 2 * s ^ 3 + Yd ∧
          H ∣ t ∧ H ^ 2 ∣ p.coeff 4 ∧ H ∣ p.coeff 3 ∧
          A1 = t1 - C (5 / 12 : k) * H * s ^ 2 ∧
          cubicANumerator68 t r = H * A1 ∧
          c2 = C (1 / 3 : k) * A1 ^ 2 + C (9 / 4 : k) * w2 -
            C (3 / 2 * S.gamma : k) ∧
          cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r = H ^ 2 * c2 ∧
          e3 = p.coeff 0 - C (1 / 6 : k) * p.coeff 1 * s +
              C (1 / 36 : k) * p.coeff 2 * s ^ 2 -
              C (1 / 216 : k) * H * y1 * s ^ 3 +
              C (1 / 1296 : k) * H ^ 2 * t1 * s ^ 4 -
              C (5 / 46656 : k) * H ^ 3 * s ^ 6 ∧
          cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) t r = H ^ 3 * e3 ∧
          terminalEDerivativeNumerator68 H
              (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
                (p.coeff 3) t r) = H ^ 4 * e3.derivative ∧
          psi = rDivisorLowerZeroPhiQuotient68 H A1 b2 c2 e3
            S.gamma S.epsilon ∧
          phi1 = H ^ 2 * psi ∧
          H ^ 2 ∣ phi1 ∧ H ∣ phi1 ∧
          w2 * d2 = -(C (1 / 6 : k)) * (H * b2 * psi) ∧
          H ∣ w2 * d2 ∧
          terminalLowerZeroCleared68 H (cubicANumerator68 t r) (H * b2)
            (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r) (H * d2)
            (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) t r)
            S.alpha S.gamma S.epsilon S.eta = 0 ∧
          terminalLowerZeroCleared68 H (H * A1) (H * b2) (H ^ 2 * c2)
            (H * d2) (H ^ 3 * e3) S.alpha S.gamma S.epsilon S.eta =
            H ^ 4 * rDivisorLowerZeroQuotient68 H A1 b2 c2 d2 e3
              S.alpha S.gamma S.epsilon S.eta ∧
          rDivisorLowerZeroQuotient68 H A1 b2 c2 d2 e3
            S.alpha S.gamma S.epsilon S.eta = 0 ∧
          H ∣ d2 * psi ∧
          (∀ a : k, H.eval a = 0 →
            (w2 * d2).eval a = 0 ∧ (d2 * psi).eval a = 0 ∧
              d2.eval a * k1.eval a = 0) ∧
          m = H * b2 * w2 * e3.derivative - C j ∧
          d2 * k1 = H ^ 4 * m ∧
          H ^ 4 ∣ d2 * k1 ∧
          (∀ a : k, H.eval a = 0 → m.eval a = -j ∧ m.eval a ≠ 0) ∧
          d2 ≠ 0 ∧ k1 ≠ 0 ∧
          ((∃ d3 d4 b3 : k[X],
              d2 = H * d3 ∧ d3 = H * d4 ∧ d2 = H ^ 2 * d4 ∧
              b2 = H * b3 ∧ H ∣ b2 ∧
              b3 * psi = -(6 : k[X]) * (w2 * d4) ∧
              d4 * k1 = H ^ 2 * m ∧ d4 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                b2.eval a = 0 ∧
                b3.eval a * psi.eval a =
                  -(6 : k) * (w2.eval a * d4.eval a) ∧
                d4.eval a * k1.eval a = 0 ∧
                c2.eval a * (b2.eval a * w2.eval a) = 0 ∧
                d4.derivative.eval a * k1.eval a +
                  d4.eval a * k1.derivative.eval a = 0 ∧
                d4.derivative.derivative.eval a * k1.eval a +
                  2 * (d4.derivative.eval a * k1.derivative.eval a) +
                  d4.eval a * k1.derivative.derivative.eval a =
                  -(2 * j) * H.derivative.eval a ^ 2 ∧
                b2.derivative.eval a * psi.eval a +
                  b2.eval a * psi.derivative.eval a =
                  -(6 : k) *
                    (H.derivative.eval a *
                      (w2.eval a * d4.eval a)))) ∨
            (∃ psi2 d3 D : k[X],
              psi = H * psi2 ∧ H ∣ psi ∧
              phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              d2 = H * d3 ∧ d3 = H * D ∧ d2 = H ^ 2 * D ∧
              b2 * psi2 = -(6 : k[X]) * (w2 * D) ∧
              w2 * d2 = -(C (1 / 6 : k)) * (H ^ 2 * (b2 * psi2)) ∧
              D * k1 = H ^ 2 * m ∧ D ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧ d3.eval a = 0 ∧
                b2.eval a * psi2.eval a =
                  -(6 : k) * (w2.eval a * D.eval a) ∧
                D.eval a * k1.eval a = 0 ∧
                c2.eval a *
                  (rDivisorDTwoUOne68 A1 b2 c2 d3
                    S.alpha S.gamma).eval a = 0) ∧
              ((∀ a : k, H.eval a = 0 →
                  D.derivative.eval a * k1.eval a +
                    D.eval a * k1.derivative.eval a = 0 ∧
                  D.derivative.derivative.eval a * k1.eval a +
                    2 * (D.derivative.eval a * k1.derivative.eval a) +
                    D.eval a * k1.derivative.derivative.eval a =
                    -(2 * j) * H.derivative.eval a ^ 2 ∧
                  b2.derivative.eval a * psi.eval a +
                    b2.eval a * psi.derivative.eval a =
                    -(6 : k) *
                      (H.derivative.eval a *
                        (w2.eval a * D.eval a))) ∨
                (∀ a : k, H.eval a = 0 →
                  d3.derivative.eval a * k1.eval a +
                    d3.eval a * k1.derivative.eval a = 0 ∧
                  d3.derivative.derivative.eval a * k1.eval a +
                    2 * (d3.derivative.eval a *
                      k1.derivative.eval a) +
                    d3.eval a * k1.derivative.derivative.eval a = 0 ∧
                  w2.derivative.eval a * d3.eval a +
                    w2.eval a * d3.derivative.eval a =
                    -(1 / 6 : k) *
                      (H.derivative.eval a *
                        (b2.eval a * psi2.eval a))))) ∨
            (∃ psi2 w3 w4 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 = H * w3 ∧ w3 = H * w4 ∧ w2 = H ^ 2 * w4 ∧
              w4 * d2 = -(C (1 / 6 : k)) * (b2 * psi2) ∧
              w2 * d2 = -(C (1 / 6 : k)) * (H ^ 2 * (b2 * psi2)) ∧
              H ∣ rDivisorBetaNumerator68 A1 e3 S.gamma S.epsilon ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧ w2.eval a = 0 ∧ w3.eval a = 0 ∧
                w2.derivative.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon = 0 ∧
                d2.eval a * k1.eval a = 0)) ∨
            (∃ psi2 w3 d3 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 = H * w3 ∧ d2 = H * d3 ∧ d3 ≠ 0 ∧
              w3 * d3 = -(C (1 / 6 : k)) * (b2 * psi2) ∧
              d3 * k1 = H ^ 3 * m ∧
              H ∣ rDivisorBetaNumerator68 A1 e3 S.gamma S.epsilon ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧ w2.eval a = 0 ∧ d2.eval a = 0 ∧
                d3.eval a * k1.eval a = 0 ∧
                (rDivisorLowerZeroTThree68 H A1 b2 c2 e3
                    S.alpha S.gamma S.epsilon).eval a * d3.eval a =
                  c2.eval a *
                    (rDivisorDTwoUOne68 A1 b2 c2 d3
                      S.alpha S.gamma).eval a ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon = 0) ∧
              ((∀ a : k, H.eval a = 0 →
                  w2.derivative.eval a =
                    H.derivative.eval a * w3.eval a ∧
                  w3.derivative.eval a * d2.eval a +
                    w3.eval a * d2.derivative.eval a =
                    -(1 / 6 : k) *
                      (H.derivative.eval a *
                        (b2.eval a * psi2.eval a)) ∧
                  d2.derivative.eval a * k1.eval a +
                    d2.eval a * k1.derivative.eval a = 0) ∨
                (∀ a : k, H.eval a = 0 →
                  d3.derivative.eval a * k1.eval a +
                    d3.eval a * k1.derivative.eval a = 0 ∧
                  d3.derivative.derivative.eval a * k1.eval a +
                    2 * (d3.derivative.eval a *
                      k1.derivative.eval a) +
                    d3.eval a * k1.derivative.derivative.eval a = 0 ∧
                  w2.derivative.eval a * d3.eval a +
                    w2.eval a * d3.derivative.eval a =
                    -(1 / 6 : k) *
                      (H.derivative.eval a *
                        (b2.eval a * psi2.eval a))))) ∨
            (∃ d3 k2 d5 d7 : k[X],
              d2 = H * d3 ∧ d3 = H * d5 ∧ d5 = H * d7 ∧
              d2 = H ^ 3 * d7 ∧ k1 = H * k2 ∧
              d7 * k2 = m ∧
              d7 * k2 + C j = H * b2 * w2 * e3.derivative ∧
              b2 * psi = -(6 : k[X]) * (H ^ 2 * (w2 * d7)) ∧
              H ∣ b2 * psi ∧ d7 ≠ 0 ∧ k2 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                d7.eval a * k2.eval a = -j ∧
                d7.eval a ≠ 0 ∧ k2.eval a ≠ 0 ∧
                d3.derivative.eval a = 0 ∧
                d3.derivative.derivative.eval a * k2.eval a =
                  -(2 * j) * H.derivative.eval a ^ 2 ∧
                d3.derivative.derivative.eval a ≠ 0)) ∨
            (∃ d3 k2 d5 k3 : k[X],
              d2 = H * d3 ∧ d3 = H * d5 ∧ d2 = H ^ 2 * d5 ∧
              k1 = H * k2 ∧ k2 = H * k3 ∧ k1 = H ^ 2 * k3 ∧
              d5 * k3 = m ∧
              d5 * k3 + C j = H * b2 * w2 * e3.derivative ∧
              b2 * psi = -(6 : k[X]) * (H * (w2 * d5)) ∧
              H ∣ b2 * psi ∧ d5 ≠ 0 ∧ k3 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                d5.eval a * k3.eval a = -j ∧
                d5.eval a ≠ 0 ∧ k3.eval a ≠ 0 ∧
                d3.derivative.eval a * k2.derivative.eval a =
                  -j * H.derivative.eval a ^ 2 ∧
                d3.derivative.eval a ≠ 0 ∧
                k2.derivative.eval a ≠ 0)) ∨
            (∃ d3 k2 k3 k4 : k[X],
              d2 = H * d3 ∧ k1 = H * k2 ∧ k2 = H * k3 ∧
              k3 = H * k4 ∧ k1 = H ^ 3 * k4 ∧
              d3 * k4 = m ∧
              d3 * k4 + C j = H * b2 * w2 * e3.derivative ∧
              w2 * d3 = -(C (1 / 6 : k)) * (b2 * psi) ∧
              d3 ≠ 0 ∧ k4 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                d3.eval a * k4.eval a = -j ∧
                d3.eval a ≠ 0 ∧ k4.eval a ≠ 0 ∧
                k2.derivative.eval a = 0 ∧
                d3.eval a * k2.derivative.derivative.eval a =
                  -(2 * j) * H.derivative.eval a ^ 2 ∧
                k2.derivative.derivative.eval a ≠ 0)) ∨
            (∃ d3 k2 d5 : k[X],
              d2 = H * d3 ∧ d3 = H * d5 ∧ d2 = H ^ 2 * d5 ∧
              k1 = H * k2 ∧
              d5 * k2 = H * m ∧
              b2 * psi = -(6 : k[X]) * (H * (w2 * d5)) ∧
              H ∣ b2 * psi ∧ d5 ≠ 0 ∧ k2 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                k2.eval x = 0 ∧
                d3.derivative.eval x * k2.derivative.eval x =
                  -j * H.derivative.eval x ^ 2 ∧
                d3.derivative.eval x ≠ 0 ∧
                k2.derivative.eval x ≠ 0 ∧
                k2.eval y ≠ 0 ∧ d5.eval y = 0 ∧
                d3.derivative.eval y = 0 ∧
                d3.derivative.derivative.eval y * k2.eval y =
                  -(2 * j) * H.derivative.eval y ^ 2 ∧
                d3.derivative.derivative.eval y ≠ 0) ∨
            (∃ d3 k2 k3 : k[X],
              d2 = H * d3 ∧ k1 = H * k2 ∧ k2 = H * k3 ∧
              k1 = H ^ 2 * k3 ∧
              d3 * k3 = H * m ∧
              w2 * d3 = -(C (1 / 6 : k)) * (b2 * psi) ∧
              d3 ≠ 0 ∧ k3 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                d3.eval x = 0 ∧
                d3.derivative.eval x * k2.derivative.eval x =
                  -j * H.derivative.eval x ^ 2 ∧
                d3.derivative.eval x ≠ 0 ∧
                k2.derivative.eval x ≠ 0 ∧
                d3.eval y ≠ 0 ∧ k3.eval y = 0 ∧
                k2.derivative.eval y = 0 ∧
                d3.eval y * k2.derivative.derivative.eval y =
                  -(2 * j) * H.derivative.eval y ^ 2 ∧
                k2.derivative.derivative.eval y ≠ 0) ∨
            (∃ d3 k2 : k[X],
              d2 = H * d3 ∧ k1 = H * k2 ∧ d3 * k2 = H ^ 2 * m ∧
              w2 * d3 = -(C (1 / 6 : k)) * (b2 * psi) ∧
              d3 ≠ 0 ∧ k2 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                d3.eval x = 0 ∧ k2.eval x ≠ 0 ∧
                d3.eval y ≠ 0 ∧ k2.eval y = 0 ∧
                d3.derivative.eval x = 0 ∧
                d3.derivative.derivative.eval x * k2.eval x =
                  -(2 * j) * H.derivative.eval x ^ 2 ∧
                d3.derivative.derivative.eval x ≠ 0 ∧
                k2.derivative.eval y = 0 ∧
                d3.eval y * k2.derivative.derivative.eval y =
                  -(2 * j) * H.derivative.eval y ^ 2 ∧
                k2.derivative.derivative.eval y ≠ 0 ∧
                H ∣ d3.derivative * k2.derivative) ∨
            (∃ d3 d4 : k[X],
              d2 = H * d3 ∧ d3 = H * d4 ∧ d2 = H ^ 2 * d4 ∧
              b2 * psi = -(6 : k[X]) * (H * (w2 * d4)) ∧
              H ∣ b2 * psi ∧
              d4 * k1 = H ^ 2 * m ∧ d4 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                b2.eval x = 0 ∧ psi.eval x ≠ 0 ∧
                b2.eval y ≠ 0 ∧ psi.eval y = 0 ∧
                b2.derivative.eval x * psi.eval x =
                  -(6 : k) *
                    (H.derivative.eval x *
                      (w2.eval x * d4.eval x)) ∧
                b2.eval y * psi.derivative.eval y =
                  -(6 : k) *
                    (H.derivative.eval y *
                      (w2.eval y * d4.eval y)) ∧
                (c2.eval y = 0 ∨ w2.eval y = 0)) ∨
            (∃ d3 : k[X],
              d2 = H * d3 ∧
              w2 * d3 = -(C (1 / 6 : k)) * (b2 * psi) ∧
              d3 * k1 = H ^ 3 * m ∧ d3 ≠ 0 ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
                d3.eval a = 0 ∧ k1.eval a ≠ 0 ∧
                d3.eval b ≠ 0 ∧ k1.eval b = 0 ∧
                d3.derivative.eval a = 0 ∧
                d3.derivative.derivative.eval a = 0 ∧
                b2.eval a * psi.eval a = 0 ∧
                k1.derivative.eval b = 0 ∧
                k1.derivative.derivative.eval b = 0 ∧
                d3.derivative.derivative.derivative.eval a *
                    k1.eval a =
                  -(6 * j) * H.derivative.eval a ^ 3 ∧
                d3.derivative.derivative.derivative.eval a ≠ 0 ∧
                d3.eval b *
                    k1.derivative.derivative.derivative.eval b =
                  -(6 * j) * H.derivative.eval b ^ 3 ∧
                k1.derivative.derivative.derivative.eval b ≠ 0 ∧
                H ∣ d3.derivative * k1.derivative ∧
                H ∣ d3.derivative.derivative *
                  k1.derivative.derivative ∧
                (b2.eval a = 0 ∨ psi.eval a = 0) ∧
                (c2.eval a = 0 ∨
                  (rDivisorDTwoUOne68 A1 b2 c2 d3
                    S.alpha S.gamma).eval a = 0) ∧
                b2.eval b * psi.eval b =
                  -(6 : k) * (w2.eval b * d3.eval b)) ∨
            (∃ psi2 w3 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 = H * w3 ∧
              w3 * d2 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) ∧
              H ∣ rDivisorBetaNumerator68 A1 e3 S.gamma S.epsilon ∧
              (∀ a : k, H.eval a = 0 →
                w2.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon = 0) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w3.eval x = 0 ∧ d2.eval x ≠ 0 ∧
                w3.eval y ≠ 0 ∧ d2.eval y = 0 ∧
                w2.derivative.eval x = 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                w3.derivative.eval x * d2.eval x =
                  -(1 / 6 : k) *
                    (H.derivative.eval x *
                      (b2.eval x * psi2.eval x)) ∧
                w2.derivative.eval y ≠ 0 ∧
                w3.eval y * d2.derivative.eval y =
                  -(1 / 6 : k) *
                    (H.derivative.eval y *
                      (b2.eval y * psi2.eval y)) ∧
                d2.derivative.eval y = 0 ∧
                b2.eval y * psi2.eval y = 0 ∧
                (b2.eval y = 0 ∨ psi2.eval y = 0)) ∨
            (∃ psi2 w3 k2 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 = H * w3 ∧
              w3 * d2 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) ∧
              H ∣ rDivisorBetaNumerator68 A1 e3 S.gamma S.epsilon ∧
              (∀ a : k, H.eval a = 0 →
                w2.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon = 0) ∧
              k1 = H * k2 ∧ k2 ≠ 0 ∧ d2 * k2 = H ^ 3 * m ∧
              (∀ a : k, H.eval a = 0 →
                d2.eval a * k2.eval a = 0) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w3.eval x = 0 ∧ d2.eval x ≠ 0 ∧ k2.eval x = 0 ∧
                w3.eval y ≠ 0 ∧ d2.eval y = 0 ∧
                d2.derivative.eval y ≠ 0 ∧
                w2.derivative.eval x = 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.eval y = 0 ∧
                w2.derivative.eval y ≠ 0 ∧
                w3.derivative.eval x * d2.eval x =
                  -(1 / 6 : k) *
                    (H.derivative.eval x *
                      (b2.eval x * psi2.eval x)) ∧
                w3.eval y * d2.derivative.eval y =
                  -(1 / 6 : k) *
                    (H.derivative.eval y *
                      (b2.eval y * psi2.eval y))) ∨
            (∃ psi2 d3 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              d2 = H * d3 ∧ d3 ≠ 0 ∧
              w2 * d3 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) ∧
              d3 * k1 = H ^ 3 * m ∧
              H ∣ rDivisorPsiDivisorBetaGap68 A1 e3 w2
                S.gamma S.epsilon ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon =
                  2 * A1.eval a * w2.eval a) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w2.eval x = 0 ∧ d3.eval x ≠ 0 ∧
                w2.eval y ≠ 0 ∧ d3.eval y = 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.derivative.derivative.eval x = 0 ∧
                (4 / 3 : k) * e3.eval x -
                    (4 / 81 : k) * A1.eval x ^ 3 +
                    2 / 3 * S.gamma * A1.eval x + S.epsilon = 0 ∧
                w2.derivative.eval x * d3.eval x =
                  -(1 / 6 : k) *
                    (H.derivative.eval x *
                      (b2.eval x * psi2.eval x)) ∧
                (c2.eval y = 0 ∨
                  (rDivisorDTwoUOne68 A1 b2 c2 d3
                    S.alpha S.gamma).eval y = 0) ∧
                d3.derivative.eval y = 0 ∧
                b2.eval y * psi2.eval y = 0 ∧
                (b2.eval y = 0 ∨ psi2.eval y = 0) ∧
                d3.derivative.derivative.eval y * k1.eval y = 0) ∨
            (∃ psi2 d3 k2 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              d2 = H * d3 ∧ k1 = H * k2 ∧ d3 * k2 = H ^ 2 * m ∧
              w2 * d3 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) ∧
              d3 ≠ 0 ∧ k2 ≠ 0 ∧
              H ∣ rDivisorPsiDivisorBetaGap68 A1 e3 w2
                S.gamma S.epsilon ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧
                d3.eval a * k2.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon =
                  2 * A1.eval a * w2.eval a) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w2.eval x = 0 ∧ d3.eval x ≠ 0 ∧ k2.eval x = 0 ∧
                w2.eval y ≠ 0 ∧ d3.eval y = 0 ∧
                d3.derivative.eval y ≠ 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.derivative.derivative.eval x = 0 ∧
                k1.eval y = 0 ∧ k1.derivative.eval y = 0 ∧
                (4 / 3 : k) * e3.eval x -
                    (4 / 81 : k) * A1.eval x ^ 3 +
                    2 / 3 * S.gamma * A1.eval x + S.epsilon = 0 ∧
                w2.derivative.eval x * d3.eval x =
                  -(1 / 6 : k) *
                    (H.derivative.eval x *
                      (b2.eval x * psi2.eval x)) ∧
                (c2.eval y = 0 ∨
                  (rDivisorDTwoUOne68 A1 b2 c2 d3
                    S.alpha S.gamma).eval y = 0)) ∨
            (∃ psi2 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 * d2 = -(C (1 / 6 : k)) * (H ^ 2 * (b2 * psi2)) ∧
              H ∣ rDivisorPsiDivisorBetaGap68 A1 e3 w2
                S.gamma S.epsilon ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon =
                  2 * A1.eval a * w2.eval a) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w2.eval x = 0 ∧ d2.eval x ≠ 0 ∧
                w2.eval y ≠ 0 ∧ d2.eval y = 0 ∧
                w2.derivative.eval x = 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.derivative.derivative.eval x = 0 ∧
                k1.derivative.derivative.derivative.eval x = 0 ∧
                d2.eval x *
                    k1.derivative.derivative.derivative.derivative.eval
                      x =
                  -(24 * j) * H.derivative.eval x ^ 4 ∧
                k1.derivative.derivative.derivative.derivative.eval
                    x ≠ 0 ∧
                (4 / 3 : k) * e3.eval x -
                    (4 / 81 : k) * A1.eval x ^ 3 +
                    2 / 3 * S.gamma * A1.eval x + S.epsilon = 0 ∧
                d2.derivative.eval y = 0 ∧
                d2.derivative.derivative.eval y = 0 ∧
                b2.eval y * psi2.eval y = 0 ∧
                (b2.eval y = 0 ∨ psi2.eval y = 0) ∧
                d2.derivative.derivative.derivative.eval y *
                  k1.eval y = 0 ∧
                (d2.derivative.derivative.derivative.eval y = 0 ∨
                  k1.eval y = 0) ∧
                H ∣ w2 * d2.derivative ∧
                H ∣ k1 * d2.derivative) ∨
            (∃ psi2 k2 : k[X],
              psi = H * psi2 ∧ phi1 = H ^ 3 * psi2 ∧ H ^ 3 ∣ phi1 ∧
              w2 * d2 = -(C (1 / 6 : k)) * (H ^ 2 * (b2 * psi2)) ∧
              H ∣ rDivisorPsiDivisorBetaGap68 A1 e3 w2
                S.gamma S.epsilon ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon =
                  2 * A1.eval a * w2.eval a) ∧
              k1 = H * k2 ∧ k2 ≠ 0 ∧ d2 * k2 = H ^ 3 * m ∧
              (∀ a : k, H.eval a = 0 →
                d2.eval a * k2.eval a = 0) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                w2.eval x = 0 ∧ d2.eval x ≠ 0 ∧ k2.eval x = 0 ∧
                w2.eval y ≠ 0 ∧ d2.eval y = 0 ∧
                d2.derivative.eval y = 0 ∧
                d2.derivative.derivative.eval y ≠ 0 ∧
                b2.eval y ≠ 0 ∧ psi2.eval y ≠ 0 ∧
                k1.eval y = 0 ∧ k1.derivative.eval y = 0 ∧
                w2.derivative.eval x = 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.derivative.derivative.eval x = 0 ∧
                k1.derivative.derivative.derivative.eval x = 0 ∧
                d2.eval x *
                    k1.derivative.derivative.derivative.derivative.eval
                      x =
                  -(24 * j) * H.derivative.eval x ^ 4 ∧
                k1.derivative.derivative.derivative.derivative.eval
                    x ≠ 0 ∧
                (4 / 3 : k) * e3.eval x -
                    (4 / 81 : k) * A1.eval x ^ 3 +
                    2 / 3 * S.gamma * A1.eval x + S.epsilon = 0 ∧
                w2.eval y * d2.derivative.derivative.eval y =
                  -(1 / 3 : k) * (H.derivative.eval y ^ 2 *
                    (b2.eval y * psi2.eval y)) ∧
                H ∣ w2 * d2.derivative ∧
                H ∣ k1 * d2.derivative) ∨
            (∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
              d2.eval x = 0 ∧ psi.eval x ≠ 0 ∧
              d2.eval y ≠ 0 ∧ psi.eval y = 0 ∧
              d2.derivative.eval x = 0 ∧ b2.eval x = 0 ∧
              w2.eval y = 0 ∧ k1.eval y = 0 ∧
              w2.derivative.eval y = 0 ∧ k1.derivative.eval y = 0 ∧
              k1.derivative.derivative.eval y = 0 ∧
              k1.derivative.derivative.derivative.eval y = 0 ∧
              (4 / 3 : k) * e3.eval y -
                  (4 / 81 : k) * A1.eval y ^ 3 +
                  2 / 3 * S.gamma * A1.eval y + S.epsilon = 0 ∧
              d2.eval y *
                  k1.derivative.derivative.derivative.derivative.eval
                    y =
                -(24 * j) * H.derivative.eval y ^ 4 ∧
              k1.derivative.derivative.derivative.derivative.eval
                  y ≠ 0 ∧
              w2.derivative.derivative.eval y * d2.eval y =
                -(1 / 3 : k) * (H.derivative.eval y * b2.eval y *
                  psi.derivative.eval y) ∧
              d2.derivative.derivative.eval x * k1.eval x = 0 ∧
              (d2.derivative.derivative.eval x = 0 ∨
                k1.eval x = 0) ∧
              d2.derivative.derivative.derivative.eval x *
                  k1.eval x +
                3 * (d2.derivative.derivative.eval x *
                  k1.derivative.eval x) = 0 ∧
              H ∣ d2 * k1.derivative ∧ H ∣ d2 * w2.derivative) ∨
            (∃ k2 : k[X],
              k1 = H * k2 ∧ k2 ≠ 0 ∧ d2 * k2 = H ^ 3 * m ∧
              (∀ a : k, H.eval a = 0 →
                d2.eval a * k2.eval a = 0) ∧
              ∃ x y : k, x ≠ y ∧ H.eval x = 0 ∧ H.eval y = 0 ∧
                d2.eval x = 0 ∧ psi.eval x ≠ 0 ∧
                d2.eval y ≠ 0 ∧ psi.eval y = 0 ∧ k2.eval y = 0 ∧
                d2.derivative.eval x ≠ 0 ∧
                k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                k1.derivative.derivative.eval x = 0 ∧
                w2.eval y = 0 ∧ k1.eval y = 0 ∧
                w2.derivative.eval y = 0 ∧
                k1.derivative.eval y = 0 ∧
                k1.derivative.derivative.eval y = 0 ∧
                k1.derivative.derivative.derivative.eval y = 0 ∧
                (4 / 3 : k) * e3.eval y -
                    (4 / 81 : k) * A1.eval y ^ 3 +
                    2 / 3 * S.gamma * A1.eval y + S.epsilon = 0 ∧
                d2.eval y *
                    k1.derivative.derivative.derivative.derivative.eval
                      y =
                  -(24 * j) * H.derivative.eval y ^ 4 ∧
                k1.derivative.derivative.derivative.derivative.eval
                    y ≠ 0 ∧
                w2.derivative.derivative.eval y * d2.eval y =
                  -(1 / 3 : k) * (H.derivative.eval y * b2.eval y *
                    psi.derivative.eval y) ∧
                H ∣ d2 * k1.derivative ∧
                H ∣ d2 * w2.derivative))) ∨
        H ∣ phi1 ∨
        (let A0 := cubicANumerator68 t r
         let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
         let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
           (p.coeff 3) t r
         let eDot := terminalEDerivativeNumerator68 H E0
         ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
           r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
           r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
           b2.eval a = 0 ∧
           b2.derivative.eval a * phi1.eval a +
             6 * H.derivative.eval a * w2.eval a * d2.eval a = 0 ∧
           (d2.eval a = 0 ∨ k1.eval a = 0) ∧
           H.derivative.eval a * b2.eval a * w2.eval a * eDot.eval a -
             (d2.derivative.eval a * k1.eval a +
               d2.eval a * k1.derivative.eval a) = 0 ∧
           b2.eval b * phi1.derivative.eval b +
             6 * H.derivative.eval b * w2.eval b * d2.eval b = 0 ∧
           H.derivative.eval b * b2.eval b * w2.eval b * eDot.eval b -
             (d2.derivative.eval b * k1.eval b +
               d2.eval b * k1.derivative.eval b) = 0 ∧
           (d2.eval b = 0 ∨ k1.eval b = 0))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, hbranch⟩ :=
    S.terminalAfterLowerOneRDivisorLowerZeroAllocationPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hI4, hrow, ?_⟩
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hmj : (-j : k) ≠ 0 := neg_ne_zero.mpr hj
  obtain ⟨u, v, huv, hu, hv⟩ :=
    rDivisorReduction_root_pair_exists_68 H hdeg hsimple
  rcases hbranch with hmain | hphiDvd | htrans
  · left
    obtain ⟨s, t1, y1, A1, c2, e3, psi, m, hs, ht1c, ht1sc, hp4sc,
        hy1c, hy1sc, hdvdt, hdvdp4, hdvdp3, hA1def, hAf, hc2def, hCf,
        he3def, hEf, heDot, hpsidef, hphi2, hphidvd2, hphidvd1, hwd,
        hwddvd, hlowerB, hrowfact, hQ0, hdpsi, hfaces, hmdef, hdk,
        hdkdvd, hval, hd2ne, hk1ne, hsplit3⟩ := hmain
    refine ⟨s, t1, y1, A1, c2, e3, psi, m, hs, ht1c, ht1sc, hp4sc,
      hy1c, hy1sc, hdvdt, hdvdp4, hdvdp3, hA1def, hAf, hc2def, hCf,
      he3def, hEf, heDot, hpsidef, hphi2, hphidvd2, hphidvd1, hwd,
      hwddvd, hlowerB, hrowfact, hQ0, hdpsi, hfaces, hmdef, hdk,
      hdkdvd, hval, hd2ne, hk1ne, ?_⟩
    have hmne : m ≠ 0 := by
      intro h0
      have h1 := (hval u hu).2
      rw [h0] at h1
      simp at h1
    rcases hsplit3 with hA | hB | hC
    · -- The coordinate `d₂ = H·d₃` child.
      obtain ⟨d3, hd3, hd2dvd, hwdA, hdkA, hdk3dvd, hQfact, hQ3,
          hAfaces, hd3ne, hdvd1, hAsplit⟩ := hA
      rcases hAsplit with hA1 | hA2 | hA3
      · -- The `d₄` grandchild.
        obtain ⟨d4, hd4, hd2d4, hd2dvd2, hbpsi, hbpsidvd, hd4k,
            hd4kdvd, hA1faces, hd4ne, hA1seventh, hA1alloc⟩ := hA1
        have hd3z : ∀ a : k, H.eval a = 0 → d3.eval a = 0 := by
          intro a ha
          rw [hd4, eval_mul, ha, zero_mul]
        rcases hA1alloc with hA1a | hA1b | hA1c
        · -- `H ∣ b₂` merges into the `b`-divisor leaf.
          obtain ⟨b3, hb3, hb2dvd', hcoreA, hA1aFaces⟩ := hA1a
          left
          exact ⟨d3, d4, b3, hd3, hd4, hd2d4, hb3, hb2dvd', hcoreA,
            hd4k, hd4ne, hQ3, fun a ha =>
              ⟨(hA1aFaces a ha).1, (hA1aFaces a ha).2,
                (hA1faces a ha).2.1, (hA1faces a ha).2.2,
                (hA1seventh a ha).1, (hA1seventh a ha).2.1,
                (hA1seventh a ha).2.2⟩⟩
        · -- `H ∣ ψ` merges into the balanced `ψ∩d²` regime.
          obtain ⟨psi3, hpsi3, hpsidvd', hcoreB, hphi3', hphidvd3,
              hwd2, hA1bFaces⟩ := hA1b
          right; left
          refine ⟨psi3, d3, d4, hpsi3, hpsidvd', hphi3', hphidvd3,
            hd3, hd4, hd2d4, hcoreB, hwd2, hd4k, hd4ne, hQ3, ?_, ?_⟩
          · intro a ha
            have hcu : c2.eval a *
                (rDivisorDTwoUOne68 A1 b2 c2 d3
                  S.alpha S.gamma).eval a = 0 := by
              have htie := (hAfaces a ha).1
              rw [hd3z a ha, mul_zero] at htie
              exact htie.symm
            exact ⟨(hA1bFaces a ha).1, hd3z a ha,
              (hA1bFaces a ha).2, (hA1faces a ha).2.1, hcu⟩
          · exact Or.inl (fun a ha => ⟨(hA1seventh a ha).1,
              (hA1seventh a ha).2.1, (hA1seventh a ha).2.2⟩)
        · -- Transverse `b₂/ψ` allocation leaf.
          obtain ⟨x, y, hxy, hx, hy, hb2x, hpsix, hb2y, hpsiy,
              htiex, htiey, hcw⟩ := hA1c
          iterate 10 right
          left
          exact ⟨d3, d4, hd3, hd4, hd2d4, hbpsi, hbpsidvd, hd4k,
            hd4ne, hQ3, x, y, hxy, hx, hy, hb2x, hpsix, hb2y, hpsiy,
            htiex, htiey, hcw⟩
      · -- The `k₁ = H·k₂` grandchild: resolve both dichotomies.
        obtain ⟨k2, hk2, hk1dvdH, hd3k2, hd3k2dvd, hA2faces, hk2ne,
            hA2seventh, hA2alloc⟩ := hA2
        rcases hA2alloc with hA2a | hA2b | hA2c
        · obtain ⟨d5, hd5, hd3dvdH, hd2d5, hd2dvdH2, hbpsi5, hd5k,
              hd5kdvd, hd5ne, hA2aFaces⟩ := hA2a
          have hd5k2z : ∀ a : k, H.eval a = 0 →
              d5.eval a * k2.eval a = 0 :=
            fun a ha => (hA2aFaces a ha).2.1
          rcases (hA2aFaces u hu).2.2 with
            ⟨hk2u, hpinu, hd3du, hk2du⟩ |
            ⟨hk2u, hd3du, hpinu, hd3ddu⟩
          · rcases (hA2aFaces v hv).2.2 with
              ⟨hk2v, hpinv, hd3dv, hk2dv⟩ |
              ⟨hk2v, hd3dv, hpinv, hd3ddv⟩
            · -- Both `k₂`-dead: the exact balanced `(2,2)` leaf.
              have hk2dvd2 : H ∣ k2 :=
                rDivisorSeventh_dvd_of_two_root_evals_68 H k2 hdeg
                  hsimple u v huv hu hv hk2u hk2v
              obtain ⟨k3, hk3⟩ := hk2dvd2
              have hd5k3 : d5 * k3 = m := by
                apply mul_left_cancel₀ hH
                have h' := hd5k
                rw [hk3] at h'
                linear_combination h'
              have hk1k3 : k1 = H ^ 2 * k3 := by
                rw [hk2, hk3]; ring
              have hk3ne : k3 ≠ 0 := by
                intro h0
                rw [h0, mul_zero] at hd5k3
                exact hmne hd5k3.symm
              have hsrc : d5 * k3 + C j =
                  H * b2 * w2 * e3.derivative := by
                rw [hd5k3, hmdef]; ring
              iterate 5 right
              left
              refine ⟨d3, k2, d5, k3, hd3, hd5, hd2d5, hk2, hk3,
                hk1k3, hd5k3, hsrc, hbpsi5,
                ⟨-(6 : k[X]) * (w2 * d5), by rw [hbpsi5]; ring⟩,
                hd5ne, hk3ne, hQ3, ?_⟩
              intro a ha
              have hk2a : k2.eval a = 0 := by
                rw [hk3, eval_mul, ha, zero_mul]
              have hprod : d5.eval a * k3.eval a = -j := by
                have h := congrArg (fun P : k[X] => P.eval a) hd5k3
                simp only [eval_mul] at h
                rw [h]
                exact (hval a ha).1
              have hd5a : d5.eval a ≠ 0 := by
                intro h0
                rw [h0, zero_mul] at hprod
                exact hmj hprod.symm
              have hk3a : k3.eval a ≠ 0 := by
                intro h0
                rw [h0, mul_zero] at hprod
                exact hmj hprod.symm
              rcases (hA2aFaces a ha).2.2 with
                ⟨_, hpin, hne1, hne2⟩ | ⟨hk2ane, _, _, _⟩
              · exact ⟨hprod, hd5a, hk3a, hpin, hne1, hne2⟩
              · exact absurd hk2a hk2ane
            · -- Mixed orientation: `k₂` dead at `u`, unit at `v`.
              have hd5v : d5.eval v = 0 :=
                (mul_eq_zero.mp (hd5k2z v hv)).resolve_right hk2v
              iterate 7 right
              left
              exact ⟨d3, k2, d5, hd3, hd5, hd2d5, hk2, hd5k, hbpsi5,
                ⟨-(6 : k[X]) * (w2 * d5), by rw [hbpsi5]; ring⟩,
                hd5ne, hk2ne, hQ3, u, v, huv, hu, hv, hk2u, hpinu,
                hd3du, hk2du, hk2v, hd5v, hd3dv, hpinv, hd3ddv⟩
          · rcases (hA2aFaces v hv).2.2 with
              ⟨hk2v, hpinv, hd3dv, hk2dv⟩ |
              ⟨hk2v, hd3dv, hpinv, hd3ddv⟩
            · -- Mixed orientation: `k₂` dead at `v`, unit at `u`.
              have hd5u : d5.eval u = 0 :=
                (mul_eq_zero.mp (hd5k2z u hu)).resolve_right hk2u
              iterate 7 right
              left
              exact ⟨d3, k2, d5, hd3, hd5, hd2d5, hk2, hd5k, hbpsi5,
                ⟨-(6 : k[X]) * (w2 * d5), by rw [hbpsi5]; ring⟩,
                hd5ne, hk2ne, hQ3, v, u, huv.symm, hv, hu, hk2v,
                hpinv, hd3dv, hk2dv, hk2u, hd5u, hd3du, hpinu,
                hd3ddu⟩
            · -- Both `k₂`-unit: the exact `(3,1)` leaf.
              have hd5u : d5.eval u = 0 :=
                (mul_eq_zero.mp (hd5k2z u hu)).resolve_right hk2u
              have hd5v : d5.eval v = 0 :=
                (mul_eq_zero.mp (hd5k2z v hv)).resolve_right hk2v
              have hd5dvd : H ∣ d5 :=
                rDivisorSeventh_dvd_of_two_root_evals_68 H d5 hdeg
                  hsimple u v huv hu hv hd5u hd5v
              obtain ⟨d7, hd7⟩ := hd5dvd
              have hd7k2 : d7 * k2 = m := by
                apply mul_left_cancel₀ hH
                have h' := hd5k
                rw [hd7] at h'
                linear_combination h'
              have hd2d7 : d2 = H ^ 3 * d7 := by
                rw [hd2d5, hd7]; ring
              have hbpsi7 : b2 * psi =
                  -(6 : k[X]) * (H ^ 2 * (w2 * d7)) := by
                rw [hbpsi5, hd7]; ring
              have hd7ne : d7 ≠ 0 := by
                intro h0
                rw [h0, zero_mul] at hd7k2
                exact hmne hd7k2.symm
              have hsrc : d7 * k2 + C j =
                  H * b2 * w2 * e3.derivative := by
                rw [hd7k2, hmdef]; ring
              iterate 4 right
              left
              refine ⟨d3, k2, d5, d7, hd3, hd5, hd7, hd2d7, hk2,
                hd7k2, hsrc, hbpsi7,
                ⟨-(6 : k[X]) * (H * (w2 * d7)),
                  by rw [hbpsi7]; ring⟩,
                hd7ne, hk2ne, hQ3, ?_⟩
              intro a ha
              have hprod : d7.eval a * k2.eval a = -j := by
                have h := congrArg (fun P : k[X] => P.eval a) hd7k2
                simp only [eval_mul] at h
                rw [h]
                exact (hval a ha).1
              have hd7a : d7.eval a ≠ 0 := by
                intro h0
                rw [h0, zero_mul] at hprod
                exact hmj hprod.symm
              have hk2a : k2.eval a ≠ 0 := by
                intro h0
                rw [h0, mul_zero] at hprod
                exact hmj hprod.symm
              rcases (hA2aFaces a ha).2.2 with
                ⟨hk2a0, _, _, _⟩ | ⟨_, hd3da, hpina, hd3dda⟩
              · exact absurd hk2a0 hk2a
              · exact ⟨hprod, hd7a, hk2a, hd3da, hpina, hd3dda⟩
        · obtain ⟨k3, hk3, hk2dvdH, hk1k3, hk1dvd2, hd3k3, hd3k3dvd,
              hk3ne, hA2bFaces⟩ := hA2b
          have hd3k3z : ∀ a : k, H.eval a = 0 →
              d3.eval a * k3.eval a = 0 :=
            fun a ha => (hA2bFaces a ha).2.1
          rcases (hA2bFaces u hu).2.2 with
            ⟨hd3u, hpinu, hd3du, hk2du⟩ |
            ⟨hd3u, hk2du, hpinu, hk2ddu⟩
          · rcases (hA2bFaces v hv).2.2 with
              ⟨hd3v, hpinv, hd3dv, hk2dv⟩ |
              ⟨hd3v, hk2dv, hpinv, hk2ddv⟩
            · -- Both `d₃`-dead: the exact balanced `(2,2)` leaf,
              -- reached through the mirrored dichotomy — it MERGES.
              have hd3dvd' : H ∣ d3 :=
                rDivisorSeventh_dvd_of_two_root_evals_68 H d3 hdeg
                  hsimple u v huv hu hv hd3u hd3v
              obtain ⟨d5, hd5eq⟩ := hd3dvd'
              have hd5k3 : d5 * k3 = m := by
                apply mul_left_cancel₀ hH
                have h' := hd3k3
                rw [hd5eq] at h'
                linear_combination h'
              have hd2d5 : d2 = H ^ 2 * d5 := by
                rw [hd3, hd5eq]; ring
              have hd5ne : d5 ≠ 0 := by
                intro h0
                rw [h0, zero_mul] at hd5k3
                exact hmne hd5k3.symm
              have hsrc : d5 * k3 + C j =
                  H * b2 * w2 * e3.derivative := by
                rw [hd5k3, hmdef]; ring
              have hwdA' := hwdA
              rw [hd5eq] at hwdA'
              have h6 : (6 : k[X]) * (H * (w2 * d5)) =
                  -(((6 : k[X]) * C (1 / 6 : k)) * (b2 * psi)) := by
                linear_combination (6 : k[X]) * hwdA'
              rw [rDivisorLowerZeroSixUnit68, one_mul] at h6
              have hbpsi5 : b2 * psi =
                  -(6 : k[X]) * (H * (w2 * d5)) := by
                linear_combination h6
              iterate 5 right
              left
              refine ⟨d3, k2, d5, k3, hd3, hd5eq, hd2d5, hk2, hk3,
                hk1k3, hd5k3, hsrc, hbpsi5,
                ⟨-(6 : k[X]) * (w2 * d5), by rw [hbpsi5]; ring⟩,
                hd5ne, hk3ne, hQ3, ?_⟩
              intro a ha
              have hd3a : d3.eval a = 0 := by
                rw [hd5eq, eval_mul, ha, zero_mul]
              have hprod : d5.eval a * k3.eval a = -j := by
                have h := congrArg (fun P : k[X] => P.eval a) hd5k3
                simp only [eval_mul] at h
                rw [h]
                exact (hval a ha).1
              have hd5a : d5.eval a ≠ 0 := by
                intro h0
                rw [h0, zero_mul] at hprod
                exact hmj hprod.symm
              have hk3a : k3.eval a ≠ 0 := by
                intro h0
                rw [h0, mul_zero] at hprod
                exact hmj hprod.symm
              rcases (hA2bFaces a ha).2.2 with
                ⟨_, hpin, hne1, hne2⟩ | ⟨hd3ane, _, _, _⟩
              · exact ⟨hprod, hd5a, hk3a, hpin, hne1, hne2⟩
              · exact absurd hd3a hd3ane
            · -- Mixed orientation: `d₃` dead at `u`, unit at `v`.
              have hk3v : k3.eval v = 0 :=
                (mul_eq_zero.mp (hd3k3z v hv)).resolve_left hd3v
              iterate 8 right
              left
              exact ⟨d3, k2, k3, hd3, hk2, hk3, hk1k3, hd3k3, hwdA,
                hd3ne, hk3ne, hQ3, u, v, huv, hu, hv, hd3u, hpinu,
                hd3du, hk2du, hd3v, hk3v, hk2dv, hpinv, hk2ddv⟩
          · rcases (hA2bFaces v hv).2.2 with
              ⟨hd3v, hpinv, hd3dv, hk2dv⟩ |
              ⟨hd3v, hk2dv, hpinv, hk2ddv⟩
            · -- Mixed orientation: `d₃` dead at `v`, unit at `u`.
              have hk3u : k3.eval u = 0 :=
                (mul_eq_zero.mp (hd3k3z u hu)).resolve_left hd3u
              iterate 8 right
              left
              exact ⟨d3, k2, k3, hd3, hk2, hk3, hk1k3, hd3k3, hwdA,
                hd3ne, hk3ne, hQ3, v, u, huv.symm, hv, hu, hd3v,
                hpinv, hd3dv, hk2dv, hd3u, hk3u, hk2du, hpinu,
                hk2ddu⟩
            · -- Both `d₃`-unit: the exact `(1,3)` leaf.
              have hk3u : k3.eval u = 0 :=
                (mul_eq_zero.mp (hd3k3z u hu)).resolve_left hd3u
              have hk3v : k3.eval v = 0 :=
                (mul_eq_zero.mp (hd3k3z v hv)).resolve_left hd3v
              have hk3dvd : H ∣ k3 :=
                rDivisorSeventh_dvd_of_two_root_evals_68 H k3 hdeg
                  hsimple u v huv hu hv hk3u hk3v
              obtain ⟨k4, hk4⟩ := hk3dvd
              have hd3k4 : d3 * k4 = m := by
                apply mul_left_cancel₀ hH
                have h' := hd3k3
                rw [hk4] at h'
                linear_combination h'
              have hk1k4 : k1 = H ^ 3 * k4 := by
                rw [hk1k3, hk4]; ring
              have hk4ne : k4 ≠ 0 := by
                intro h0
                rw [h0, mul_zero] at hd3k4
                exact hmne hd3k4.symm
              have hsrc : d3 * k4 + C j =
                  H * b2 * w2 * e3.derivative := by
                rw [hd3k4, hmdef]; ring
              iterate 6 right
              left
              refine ⟨d3, k2, k3, k4, hd3, hk2, hk3, hk4, hk1k4,
                hd3k4, hsrc, hwdA, hd3ne, hk4ne, hQ3, ?_⟩
              intro a ha
              have hk3a : k3.eval a = 0 := by
                rw [hk4, eval_mul, ha, zero_mul]
              have hprod : d3.eval a * k4.eval a = -j := by
                have h := congrArg (fun P : k[X] => P.eval a) hd3k4
                simp only [eval_mul] at h
                rw [h]
                exact (hval a ha).1
              have hd3a : d3.eval a ≠ 0 := by
                intro h0
                rw [h0, zero_mul] at hprod
                exact hmj hprod.symm
              have hk4a : k4.eval a ≠ 0 := by
                intro h0
                rw [h0, mul_zero] at hprod
                exact hmj hprod.symm
              rcases (hA2bFaces a ha).2.2 with
                ⟨hd3a0, _, _, _⟩ | ⟨_, hk2da, hpina, hk2dda⟩
              · exact absurd hd3a0 hd3a
              · exact ⟨hprod, hd3a, hk4a, hk2da, hpina, hk2dda⟩
        · -- Transverse `d₃/k₂` leaf, transported with its ambient.
          obtain ⟨x, y, hxy, hx, hy, hd3x, hk2x, hd3y, hk2y, hd3dx,
              hpinx, hd3ddx, hk2dy, hpiny, hk2ddy, hdvdD⟩ := hA2c
          iterate 9 right
          left
          exact ⟨d3, k2, hd3, hk2, hd3k2, hwdA, hd3ne, hk2ne, hQ3,
            x, y, hxy, hx, hy, hd3x, hk2x, hd3y, hk2y, hd3dx, hpinx,
            hd3ddx, hk2dy, hpiny, hk2ddy, hdvdD⟩
      · -- Transverse `d₃/k₁` leaf, transported with its ambient.
        obtain ⟨a, b, hab, ha, hb, hd3a, hk1a, hd3b, hk1b, hd3da,
            hd3dda, hbpsia, hk1db, hk1ddb, hpina, hd3ddda, hpinb,
            hk1dddb, hdvdDK1, hdvdDDKK, hsplit1, hsplit2,
            htieb⟩ := hA3
        iterate 11 right
        left
        exact ⟨d3, hd3, hwdA, hdkA, hd3ne, hQ3, a, b, hab, ha, hb,
          hd3a, hk1a, hd3b, hk1b, hd3da, hd3dda, hbpsia, hk1db,
          hk1ddb, hpina, hd3ddda, hpinb, hk1dddb, hdvdDK1, hdvdDDKK,
          hsplit1, hsplit2, htieb⟩
    · -- The `ψ = H·ψ₂` child.
      obtain ⟨psi2, hpsi2, hpsidvdH, hphi3, hphi3dvd, hwdB, hwd2dvd,
          hgapdvd, hBfaces, hBsplit⟩ := hB
      rcases hBsplit with hB1 | hB2 | hB3
      · obtain ⟨w3, hw3, hw2dvdH, hw3d, hw3ddvd, hgapbridge,
            hbetadvd, hB1faces, hB1seventh, hB1alloc⟩ := hB1
        rcases hB1alloc with hB1a | hB1b | hB1c
        · -- `H ∣ w₃`: the `w²`-deep leaf.
          obtain ⟨w4, hw4, hw3dvd', hw2w4, hw2dvd2, hw4d,
              hB1aFaces⟩ := hB1a
          right; right; left
          exact ⟨psi2, w3, w4, hpsi2, hphi3, hphi3dvd, hw3, hw4,
            hw2w4, hw4d, hwdB, hbetadvd, fun a ha =>
              ⟨(hBfaces a ha).1, (hB1faces a ha).1,
                (hB1aFaces a ha).1, (hB1aFaces a ha).2,
                (hB1faces a ha).2.2, (hfaces a ha).2.2⟩⟩
        · -- `H ∣ d₂` in the `w`-regime: the merged `ψ∩w∩d` leaf,
          -- with the quotient row and root tie threaded in through
          -- the standalone factor lemma.
          obtain ⟨d3, hd3', hd2dvd', hd3ne', hw3d3, hw2d3, hd3k1,
              hd3k1dvd, hB1bFaces⟩ := hB1b
          have hQ3' : rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
              S.alpha S.gamma S.epsilon S.eta = 0 := by
            have hz : H * rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 := by
              rw [← rDivisorDTwo_quotient_factor_68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta, ← hd3']
              exact hQ0
            exact (mul_eq_zero.mp hz).resolve_left hH
          iterate 3 right
          left
          refine ⟨psi2, w3, d3, hpsi2, hphi3, hphi3dvd, hw3, hd3',
            hd3ne', hw3d3, hd3k1, hbetadvd, hQ3', ?_, Or.inl ?_⟩
          · intro a ha
            exact ⟨(hBfaces a ha).1, (hB1faces a ha).1,
              (hB1bFaces a ha).1, (hB1bFaces a ha).2,
              (rDivisorDTwo_root_faces_68 H A1 b2 c2 d3 e3 k1 m
                S.alpha S.gamma S.epsilon S.eta hQ3' hd3k1 a ha
                (hsimple a ha)).1,
              (hB1faces a ha).2.2⟩
          · intro a ha
            exact ⟨(hB1seventh a ha).1, (hB1seventh a ha).2.1,
              (hB1seventh a ha).2.2⟩
        · -- Transverse `w₃/d₂` allocation.
          obtain ⟨x, y, hxy, hx, hy, hw3x, hd2x, hw3y, hd2y, hw2dx0,
              hk1x0, hk1dx0, htiex, hw2dy, htiey, hbranch1c⟩ := hB1c
          have hB1r : ∀ a : k, H.eval a = 0 →
              w2.eval a = 0 ∧
              (4 / 3 : k) * e3.eval a -
                  (4 / 81 : k) * A1.eval a ^ 3 +
                  2 / 3 * S.gamma * A1.eval a + S.epsilon = 0 :=
            fun a ha => ⟨(hB1faces a ha).1, (hB1faces a ha).2.2⟩
          rcases hbranch1c with ⟨hd2dy, hbp, hbpsplit⟩ |
            ⟨hd2dy, hk1y0, hk1dvd, k2, hk2', hk2ne', hd2k2⟩
          · -- The residual `b₂ψ₂`-split leaf.
            iterate 12 right
            left
            exact ⟨psi2, w3, hpsi2, hphi3, hphi3dvd, hw3, hw3d,
              hbetadvd, hB1r, x, y, hxy, hx, hy, hw3x, hd2x, hw3y,
              hd2y, hw2dx0, hk1x0, hk1dx0, htiex, hw2dy, htiey,
              hd2dy, hbp, hbpsplit⟩
          · -- The `{ψ,w,k}` consumer with its free `k₂`-root pin.
            have hd2k2z : ∀ a : k, H.eval a = 0 →
                d2.eval a * k2.eval a = 0 := by
              intro a ha
              have h := congrArg (fun P : k[X] => P.eval a) hd2k2
              simp only [eval_mul, eval_pow] at h
              linear_combination h + m.eval a * H.eval a ^ 2 * ha
            have hk2x0 : k2.eval x = 0 :=
              (mul_eq_zero.mp (hd2k2z x hx)).resolve_left hd2x
            iterate 13 right
            left
            exact ⟨psi2, w3, k2, hpsi2, hphi3, hphi3dvd, hw3, hw3d,
              hbetadvd, hB1r, hk2', hk2ne', hd2k2, hd2k2z, x, y,
              hxy, hx, hy, hw3x, hd2x, hk2x0, hw3y, hd2y, hd2dy,
              hw2dx0, hk1x0, hk1dx0, hk1y0, hw2dy, htiex, htiey⟩
      · obtain ⟨d3, hd3B, hd2dvdB, hwd3, hwd3dvd, hd3k, hd3kdvd,
            hQfactB, hQ3B, hB2faces, hd3neB, hB2seventh,
            hB2alloc⟩ := hB2
        rcases hB2alloc with hB2a | hB2b | hB2c
        · -- `H ∣ w₂` in the `d`-regime: the merged `ψ∩w∩d` leaf
          -- through the mirrored path.
          obtain ⟨w5, hw5, hw2dvd', hw5d3, hbeta, hB2aFaces⟩ := hB2a
          have hd2z : ∀ a : k, H.eval a = 0 → d2.eval a = 0 := by
            intro a ha
            rw [hd3B, eval_mul, ha, zero_mul]
          iterate 3 right
          left
          refine ⟨psi2, w5, d3, hpsi2, hphi3, hphi3dvd, hw5, hd3B,
            hd3neB, hw5d3, hd3k, hbeta, hQ3B, ?_, Or.inr ?_⟩
          · intro a ha
            exact ⟨(hBfaces a ha).1, (hB2aFaces a ha).1, hd2z a ha,
              (hB2faces a ha).2.1, (hB2faces a ha).1,
              (hB2aFaces a ha).2⟩
          · intro a ha
            exact ⟨(hB2seventh a ha).1, (hB2seventh a ha).2.1,
              (hB2seventh a ha).2.2⟩
        · -- `H ∣ d₃` in the `ψ`-regime: the merged `ψ∩d²` leaf
          -- through the mirrored path.
          obtain ⟨d6, hd6, hd3dvd', hd2d6, hd2dvd2', hd6ne, hw2d6,
              hd6k1, hd6k1dvd, hB2bFaces⟩ := hB2b
          have h6 : (6 : k[X]) * (w2 * d6) =
              -(((6 : k[X]) * C (1 / 6 : k)) * (b2 * psi2)) := by
            rw [hw2d6]; ring
          rw [rDivisorLowerZeroSixUnit68, one_mul] at h6
          have hcore6 : b2 * psi2 = -(6 : k[X]) * (w2 * d6) := by
            linear_combination h6
          right; left
          refine ⟨psi2, d3, d6, hpsi2, hpsidvdH, hphi3, hphi3dvd,
            hd3B, hd6, hd2d6, hcore6, hwdB, hd6k1, hd6ne, hQ3B,
            ?_, Or.inr ?_⟩
          · intro a ha
            have hd3a : d3.eval a = 0 := (hB2bFaces a ha).1
            have hcu : c2.eval a *
                (rDivisorDTwoUOne68 A1 b2 c2 d3
                  S.alpha S.gamma).eval a = 0 := by
              have htie := (hB2faces a ha).1
              rw [hd3a, mul_zero] at htie
              exact htie.symm
            have hbe : b2.eval a * psi2.eval a =
                -(6 : k) * (w2.eval a * d6.eval a) := by
              have h := congrArg (fun P : k[X] => P.eval a) hcore6
              simp only [eval_mul, eval_neg, eval_ofNat] at h
              linear_combination h
            exact ⟨(hBfaces a ha).1, hd3a, hbe,
              (hB2bFaces a ha).2, hcu⟩
          · intro a ha
            exact ⟨(hB2seventh a ha).1, (hB2seventh a ha).2.1,
              (hB2seventh a ha).2.2⟩
        · -- Transverse `w₂/d₃` allocation.
          obtain ⟨x, y, hxy, hx, hy, hw2x, hd3x, hw2y, hd3y, hk1x0,
              hk1dx0, hk1ddx0, hbetax, htiex, hcU,
              hbranch2c⟩ := hB2c
          rcases hbranch2c with ⟨hd3dy, hbp, hbpsplit, hddk1y⟩ |
            ⟨hd3dy, hk1y0, hk1dy0, hk1dvd, k2, hk2', hk2ne',
              hd3k2'⟩
          · -- The residual `b₂ψ₂`-split leaf.
            iterate 14 right
            left
            exact ⟨psi2, d3, hpsi2, hphi3, hphi3dvd, hd3B, hd3neB,
              hwd3, hd3k, hgapdvd, hQ3B, hBfaces, x, y, hxy, hx, hy,
              hw2x, hd3x, hw2y, hd3y, hk1x0, hk1dx0, hk1ddx0,
              hbetax, htiex, hcU, hd3dy, hbp, hbpsplit, hddk1y⟩
          · -- The `{ψ,d,k}` consumer re-based into the `d`-child
            -- `k₂`-regime, with its free `k₂`-root pin.
            have hd3k2z : ∀ a : k, H.eval a = 0 →
                d3.eval a * k2.eval a = 0 := by
              intro a ha
              have h := congrArg (fun P : k[X] => P.eval a) hd3k2'
              simp only [eval_mul, eval_pow] at h
              linear_combination h + m.eval a * H.eval a * ha
            have hk2x0 : k2.eval x = 0 :=
              (mul_eq_zero.mp (hd3k2z x hx)).resolve_left hd3x
            iterate 15 right
            left
            exact ⟨psi2, d3, k2, hpsi2, hphi3, hphi3dvd, hd3B, hk2',
              hd3k2', hwd3, hd3neB, hk2ne', hgapdvd, hQ3B,
              (fun a ha => ⟨(hBfaces a ha).1, hd3k2z a ha,
                (hBfaces a ha).2⟩),
              x, y, hxy, hx, hy, hw2x, hd3x, hk2x0, hw2y, hd3y,
              hd3dy, hk1x0, hk1dx0, hk1ddx0, hk1y0, hk1dy0, hbetax,
              htiex, hcU⟩
      · -- Transverse `w₂/d₂` grandchild.
        obtain ⟨x, y, hxy, hx, hy, hw2x, hd2x, hw2y, hd2y, hw2dx,
            hk1x, hk1dx, hk1ddx, hbetax, hd2dy, hd2ddk1y, hI4y,
            hk1dddx, hpin4x, hk1ddddx, hfacey, hdvdWD, hdvdKD,
            hbranch3⟩ := hB3
        rcases hbranch3 with
          ⟨hdd, hbp, hbpsplit, hd3k1y, hd3split⟩ |
          ⟨hdd, hk1y0, hk1dy0, hb2yne, hpsi2yne, hk1dvd, k2, hk2',
            hk2ne', hd2k2⟩
        · -- The residual `b₂ψ₂`-split leaf.
          iterate 16 right
          left
          exact ⟨psi2, hpsi2, hphi3, hphi3dvd, hwdB, hgapdvd,
            hBfaces, x, y, hxy, hx, hy, hw2x, hd2x, hw2y, hd2y,
            hw2dx, hk1x, hk1dx, hk1ddx, hk1dddx, hpin4x, hk1ddddx,
            hbetax, hd2dy, hdd, hbp, hbpsplit, hd3k1y, hd3split,
            hdvdWD, hdvdKD⟩
        · -- The `{ψ,k}` consumer with its free `k₂`-root pin.
          have hd2k2z : ∀ a : k, H.eval a = 0 →
              d2.eval a * k2.eval a = 0 := by
            intro a ha
            have h := congrArg (fun P : k[X] => P.eval a) hd2k2
            simp only [eval_mul, eval_pow] at h
            linear_combination h + m.eval a * H.eval a ^ 2 * ha
          have hk2x0 : k2.eval x = 0 :=
            (mul_eq_zero.mp (hd2k2z x hx)).resolve_left hd2x
          iterate 17 right
          left
          exact ⟨psi2, k2, hpsi2, hphi3, hphi3dvd, hwdB, hgapdvd,
            hBfaces, hk2', hk2ne', hd2k2, hd2k2z, x, y, hxy, hx, hy,
            hw2x, hd2x, hk2x0, hw2y, hd2y, hd2dy, hdd, hb2yne,
            hpsi2yne, hk1y0, hk1dy0, hw2dx, hk1x, hk1dx, hk1ddx,
            hk1dddx, hpin4x, hk1ddddx, hbetax, hI4y, hdvdWD,
            hdvdKD⟩
    · -- The transverse `d₂/ψ` child.
      obtain ⟨a, b, hab, ha, hb, hd2a, hpsia, hd2b, hpsib, hCf1,
          hCf2, hw2b, hk1b, hw2db, hk1db, hbetab, hCsecond, hk1ddb,
          hI4b, hfacea, hk1dddb, hpin4b, hk1ddddb, hdvdDK, hdvdDW,
          hCbranch⟩ := hC
      rcases hCbranch with ⟨hd2da, hb2a, hd2dda, hddsplit, hface3⟩ |
        ⟨hd2da, hk1a0, hk1da0, hk1dda0, hk1dvd, k2, hk2', hk2ne',
          hd2k2⟩
      · -- The residual `d₂'(a) = 0` leaf.
        iterate 18 right
        left
        exact ⟨a, b, hab, ha, hb, hd2a, hpsia, hd2b, hpsib, hd2da,
          hb2a, hw2b, hk1b, hw2db, hk1db, hk1ddb, hk1dddb, hbetab,
          hpin4b, hk1ddddb, hI4b, hd2dda, hddsplit, hface3, hdvdDK,
          hdvdDW⟩
      · -- The bare `{k}` consumer with its free `k₂`-root pin.
        have hd2k2z : ∀ z : k, H.eval z = 0 →
            d2.eval z * k2.eval z = 0 := by
          intro z hz
          have h := congrArg (fun P : k[X] => P.eval z) hd2k2
          simp only [eval_mul, eval_pow] at h
          linear_combination h + m.eval z * H.eval z ^ 2 * hz
        have hk2b0 : k2.eval b = 0 :=
          (mul_eq_zero.mp (hd2k2z b hb)).resolve_left hd2b
        iterate 19 right
        exact ⟨k2, hk2', hk2ne', hd2k2, hd2k2z, a, b, hab, ha, hb,
          hd2a, hpsia, hd2b, hpsib, hk2b0, hd2da, hk1a0, hk1da0,
          hk1dda0, hw2b, hk1b, hw2db, hk1db, hk1ddb, hk1dddb,
          hbetab, hpin4b, hk1ddddb, hI4b, hdvdDK, hdvdDW⟩
  · exact Or.inr (Or.inl hphiDvd)
  · exact Or.inr (Or.inr htrans)

end RDivisorLowerZeroAllocationReductionSource68

end Max11DegreeRoutes
