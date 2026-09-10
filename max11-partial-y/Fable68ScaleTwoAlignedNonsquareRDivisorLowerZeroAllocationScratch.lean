import Fable68ScaleTwoAlignedNonsquareRDivisorLowerZeroSeventhScratch

/-! # Allocation of the fresh product divisibilities across the two core roots

Every surviving leaf of the `H ∣ r` lower-zero allocation tree carries a
fresh global product divisibility produced by the Following/Seventh
refinements.  Here each of them is consumed by the two-root coordinate
allocation, with no further differentiation: only retained faces, unit
pins and evaluations are combined.

On the `d₄` grandchild the fresh `H ∣ b₂ψ` splits into `H ∣ b₂` (the
`I₄` relation de-cores to `b₃ψ = −6w₂d₄`), `H ∣ ψ` (the leaf merges into
the coordinate `ψ`-divisor regime one core power deeper: `φ₁ = H³ψ₃`,
`w₂d₂ = −(1/6)H²b₂ψ₃`, `b₂ψ₃ = −6w₂d₄`), or the transverse allocation
with the retained `(b₂ψ)'` face reduced at each root and the root factor
split `c₂(y) = 0 ∨ w₂(y) = 0`.  On the `k₂` grandchild the fresh
`H ∣ d₃k₂` splits into `H ∣ d₃` (merging into the `d₄`-shape
`d₂ = H²d₅` with `d₅k₂ = Hm` and, per root, the exclusive unit
dichotomy `d₃'k₂' = −jH'²` versus `d₃''k₂ = −2jH'²` from the retained
faces), `H ∣ k₂` (the symmetric merge `k₁ = H²k₃`, `d₃k₃ = Hm` with the
mirrored dichotomy), or the transverse allocation with exact order-two
pins `d₃''(x)k₂(x) = −2jH'(x)²`, `d₃(y)k₂''(y) = −2jH'(y)²` and the new
globalization `H ∣ d₃'k₂'`.  On the transverse `d₃/k₁` grandchild the
retained root products factor-split (`b₂(x) = 0 ∨ ψ(x) = 0`,
`c₂(x) = 0 ∨ U₁(x) = 0`) and the `I₄` quotient evaluates at the
`k₁`-root.

On the `w₃` grandchild the fresh `H ∣ w₃d₂` splits into `H ∣ w₃`
(`w₂ = H²w₄` with the de-cored `w₄d₂ = −(1/6)b₂ψ₂` and `w₂'` dead at
every root), `H ∣ d₂` (merging into the coordinate `d₃`-leaf with the
fully de-cored `w₃d₃ = −(1/6)b₂ψ₂` and `d₃k₁ = H³m`), or the transverse
allocation where `k₁` dies to order two at the `w₃`-root, `w₂'(y)` is a
unit, and the `d₂`-root splits exclusively into `d₂'(y) = 0` (forcing
`b₂(y)ψ₂(y) = 0`) versus `k₁(y) = 0` (globalizing to `H ∣ k₁` with
`d₂k₂ = H³m`).  On the `ψ`-regime `d₃` grandchild the fresh `H ∣ w₂d₃`
splits into `H ∣ w₂` (the `β`-numerator becomes globally divisible
through the gap bridge), `H ∣ d₃` (`d₂ = H²d₆`, `w₂d₆ = −(1/6)b₂ψ₂`,
`d₆k₁ = H²m`), or the transverse allocation with `k₁` dead to order
three at the `w₂`-root, the `β`-pin, the factor split
`c₂(y) = 0 ∨ U₁(y) = 0` and the exclusive `d₃'(y)` dichotomy again
globalizing to `H ∣ k₁`, `d₃k₂ = H²m` on its unit side.

On the transverse `w₂/d₂` grandchild the retained product
`d₂''(b)k₁(b) = 0` splits exclusively against the loaded `I₄` mate:
`d₂''(b) = 0` forces `b₂(b)ψ₂(b) = 0` with the reduced third face, while
`d₂''(b) ≠ 0` pins `b₂(b)`, `ψ₂(b)` as units, kills `k₁` to first order
at `b` and globalizes `H ∣ k₁`, `d₂k₂ = H³m`.  On the transverse `d₂/ψ`
child the retained `d₂'(a)k₁(a) = 0` splits exclusively: `d₂'(a) = 0`
forces `b₂(a) = 0` through the `I₄` tie (with `ψ(a)` a unit), while
`d₂'(a) ≠ 0` kills `k₁` to order three at `a` and again globalizes
`H ∣ k₁` with `d₂k₂ = H³m`.

No allocation closes (no `x`-degree bounds are available); the `H ∣ φ₁`
and outer transverse siblings are transported literally. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section RDivisorLowerZeroAllocationSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Allocation of the fresh global product divisibilities of the `H ∣ r`
lower-zero tree across the two simple core roots.  Each of the seven
leaves either globalizes one factor (merging into the coordinate sibling
regime one core power deeper, with the corresponding relation de-cored
exactly) or lands in an exclusive transverse allocation whose retained
faces and unit pins are combined at both roots; the joint `k₁`-zeros
globalize to `H ∣ k₁` with the cofactor relation descended.  No
allocation closes; the `H ∣ φ₁` and outer transverse siblings are
transported literally. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneRDivisorLowerZeroAllocationPacket
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
          ((∃ d3 : k[X],
              d2 = H * d3 ∧
              H ∣ d2 ∧
              w2 * d3 = -(C (1 / 6 : k)) * (b2 * psi) ∧
              d3 * k1 = H ^ 3 * m ∧
              H ^ 3 ∣ d3 * k1 ∧
              rDivisorLowerZeroQuotient68 H A1 b2 c2 (H * d3) e3
                  S.alpha S.gamma S.epsilon S.eta =
                H * rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                  S.alpha S.gamma S.epsilon S.eta ∧
              rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                S.alpha S.gamma S.epsilon S.eta = 0 ∧
              (∀ a : k, H.eval a = 0 →
                (rDivisorLowerZeroTThree68 H A1 b2 c2 e3
                    S.alpha S.gamma S.epsilon).eval a * d3.eval a =
                  c2.eval a *
                    (rDivisorDTwoUOne68 A1 b2 c2 d3
                      S.alpha S.gamma).eval a ∧
                d3.eval a * k1.eval a = 0) ∧
              d3 ≠ 0 ∧
              H ∣ d3 * k1 ∧
              ((∃ d4 : k[X],
                  d3 = H * d4 ∧
                  d2 = H ^ 2 * d4 ∧
                  H ^ 2 ∣ d2 ∧
                  b2 * psi = -(6 : k[X]) * (H * (w2 * d4)) ∧
                  H ∣ b2 * psi ∧
                  d4 * k1 = H ^ 2 * m ∧
                  H ^ 2 ∣ d4 * k1 ∧
                  (∀ a : k, H.eval a = 0 →
                    b2.eval a * psi.eval a = 0 ∧
                    d4.eval a * k1.eval a = 0 ∧
                    c2.eval a * (b2.eval a * w2.eval a) = 0) ∧
                  d4 ≠ 0 ∧
                  (∀ a : k, H.eval a = 0 →
                    d4.derivative.eval a * k1.eval a +
                      d4.eval a * k1.derivative.eval a = 0 ∧
                    d4.derivative.derivative.eval a * k1.eval a +
                      2 * (d4.derivative.eval a *
                        k1.derivative.eval a) +
                      d4.eval a * k1.derivative.derivative.eval a =
                      -(2 * j) * H.derivative.eval a ^ 2 ∧
                    b2.derivative.eval a * psi.eval a +
                      b2.eval a * psi.derivative.eval a =
                      -(6 : k) *
                        (H.derivative.eval a *
                          (w2.eval a * d4.eval a))) ∧
                  ((∃ b3 : k[X],
                      b2 = H * b3 ∧ H ∣ b2 ∧
                      b3 * psi = -(6 : k[X]) * (w2 * d4) ∧
                      (∀ a : k, H.eval a = 0 →
                        b2.eval a = 0 ∧
                        b3.eval a * psi.eval a =
                          -(6 : k) * (w2.eval a * d4.eval a))) ∨
                    (∃ psi3 : k[X],
                      psi = H * psi3 ∧ H ∣ psi ∧
                      b2 * psi3 = -(6 : k[X]) * (w2 * d4) ∧
                      phi1 = H ^ 3 * psi3 ∧ H ^ 3 ∣ phi1 ∧
                      w2 * d2 =
                        -(C (1 / 6 : k)) * (H ^ 2 * (b2 * psi3)) ∧
                      (∀ a : k, H.eval a = 0 →
                        psi.eval a = 0 ∧
                        b2.eval a * psi3.eval a =
                          -(6 : k) * (w2.eval a * d4.eval a))) ∨
                    (∃ x y : k, x ≠ y ∧
                      H.eval x = 0 ∧ H.eval y = 0 ∧
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
                      (c2.eval y = 0 ∨ w2.eval y = 0)))) ∨
                (∃ k2 : k[X],
                  k1 = H * k2 ∧
                  H ∣ k1 ∧
                  d3 * k2 = H ^ 2 * m ∧
                  H ^ 2 ∣ d3 * k2 ∧
                  (∀ a : k, H.eval a = 0 →
                    d3.eval a * k2.eval a = 0 ∧
                    d3.derivative.eval a * k2.eval a +
                      d3.eval a * k2.derivative.eval a = 0 ∧
                    d3.derivative.derivative.eval a * k2.eval a +
                      2 * (d3.derivative.eval a *
                        k2.derivative.eval a) +
                      d3.eval a * k2.derivative.derivative.eval a =
                      -(2 * j) * H.derivative.eval a ^ 2) ∧
                  k2 ≠ 0 ∧
                  (∀ a : k, H.eval a = 0 →
                    d3.derivative.derivative.derivative.eval a *
                        k2.eval a +
                      3 * (d3.derivative.derivative.eval a *
                        k2.derivative.eval a) +
                      3 * (d3.derivative.eval a *
                        k2.derivative.derivative.eval a) +
                      d3.eval a *
                        k2.derivative.derivative.derivative.eval a =
                      -(6 * j) *
                          (H.derivative.eval a *
                            H.derivative.derivative.eval a) +
                        6 * H.derivative.eval a ^ 3 *
                          (b2.eval a * w2.eval a *
                            e3.derivative.eval a)) ∧
                  ((∃ d5 : k[X],
                      d3 = H * d5 ∧ H ∣ d3 ∧
                      d2 = H ^ 2 * d5 ∧ H ^ 2 ∣ d2 ∧
                      b2 * psi = -(6 : k[X]) * (H * (w2 * d5)) ∧
                      d5 * k2 = H * m ∧ H ∣ d5 * k2 ∧ d5 ≠ 0 ∧
                      (∀ a : k, H.eval a = 0 →
                        d3.eval a = 0 ∧
                        d5.eval a * k2.eval a = 0 ∧
                        ((k2.eval a = 0 ∧
                            d3.derivative.eval a *
                                k2.derivative.eval a =
                              -j * H.derivative.eval a ^ 2 ∧
                            d3.derivative.eval a ≠ 0 ∧
                            k2.derivative.eval a ≠ 0) ∨
                          (k2.eval a ≠ 0 ∧
                            d3.derivative.eval a = 0 ∧
                            d3.derivative.derivative.eval a *
                                k2.eval a =
                              -(2 * j) *
                                H.derivative.eval a ^ 2 ∧
                            d3.derivative.derivative.eval a ≠
                              0)))) ∨
                    (∃ k3 : k[X],
                      k2 = H * k3 ∧ H ∣ k2 ∧
                      k1 = H ^ 2 * k3 ∧ H ^ 2 ∣ k1 ∧
                      d3 * k3 = H * m ∧ H ∣ d3 * k3 ∧ k3 ≠ 0 ∧
                      (∀ a : k, H.eval a = 0 →
                        k2.eval a = 0 ∧
                        d3.eval a * k3.eval a = 0 ∧
                        ((d3.eval a = 0 ∧
                            d3.derivative.eval a *
                                k2.derivative.eval a =
                              -j * H.derivative.eval a ^ 2 ∧
                            d3.derivative.eval a ≠ 0 ∧
                            k2.derivative.eval a ≠ 0) ∨
                          (d3.eval a ≠ 0 ∧
                            k2.derivative.eval a = 0 ∧
                            d3.eval a *
                                k2.derivative.derivative.eval a =
                              -(2 * j) *
                                H.derivative.eval a ^ 2 ∧
                            k2.derivative.derivative.eval a ≠
                              0)))) ∨
                    (∃ x y : k, x ≠ y ∧
                      H.eval x = 0 ∧ H.eval y = 0 ∧
                      d3.eval x = 0 ∧ k2.eval x ≠ 0 ∧
                      d3.eval y ≠ 0 ∧ k2.eval y = 0 ∧
                      d3.derivative.eval x = 0 ∧
                      d3.derivative.derivative.eval x * k2.eval x =
                        -(2 * j) * H.derivative.eval x ^ 2 ∧
                      d3.derivative.derivative.eval x ≠ 0 ∧
                      k2.derivative.eval y = 0 ∧
                      d3.eval y *
                          k2.derivative.derivative.eval y =
                        -(2 * j) * H.derivative.eval y ^ 2 ∧
                      k2.derivative.derivative.eval y ≠ 0 ∧
                      H ∣ d3.derivative * k2.derivative))) ∨
                (∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
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
                    -(6 : k) * (w2.eval b * d3.eval b)))) ∨
            (∃ psi2 : k[X],
              psi = H * psi2 ∧
              H ∣ psi ∧
              phi1 = H ^ 3 * psi2 ∧
              H ^ 3 ∣ phi1 ∧
              w2 * d2 = -(C (1 / 6 : k)) * (H ^ 2 * (b2 * psi2)) ∧
              H ^ 2 ∣ w2 * d2 ∧
              H ∣ rDivisorPsiDivisorBetaGap68 A1 e3 w2
                S.gamma S.epsilon ∧
              (∀ a : k, H.eval a = 0 →
                psi.eval a = 0 ∧
                (4 / 3 : k) * e3.eval a -
                    (4 / 81 : k) * A1.eval a ^ 3 +
                    2 / 3 * S.gamma * A1.eval a + S.epsilon =
                  2 * A1.eval a * w2.eval a) ∧
              ((∃ w3 : k[X],
                  w2 = H * w3 ∧
                  H ∣ w2 ∧
                  w3 * d2 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) ∧
                  H ∣ w3 * d2 ∧
                  rDivisorBetaNumerator68 A1 e3 S.gamma S.epsilon =
                    rDivisorPsiDivisorBetaGap68 A1 e3 w2
                      S.gamma S.epsilon + C 2 * A1 * w2 ∧
                  H ∣ rDivisorBetaNumerator68 A1 e3
                    S.gamma S.epsilon ∧
                  (∀ a : k, H.eval a = 0 →
                    w2.eval a = 0 ∧
                    w3.eval a * d2.eval a = 0 ∧
                    (4 / 3 : k) * e3.eval a -
                        (4 / 81 : k) * A1.eval a ^ 3 +
                        2 / 3 * S.gamma * A1.eval a + S.epsilon =
                      0) ∧
                  (∀ a : k, H.eval a = 0 →
                    w2.derivative.eval a =
                      H.derivative.eval a * w3.eval a ∧
                    w3.derivative.eval a * d2.eval a +
                      w3.eval a * d2.derivative.eval a =
                      -(1 / 6 : k) *
                        (H.derivative.eval a *
                          (b2.eval a * psi2.eval a)) ∧
                    d2.derivative.eval a * k1.eval a +
                      d2.eval a * k1.derivative.eval a = 0) ∧
                  ((∃ w4 : k[X],
                      w3 = H * w4 ∧ H ∣ w3 ∧
                      w2 = H ^ 2 * w4 ∧ H ^ 2 ∣ w2 ∧
                      w4 * d2 = -(C (1 / 6 : k)) * (b2 * psi2) ∧
                      (∀ a : k, H.eval a = 0 →
                        w3.eval a = 0 ∧
                        w2.derivative.eval a = 0)) ∨
                    (∃ d3 : k[X],
                      d2 = H * d3 ∧ H ∣ d2 ∧ d3 ≠ 0 ∧
                      w3 * d3 = -(C (1 / 6 : k)) * (b2 * psi2) ∧
                      w2 * d3 =
                        -(C (1 / 6 : k)) * (H * (b2 * psi2)) ∧
                      d3 * k1 = H ^ 3 * m ∧ H ^ 3 ∣ d3 * k1 ∧
                      (∀ a : k, H.eval a = 0 →
                        d2.eval a = 0 ∧
                        d3.eval a * k1.eval a = 0)) ∨
                    (∃ x y : k, x ≠ y ∧
                      H.eval x = 0 ∧ H.eval y = 0 ∧
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
                      ((d2.derivative.eval y = 0 ∧
                          b2.eval y * psi2.eval y = 0 ∧
                          (b2.eval y = 0 ∨ psi2.eval y = 0)) ∨
                        (d2.derivative.eval y ≠ 0 ∧
                          k1.eval y = 0 ∧ H ∣ k1 ∧
                          ∃ k2 : k[X], k1 = H * k2 ∧ k2 ≠ 0 ∧
                            d2 * k2 = H ^ 3 * m))))) ∨
                (∃ d3 : k[X],
                  d2 = H * d3 ∧
                  H ∣ d2 ∧
                  w2 * d3 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) ∧
                  H ∣ w2 * d3 ∧
                  d3 * k1 = H ^ 3 * m ∧
                  H ^ 3 ∣ d3 * k1 ∧
                  rDivisorLowerZeroQuotient68 H A1 b2 c2 (H * d3) e3
                      S.alpha S.gamma S.epsilon S.eta =
                    H * rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                      S.alpha S.gamma S.epsilon S.eta ∧
                  rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
                    S.alpha S.gamma S.epsilon S.eta = 0 ∧
                  (∀ a : k, H.eval a = 0 →
                    (rDivisorLowerZeroTThree68 H A1 b2 c2 e3
                        S.alpha S.gamma S.epsilon).eval a *
                        d3.eval a =
                      c2.eval a *
                        (rDivisorDTwoUOne68 A1 b2 c2 d3
                          S.alpha S.gamma).eval a ∧
                    d3.eval a * k1.eval a = 0 ∧
                    w2.eval a * d3.eval a = 0) ∧
                  d3 ≠ 0 ∧
                  (∀ a : k, H.eval a = 0 →
                    d3.derivative.eval a * k1.eval a +
                      d3.eval a * k1.derivative.eval a = 0 ∧
                    d3.derivative.derivative.eval a * k1.eval a +
                      2 * (d3.derivative.eval a *
                        k1.derivative.eval a) +
                      d3.eval a * k1.derivative.derivative.eval a =
                      0 ∧
                    w2.derivative.eval a * d3.eval a +
                      w2.eval a * d3.derivative.eval a =
                      -(1 / 6 : k) *
                        (H.derivative.eval a *
                          (b2.eval a * psi2.eval a))) ∧
                  ((∃ w5 : k[X],
                      w2 = H * w5 ∧ H ∣ w2 ∧
                      w5 * d3 = -(C (1 / 6 : k)) * (b2 * psi2) ∧
                      H ∣ rDivisorBetaNumerator68 A1 e3
                        S.gamma S.epsilon ∧
                      (∀ a : k, H.eval a = 0 →
                        w2.eval a = 0 ∧
                        (4 / 3 : k) * e3.eval a -
                            (4 / 81 : k) * A1.eval a ^ 3 +
                            2 / 3 * S.gamma * A1.eval a +
                            S.epsilon = 0)) ∨
                    (∃ d6 : k[X],
                      d3 = H * d6 ∧ H ∣ d3 ∧
                      d2 = H ^ 2 * d6 ∧ H ^ 2 ∣ d2 ∧ d6 ≠ 0 ∧
                      w2 * d6 = -(C (1 / 6 : k)) * (b2 * psi2) ∧
                      d6 * k1 = H ^ 2 * m ∧ H ^ 2 ∣ d6 * k1 ∧
                      (∀ a : k, H.eval a = 0 →
                        d3.eval a = 0 ∧
                        d6.eval a * k1.eval a = 0)) ∨
                    (∃ x y : k, x ≠ y ∧
                      H.eval x = 0 ∧ H.eval y = 0 ∧
                      w2.eval x = 0 ∧ d3.eval x ≠ 0 ∧
                      w2.eval y ≠ 0 ∧ d3.eval y = 0 ∧
                      k1.eval x = 0 ∧ k1.derivative.eval x = 0 ∧
                      k1.derivative.derivative.eval x = 0 ∧
                      (4 / 3 : k) * e3.eval x -
                          (4 / 81 : k) * A1.eval x ^ 3 +
                          2 / 3 * S.gamma * A1.eval x +
                          S.epsilon = 0 ∧
                      w2.derivative.eval x * d3.eval x =
                        -(1 / 6 : k) *
                          (H.derivative.eval x *
                            (b2.eval x * psi2.eval x)) ∧
                      (c2.eval y = 0 ∨
                        (rDivisorDTwoUOne68 A1 b2 c2 d3
                          S.alpha S.gamma).eval y = 0) ∧
                      ((d3.derivative.eval y = 0 ∧
                          b2.eval y * psi2.eval y = 0 ∧
                          (b2.eval y = 0 ∨ psi2.eval y = 0) ∧
                          d3.derivative.derivative.eval y *
                            k1.eval y = 0) ∨
                        (d3.derivative.eval y ≠ 0 ∧
                          k1.eval y = 0 ∧
                          k1.derivative.eval y = 0 ∧ H ∣ k1 ∧
                          ∃ k2 : k[X], k1 = H * k2 ∧ k2 ≠ 0 ∧
                            d3 * k2 = H ^ 2 * m))))) ∨
                (∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
                  w2.eval a = 0 ∧ d2.eval a ≠ 0 ∧
                  w2.eval b ≠ 0 ∧ d2.eval b = 0 ∧
                  w2.derivative.eval a = 0 ∧
                  k1.eval a = 0 ∧ k1.derivative.eval a = 0 ∧
                  k1.derivative.derivative.eval a = 0 ∧
                  (4 / 3 : k) * e3.eval a -
                      (4 / 81 : k) * A1.eval a ^ 3 +
                      2 / 3 * S.gamma * A1.eval a + S.epsilon = 0 ∧
                  d2.derivative.eval b = 0 ∧
                  d2.derivative.derivative.eval b * k1.eval b = 0 ∧
                  w2.eval b * d2.derivative.derivative.eval b =
                    -(1 / 3 : k) * (H.derivative.eval b ^ 2 *
                      (b2.eval b * psi2.eval b)) ∧
                  k1.derivative.derivative.derivative.eval a = 0 ∧
                  d2.eval a *
                      k1.derivative.derivative.derivative.derivative.eval
                        a =
                    -(24 * j) * H.derivative.eval a ^ 4 ∧
                  k1.derivative.derivative.derivative.derivative.eval
                      a ≠ 0 ∧
                  d2.derivative.derivative.derivative.eval b *
                      k1.eval b +
                    3 * (d2.derivative.derivative.eval b *
                      k1.derivative.eval b) = 0 ∧
                  H ∣ w2 * d2.derivative ∧
                  H ∣ k1 * d2.derivative ∧
                  ((d2.derivative.derivative.eval b = 0 ∧
                      b2.eval b * psi2.eval b = 0 ∧
                      (b2.eval b = 0 ∨ psi2.eval b = 0) ∧
                      d2.derivative.derivative.derivative.eval b *
                        k1.eval b = 0 ∧
                      (d2.derivative.derivative.derivative.eval b =
                          0 ∨
                        k1.eval b = 0)) ∨
                    (d2.derivative.derivative.eval b ≠ 0 ∧
                      k1.eval b = 0 ∧
                      k1.derivative.eval b = 0 ∧
                      b2.eval b ≠ 0 ∧ psi2.eval b ≠ 0 ∧ H ∣ k1 ∧
                      ∃ k2 : k[X], k1 = H * k2 ∧ k2 ≠ 0 ∧
                        d2 * k2 = H ^ 3 * m))))) ∨
            (∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
              d2.eval a = 0 ∧ psi.eval a ≠ 0 ∧
              d2.eval b ≠ 0 ∧ psi.eval b = 0 ∧
              w2.eval a * d2.derivative.eval a =
                -(1 / 6 : k) *
                  (H.derivative.eval a * b2.eval a * psi.eval a) ∧
              d2.derivative.eval a * k1.eval a = 0 ∧
              w2.eval b = 0 ∧ k1.eval b = 0 ∧
              w2.derivative.eval b = 0 ∧ k1.derivative.eval b = 0 ∧
              (4 / 3 : k) * e3.eval b - (4 / 81 : k) * A1.eval b ^ 3 +
                  2 / 3 * S.gamma * A1.eval b + S.epsilon = 0 ∧
              d2.derivative.derivative.eval a * k1.eval a +
                2 * (d2.derivative.eval a * k1.derivative.eval a) =
                0 ∧
              k1.derivative.derivative.eval b = 0 ∧
              w2.derivative.derivative.eval b * d2.eval b =
                -(1 / 3 : k) * (H.derivative.eval b * b2.eval b *
                  psi.derivative.eval b) ∧
              d2.derivative.derivative.derivative.eval a * k1.eval a +
                3 * (d2.derivative.derivative.eval a *
                  k1.derivative.eval a) +
                3 * (d2.derivative.eval a *
                  k1.derivative.derivative.eval a) = 0 ∧
              k1.derivative.derivative.derivative.eval b = 0 ∧
              d2.eval b *
                  k1.derivative.derivative.derivative.derivative.eval
                    b =
                -(24 * j) * H.derivative.eval b ^ 4 ∧
              k1.derivative.derivative.derivative.derivative.eval b ≠
                0 ∧
              H ∣ d2 * k1.derivative ∧
              H ∣ d2 * w2.derivative ∧
              ((d2.derivative.eval a = 0 ∧ b2.eval a = 0 ∧
                  d2.derivative.derivative.eval a * k1.eval a = 0 ∧
                  (d2.derivative.derivative.eval a = 0 ∨
                    k1.eval a = 0) ∧
                  d2.derivative.derivative.derivative.eval a *
                      k1.eval a +
                    3 * (d2.derivative.derivative.eval a *
                      k1.derivative.eval a) = 0) ∨
                (d2.derivative.eval a ≠ 0 ∧ k1.eval a = 0 ∧
                  k1.derivative.eval a = 0 ∧
                  k1.derivative.derivative.eval a = 0 ∧ H ∣ k1 ∧
                  ∃ k2 : k[X], k1 = H * k2 ∧ k2 ≠ 0 ∧
                    d2 * k2 = H ^ 3 * m))))) ∨
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
    S.terminalAfterLowerOneRDivisorLowerZeroSeventhPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hI4, hrow, ?_⟩
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hmj : (-j : k) ≠ 0 := neg_ne_zero.mpr hj
  have h2j : -(2 * j) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, not_or]
    exact ⟨by norm_num, hj⟩
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
    rcases hsplit3 with hA | hB | hC
    · -- `d₂ = H·d₃` child.
      left
      obtain ⟨d3, hd3, hd2dvd, hwdA, hdkA, hdk3dvd, hQfact, hQ3,
          hAfaces, hd3ne, hdvd1, hAsplit⟩ := hA
      refine ⟨d3, hd3, hd2dvd, hwdA, hdkA, hdk3dvd, hQfact, hQ3,
        hAfaces, hd3ne, hdvd1, ?_⟩
      rcases hAsplit with hA1 | hA2 | hA3
      · -- `d₃ = H·d₄` grandchild: allocate the fresh `H ∣ b₂ψ`.
        left
        obtain ⟨d4, hd4, hd2d4, hd2dvd2, hbpsi, hbpsidvd, hd4k,
            hd4kdvd, hA1faces, hd4ne, hA1seventh⟩ := hA1
        refine ⟨d4, hd4, hd2d4, hd2dvd2, hbpsi, hbpsidvd, hd4k,
          hd4kdvd, hA1faces, hd4ne, hA1seventh, ?_⟩
        rcases simpleQuadratic_dvd_product_coordinate_split_68 H b2 psi
            hdeg hsimple hbpsidvd with hb2dvd | hpsidvd |
          ⟨x, y, hxy, hx, hy, hb2x, hpsix, hb2y, hpsiy⟩
        · -- `H ∣ b₂`: the `I₄` relation de-cores completely.
          left
          obtain ⟨b3, hb3⟩ := hb2dvd
          have hcore : b3 * psi = -(6 : k[X]) * (w2 * d4) := by
            apply mul_left_cancel₀ hH
            have h' := hbpsi
            rw [hb3] at h'
            linear_combination h'
          refine ⟨b3, hb3, ⟨b3, hb3⟩, hcore, ?_⟩
          intro a ha
          refine ⟨by rw [hb3]; simp [ha], ?_⟩
          have h := congrArg (fun P : k[X] => P.eval a) hcore
          simp only [eval_mul, eval_neg, eval_ofNat] at h
          linear_combination h
        · -- `H ∣ ψ`: merge into the `ψ`-divisor regime one power deeper.
          right
          left
          obtain ⟨psi3, hpsi3⟩ := hpsidvd
          have hcore : b2 * psi3 = -(6 : k[X]) * (w2 * d4) := by
            apply mul_left_cancel₀ hH
            have h' := hbpsi
            rw [hpsi3] at h'
            linear_combination h'
          have hphi3' : phi1 = H ^ 3 * psi3 := by
            rw [hphi2, hpsi3]
            ring
          refine ⟨psi3, hpsi3, ⟨psi3, hpsi3⟩, hcore, hphi3',
            ⟨psi3, hphi3'⟩, ?_, ?_⟩
          · rw [hwd, hpsi3]
            ring
          · intro a ha
            refine ⟨by rw [hpsi3]; simp [ha], ?_⟩
            have h := congrArg (fun P : k[X] => P.eval a) hcore
            simp only [eval_mul, eval_neg, eval_ofNat] at h
            linear_combination h
        · -- Transverse `b₂/ψ` allocation.
          right
          right
          have htiex : b2.derivative.eval x * psi.eval x =
              -(6 : k) *
                (H.derivative.eval x * (w2.eval x * d4.eval x)) := by
            linear_combination (hA1seventh x hx).2.2 -
              psi.derivative.eval x * hb2x
          have htiey : b2.eval y * psi.derivative.eval y =
              -(6 : k) *
                (H.derivative.eval y * (w2.eval y * d4.eval y)) := by
            linear_combination (hA1seventh y hy).2.2 -
              b2.derivative.eval y * hpsiy
          have hcw : c2.eval y = 0 ∨ w2.eval y = 0 := by
            rcases mul_eq_zero.mp ((hA1faces y hy).2.2) with h | h
            · exact Or.inl h
            · rcases mul_eq_zero.mp h with h' | h'
              · exact absurd h' hb2y
              · exact Or.inr h'
          exact ⟨x, y, hxy, hx, hy, hb2x, hpsix, hb2y, hpsiy,
            htiex, htiey, hcw⟩
      · -- `k₁ = H·k₂` grandchild: allocate the fresh `H ∣ d₃k₂`.
        right
        left
        obtain ⟨k2, hk2, hk1dvdH, hd3k2, hd3k2dvd, hA2faces, hk2ne,
            hA2seventh⟩ := hA2
        refine ⟨k2, hk2, hk1dvdH, hd3k2, hd3k2dvd, hA2faces, hk2ne,
          hA2seventh, ?_⟩
        have hdvdDK : H ∣ d3 * k2 :=
          dvd_trans ⟨H, by ring⟩ hd3k2dvd
        rcases simpleQuadratic_dvd_product_coordinate_split_68 H d3 k2
            hdeg hsimple hdvdDK with hd3dvd | hk2dvd |
          ⟨x, y, hxy, hx, hy, hd3x, hk2x, hd3y, hk2y⟩
        · -- `H ∣ d₃`: merge into the `d₄`-shape with `d₅k₂ = Hm`.
          left
          obtain ⟨d5, hd5⟩ := hd3dvd
          have hd2d5 : d2 = H ^ 2 * d5 := by
            rw [hd3, hd5]
            ring
          have hwdA' := hwdA
          rw [hd5] at hwdA'
          have hbpsi5 : b2 * psi = -(6 : k[X]) * (H * (w2 * d5)) := by
            have h6 : (6 : k[X]) * (w2 * (H * d5)) =
                -(((6 : k[X]) * C (1 / 6 : k)) * (b2 * psi)) := by
              rw [hwdA']
              ring
            rw [rDivisorLowerZeroSixUnit68, one_mul] at h6
            linear_combination h6
          have hd5k : d5 * k2 = H * m := by
            apply mul_left_cancel₀ hH
            have h' := hd3k2
            rw [hd5] at h'
            linear_combination h'
          have hd5ne : d5 ≠ 0 :=
            fun h0 => hd3ne (by rw [hd5, h0, mul_zero])
          refine ⟨d5, hd5, ⟨d5, hd5⟩, hd2d5, ⟨d5, hd2d5⟩, hbpsi5,
            hd5k, ⟨m, hd5k⟩, hd5ne, ?_⟩
          intro a ha
          have hd3a : d3.eval a = 0 := by
            rw [hd5]
            simp [ha]
          have hd5k2a : d5.eval a * k2.eval a = 0 := by
            have h := congrArg (fun P : k[X] => P.eval a) hd5k
            simp only [eval_mul] at h
            linear_combination h + m.eval a * ha
          refine ⟨hd3a, hd5k2a, ?_⟩
          have hface1 := (hA2faces a ha).2.1
          have hface2 := (hA2faces a ha).2.2
          by_cases hk2a : k2.eval a = 0
          · left
            have hpin : d3.derivative.eval a * k2.derivative.eval a =
                -j * H.derivative.eval a ^ 2 := by
              linear_combination (1 / 2 : k) * hface2 -
                (1 / 2 : k) *
                  d3.derivative.derivative.eval a * hk2a -
                (1 / 2 : k) *
                  k2.derivative.derivative.eval a * hd3a
            have hRne : -j * H.derivative.eval a ^ 2 ≠ 0 :=
              mul_ne_zero hmj (pow_ne_zero 2 (hsimple a ha))
            exact ⟨hk2a, hpin,
              fun h0 => hRne (by rw [← hpin, h0, zero_mul]),
              fun h0 => hRne (by rw [← hpin, h0, mul_zero])⟩
          · right
            have hd3da : d3.derivative.eval a = 0 := by
              have hprod : d3.derivative.eval a * k2.eval a = 0 := by
                linear_combination hface1 -
                  k2.derivative.eval a * hd3a
              exact (mul_eq_zero.mp hprod).resolve_right hk2a
            have hpin : d3.derivative.derivative.eval a * k2.eval a =
                -(2 * j) * H.derivative.eval a ^ 2 := by
              linear_combination hface2 -
                2 * k2.derivative.eval a * hd3da -
                k2.derivative.derivative.eval a * hd3a
            have hRne : -(2 * j) * H.derivative.eval a ^ 2 ≠ 0 :=
              mul_ne_zero h2j (pow_ne_zero 2 (hsimple a ha))
            exact ⟨hk2a, hd3da, hpin,
              fun h0 => hRne (by rw [← hpin, h0, zero_mul])⟩
        · -- `H ∣ k₂`: the symmetric merge `k₁ = H²k₃`.
          right
          left
          obtain ⟨k3, hk3⟩ := hk2dvd
          have hk1k3 : k1 = H ^ 2 * k3 := by
            rw [hk2, hk3]
            ring
          have hd3k3 : d3 * k3 = H * m := by
            apply mul_left_cancel₀ hH
            have h' := hd3k2
            rw [hk3] at h'
            linear_combination h'
          have hk3ne : k3 ≠ 0 :=
            fun h0 => hk2ne (by rw [hk3, h0, mul_zero])
          refine ⟨k3, hk3, ⟨k3, hk3⟩, hk1k3, ⟨k3, hk1k3⟩, hd3k3,
            ⟨m, hd3k3⟩, hk3ne, ?_⟩
          intro a ha
          have hk2a : k2.eval a = 0 := by
            rw [hk3]
            simp [ha]
          have hd3k3a : d3.eval a * k3.eval a = 0 := by
            have h := congrArg (fun P : k[X] => P.eval a) hd3k3
            simp only [eval_mul] at h
            linear_combination h + m.eval a * ha
          refine ⟨hk2a, hd3k3a, ?_⟩
          have hface1 := (hA2faces a ha).2.1
          have hface2 := (hA2faces a ha).2.2
          by_cases hd3a : d3.eval a = 0
          · left
            have hpin : d3.derivative.eval a * k2.derivative.eval a =
                -j * H.derivative.eval a ^ 2 := by
              linear_combination (1 / 2 : k) * hface2 -
                (1 / 2 : k) *
                  d3.derivative.derivative.eval a * hk2a -
                (1 / 2 : k) *
                  k2.derivative.derivative.eval a * hd3a
            have hRne : -j * H.derivative.eval a ^ 2 ≠ 0 :=
              mul_ne_zero hmj (pow_ne_zero 2 (hsimple a ha))
            exact ⟨hd3a, hpin,
              fun h0 => hRne (by rw [← hpin, h0, zero_mul]),
              fun h0 => hRne (by rw [← hpin, h0, mul_zero])⟩
          · right
            have hk2da : k2.derivative.eval a = 0 := by
              have hprod : d3.eval a * k2.derivative.eval a = 0 := by
                linear_combination hface1 -
                  d3.derivative.eval a * hk2a
              exact (mul_eq_zero.mp hprod).resolve_left hd3a
            have hpin : d3.eval a *
                k2.derivative.derivative.eval a =
                -(2 * j) * H.derivative.eval a ^ 2 := by
              linear_combination hface2 -
                d3.derivative.derivative.eval a * hk2a -
                2 * d3.derivative.eval a * hk2da
            have hRne : -(2 * j) * H.derivative.eval a ^ 2 ≠ 0 :=
              mul_ne_zero h2j (pow_ne_zero 2 (hsimple a ha))
            exact ⟨hd3a, hk2da, hpin,
              fun h0 => hRne (by rw [← hpin, h0, mul_zero])⟩
        · -- Transverse `d₃/k₂` allocation with exact order-two pins.
          right
          right
          have hd3dx : d3.derivative.eval x = 0 := by
            have hprod : d3.derivative.eval x * k2.eval x = 0 := by
              linear_combination (hA2faces x hx).2.1 -
                k2.derivative.eval x * hd3x
            exact (mul_eq_zero.mp hprod).resolve_right hk2x
          have hpinx : d3.derivative.derivative.eval x * k2.eval x =
              -(2 * j) * H.derivative.eval x ^ 2 := by
            linear_combination (hA2faces x hx).2.2 -
              2 * k2.derivative.eval x * hd3dx -
              k2.derivative.derivative.eval x * hd3x
          have hRnex : -(2 * j) * H.derivative.eval x ^ 2 ≠ 0 :=
            mul_ne_zero h2j (pow_ne_zero 2 (hsimple x hx))
          have hd3ddx : d3.derivative.derivative.eval x ≠ 0 :=
            fun h0 => hRnex (by rw [← hpinx, h0, zero_mul])
          have hk2dy : k2.derivative.eval y = 0 := by
            have hprod : d3.eval y * k2.derivative.eval y = 0 := by
              linear_combination (hA2faces y hy).2.1 -
                d3.derivative.eval y * hk2y
            exact (mul_eq_zero.mp hprod).resolve_left hd3y
          have hpiny : d3.eval y *
              k2.derivative.derivative.eval y =
              -(2 * j) * H.derivative.eval y ^ 2 := by
            linear_combination (hA2faces y hy).2.2 -
              d3.derivative.derivative.eval y * hk2y -
              2 * d3.derivative.eval y * hk2dy
          have hRney : -(2 * j) * H.derivative.eval y ^ 2 ≠ 0 :=
            mul_ne_zero h2j (pow_ne_zero 2 (hsimple y hy))
          have hk2ddy : k2.derivative.derivative.eval y ≠ 0 :=
            fun h0 => hRney (by rw [← hpiny, h0, mul_zero])
          have hdvdD : H ∣ d3.derivative * k2.derivative :=
            rDivisorSeventh_dvd_of_two_root_evals_68 H
              (d3.derivative * k2.derivative) hdeg hsimple x y hxy
              hx hy
              (by rw [eval_mul, hd3dx, zero_mul])
              (by rw [eval_mul, hk2dy, mul_zero])
          exact ⟨x, y, hxy, hx, hy, hd3x, hk2x, hd3y, hk2y, hd3dx,
            hpinx, hd3ddx, hk2dy, hpiny, hk2ddy, hdvdD⟩
      · -- Transverse `d₃/k₁` grandchild: factor splits at both roots.
        right
        right
        obtain ⟨x, y, hxy, hx, hy, hd3x, hk1x, hd3y, hk1y, hd3dx,
            hd3ddx, hbpsix, hk1dy, hk1ddy, hpinx, hd3dddx, hpiny,
            hk1dddy, hdvdD1, hdvdD2⟩ := hA3
        have hcU : c2.eval x = 0 ∨
            (rDivisorDTwoUOne68 A1 b2 c2 d3
              S.alpha S.gamma).eval x = 0 := by
          have h := (hAfaces x hx).1
          rw [hd3x, mul_zero] at h
          exact mul_eq_zero.mp h.symm
        have htiey : b2.eval y * psi.eval y =
            -(6 : k) * (w2.eval y * d3.eval y) := by
          have h := congrArg (fun P : k[X] => P.eval y) hwdA
          simp only [eval_mul, eval_neg, eval_C] at h
          linear_combination (6 : k) * h
        exact ⟨x, y, hxy, hx, hy, hd3x, hk1x, hd3y, hk1y, hd3dx,
          hd3ddx, hbpsix, hk1dy, hk1ddy, hpinx, hd3dddx, hpiny,
          hk1dddy, hdvdD1, hdvdD2, mul_eq_zero.mp hbpsix, hcU,
          htiey⟩
    · -- `ψ = H·ψ₂` child.
      right
      left
      obtain ⟨psi2, hpsi2, hpsidvdH, hphi3, hphi3dvd, hwdB, hwd2dvd,
          hgapdvd, hBfaces, hBsplit⟩ := hB
      refine ⟨psi2, hpsi2, hpsidvdH, hphi3, hphi3dvd, hwdB, hwd2dvd,
        hgapdvd, hBfaces, ?_⟩
      rcases hBsplit with hB1 | hB2 | hB3
      · -- `w₂ = H·w₃` grandchild: allocate the fresh `H ∣ w₃d₂`.
        left
        obtain ⟨w3, hw3, hw2dvdH, hw3d, hw3ddvd, hgapbridge, hbetadvd,
            hB1faces, hB1seventh⟩ := hB1
        refine ⟨w3, hw3, hw2dvdH, hw3d, hw3ddvd, hgapbridge, hbetadvd,
          hB1faces, hB1seventh, ?_⟩
        rcases simpleQuadratic_dvd_product_coordinate_split_68 H w3 d2
            hdeg hsimple hw3ddvd with hw3dvd | hd2dvd' |
          ⟨x, y, hxy, hx, hy, hw3x, hd2x, hw3y, hd2y⟩
        · -- `H ∣ w₃`: `w₂ = H²w₄` with the de-cored `I₄` relation.
          left
          obtain ⟨w4, hw4⟩ := hw3dvd
          have hw2w4 : w2 = H ^ 2 * w4 := by
            rw [hw3, hw4]
            ring
          have hw4d : w4 * d2 = -(C (1 / 6 : k)) * (b2 * psi2) := by
            apply mul_left_cancel₀ hH
            have h' := hw3d
            rw [hw4] at h'
            linear_combination h'
          refine ⟨w4, hw4, ⟨w4, hw4⟩, hw2w4, ⟨w4, hw2w4⟩, hw4d, ?_⟩
          intro a ha
          have hw3a : w3.eval a = 0 := by
            rw [hw4]
            simp [ha]
          refine ⟨hw3a, ?_⟩
          have h := (hB1seventh a ha).1
          rw [hw3a, mul_zero] at h
          exact h
        · -- `H ∣ d₂`: merge into the coordinate `d₃`-leaf, fully
          -- de-cored.
          right
          left
          obtain ⟨d3, hd3'⟩ := hd2dvd'
          have hw3d3 : w3 * d3 = -(C (1 / 6 : k)) * (b2 * psi2) := by
            apply mul_left_cancel₀ hH
            have h' := hw3d
            rw [hd3'] at h'
            linear_combination h'
          have hw2d3 : w2 * d3 =
              -(C (1 / 6 : k)) * (H * (b2 * psi2)) := by
            rw [hw3]
            linear_combination H * hw3d3
          have hd3k1 : d3 * k1 = H ^ 3 * m := by
            apply mul_left_cancel₀ hH
            have h' := hdk
            rw [hd3'] at h'
            linear_combination h'
          have hd3ne' : d3 ≠ 0 :=
            fun h0 => hd2ne (by rw [hd3', h0, mul_zero])
          refine ⟨d3, hd3', ⟨d3, hd3'⟩, hd3ne', hw3d3, hw2d3, hd3k1,
            ⟨m, hd3k1⟩, ?_⟩
          intro a ha
          refine ⟨by rw [hd3']; simp [ha], ?_⟩
          have h := congrArg (fun P : k[X] => P.eval a) hd3k1
          simp only [eval_mul, eval_pow] at h
          linear_combination h + m.eval a * H.eval a ^ 2 * ha
        · -- Transverse `w₃/d₂` allocation.
          right
          right
          have hw2dx0 : w2.derivative.eval x = 0 := by
            have h := (hB1seventh x hx).1
            rw [hw3x, mul_zero] at h
            exact h
          have hk1x0 : k1.eval x = 0 :=
            (mul_eq_zero.mp ((hfaces x hx).2.2)).resolve_left hd2x
          have hk1dx0 : k1.derivative.eval x = 0 := by
            have hprod : d2.eval x * k1.derivative.eval x = 0 := by
              linear_combination (hB1seventh x hx).2.2 -
                d2.derivative.eval x * hk1x0
            exact (mul_eq_zero.mp hprod).resolve_left hd2x
          have htiex : w3.derivative.eval x * d2.eval x =
              -(1 / 6 : k) *
                (H.derivative.eval x *
                  (b2.eval x * psi2.eval x)) := by
            linear_combination (hB1seventh x hx).2.1 -
              d2.derivative.eval x * hw3x
          have hw2dy : w2.derivative.eval y ≠ 0 := by
            rw [(hB1seventh y hy).1]
            exact mul_ne_zero (hsimple y hy) hw3y
          have htiey : w3.eval y * d2.derivative.eval y =
              -(1 / 6 : k) *
                (H.derivative.eval y *
                  (b2.eval y * psi2.eval y)) := by
            linear_combination (hB1seventh y hy).2.1 -
              w3.derivative.eval y * hd2y
          refine ⟨x, y, hxy, hx, hy, hw3x, hd2x, hw3y, hd2y, hw2dx0,
            hk1x0, hk1dx0, htiex, hw2dy, htiey, ?_⟩
          by_cases hd2dy : d2.derivative.eval y = 0
          · left
            have hbp : b2.eval y * psi2.eval y = 0 := by
              have h := htiey
              rw [hd2dy, mul_zero] at h
              have h0 : H.derivative.eval y *
                  (b2.eval y * psi2.eval y) = 0 := by
                linear_combination (6 : k) * h
              exact (mul_eq_zero.mp h0).resolve_left (hsimple y hy)
            exact ⟨hd2dy, hbp, mul_eq_zero.mp hbp⟩
          · right
            have hk1y0 : k1.eval y = 0 := by
              have hprod : d2.derivative.eval y * k1.eval y = 0 := by
                linear_combination (hB1seventh y hy).2.2 -
                  k1.derivative.eval y * hd2y
              exact (mul_eq_zero.mp hprod).resolve_left hd2dy
            have hdvdk1 : H ∣ k1 :=
              rDivisorSeventh_dvd_of_two_root_evals_68 H k1 hdeg
                hsimple x y hxy hx hy hk1x0 hk1y0
            obtain ⟨k2, hk2'⟩ := hdvdk1
            have hk2ne' : k2 ≠ 0 :=
              fun h0 => hk1ne (by rw [hk2', h0, mul_zero])
            have hd2k2 : d2 * k2 = H ^ 3 * m := by
              apply mul_left_cancel₀ hH
              have h' := hdk
              rw [hk2'] at h'
              linear_combination h'
            exact ⟨hd2dy, hk1y0, ⟨k2, hk2'⟩, k2, hk2', hk2ne',
              hd2k2⟩
      · -- `d₂ = H·d₃` grandchild in the `ψ`-regime: allocate the
        -- fresh `H ∣ w₂d₃`.
        right
        left
        obtain ⟨d3, hd3B, hd2dvdB, hwd3, hwd3dvd, hd3k, hd3kdvd,
            hQfactB, hQ3B, hB2faces, hd3neB, hB2seventh⟩ := hB2
        refine ⟨d3, hd3B, hd2dvdB, hwd3, hwd3dvd, hd3k, hd3kdvd,
          hQfactB, hQ3B, hB2faces, hd3neB, hB2seventh, ?_⟩
        rcases simpleQuadratic_dvd_product_coordinate_split_68 H w2 d3
            hdeg hsimple hwd3dvd with hw2dvd' | hd3dvd' |
          ⟨x, y, hxy, hx, hy, hw2x, hd3x, hw2y, hd3y⟩
        · -- `H ∣ w₂`: the `β`-numerator becomes globally divisible.
          left
          obtain ⟨w5, hw5⟩ := hw2dvd'
          have hw5d3 : w5 * d3 = -(C (1 / 6 : k)) * (b2 * psi2) := by
            apply mul_left_cancel₀ hH
            have h' := hwd3
            rw [hw5] at h'
            linear_combination h'
          have hbeta : H ∣ rDivisorBetaNumerator68 A1 e3
              S.gamma S.epsilon := by
            rw [rDivisorBetaNumerator_gap_bridge_68 A1 e3 w2
              S.gamma S.epsilon]
            exact dvd_add hgapdvd
              (Dvd.dvd.mul_left ⟨w5, hw5⟩ (C 2 * A1))
          refine ⟨w5, hw5, ⟨w5, hw5⟩, hw5d3, hbeta, ?_⟩
          intro a ha
          have hw2a : w2.eval a = 0 := by
            rw [hw5]
            simp [ha]
          refine ⟨hw2a, ?_⟩
          have h := (hBfaces a ha).2
          rw [hw2a, mul_zero] at h
          exact h
        · -- `H ∣ d₃`: the deep `d₂ = H²d₆` merge.
          right
          left
          obtain ⟨d6, hd6⟩ := hd3dvd'
          have hd2d6 : d2 = H ^ 2 * d6 := by
            rw [hd3B, hd6]
            ring
          have hw2d6 : w2 * d6 = -(C (1 / 6 : k)) * (b2 * psi2) := by
            apply mul_left_cancel₀ hH
            have h' := hwd3
            rw [hd6] at h'
            linear_combination h'
          have hd6k1 : d6 * k1 = H ^ 2 * m := by
            apply mul_left_cancel₀ hH
            have h' := hd3k
            rw [hd6] at h'
            linear_combination h'
          have hd6ne : d6 ≠ 0 :=
            fun h0 => hd3neB (by rw [hd6, h0, mul_zero])
          refine ⟨d6, hd6, ⟨d6, hd6⟩, hd2d6, ⟨d6, hd2d6⟩, hd6ne,
            hw2d6, hd6k1, ⟨m, hd6k1⟩, ?_⟩
          intro a ha
          refine ⟨by rw [hd6]; simp [ha], ?_⟩
          have h := congrArg (fun P : k[X] => P.eval a) hd6k1
          simp only [eval_mul, eval_pow] at h
          linear_combination h + m.eval a * H.eval a * ha
        · -- Transverse `w₂/d₃` allocation.
          right
          right
          have hk1x0 : k1.eval x = 0 :=
            (mul_eq_zero.mp ((hB2faces x hx).2.1)).resolve_left hd3x
          have hk1dx0 : k1.derivative.eval x = 0 := by
            have hprod : d3.eval x * k1.derivative.eval x = 0 := by
              linear_combination (hB2seventh x hx).1 -
                d3.derivative.eval x * hk1x0
            exact (mul_eq_zero.mp hprod).resolve_left hd3x
          have hk1ddx0 : k1.derivative.derivative.eval x = 0 := by
            have hprod : d3.eval x *
                k1.derivative.derivative.eval x = 0 := by
              linear_combination (hB2seventh x hx).2.1 -
                d3.derivative.derivative.eval x * hk1x0 -
                2 * d3.derivative.eval x * hk1dx0
            exact (mul_eq_zero.mp hprod).resolve_left hd3x
          have hbetax : (4 / 3 : k) * e3.eval x -
              (4 / 81 : k) * A1.eval x ^ 3 +
              2 / 3 * S.gamma * A1.eval x + S.epsilon = 0 := by
            have h := (hBfaces x hx).2
            rw [hw2x, mul_zero] at h
            exact h
          have htiex : w2.derivative.eval x * d3.eval x =
              -(1 / 6 : k) *
                (H.derivative.eval x *
                  (b2.eval x * psi2.eval x)) := by
            linear_combination (hB2seventh x hx).2.2 -
              d3.derivative.eval x * hw2x
          have hcU : c2.eval y = 0 ∨
              (rDivisorDTwoUOne68 A1 b2 c2 d3
                S.alpha S.gamma).eval y = 0 := by
            have h := (hB2faces y hy).1
            rw [hd3y, mul_zero] at h
            exact mul_eq_zero.mp h.symm
          refine ⟨x, y, hxy, hx, hy, hw2x, hd3x, hw2y, hd3y, hk1x0,
            hk1dx0, hk1ddx0, hbetax, htiex, hcU, ?_⟩
          by_cases hd3dy : d3.derivative.eval y = 0
          · left
            have hbp : b2.eval y * psi2.eval y = 0 := by
              have h0 : H.derivative.eval y *
                  (b2.eval y * psi2.eval y) = 0 := by
                linear_combination
                  (6 : k) * (hB2seventh y hy).2.2 -
                  6 * w2.derivative.eval y * hd3y -
                  6 * w2.eval y * hd3dy
              exact (mul_eq_zero.mp h0).resolve_left (hsimple y hy)
            have hddk1y : d3.derivative.derivative.eval y *
                k1.eval y = 0 := by
              linear_combination (hB2seventh y hy).2.1 -
                2 * k1.derivative.eval y * hd3dy -
                k1.derivative.derivative.eval y * hd3y
            exact ⟨hd3dy, hbp, mul_eq_zero.mp hbp, hddk1y⟩
          · right
            have hk1y0 : k1.eval y = 0 := by
              have hprod : d3.derivative.eval y * k1.eval y = 0 := by
                linear_combination (hB2seventh y hy).1 -
                  k1.derivative.eval y * hd3y
              exact (mul_eq_zero.mp hprod).resolve_left hd3dy
            have hk1dy0 : k1.derivative.eval y = 0 := by
              have hprod : d3.derivative.eval y *
                  k1.derivative.eval y = 0 := by
                linear_combination
                  (1 / 2 : k) * (hB2seventh y hy).2.1 -
                  (1 / 2 : k) *
                    d3.derivative.derivative.eval y * hk1y0 -
                  (1 / 2 : k) *
                    k1.derivative.derivative.eval y * hd3y
              exact (mul_eq_zero.mp hprod).resolve_left hd3dy
            have hdvdk1 : H ∣ k1 :=
              rDivisorSeventh_dvd_of_two_root_evals_68 H k1 hdeg
                hsimple x y hxy hx hy hk1x0 hk1y0
            obtain ⟨k2, hk2'⟩ := hdvdk1
            have hk2ne' : k2 ≠ 0 :=
              fun h0 => hk1ne (by rw [hk2', h0, mul_zero])
            have hd3k2' : d3 * k2 = H ^ 2 * m := by
              apply mul_left_cancel₀ hH
              have h' := hd3k
              rw [hk2'] at h'
              linear_combination h'
            exact ⟨hd3dy, hk1y0, hk1dy0, ⟨k2, hk2'⟩, k2, hk2',
              hk2ne', hd3k2'⟩
      · -- Transverse `w₂/d₂` grandchild: exclusive `d₂''(b)` split
        -- against the loaded `I₄` mate.
        right
        right
        obtain ⟨x, y, hxy, hx, hy, hw2x, hd2x, hw2y, hd2y, hw2dx,
            hk1x, hk1dx, hk1ddx, hbetax, hd2dy, hd2ddk1y, hI4y,
            hk1dddx, hpin4x, hk1ddddx, hfacey, hdvdWD,
            hdvdKD⟩ := hB3
        refine ⟨x, y, hxy, hx, hy, hw2x, hd2x, hw2y, hd2y, hw2dx,
          hk1x, hk1dx, hk1ddx, hbetax, hd2dy, hd2ddk1y, hI4y,
          hk1dddx, hpin4x, hk1ddddx, hfacey, hdvdWD, hdvdKD, ?_⟩
        by_cases hdd : d2.derivative.derivative.eval y = 0
        · left
          have hbp : b2.eval y * psi2.eval y = 0 := by
            have h0 : H.derivative.eval y ^ 2 *
                (b2.eval y * psi2.eval y) = 0 := by
              linear_combination (3 : k) * hI4y -
                3 * w2.eval y * hdd
            exact (mul_eq_zero.mp h0).resolve_left
              (pow_ne_zero 2 (hsimple y hy))
          have hd3k1y :
              d2.derivative.derivative.derivative.eval y *
                k1.eval y = 0 := by
            linear_combination hfacey -
              3 * k1.derivative.eval y * hdd
          exact ⟨hdd, hbp, mul_eq_zero.mp hbp, hd3k1y,
            mul_eq_zero.mp hd3k1y⟩
        · right
          have hk1y0 : k1.eval y = 0 :=
            (mul_eq_zero.mp hd2ddk1y).resolve_left hdd
          have hk1dy0 : k1.derivative.eval y = 0 := by
            have hprod : d2.derivative.derivative.eval y *
                k1.derivative.eval y = 0 := by
              linear_combination (1 / 3 : k) * hfacey -
                (1 / 3 : k) *
                  d2.derivative.derivative.derivative.eval y *
                  hk1y0
            exact (mul_eq_zero.mp hprod).resolve_left hdd
          have hbpne : b2.eval y * psi2.eval y ≠ 0 := by
            intro h0
            have hz : w2.eval y *
                d2.derivative.derivative.eval y = 0 := by
              rw [hI4y, h0]
              ring
            exact (mul_ne_zero hw2y hdd) hz
          have hdvdk1 : H ∣ k1 :=
            rDivisorSeventh_dvd_of_two_root_evals_68 H k1 hdeg
              hsimple x y hxy hx hy hk1x hk1y0
          obtain ⟨k2, hk2'⟩ := hdvdk1
          have hk2ne' : k2 ≠ 0 :=
            fun h0 => hk1ne (by rw [hk2', h0, mul_zero])
          have hd2k2 : d2 * k2 = H ^ 3 * m := by
            apply mul_left_cancel₀ hH
            have h' := hdk
            rw [hk2'] at h'
            linear_combination h'
          exact ⟨hdd, hk1y0, hk1dy0,
            fun h0 => hbpne (by rw [h0, zero_mul]),
            fun h0 => hbpne (by rw [h0, mul_zero]),
            ⟨k2, hk2'⟩, k2, hk2', hk2ne', hd2k2⟩
    · -- Transverse `d₂/ψ` child: exclusive `d₂'(a)` split.
      right
      right
      obtain ⟨a, b, hab, ha, hb, hd2a, hpsia, hd2b, hpsib, hCf1, hCf2,
          hw2b, hk1b, hw2db, hk1db, hbetab, hCsecond, hk1ddb, hI4b,
          hfacea, hk1dddb, hpin4b, hk1ddddb, hdvdDK, hdvdDW⟩ := hC
      refine ⟨a, b, hab, ha, hb, hd2a, hpsia, hd2b, hpsib, hCf1, hCf2,
        hw2b, hk1b, hw2db, hk1db, hbetab, hCsecond, hk1ddb, hI4b,
        hfacea, hk1dddb, hpin4b, hk1ddddb, hdvdDK, hdvdDW, ?_⟩
      by_cases hd2da : d2.derivative.eval a = 0
      · left
        have hb2a : b2.eval a = 0 := by
          have h0 : H.derivative.eval a * b2.eval a * psi.eval a =
              0 := by
            linear_combination (6 : k) * hCf1 -
              6 * w2.eval a * hd2da
          have h1 : H.derivative.eval a * b2.eval a = 0 :=
            (mul_eq_zero.mp h0).resolve_right hpsia
          exact (mul_eq_zero.mp h1).resolve_left (hsimple a ha)
        have hd2dda : d2.derivative.derivative.eval a * k1.eval a =
            0 := by
          linear_combination hCsecond -
            2 * k1.derivative.eval a * hd2da
        have hface3 : d2.derivative.derivative.derivative.eval a *
              k1.eval a +
            3 * (d2.derivative.derivative.eval a *
              k1.derivative.eval a) = 0 := by
          linear_combination hfacea -
            3 * k1.derivative.derivative.eval a * hd2da
        exact ⟨hd2da, hb2a, hd2dda, mul_eq_zero.mp hd2dda, hface3⟩
      · right
        have hk1a0 : k1.eval a = 0 :=
          (mul_eq_zero.mp hCf2).resolve_left hd2da
        have hk1da0 : k1.derivative.eval a = 0 := by
          have hprod : d2.derivative.eval a *
              k1.derivative.eval a = 0 := by
            linear_combination (1 / 2 : k) * hCsecond -
              (1 / 2 : k) *
                d2.derivative.derivative.eval a * hk1a0
          exact (mul_eq_zero.mp hprod).resolve_left hd2da
        have hk1dda0 : k1.derivative.derivative.eval a = 0 := by
          have hprod : d2.derivative.eval a *
              k1.derivative.derivative.eval a = 0 := by
            linear_combination (1 / 3 : k) * hfacea -
              (1 / 3 : k) *
                d2.derivative.derivative.derivative.eval a *
                hk1a0 -
              d2.derivative.derivative.eval a * hk1da0
          exact (mul_eq_zero.mp hprod).resolve_left hd2da
        have hdvdk1 : H ∣ k1 :=
          rDivisorSeventh_dvd_of_two_root_evals_68 H k1 hdeg hsimple
            a b hab ha hb hk1a0 hk1b
        obtain ⟨k2, hk2'⟩ := hdvdk1
        have hk2ne' : k2 ≠ 0 :=
          fun h0 => hk1ne (by rw [hk2', h0, mul_zero])
        have hd2k2 : d2 * k2 = H ^ 3 * m := by
          apply mul_left_cancel₀ hH
          have h' := hdk
          rw [hk2'] at h'
          linear_combination h'
        exact ⟨hd2da, hk1a0, hk1da0, hk1dda0, ⟨k2, hk2'⟩, k2, hk2',
          hk2ne', hd2k2⟩
  · exact Or.inr (Or.inl hphiDvd)
  · exact Or.inr (Or.inr htrans)

end RDivisorLowerZeroAllocationSource68

end Max11DegreeRoutes
