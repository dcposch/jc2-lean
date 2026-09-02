import Fable68ScaleTwoAlignedNonsquareRDivisorLowerZeroNextScratch

/-! # Refinement of the three-way `d₂/ψ` allocation on the `H ∣ r` lower-zero branch

The allocation split of the fresh `H ∣ d₂ψ` left three live children.  Here
each child consumes its next genuinely unused row exactly, with every new
scalar backwired to the source data through the retained shape identities.

On the `d₂ = H·d₃` child the descended cofactor relation `d₃k₁ = H³m`
supplies `H ∣ d₃k₁`, which the coordinate allocation split (root allocation,
never primality) refines into three grandchildren: on `d₃ = H·d₄` the
`I₄` face inverts to `b₂ψ = −6H(w₂d₄)` (so `H ∣ b₂ψ` is fresh and
`d₂ = H²d₄`), the cofactor relation descends to `d₄k₁ = H²m`, and the spent
`Q₃` root tie collapses to the new per-root face `c₂(a)·b₂(a)w₂(a) = 0`
because the `U₁` cofactor evaluates to `b₂w₂` at any `d₃`-root; on
`k₁ = H·k₂` the relation descends to `d₃k₂ = H²m` with the nonvanishing
second-order face `d₃''k₂ + 2d₃'k₂' + d₃k₂'' = −2j·H'² ≠ 0` at every core
root; on the transverse allocation the exact third-order core power forces
`d₃` to vanish to third order at its root and `k₁` to vanish to third order
at its root, with `b₂(a)ψ(a) = 0` at the `d₃`-root.

On the `ψ = H·ψ₂` child the retained `H ∣ w₂d₂` is split the same way: on
`w₂ = H·w₃` the `I₄` face de-cores to `w₃d₂ = −(1/6)H(b₂ψ₂)` and the spent
`β`-gap pin upgrades to the full divisibility `H ∣ β` of the source-wired
numerator `β = (4/3)e₃ − (4/81)A₁³ + (2/3)γA₁ + ε`; on `d₂ = H·d₃` the
spent quotient factorisation and root-face lemmas replay opaquely
(`Q₃ = 0`, `T₃d₃ = c₂U₁`, `d₃k₁ = H³m`) inside the `ψ`-divisor regime; on
the transverse allocation `w₂` vanishes to second order at its root with
`k₁` vanishing to third order there and `β(a) = 0`, while at the `d₂`-root
`d₂` vanishes to second order with the honest faces `d₂''k₁ = 0` and
`w₂d₂'' = −(1/3)H'²(b₂ψ₂)`.

On the transverse `d₂/ψ` child the next unused second-derivative faces are
extracted: at the `d₂`-root `d₂''k₁ + 2d₂'k₁' = 0`, and at the `ψ`-root the
quartic core forces `k₁''(b) = 0` (third-order vanishing of `k₁`) and the
`I₄` face loads `w₂''(b)d₂(b) = −(1/3)H'(b)b₂(b)ψ'(b)`.

No `x`-degree bounds are available, so no child is eliminated; every honest
residual is preserved and the `H ∣ φ₁` and outer transverse siblings are
transported literally. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section RDivisorLowerZeroFollowingAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Source-wired `β` numerator `(4/3)e₃ − (4/81)A₁³ + (2/3)γA₁ + ε`. -/
def rDivisorBetaNumerator68 (A1 e3 : k[X]) (gamma epsilon : k) : k[X] :=
  C (4 / 3 : k) * e3 - C (4 / 81 : k) * A1 ^ 3 +
    C (2 / 3 * gamma : k) * A1 + C epsilon

/-- The `β` numerator is the spent `β`-gap polynomial plus `2A₁w₂`,
backwiring it to the `H ∣ ψ` child data. -/
theorem rDivisorBetaNumerator_gap_bridge_68
    (A1 e3 w2 : k[X]) (gamma epsilon : k) :
    rDivisorBetaNumerator68 A1 e3 gamma epsilon =
      rDivisorPsiDivisorBetaGap68 A1 e3 w2 gamma epsilon +
        C 2 * A1 * w2 := by
  simp only [rDivisorBetaNumerator68, rDivisorPsiDivisorBetaGap68]
  ring

/-- The first derivative of a square-cored product vanishes at a core
root. -/
theorem squareCore_derivative_eval_zero_68
    (H m : k[X]) (x : k) (hx : H.eval x = 0) :
    ((H ^ 2 * m).derivative).eval x = 0 := by
  have hpow2 : (H ^ 2 : k[X]).derivative = C 2 * H * H.derivative := by
    rw [derivative_pow]
    norm_num
  simp only [derivative_mul, hpow2, eval_add, eval_mul, eval_pow, eval_C,
    hx, zero_mul, mul_zero, zero_pow, zero_add, add_zero]
  ring

/-- The second derivative of a square-cored product evaluates to
`2H'(x)²m(x)` at a core root. -/
theorem squareCore_second_derivative_eval_68
    (H m : k[X]) (x : k) (hx : H.eval x = 0) :
    ((H ^ 2 * m).derivative.derivative).eval x =
      2 * H.derivative.eval x ^ 2 * m.eval x := by
  have hpow2 : (H ^ 2 : k[X]).derivative = C 2 * H * H.derivative := by
    rw [derivative_pow]
    norm_num
  simp only [derivative_mul, derivative_add, hpow2, derivative_C, zero_mul,
    zero_add, eval_add, eval_mul, eval_pow, eval_C, hx, mul_zero, add_zero,
    zero_pow]
  ring

/-- The second derivative of a cube-cored product vanishes at a core
root. -/
theorem cubeCore_second_derivative_eval_zero_68
    (H m : k[X]) (x : k) (hx : H.eval x = 0) :
    ((H ^ 3 * m).derivative.derivative).eval x = 0 := by
  have hpow2 : (H ^ 2 : k[X]).derivative = C 2 * H * H.derivative := by
    rw [derivative_pow]
    norm_num
  have hpow3 : (H ^ 3 : k[X]).derivative = C 3 * H ^ 2 * H.derivative := by
    rw [derivative_pow]
    norm_num
  simp only [derivative_mul, derivative_add, hpow3, hpow2, derivative_C,
    zero_mul, zero_add, eval_add, eval_mul, eval_pow, eval_C, hx, mul_zero,
    add_zero, zero_pow]
  ring

/-- First differentiated face of a square-cored product relation at a core
root. -/
theorem squareCore_first_face_68 (H d ka m : k[X]) (x : k)
    (hdk : d * ka = H ^ 2 * m) (hx : H.eval x = 0) :
    d.derivative.eval x * ka.eval x + d.eval x * ka.derivative.eval x =
      0 := by
  have h1 : ((d * ka).derivative).eval x = 0 := by
    rw [hdk]
    exact squareCore_derivative_eval_zero_68 H m x hx
  simp only [derivative_mul, eval_add, eval_mul] at h1
  linear_combination h1

/-- Second differentiated face of a square-cored product relation at a
core root: the loaded value `2H'(x)²m(x)` survives. -/
theorem squareCore_second_face_68 (H d ka m : k[X]) (x : k)
    (hdk : d * ka = H ^ 2 * m) (hx : H.eval x = 0) :
    d.derivative.derivative.eval x * ka.eval x +
      2 * (d.derivative.eval x * ka.derivative.eval x) +
      d.eval x * ka.derivative.derivative.eval x =
      2 * H.derivative.eval x ^ 2 * m.eval x := by
  have h2 : ((d * ka).derivative.derivative).eval x =
      2 * H.derivative.eval x ^ 2 * m.eval x := by
    rw [hdk]
    exact squareCore_second_derivative_eval_68 H m x hx
  simp only [derivative_mul, derivative_add, eval_add, eval_mul] at h2
  linear_combination h2

/-- Second differentiated face of a quartic-cored product relation at a
core root: the face closes to zero. -/
theorem quarticCore_second_face_68 (H d ka m : k[X]) (x : k)
    (hdk : d * ka = H ^ 4 * m) (hx : H.eval x = 0) :
    d.derivative.derivative.eval x * ka.eval x +
      2 * (d.derivative.eval x * ka.derivative.eval x) +
      d.eval x * ka.derivative.derivative.eval x = 0 := by
  have h2 : ((d * ka).derivative.derivative).eval x = 0 := by
    have hshape : d * ka = H ^ 3 * (H * m) := by
      rw [hdk]
      ring
    rw [hshape]
    exact cubeCore_second_derivative_eval_zero_68 H (H * m) x hx
  simp only [derivative_mul, derivative_add, eval_add, eval_mul] at h2
  linear_combination h2

/-- A cube-cored product relation forces the factor vanishing at a core
root to vanish to third order there (the cofactor is a unit at that
root). -/
theorem cubeCore_transverse_jets_68 (H d ka m : k[X]) (x : k)
    (hdk : d * ka = H ^ 3 * m) (hx : H.eval x = 0)
    (hd0 : d.eval x = 0) (hkne : ka.eval x ≠ 0) :
    d.derivative.eval x = 0 ∧ d.derivative.derivative.eval x = 0 := by
  have h1 : ((d * ka).derivative).eval x = 0 := by
    have hshape : d * ka = H ^ 2 * (H * m) := by
      rw [hdk]
      ring
    rw [hshape]
    exact squareCore_derivative_eval_zero_68 H (H * m) x hx
  simp only [derivative_mul, eval_add, eval_mul] at h1
  have hd1 : d.derivative.eval x = 0 := by
    have hprod : d.derivative.eval x * ka.eval x = 0 := by
      linear_combination h1 - ka.derivative.eval x * hd0
    exact (mul_eq_zero.mp hprod).resolve_right hkne
  have h2 : ((d * ka).derivative.derivative).eval x = 0 := by
    rw [hdk]
    exact cubeCore_second_derivative_eval_zero_68 H m x hx
  simp only [derivative_mul, derivative_add, eval_add, eval_mul] at h2
  have hd2 : d.derivative.derivative.eval x * ka.eval x = 0 := by
    linear_combination h2 - 2 * ka.derivative.eval x * hd1 -
      ka.derivative.derivative.eval x * hd0
  exact ⟨hd1, (mul_eq_zero.mp hd2).resolve_right hkne⟩

/-- Second differentiated face of a linear-cored product relation at a
core root where the cofactor also vanishes. -/
theorem linearCore_second_face_68 (H w d M : k[X]) (b : k)
    (hb : H.eval b = 0) (hMb : M.eval b = 0)
    (hwd : w * d = H * M) :
    w.derivative.derivative.eval b * d.eval b +
      2 * (w.derivative.eval b * d.derivative.eval b) +
      w.eval b * d.derivative.derivative.eval b =
      2 * H.derivative.eval b * M.derivative.eval b := by
  have h := congrArg (fun P : k[X] => P.derivative.derivative.eval b) hwd
  simp only [derivative_mul, derivative_add, eval_add, eval_mul, hb, hMb,
    zero_mul, mul_zero, add_zero, zero_add] at h
  linear_combination h

end RDivisorLowerZeroFollowingAlgebra68

section RDivisorLowerZeroFollowingSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Refinement of the three-way `d₂/ψ` allocation on the `H ∣ r`
lower-zero branch.  The full allocation packet is transported unchanged.
The `d₂ = H·d₃` child splits its fresh `H ∣ d₃k₁`: on `d₃ = H·d₄` the
`I₄` face inverts to `b₂ψ = −6H(w₂d₄)` with the new per-root face
`c₂b₂w₂ = 0`; on `k₁ = H·k₂` the descended relation `d₃k₂ = H²m` carries
the nonvanishing second-order face `−2jH'²`; transversely the cubic core
forces third-order vanishing of `d₃` and `k₁` at their respective roots.
The `ψ = H·ψ₂` child splits the retained `H ∣ w₂d₂`: on `w₂ = H·w₃` the
`β` numerator is fully divisible by the core; on `d₂ = H·d₃` the spent
quotient and root-face lemmas replay opaquely; transversely `w₂` and `d₂`
vanish to second order at their roots with `k₁` third-order at the
`w₂`-root and the loaded face `w₂d₂'' = −(1/3)H'²(b₂ψ₂)`.  The transverse
`d₂/ψ` child gains its second-derivative faces `d₂''k₁ + 2d₂'k₁' = 0`,
`k₁''(b) = 0` and `w₂''(b)d₂(b) = −(1/3)H'(b)b₂(b)ψ'(b)`.  No allocation
is eliminated; the `H ∣ φ₁` and outer transverse siblings are transported
literally. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneRDivisorLowerZeroFollowingPacket
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
                  d4 ≠ 0) ∨
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
                  k2 ≠ 0) ∨
                (∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
                  d3.eval a = 0 ∧ k1.eval a ≠ 0 ∧
                  d3.eval b ≠ 0 ∧ k1.eval b = 0 ∧
                  d3.derivative.eval a = 0 ∧
                  d3.derivative.derivative.eval a = 0 ∧
                  b2.eval a * psi.eval a = 0 ∧
                  k1.derivative.eval b = 0 ∧
                  k1.derivative.derivative.eval b = 0))) ∨
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
                      0)) ∨
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
                  d3 ≠ 0) ∨
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
                      (b2.eval b * psi2.eval b))))) ∨
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
                  psi.derivative.eval b)))) ∨
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
    S.terminalAfterLowerOneRDivisorLowerZeroNextPacket (H := H) hdeg hp hq
      hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hI4, hrow, ?_⟩
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
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
    · -- `d₂ = H·d₃` child: split the fresh `H ∣ d₃k₁`.
      left
      obtain ⟨d3, hd3, hd2dvd, hwdA, hdkA, hdk3dvd, hQfact, hQ3,
          hAfaces, hd3ne⟩ := hA
      have hdvd1 : H ∣ d3 * k1 := ⟨H ^ 2 * m, by rw [hdkA]; ring⟩
      refine ⟨d3, hd3, hd2dvd, hwdA, hdkA, hdk3dvd, hQfact, hQ3,
        hAfaces, hd3ne, hdvd1, ?_⟩
      rcases simpleQuadratic_dvd_product_coordinate_split_68 H d3 k1
          hdeg hsimple hdvd1 with hd3dvd | hk1dvd | hmixA
      · left
        obtain ⟨d4, hd4⟩ := hd3dvd
        have hd2d4 : d2 = H ^ 2 * d4 := by
          rw [hd3, hd4]
          ring
        have hwdA' := hwdA
        rw [hd4] at hwdA'
        have hbpsi : b2 * psi = -(6 : k[X]) * (H * (w2 * d4)) := by
          have h6 : (6 : k[X]) * (w2 * (H * d4)) =
              -(((6 : k[X]) * C (1 / 6 : k)) * (b2 * psi)) := by
            rw [hwdA']
            ring
          rw [rDivisorLowerZeroSixUnit68, one_mul] at h6
          linear_combination h6
        have hbpsidvd : H ∣ b2 * psi :=
          ⟨-(6 : k[X]) * (w2 * d4), by rw [hbpsi]; ring⟩
        have hd4k : d4 * k1 = H ^ 2 * m := by
          apply mul_left_cancel₀ hH
          have hdkA' := hdkA
          rw [hd4] at hdkA'
          linear_combination hdkA'
        have hd4ne : d4 ≠ 0 := fun h0 => hd3ne (by rw [hd4, h0, mul_zero])
        refine ⟨d4, hd4, hd2d4, ⟨d4, hd2d4⟩, hbpsi, hbpsidvd, hd4k,
          ⟨m, hd4k⟩, ?_, hd4ne⟩
        intro a ha
        have hd3a : d3.eval a = 0 := by
          rw [hd4]
          simp [ha]
        refine ⟨?_, ?_, ?_⟩
        · have h := congrArg (fun P : k[X] => P.eval a) hbpsi
          simp only [eval_mul, eval_neg, eval_ofNat, ha, zero_mul,
            mul_zero, neg_zero] at h
          exact h
        · have h := congrArg (fun P : k[X] => P.eval a) hd4k
          simp only [eval_mul, eval_pow, ha, zero_pow, zero_mul] at h
          linear_combination h
        · have htie := (hAfaces a ha).1
          have hU1a : (rDivisorDTwoUOne68 A1 b2 c2 d3
              S.alpha S.gamma).eval a = b2.eval a * w2.eval a := by
            simp only [rDivisorDTwoUOne68, hc2def, eval_add, eval_sub,
              eval_mul, eval_pow, eval_C, hd3a, mul_zero, add_zero]
            ring
          rw [hd3a, mul_zero, hU1a] at htie
          exact htie.symm
      · right
        left
        obtain ⟨k2, hk2⟩ := hk1dvd
        have hd3k2 : d3 * k2 = H ^ 2 * m := by
          apply mul_left_cancel₀ hH
          have hdkA' := hdkA
          rw [hk2] at hdkA'
          linear_combination hdkA'
        have hk2ne : k2 ≠ 0 := fun h0 => hk1ne (by rw [hk2, h0, mul_zero])
        refine ⟨k2, hk2, ⟨k2, hk2⟩, hd3k2, ⟨m, hd3k2⟩, ?_, hk2ne⟩
        intro a ha
        refine ⟨?_, squareCore_first_face_68 H d3 k2 m a hd3k2 ha, ?_⟩
        · have h := congrArg (fun P : k[X] => P.eval a) hd3k2
          simp only [eval_mul, eval_pow, ha, zero_pow, zero_mul] at h
          linear_combination h
        · have hface := squareCore_second_face_68 H d3 k2 m a hd3k2 ha
          rw [(hval a ha).1] at hface
          linear_combination hface
      · right
        right
        obtain ⟨x, y, hxy, hx, hy, hd3x, hk1x, hd3y, hk1y⟩ := hmixA
        have hjx := cubeCore_transverse_jets_68 H d3 k1 m x hdkA hx
          hd3x hk1x
        have hdkA' : k1 * d3 = H ^ 3 * m := by
          rw [mul_comm]
          exact hdkA
        have hjy := cubeCore_transverse_jets_68 H k1 d3 m y hdkA' hy
          hk1y hd3y
        have hbpsix : b2.eval x * psi.eval x = 0 := by
          have h := congrArg (fun P : k[X] => P.eval x) hwdA
          simp only [eval_mul, eval_neg, eval_C, hd3x, mul_zero] at h
          have h' : (-(1 / 6 : k)) * (b2.eval x * psi.eval x) = 0 := by
            linear_combination -h
          rcases mul_eq_zero.mp h' with h6 | hbp
          · exact absurd h6 (by norm_num)
          · exact hbp
        exact ⟨x, y, hxy, hx, hy, hd3x, hk1x, hd3y, hk1y, hjx.1, hjx.2,
          hbpsix, hjy.1, hjy.2⟩
    · -- `ψ = H·ψ₂` child: split the retained `H ∣ w₂d₂`.
      right
      left
      obtain ⟨psi2, hpsi2, hpsidvdH, hphi3, hphi3dvd, hwdB, hwd2dvd,
          hgapdvd, hBfaces⟩ := hB
      refine ⟨psi2, hpsi2, hpsidvdH, hphi3, hphi3dvd, hwdB, hwd2dvd,
        hgapdvd, hBfaces, ?_⟩
      rcases simpleQuadratic_dvd_product_coordinate_split_68 H w2 d2
          hdeg hsimple hwddvd with hw2dvd | hd2dvd' | hmixB
      · left
        obtain ⟨w3, hw3⟩ := hw2dvd
        have hw3d : w3 * d2 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) := by
          apply mul_left_cancel₀ hH
          have h := hwdB
          rw [hw3] at h
          linear_combination h
        have hw2root : ∀ a : k, H.eval a = 0 → w2.eval a = 0 := by
          intro a ha
          rw [hw3]
          simp [ha]
        have hbeta0 : ∀ a : k, H.eval a = 0 →
            (4 / 3 : k) * e3.eval a - (4 / 81 : k) * A1.eval a ^ 3 +
              2 / 3 * S.gamma * A1.eval a + S.epsilon = 0 := by
          intro a ha
          have hface := (hBfaces a ha).2
          rw [hw2root a ha] at hface
          linear_combination hface
        have hbetadvd : H ∣ rDivisorBetaNumerator68 A1 e3
            S.gamma S.epsilon := by
          apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
          intro a ha
          simp only [rDivisorBetaNumerator68, eval_add, eval_sub,
            eval_mul, eval_pow, eval_C]
          linear_combination hbeta0 a ha
        refine ⟨w3, hw3, ⟨w3, hw3⟩, hw3d,
          ⟨-(C (1 / 6 : k)) * (b2 * psi2), by rw [hw3d]; ring⟩,
          rDivisorBetaNumerator_gap_bridge_68 A1 e3 w2
            S.gamma S.epsilon, hbetadvd, ?_⟩
        intro a ha
        refine ⟨hw2root a ha, ?_, hbeta0 a ha⟩
        have h := congrArg (fun P : k[X] => P.eval a) hw3d
        simp only [eval_mul, eval_neg, eval_C, ha, zero_mul, mul_zero,
          neg_zero] at h
        exact h
      · right
        left
        obtain ⟨d3, hd3B⟩ := hd2dvd'
        have hwd3 : w2 * d3 = -(C (1 / 6 : k)) * (H * (b2 * psi2)) := by
          apply mul_left_cancel₀ hH
          have h := hwdB
          rw [hd3B] at h
          linear_combination h
        have hd3k : d3 * k1 = H ^ 3 * m := by
          apply mul_left_cancel₀ hH
          have h := hdk
          rw [hd3B] at h
          linear_combination h
        have hQfactB := rDivisorDTwo_quotient_factor_68 H A1 b2 c2 d3 e3
          S.alpha S.gamma S.epsilon S.eta
        have hQ3B : rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
            S.alpha S.gamma S.epsilon S.eta = 0 := by
          have h := hQ0
          rw [hd3B, hQfactB] at h
          exact (mul_eq_zero.mp h).resolve_left hH
        have hd3neB : d3 ≠ 0 := fun h0 =>
          hd2ne (by rw [hd3B, h0, mul_zero])
        refine ⟨d3, hd3B, ⟨d3, hd3B⟩, hwd3,
          ⟨-(C (1 / 6 : k)) * (b2 * psi2), by rw [hwd3]; ring⟩,
          hd3k, ⟨m, hd3k⟩, hQfactB, hQ3B, ?_, hd3neB⟩
        intro a ha
        have hroot := rDivisorDTwo_root_faces_68 H A1 b2 c2 d3 e3 k1 m
          S.alpha S.gamma S.epsilon S.eta hQ3B hd3k a ha (hsimple a ha)
        refine ⟨hroot.1, hroot.2, ?_⟩
        have h := congrArg (fun P : k[X] => P.eval a) hwd3
        simp only [eval_mul, eval_neg, eval_C, ha, zero_mul, mul_zero,
          neg_zero] at h
        exact h
      · right
        right
        obtain ⟨x, y, hxy, hx, hy, hw2x, hd2x, hw2y, hd2y⟩ := hmixB
        have hwdBsq : w2 * d2 =
            H ^ 2 * (-(C (1 / 6 : k)) * (b2 * psi2)) := by
          rw [hwdB]
          ring
        have hfx := squareCore_first_face_68 H w2 d2
          (-(C (1 / 6 : k)) * (b2 * psi2)) x hwdBsq hx
        have hw2dx : w2.derivative.eval x = 0 := by
          have hprod : w2.derivative.eval x * d2.eval x = 0 := by
            linear_combination hfx - d2.derivative.eval x * hw2x
          exact (mul_eq_zero.mp hprod).resolve_right hd2x
        have hfy := squareCore_first_face_68 H w2 d2
          (-(C (1 / 6 : k)) * (b2 * psi2)) y hwdBsq hy
        have hd2dy : d2.derivative.eval y = 0 := by
          have hprod : w2.eval y * d2.derivative.eval y = 0 := by
            linear_combination hfy - w2.derivative.eval y * hd2y
          exact (mul_eq_zero.mp hprod).resolve_left hw2y
        have hk1x : k1.eval x = 0 :=
          (mul_eq_zero.mp (hfaces x hx).2.2).resolve_left hd2x
        have hdkH3 : k1 * d2 = H ^ 3 * (H * m) := by
          rw [mul_comm, hdk]
          ring
        have hjkx := cubeCore_transverse_jets_68 H k1 d2 (H * m) x
          hdkH3 hx hk1x hd2x
        have hbetax : (4 / 3 : k) * e3.eval x -
            (4 / 81 : k) * A1.eval x ^ 3 +
            2 / 3 * S.gamma * A1.eval x + S.epsilon = 0 := by
          have hface := (hBfaces x hx).2
          rw [hw2x] at hface
          linear_combination hface
        have hsfy := squareCore_second_face_68 H w2 d2
          (-(C (1 / 6 : k)) * (b2 * psi2)) y hwdBsq hy
        have hMy : (-(C (1 / 6 : k)) * (b2 * psi2)).eval y =
            -(1 / 6 : k) * (b2.eval y * psi2.eval y) := by
          simp only [eval_mul, eval_neg, eval_C]
        have hI4y : w2.eval y * d2.derivative.derivative.eval y =
            -(1 / 3 : k) * (H.derivative.eval y ^ 2 *
              (b2.eval y * psi2.eval y)) := by
          rw [hMy] at hsfy
          linear_combination hsfy - 2 * w2.derivative.eval y * hd2dy -
            w2.derivative.derivative.eval y * hd2y
        have hquarty := quarticCore_second_face_68 H d2 k1 m y hdk hy
        have hd2ddk1y :
            d2.derivative.derivative.eval y * k1.eval y = 0 := by
          linear_combination hquarty - 2 * k1.derivative.eval y * hd2dy -
            k1.derivative.derivative.eval y * hd2y
        exact ⟨x, y, hxy, hx, hy, hw2x, hd2x, hw2y, hd2y, hw2dx, hk1x,
          hjkx.1, hjkx.2, hbetax, hd2dy, hd2ddk1y, hI4y⟩
    · -- Transverse `d₂/ψ` child: next unused second-derivative faces.
      right
      right
      obtain ⟨a, b, hab, ha, hb, hd2a, hpsia, hd2b, hpsib, hCf1, hCf2,
          hw2b, hk1b, hw2db, hk1db, hbetab⟩ := hC
      have hqa := quarticCore_second_face_68 H d2 k1 m a hdk ha
      have hCsecond : d2.derivative.derivative.eval a * k1.eval a +
          2 * (d2.derivative.eval a * k1.derivative.eval a) = 0 := by
        linear_combination hqa -
          k1.derivative.derivative.eval a * hd2a
      have hdkH3b : k1 * d2 = H ^ 3 * (H * m) := by
        rw [mul_comm, hdk]
        ring
      have hjkb := cubeCore_transverse_jets_68 H k1 d2 (H * m) b
        hdkH3b hb hk1b hd2b
      have hwdH : w2 * d2 = H * (-(C (1 / 6 : k)) * (b2 * psi)) := by
        rw [hwd]
        ring
      have hMb0 : (-(C (1 / 6 : k)) * (b2 * psi)).eval b = 0 := by
        simp only [eval_mul, eval_neg, eval_C, hpsib, mul_zero]
      have hlin := linearCore_second_face_68 H w2 d2
        (-(C (1 / 6 : k)) * (b2 * psi)) b hb hMb0 hwdH
      have hMdb : (-(C (1 / 6 : k)) * (b2 * psi)).derivative.eval b =
          -(1 / 6 : k) * (b2.eval b * psi.derivative.eval b) := by
        simp only [derivative_mul, derivative_neg, derivative_C,
          neg_zero, zero_mul, zero_add, eval_add, eval_mul, eval_neg,
          eval_C, hpsib, mul_zero, add_zero]
      have hI4b : w2.derivative.derivative.eval b * d2.eval b =
          -(1 / 3 : k) * (H.derivative.eval b * b2.eval b *
            psi.derivative.eval b) := by
        rw [hMdb] at hlin
        linear_combination hlin - 2 * d2.derivative.eval b * hw2db -
          d2.derivative.derivative.eval b * hw2b
      exact ⟨a, b, hab, ha, hb, hd2a, hpsia, hd2b, hpsib, hCf1, hCf2,
        hw2b, hk1b, hw2db, hk1db, hbetab, hCsecond, hjkb.2, hI4b⟩
  · exact Or.inr (Or.inl hphiDvd)
  · exact Or.inr (Or.inr htrans)

end RDivisorLowerZeroFollowingSource68

end Max11DegreeRoutes
