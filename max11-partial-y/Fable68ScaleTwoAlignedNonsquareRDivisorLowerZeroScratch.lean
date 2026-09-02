import Fable68ScaleTwoAlignedNonsquareRDivisorScratch

/-! # Lower-zero row specialized to the preserved `H ∣ r` branch

The larger transported lower row `terminalLowerZeroCleared68 = 0` had so
far been consumed only by the mixed-allocation elimination; here it is
specialized to the `H ∣ r` branch of the coordinate split, on which the
exact divisor cascade gives `A₀ = H·A₁`, `E₀ = H³·e₃`, `Ė = H⁴·e₃'` and
`b₁ = H·b₂`, `d₁ = H·d₂`.  The `W`-shape identity sharpens the cascade to
a *second*-order kill `C₀ = H²·c₂`, and the `Φ`-shape identity then forces
`φ₁ = H²·ψ` with the exact cofactor
`ψ = (8/3)e₃ + (40/81)A₁³ − (16/9)A₁c₂ − (8/27)Hb₂² − (4/3)γA₁ + 2ε`:
the `H ∣ r` branch lands *inside* the `H ∣ φ₁` regime, one core power
deeper.  Intersecting with the `I₄` face `b₂φ₁ + 6Hw₂d₂ = 0` clears one
core factor exactly, `w₂d₂ = −(1/6)Hb₂ψ`.  Substituting the five kills
into the cleared lower row extracts the full fourth power,
`row = H⁴·Q₄`, so the exact quotient row `Q₄ = 0` holds; its value at a
core root collapses to `−H'(a)·d₂(a)·β(a)` with
`β = (4/3)e₃ − (4/81)A₁³ + (2/3)γA₁ + ε` and `ψ(a) = 2β(a) − 4A₁(a)w₂(a)`,
so together with the cleared `I₄` face every core root satisfies
`d₂(a)ψ(a) = 0`, i.e. `H ∣ d₂ψ`.  No honest contradiction is available:
the witness `b₂ = w₂ = 0`, `ψ` free, `d₂ = H⁴`, `k₁ = −Cj` satisfies the
`I₄` face, the cleared last row and all the divisibilities, and the source
API carries no `x`-degree bounds on the quotient polynomials, so the
sharpened residual is returned with the `H ∣ φ₁` and transverse two-root
siblings transported literally. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section RDivisorLowerZeroAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Scalar bridge `6 · C(1/6) = 1` used to divide the cleared `I₄` face by
the unit `6` exactly. -/
theorem rDivisorLowerZeroSixUnit68 : (6 : k[X]) * C (1 / 6 : k) = 1 := by
  rw [show (6 : k[X]) = C (6 : k) from (C_ofNat 6).symm, ← map_mul,
    show (6 : k) * (1 / 6 : k) = 1 by norm_num, map_one]

/-- Cofactor of the single core power of `S₀` on the `H ∣ r` branch. -/
def rDivisorLowerZeroSOne68 (H A1 b2 d2 : k[X]) (alpha : k) : k[X] :=
  C (4 / 3 : k) * d2 + C (4 / 9 : k) * H * A1 * b2 + C alpha * H * b2

/-- Cofactor of the third core power of `T₀` on the `H ∣ r` branch. -/
def rDivisorLowerZeroTThree68
    (H A1 b2 c2 e3 : k[X]) (alpha gamma epsilon : k) : k[X] :=
  C (4 / 3 : k) * e3 + C (2 / 9 : k) * H * b2 ^ 2 +
    C (4 / 9 : k) * A1 * c2 - C (4 / 81 : k) * A1 ^ 3 +
    C alpha * c2 + C (2 / 3 * gamma : k) * A1 + C epsilon

/-- Cofactor of the second core power of `U₀` on the `H ∣ r` branch. -/
def rDivisorLowerZeroUTwo68
    (H A1 b2 c2 d2 : k[X]) (alpha gamma : k) : k[X] :=
  C (4 / 9 : k) * H * b2 * c2 + C (4 / 9 : k) * A1 * d2 -
    C (4 / 27 : k) * H * A1 ^ 2 * b2 + C alpha * d2 +
    C (2 / 3 * gamma : k) * H * b2

/-- Cofactor of the fourth core power of `V₀` on the `H ∣ r` branch. -/
def rDivisorLowerZeroVFour68
    (H A1 b2 c2 d2 e3 : k[X]) (alpha gamma epsilon eta : k) : k[X] :=
  C (2 / 9 : k) * c2 ^ 2 + C (4 / 9 : k) * b2 * d2 +
    C (4 / 9 : k) * A1 * e3 - C (4 / 27 : k) * H * A1 * b2 ^ 2 -
    C (4 / 27 : k) * A1 ^ 2 * c2 + C (5 / 243 : k) * A1 ^ 4 +
    C alpha * e3 +
    C gamma * (C (2 / 3 : k) * c2 - C (1 / 9 : k) * A1 ^ 2) +
    C (1 / 3 : k) * C epsilon * A1 + C eta

/-- Exact cofactor `ψ` of the two core powers of `φ₁` forced on the
`H ∣ r` branch by the `Φ`-shape identity. -/
def rDivisorLowerZeroPhiQuotient68
    (H A1 b2 c2 e3 : k[X]) (gamma epsilon : k) : k[X] :=
  C (8 / 3 : k) * e3 + C (40 / 81 : k) * A1 ^ 3 -
    C (16 / 9 : k) * A1 * c2 - C (8 / 27 : k) * H * b2 ^ 2 -
    C (4 / 3 * gamma : k) * A1 + C (2 * epsilon : k)

/-- Exact quotient of the cleared lower-zero row by the full fourth core
power extracted on the `H ∣ r` branch. -/
def rDivisorLowerZeroQuotient68
    (H A1 b2 c2 d2 e3 : k[X]) (alpha gamma epsilon eta : k) : k[X] :=
  let S1 := rDivisorLowerZeroSOne68 H A1 b2 d2 alpha
  let T3 := rDivisorLowerZeroTThree68 H A1 b2 c2 e3 alpha gamma epsilon
  let U2 := rDivisorLowerZeroUTwo68 H A1 b2 c2 d2 alpha gamma
  let V4 := rDivisorLowerZeroVFour68 H A1 b2 c2 d2 e3 alpha gamma epsilon eta
  H * U2 * c2.derivative +
    T3 * ((C 2 - C 3) * H.derivative * d2 + C 2 * H * d2.derivative) +
    C 3 * H * S1 * e3.derivative -
    C 3 * H ^ 2 * b2 * V4.derivative -
    c2 * ((C 2 * C 2 - C 5) * H.derivative * U2 + C 2 * H * U2.derivative) -
    H * d2 * T3.derivative

/-- The scaled `Φ` numerator collapses to a clean third core power once all
five branch kills are substituted. -/
theorem rDivisorLowerZero_phi_factor_68
    (H A1 b2 c2 e3 : k[X]) (gamma epsilon : k) :
    terminalScaledPhi68 H (H * A1) (H * b2) (H ^ 2 * c2) (H ^ 3 * e3)
        gamma epsilon =
      H ^ 3 * rDivisorLowerZeroPhiQuotient68 H A1 b2 c2 e3 gamma epsilon := by
  simp only [terminalScaledPhi68, rDivisorLowerZeroPhiQuotient68]
  ring

/-- Substituting the five branch kills into the cleared lower-zero row
extracts the full fourth core power with the exact quotient cofactor. -/
theorem rDivisorLowerZero_row_factor_68
    (H A1 b2 c2 d2 e3 : k[X]) (alpha gamma epsilon eta : k) :
    terminalLowerZeroCleared68 H (H * A1) (H * b2) (H ^ 2 * c2) (H * d2)
        (H ^ 3 * e3) alpha gamma epsilon eta =
      H ^ 4 * rDivisorLowerZeroQuotient68 H A1 b2 c2 d2 e3
        alpha gamma epsilon eta := by
  have hpow2 : (H ^ 2).derivative = C 2 * H * H.derivative := by
    rw [derivative_pow]
    norm_num
  have hpow3 : (H ^ 3).derivative = C 3 * H ^ 2 * H.derivative := by
    rw [derivative_pow]
    norm_num
  have hpow4 : (H ^ 4).derivative = C 4 * H ^ 3 * H.derivative := by
    rw [derivative_pow]
    norm_num
  have hS : terminalLowerZeroSNumerator68 H (H * A1) (H * b2) (H * d2)
      alpha = H * rDivisorLowerZeroSOne68 H A1 b2 d2 alpha := by
    simp only [terminalLowerZeroSNumerator68, rDivisorLowerZeroSOne68]
    ring
  have hT : terminalLowerOneTNumerator68 H (H * A1) (H * b2) (H ^ 2 * c2)
      (H ^ 3 * e3) alpha gamma epsilon =
      H ^ 3 * rDivisorLowerZeroTThree68 H A1 b2 c2 e3
        alpha gamma epsilon := by
    simp only [terminalLowerOneTNumerator68, rDivisorLowerZeroTThree68]
    ring
  have hU : terminalLowerOneUNumerator68 H (H * A1) (H * b2) (H ^ 2 * c2)
      (H * d2) alpha gamma =
      H ^ 2 * rDivisorLowerZeroUTwo68 H A1 b2 c2 d2 alpha gamma := by
    simp only [terminalLowerOneUNumerator68, rDivisorLowerZeroUTwo68]
    ring
  have hV : terminalVNumerator68 H (H * A1) (H * b2) (H ^ 2 * c2) (H * d2)
      (H ^ 3 * e3) alpha gamma epsilon eta =
      H ^ 4 * rDivisorLowerZeroVFour68 H A1 b2 c2 d2 e3
        alpha gamma epsilon eta := by
    simp only [terminalVNumerator68, rDivisorLowerZeroVFour68]
    ring
  have hCD : terminalLowerZeroCDot68 H (H ^ 2 * c2) =
      H ^ 3 * c2.derivative := by
    simp only [terminalLowerZeroCDot68, derivative_mul, hpow2]
    ring
  have hDD : terminalLowerOneDTwoDot68 H (H * d2) =
      H * ((C 2 - C 3) * H.derivative * d2 + C 2 * H * d2.derivative) := by
    simp only [terminalLowerOneDTwoDot68, derivative_mul]
    ring
  have hED : terminalEDerivativeNumerator68 H (H ^ 3 * e3) =
      H ^ 4 * e3.derivative := rDivisor_derivative_collapse_68 H e3
  have hVD : terminalVDerivativeNumerator68 H
      (H ^ 4 * rDivisorLowerZeroVFour68 H A1 b2 c2 d2 e3
        alpha gamma epsilon eta) =
      H ^ 5 * (rDivisorLowerZeroVFour68 H A1 b2 c2 d2 e3
        alpha gamma epsilon eta).derivative := by
    simp only [terminalVDerivativeNumerator68, derivative_mul, hpow4]
    ring
  have hUD : terminalLowerOneUTwoDot68 H
      (H ^ 2 * rDivisorLowerZeroUTwo68 H A1 b2 c2 d2 alpha gamma) =
      H ^ 2 * ((C 2 * C 2 - C 5) * H.derivative *
          rDivisorLowerZeroUTwo68 H A1 b2 c2 d2 alpha gamma +
        C 2 * H *
          (rDivisorLowerZeroUTwo68 H A1 b2 c2 d2 alpha gamma).derivative) := by
    simp only [terminalLowerOneUTwoDot68, derivative_mul, hpow2]
    ring
  have hTD : terminalLowerZeroTDot68 H
      (H ^ 3 * rDivisorLowerZeroTThree68 H A1 b2 c2 e3
        alpha gamma epsilon) =
      H ^ 4 * (rDivisorLowerZeroTThree68 H A1 b2 c2 e3
        alpha gamma epsilon).derivative := by
    simp only [terminalLowerZeroTDot68, derivative_mul, hpow3]
    ring
  simp only [terminalLowerZeroCleared68, rDivisorLowerZeroQuotient68]
  rw [hS, hT, hU, hV, hCD, hDD, hED, hVD, hUD, hTD]
  ring

/-- At a core root the quotient row collapses to the single product
`−H'(a)·d₂(a)·β(a)` with `β = (4/3)e₃ − (4/81)A₁³ + (2/3)γA₁ + ε`. -/
theorem rDivisorLowerZero_quotient_eval_68
    (H A1 b2 c2 d2 e3 : k[X]) (alpha gamma epsilon eta : k) (a : k)
    (ha : H.eval a = 0) :
    (rDivisorLowerZeroQuotient68 H A1 b2 c2 d2 e3
        alpha gamma epsilon eta).eval a =
      -(H.derivative.eval a * (d2.eval a *
        ((4 / 3 : k) * e3.eval a - (4 / 81 : k) * A1.eval a ^ 3 +
          2 / 3 * gamma * A1.eval a + epsilon))) := by
  simp only [rDivisorLowerZeroQuotient68, rDivisorLowerZeroSOne68,
    rDivisorLowerZeroTThree68, rDivisorLowerZeroUTwo68,
    rDivisorLowerZeroVFour68, eval_add, eval_sub, eval_mul, eval_pow,
    eval_neg, eval_C, ha, zero_mul, mul_zero, zero_add, add_zero,
    sub_zero, zero_sub, zero_pow]
  ring

/-- At a core root the `φ₁` cofactor is `2β(a) − 4A₁(a)w₂(a)` once the
second-order `C` kill is substituted. -/
theorem rDivisorLowerZero_psi_eval_68
    (H A1 b2 e3 w2 : k[X]) (gamma epsilon : k) (a : k)
    (ha : H.eval a = 0) :
    (rDivisorLowerZeroPhiQuotient68 H A1 b2
        (C (1 / 3 : k) * A1 ^ 2 + C (9 / 4 : k) * w2 -
          C (3 / 2 * gamma : k)) e3 gamma epsilon).eval a =
      2 * ((4 / 3 : k) * e3.eval a - (4 / 81 : k) * A1.eval a ^ 3 +
        2 / 3 * gamma * A1.eval a + epsilon) -
      4 * A1.eval a * w2.eval a := by
  simp only [rDivisorLowerZeroPhiQuotient68, eval_add, eval_sub, eval_mul,
    eval_pow, eval_neg, eval_C, ha, zero_mul, mul_zero, zero_add,
    add_zero, sub_zero, zero_sub]
  ring

/-- The quotient row and the cleared `I₄` face together kill `d₂ψ` at
every core root. -/
theorem rDivisorLowerZero_root_faces_68
    (H A1 b2 c2 d2 e3 w2 psi : k[X]) (alpha gamma epsilon eta : k)
    (hc2 : c2 = C (1 / 3 : k) * A1 ^ 2 + C (9 / 4 : k) * w2 -
      C (3 / 2 * gamma : k))
    (hpsi : psi = rDivisorLowerZeroPhiQuotient68 H A1 b2 c2 e3
      gamma epsilon)
    (hwd : w2 * d2 = -(C (1 / 6 : k)) * (H * b2 * psi))
    (hQ : rDivisorLowerZeroQuotient68 H A1 b2 c2 d2 e3
      alpha gamma epsilon eta = 0)
    (a : k) (ha : H.eval a = 0) (hh : H.derivative.eval a ≠ 0) :
    (w2 * d2).eval a = 0 ∧ (d2 * psi).eval a = 0 := by
  have hwda : (w2 * d2).eval a = 0 := by
    rw [hwd]
    simp [ha]
  have hQa := congrArg (fun P : k[X] => P.eval a) hQ
  simp only [eval_zero] at hQa
  rw [rDivisorLowerZero_quotient_eval_68 H A1 b2 c2 d2 e3
    alpha gamma epsilon eta a ha] at hQa
  have hbeta : d2.eval a *
      ((4 / 3 : k) * e3.eval a - (4 / 81 : k) * A1.eval a ^ 3 +
        2 / 3 * gamma * A1.eval a + epsilon) = 0 :=
    (mul_eq_zero.mp (neg_eq_zero.mp hQa)).resolve_left hh
  refine ⟨hwda, ?_⟩
  have hpsia : psi.eval a =
      2 * ((4 / 3 : k) * e3.eval a - (4 / 81 : k) * A1.eval a ^ 3 +
        2 / 3 * gamma * A1.eval a + epsilon) -
      4 * A1.eval a * w2.eval a := by
    rw [hpsi, hc2]
    exact rDivisorLowerZero_psi_eval_68 H A1 b2 e3 w2 gamma epsilon a ha
  have hwda' : w2.eval a * d2.eval a = 0 := by
    simpa only [eval_mul] using hwda
  rw [eval_mul, hpsia]
  linear_combination 2 * hbeta - 4 * A1.eval a * hwda'

end RDivisorLowerZeroAlgebra68

section RDivisorLowerZeroSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Lower-zero refinement of the preserved `H ∣ r` branch.  Beyond the
divisor cascade, the shape identities force the second-order kills
`C₀ = H²c₂` and `φ₁ = H²ψ` (so the branch certifies `H ∣ φ₁` with exact
cofactor), the `I₄` face clears to `w₂d₂ = −(1/6)Hb₂ψ`, the transported
lower-zero row descends to the exact quotient `Q₄ = 0` past the full
fourth core power, and every core root satisfies `w₂d₂ = d₂ψ = d₂k₁ = 0`,
i.e. `H ∣ d₂ψ`.  Without `x`-degree data no contradiction is honest, so
the sharpened residual is returned; the `H ∣ φ₁` and transverse two-root
siblings are transported literally. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneRDivisorLowerZeroPacket
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
          d2 ≠ 0 ∧ k1 ≠ 0) ∨
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
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, phi1, k1, b2, d2, w2,
      hg, hgr, ht, hX, hY, hb1, hd1, hw1, hphi, hb2, hd2, hw2,
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
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hW1 : terminalScaledW68 H A0 C0 S.gamma = H * w1 := by
    dsimp only [A0, C0, terminalScaledW68]
    rw [← hw1]
    simp only [cubicWNumerator68]
  have hW2 : terminalScaledW68 H A0 C0 S.gamma = H ^ 2 * w2 := by
    rw [hW1, hw2]
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
    rw [← hphi, ← hb1]
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
    rw [← hBred, ← hb1]
  have hdred : terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2) =
      d1 := by
    apply mul_left_cancel₀ hH
    rw [← hDred, ← hd1]
  have hlower : terminalLowerZeroCleared68 H A0 b1 C0 d1 E0
      S.alpha S.gamma S.epsilon S.eta = 0 := by
    simpa only [A0, C0, E0, ← hAred, hbred, ← hCred, hdred, ← hEred]
      using htransport
  have hrootCoordinate : ∀ a : k, H.eval a = 0 →
      (r * phi1).eval a = 0 := by
    intro a ha
    by_contra hrphi
    have hrne : r.eval a ≠ 0 := by
      intro hr0
      exact hrphi (by simp [eval_mul, hr0])
    have hpne : phi1.eval a ≠ 0 := by
      intro hp0
      exact hrphi (by simp [eval_mul, hp0])
    rcases hroots a ha with hr0 | hp0 | hdouble
    · exact False.elim (hrne hr0)
    · exact False.elim (hpne hp0)
    · let L : k[X] := Polynomial.X - C a
      have hLH : L ∣ H := by
        dsimp only [L]
        rw [dvd_iff_isRoot]
        exact ha
      obtain ⟨M, hHM⟩ := hLH
      have hMval : M.eval a = H.derivative.eval a := by
        have hder := congrArg (fun P : k[X] => P.derivative.eval a) hHM
        dsimp only [L] at hder
        simp only [derivative_mul, derivative_sub, derivative_X,
          derivative_C, eval_add, eval_mul, eval_sub, eval_one, eval_X,
          eval_C, sub_self, zero_mul, one_mul, add_zero] at hder
        simpa using hder.symm
      have hMne : M.eval a ≠ 0 := by
        rw [hMval]
        exact hsimple a ha
      have hboot := terminalAfterLowerOne_mixedRoot_bootstrap_68
        H b2 phi1 w2 d2 eDot k1 j a ha hpne hdouble.2.2.2.2
        hdouble.1 hdouble.2.1 hdouble.2.2.1 hdouble.2.2.2.1 hI4 hrow'
      obtain ⟨B, hB⟩ := hboot.1
      obtain ⟨D, hD⟩ := hboot.2
      have hL : L ≠ 0 := by
        dsimp only [L]
        exact X_sub_C_ne_zero a
      have hrowQ : L ^ 2 * M * B * w2 * eDot - D * k1 = C j * M ^ 4 := by
        apply mul_left_cancel₀ (pow_ne_zero 4 hL)
        rw [hHM, hB, hD] at hrow'
        linear_combination hrow'
      have hDprod : D.eval a * k1.eval a = -j * (M.eval a) ^ 4 := by
        have he := congrArg (fun P : k[X] => P.eval a) hrowQ
        dsimp only [L] at he
        simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C,
          eval_X, sub_self, zero_pow, zero_mul] at he
        linear_combination -he
      have hDne : D.eval a ≠ 0 := by
        intro hDz
        rw [hDz, zero_mul] at hDprod
        exact (mul_ne_zero (neg_ne_zero.mpr hj) (pow_ne_zero 4 hMne))
          hDprod.symm
      have hbLocal : b1 = L ^ 6 * (M * B) := by
        rw [hb2, hB, hHM]
        ring
      have hdLocal : d1 = L ^ 5 * (M * D) := by
        rw [hd2, hD, hHM]
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
      exact False.elim (terminalLowerZero_mixedLocal_impossible_68
        M A0 b1 C0 d1 E0 (M * B) (M * D) phi1 w2
        S.alpha S.gamma S.epsilon S.eta a hMne
        (by simp only [eval_mul]; exact mul_ne_zero hMne hDne) hpne
        (by simpa only [L] using hbLocal)
        (by simpa only [L] using hdLocal)
        (by simpa only [L] using hClocal)
        (by simpa only [L] using hElocal)
        (by simpa only [L] using hlowerLocal))
  have hdvd : H ∣ r * phi1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      hrootCoordinate
  have hsplit := simpleQuadratic_dvd_product_coordinate_split_68
    H r phi1 hdeg hsimple hdvd
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hI4, hrow, ?_⟩
  rcases hsplit with hr | hphiDvd | htrans
  · left
    obtain ⟨s, hs⟩ := hr
    obtain ⟨ht1c, ht1sc, hp4sc, hy1c, hy1sc⟩ :=
      rDivisor_coordinate_cascade_68 H r t X Yd (p.coeff 3) (p.coeff 4)
        s hs ht hX hY
    have hnum := rDivisor_numerator_cascade_68 H s
      (C (1 / 3 : k) * (H * s ^ 2 + X))
      (C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd))
      (p.coeff 0) (p.coeff 1) (p.coeff 2)
    let t1w : k[X] := C (1 / 3 : k) * (H * s ^ 2 + X)
    let y1w : k[X] := C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)
    let A1w : k[X] := t1w - C (5 / 12 : k) * H * s ^ 2
    let c2w : k[X] := C (1 / 3 : k) * A1w ^ 2 + C (9 / 4 : k) * w2 -
      C (3 / 2 * S.gamma : k)
    let e3w : k[X] := p.coeff 0 - C (1 / 6 : k) * p.coeff 1 * s +
      C (1 / 36 : k) * p.coeff 2 * s ^ 2 -
      C (1 / 216 : k) * H * y1w * s ^ 3 +
      C (1 / 1296 : k) * H ^ 2 * t1w * s ^ 4 -
      C (5 / 46656 : k) * H ^ 3 * s ^ 6
    let psiw : k[X] := rDivisorLowerZeroPhiQuotient68 H A1w b2 c2w e3w
      S.gamma S.epsilon
    let mw : k[X] := H * b2 * w2 * e3w.derivative - C j
    have hAf : cubicANumerator68 t r = H * A1w := by
      dsimp only [A1w, t1w]
      rw [ht1c, hs]
      exact hnum.1
    have hEf : cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r = H ^ 3 * e3w := by
      dsimp only [e3w, y1w, t1w]
      rw [ht1c, hs, hy1c]
      exact hnum.2.2
    have hCshapeLit := hCshape
    dsimp only [A0, C0] at hCshapeLit
    have hCf : cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r =
        H ^ 2 * c2w := by
      rw [hCshapeLit, hAf]
      dsimp only [c2w]
      ring
    have heDot : terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) = H ^ 4 * e3w.derivative := by
      rw [hEf]
      exact rDivisor_derivative_collapse_68 H e3w
    have hphi2 : phi1 = H ^ 2 * psiw := by
      apply mul_left_cancel₀ hH
      rw [← hPhi]
      dsimp only [A0, C0, E0]
      rw [hb2, hAf, hCf, hEf, rDivisorLowerZero_phi_factor_68]
      dsimp only [psiw]
      ring
    have hwd6 : (6 : k[X]) * (w2 * d2) = -(H * b2 * psiw) := by
      apply mul_left_cancel₀ hH
      linear_combination hI4 - b2 * hphi2
    have hwd : w2 * d2 = -(C (1 / 6 : k)) * (H * b2 * psiw) := by
      linear_combination C (1 / 6 : k) * hwd6 -
        w2 * d2 * rDivisorLowerZeroSixUnit68 (k := k)
    have hlowerB : terminalLowerZeroCleared68 H (cubicANumerator68 t r)
        (H * b2) (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
        (H * d2)
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)
        S.alpha S.gamma S.epsilon S.eta = 0 := by
      rw [← hb2, ← hd2]
      exact hlower
    have hbranch : terminalLowerZeroCleared68 H (H * A1w) (H * b2)
        (H ^ 2 * c2w) (H * d2) (H ^ 3 * e3w)
        S.alpha S.gamma S.epsilon S.eta = 0 := by
      rw [← hAf, ← hCf, ← hEf]
      exact hlowerB
    have hQ0 : rDivisorLowerZeroQuotient68 H A1w b2 c2w d2 e3w
        S.alpha S.gamma S.epsilon S.eta = 0 := by
      have hz : H ^ 4 * rDivisorLowerZeroQuotient68 H A1w b2 c2w d2 e3w
          S.alpha S.gamma S.epsilon S.eta = 0 := by
        rw [← rDivisorLowerZero_row_factor_68]
        exact hbranch
      exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 4 hH)
    have hrowE : H * b2 * w2 * (H ^ 4 * e3w.derivative) - d2 * k1 =
        C j * H ^ 4 := by
      rw [← heDot]
      exact hrow'
    have hdk : d2 * k1 = H ^ 4 * mw :=
      rDivisor_row_cofactor_68 H b2 w2 d2 k1 e3w j hrowE
    have hfaces : ∀ a : k, H.eval a = 0 →
        (w2 * d2).eval a = 0 ∧ (d2 * psiw).eval a = 0 ∧
          d2.eval a * k1.eval a = 0 := by
      intro a ha
      have hf := rDivisorLowerZero_root_faces_68 H A1w b2 c2w d2 e3w w2
        psiw S.alpha S.gamma S.epsilon S.eta rfl rfl hwd hQ0 a ha
        (hsimple a ha)
      refine ⟨hf.1, hf.2, ?_⟩
      have hdka := congrArg (fun P : k[X] => P.eval a) hdk
      simpa [ha] using hdka
    have hdpsi : H ∣ d2 * psiw :=
      dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
        (fun a ha => (hfaces a ha).2.1)
    have hval : ∀ a : k, H.eval a = 0 →
        mw.eval a = -j ∧ mw.eval a ≠ 0 := by
      intro a ha
      have h1 : mw.eval a = -j :=
        rDivisor_cofactor_eval_68 H b2 w2 e3w j a ha
      exact ⟨h1, by rw [h1]; exact neg_ne_zero.mpr hj⟩
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hdeg]
      decide
    obtain ⟨a0, ha0⟩ := IsAlgClosed.exists_root H hdegne
    have ha0' : H.eval a0 = 0 := ha0
    have hne := rDivisor_factors_ne_zero_68 H d2 k1 mw j hj hH hdk
      a0 ha0' (hval a0 ha0').1
    exact ⟨s, t1w, y1w, A1w, c2w, e3w, psiw, mw,
      hs, ht1c, ht1sc, hp4sc, hy1c, hy1sc,
      ⟨t1w, ht1c⟩, ⟨t1w, hp4sc⟩, ⟨y1w, hy1c⟩,
      rfl, hAf, rfl, hCf, rfl, hEf, heDot, rfl, hphi2,
      ⟨psiw, hphi2⟩, ⟨H * psiw, by rw [hphi2]; ring⟩,
      hwd, ⟨-(C (1 / 6 : k)) * (b2 * psiw), by rw [hwd]; ring⟩,
      hlowerB,
      rDivisorLowerZero_row_factor_68 H A1w b2 c2w d2 e3w
        S.alpha S.gamma S.epsilon S.eta,
      hQ0, hdpsi, hfaces, rfl, hdk, ⟨mw, hdk⟩, hval, hne.1, hne.2⟩
  · exact Or.inr (Or.inl hphiDvd)
  · right
    right
    obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb⟩ := htrans
    have hrf := terminalAfterLowerOne_rRoot_faces_68
      H b2 phi1 w2 d2 eDot k1 j a ha hpa hI4 hrow'
    have hpf := terminalAfterLowerOne_phiRoot_faces_68
      H b2 phi1 w2 d2 eDot k1 j b hb hpb (hsimple b hb) hI4 hrow'
    exact ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb,
      hrf.1, hrf.2.1, hrf.2.2.1, hrf.2.2.2,
      hpf.1, hpf.2.1, hpf.2.2⟩

end RDivisorLowerZeroSource68

end Max11DegreeRoutes
