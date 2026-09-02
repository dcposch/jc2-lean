import Fable68ScaleTwoAlignedNonsquareRDivisorLowerZeroScratch

/-! # Allocation split of the fresh `H ∣ d₂ψ` on the `H ∣ r` lower-zero branch

The lower-zero refinement of the preserved `H ∣ r` branch ended with the
fresh divisibility `H ∣ d₂ψ` and no honest contradiction.  Here that
divisibility is consumed by the exact coordinate allocation split
(root allocation on the split simple quadratic, never primality): either
`H ∣ d₂`, or `H ∣ ψ`, or the two distinct core roots are allocated
transversely between `d₂` and `ψ`.  On `d₂ = H·d₃` the cleared `I₄` face
de-cores completely to `w₂d₃ = −(1/6)b₂ψ`, the row cofactor relation
descends to `d₃k₁ = H³m`, and the exact quotient row `Q₄ = 0` factors one
core power further, `Q₄ = H·Q₃`, so `Q₃ = 0` holds with the per-root tie
`T₃(a)d₃(a) = c₂(a)U₁(a)`.  On `ψ = H·ψ₂` the branch certifies `H³ ∣ φ₁`
and `H² ∣ w₂d₂`, and the `ψ`-shape forces `H ∣ β − 2A₁w₂` with
`β = (4/3)e₃ − (4/81)A₁³ + (2/3)γA₁ + ε`, pinning `β(a) = 2A₁(a)w₂(a)` at
every core root.  On the transverse allocation the first differentiated
faces are extracted: at the `d₂`-root `w₂(a)d₂'(a) = −(1/6)H'(a)b₂(a)ψ(a)`
and `d₂'(a)k₁(a) = 0`, while at the `ψ`-root `w₂` and `k₁` vanish to
second order (`w₂(b) = w₂'(b) = 0`, `k₁(b) = k₁'(b) = 0`) and `β(b) = 0`.
No unavailable `x`-degree bounds are used and no branch is closed; the
`H ∣ φ₁` and transverse two-root siblings of the outer split are
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

section RDivisorLowerZeroNextAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Cofactor of the core power of `S₁` once `d₂ = H·d₃`. -/
def rDivisorDTwoSZero68 (A1 b2 d3 : k[X]) (alpha : k) : k[X] :=
  C (4 / 3 : k) * d3 + C (4 / 9 : k) * A1 * b2 + C alpha * b2

/-- Cofactor of the core power of `U₂` once `d₂ = H·d₃`. -/
def rDivisorDTwoUOne68
    (A1 b2 c2 d3 : k[X]) (alpha gamma : k) : k[X] :=
  C (4 / 9 : k) * b2 * c2 + C (4 / 9 : k) * A1 * d3 -
    C (4 / 27 : k) * A1 ^ 2 * b2 + C alpha * d3 +
    C (2 / 3 * gamma : k) * b2

/-- Exact quotient of the lower-zero quotient row `Q₄` by the fifth core
power once `d₂ = H·d₃`. -/
def rDivisorDTwoQuotient68
    (H A1 b2 c2 d3 e3 : k[X]) (alpha gamma epsilon eta : k) : k[X] :=
  let S0 := rDivisorDTwoSZero68 A1 b2 d3 alpha
  let T3 := rDivisorLowerZeroTThree68 H A1 b2 c2 e3 alpha gamma epsilon
  let U1 := rDivisorDTwoUOne68 A1 b2 c2 d3 alpha gamma
  let V4 := rDivisorLowerZeroVFour68 H A1 b2 c2 (H * d3) e3
    alpha gamma epsilon eta
  H * U1 * c2.derivative +
    T3 * ((C 2 + C 2 - C 3) * H.derivative * d3 +
      C 2 * H * d3.derivative) +
    C 3 * H * S0 * e3.derivative -
    C 3 * H * b2 * V4.derivative -
    c2 * ((C 2 * C 2 - C 5 + C 2) * H.derivative * U1 +
      C 2 * H * U1.derivative) -
    H * d3 * T3.derivative

/-- Exact gap polynomial `β − 2A₁w₂` forced into the core on the
`H ∣ ψ` allocation, with `β = (4/3)e₃ − (4/81)A₁³ + (2/3)γA₁ + ε`. -/
def rDivisorPsiDivisorBetaGap68
    (A1 e3 w2 : k[X]) (gamma epsilon : k) : k[X] :=
  C (4 / 3 : k) * e3 - C (4 / 81 : k) * A1 ^ 3 +
    C (2 / 3 * gamma : k) * A1 + C epsilon - C 2 * A1 * w2

/-- On `d₂ = H·d₃` the quotient row `Q₄` factors one core power further
with the exact fifth-power cofactor. -/
theorem rDivisorDTwo_quotient_factor_68
    (H A1 b2 c2 d3 e3 : k[X]) (alpha gamma epsilon eta : k) :
    rDivisorLowerZeroQuotient68 H A1 b2 c2 (H * d3) e3
        alpha gamma epsilon eta =
      H * rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
        alpha gamma epsilon eta := by
  have hS : rDivisorLowerZeroSOne68 H A1 b2 (H * d3) alpha =
      H * rDivisorDTwoSZero68 A1 b2 d3 alpha := by
    simp only [rDivisorLowerZeroSOne68, rDivisorDTwoSZero68]
    ring
  have hU : rDivisorLowerZeroUTwo68 H A1 b2 c2 (H * d3) alpha gamma =
      H * rDivisorDTwoUOne68 A1 b2 c2 d3 alpha gamma := by
    simp only [rDivisorLowerZeroUTwo68, rDivisorDTwoUOne68]
    ring
  simp only [rDivisorLowerZeroQuotient68, rDivisorDTwoQuotient68]
  rw [hS, hU]
  simp only [derivative_mul]
  ring

/-- At a core root the fifth-power quotient collapses to the single
product `H'(a)·(T₃(a)d₃(a) − c₂(a)U₁(a))`. -/
theorem rDivisorDTwo_quotient_eval_68
    (H A1 b2 c2 d3 e3 : k[X]) (alpha gamma epsilon eta : k) (a : k)
    (ha : H.eval a = 0) :
    (rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
        alpha gamma epsilon eta).eval a =
      H.derivative.eval a *
        ((rDivisorLowerZeroTThree68 H A1 b2 c2 e3
            alpha gamma epsilon).eval a * d3.eval a -
          c2.eval a *
            (rDivisorDTwoUOne68 A1 b2 c2 d3 alpha gamma).eval a) := by
  simp only [rDivisorDTwoQuotient68, eval_add, eval_sub, eval_mul,
    eval_pow, eval_C, ha, zero_mul, mul_zero, zero_add, add_zero,
    sub_zero, zero_sub]
  ring

/-- The vanished fifth-power quotient and the descended row cofactor
relation yield the exact per-root faces of the `H ∣ d₂` allocation. -/
theorem rDivisorDTwo_root_faces_68
    (H A1 b2 c2 d3 e3 k1 m : k[X]) (alpha gamma epsilon eta : k)
    (hQ3 : rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
      alpha gamma epsilon eta = 0)
    (hdk3 : d3 * k1 = H ^ 3 * m)
    (a : k) (ha : H.eval a = 0) (hh : H.derivative.eval a ≠ 0) :
    (rDivisorLowerZeroTThree68 H A1 b2 c2 e3
        alpha gamma epsilon).eval a * d3.eval a =
      c2.eval a * (rDivisorDTwoUOne68 A1 b2 c2 d3 alpha gamma).eval a ∧
    d3.eval a * k1.eval a = 0 := by
  constructor
  · have hQa := congrArg (fun P : k[X] => P.eval a) hQ3
    simp only [eval_zero] at hQa
    rw [rDivisorDTwo_quotient_eval_68 H A1 b2 c2 d3 e3
      alpha gamma epsilon eta a ha] at hQa
    have hface := (mul_eq_zero.mp hQa).resolve_left hh
    linear_combination hface
  · have h := congrArg (fun P : k[X] => P.eval a) hdk3
    simp only [eval_mul, eval_pow, eval_C, ha, zero_pow, zero_mul] at h
    linear_combination h

/-- Exact first differentiated faces at a transverse `d₂ = 0`, `ψ ≠ 0`
core root: the cleared `I₄` face loads `d₂'` against the retained `ψ`
value and the row cofactor relation kills `d₂'k₁`. -/
theorem rDivisorDPsiTransverse_dRoot_faces_68
    (H b2 w2 d2 psi k1 m : k[X]) (a : k)
    (ha : H.eval a = 0) (hd2a : d2.eval a = 0)
    (hwd : w2 * d2 = -(C (1 / 6 : k)) * (H * b2 * psi))
    (hdk : d2 * k1 = H ^ 4 * m) :
    w2.eval a * d2.derivative.eval a =
        -(1 / 6 : k) *
          (H.derivative.eval a * b2.eval a * psi.eval a) ∧
      d2.derivative.eval a * k1.eval a = 0 := by
  have hpow4 : (H ^ 4 : k[X]).derivative =
      C 4 * H ^ 3 * H.derivative := by
    rw [derivative_pow]
    norm_num
  constructor
  · have h := congrArg (fun P : k[X] => P.derivative.eval a) hwd
    simp only [derivative_mul, derivative_neg, derivative_C, neg_zero,
      zero_mul, zero_add, eval_add, eval_mul, eval_neg, eval_C, ha,
      hd2a, mul_zero, add_zero] at h
    linear_combination h
  · have h := congrArg (fun P : k[X] => P.derivative.eval a) hdk
    simp only [derivative_mul, hpow4, eval_add, eval_mul, eval_pow,
      eval_C, ha, hd2a, zero_pow, zero_mul, mul_zero, zero_add,
      add_zero] at h
    linear_combination h

/-- Exact faces at a transverse `d₂ ≠ 0`, `ψ = 0` core root: both `w₂`
and `k₁` vanish to second order. -/
theorem rDivisorDPsiTransverse_psiRoot_faces_68
    (H b2 w2 d2 psi k1 m : k[X]) (b : k)
    (hb : H.eval b = 0) (hd2b : d2.eval b ≠ 0)
    (hpsib : psi.eval b = 0)
    (hwdb : (w2 * d2).eval b = 0)
    (hdkb : d2.eval b * k1.eval b = 0)
    (hwd : w2 * d2 = -(C (1 / 6 : k)) * (H * b2 * psi))
    (hdk : d2 * k1 = H ^ 4 * m) :
    w2.eval b = 0 ∧ k1.eval b = 0 ∧
      w2.derivative.eval b = 0 ∧ k1.derivative.eval b = 0 := by
  have hpow4 : (H ^ 4 : k[X]).derivative =
      C 4 * H ^ 3 * H.derivative := by
    rw [derivative_pow]
    norm_num
  have hw2b : w2.eval b = 0 := by
    have h : w2.eval b * d2.eval b = 0 := by
      simpa only [eval_mul] using hwdb
    exact (mul_eq_zero.mp h).resolve_right hd2b
  have hk1b : k1.eval b = 0 := (mul_eq_zero.mp hdkb).resolve_left hd2b
  refine ⟨hw2b, hk1b, ?_, ?_⟩
  · have h := congrArg (fun P : k[X] => P.derivative.eval b) hwd
    simp only [derivative_mul, derivative_neg, derivative_C, neg_zero,
      zero_mul, zero_add, eval_add, eval_mul, eval_neg, eval_C, hb,
      hpsib, hw2b, mul_zero, add_zero] at h
    have hprod : w2.derivative.eval b * d2.eval b = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hprod).resolve_right hd2b
  · have h := congrArg (fun P : k[X] => P.derivative.eval b) hdk
    simp only [derivative_mul, hpow4, eval_add, eval_mul, eval_pow,
      eval_C, hb, hk1b, zero_pow, zero_mul, mul_zero, zero_add,
      add_zero] at h
    have hprod : d2.eval b * k1.derivative.eval b = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hprod).resolve_left hd2b

end RDivisorLowerZeroNextAlgebra68

section RDivisorLowerZeroNextSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Allocation split of the fresh `H ∣ d₂ψ` on the `H ∣ r` lower-zero
branch.  The full lower-zero packet is transported unchanged, and its
final divisibility is consumed by the coordinate allocation split: on
`H ∣ d₂` the `I₄` face de-cores completely (`w₂d₃ = −(1/6)b₂ψ`), the row
cofactor relation descends to `d₃k₁ = H³m` and the quotient row factors
one core power further with the per-root tie `T₃d₃ = c₂U₁`; on `H ∣ ψ`
the branch certifies `H³ ∣ φ₁`, `H² ∣ w₂d₂` and `H ∣ β − 2A₁w₂`; on the
transverse allocation the first differentiated faces are extracted and
`w₂`, `k₁` vanish to second order at the `ψ`-root with the `β`-pin
`β(b) = 0`.  No `x`-degree bounds are available, so no allocation is
eliminated; the `H ∣ φ₁` and transverse two-root siblings of the outer
split are transported literally. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneRDivisorLowerZeroNextPacket
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
              d3 ≠ 0) ∨
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
                  2 * A1.eval a * w2.eval a)) ∨
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
                  2 / 3 * S.gamma * A1.eval b + S.epsilon = 0))) ∨
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
    S.terminalAfterLowerOneRDivisorLowerZeroPacket (H := H) hdeg hp hq
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
        hdkdvd, hval, hd2ne, hk1ne⟩ := hmain
    have hsplit := simpleQuadratic_dvd_product_coordinate_split_68
      H d2 psi hdeg hsimple hdpsi
    refine ⟨s, t1, y1, A1, c2, e3, psi, m, hs, ht1c, ht1sc, hp4sc,
      hy1c, hy1sc, hdvdt, hdvdp4, hdvdp3, hA1def, hAf, hc2def, hCf,
      he3def, hEf, heDot, hpsidef, hphi2, hphidvd2, hphidvd1, hwd,
      hwddvd, hlowerB, hrowfact, hQ0, hdpsi, hfaces, hmdef, hdk,
      hdkdvd, hval, hd2ne, hk1ne, ?_⟩
    rcases hsplit with hd2dvd | hpsidvd | hmix
    · left
      obtain ⟨d3, hd3⟩ := hd2dvd
      have hwdA : w2 * d3 = -(C (1 / 6 : k)) * (b2 * psi) := by
        apply mul_left_cancel₀ hH
        have hwd' := hwd
        rw [hd3] at hwd'
        linear_combination hwd'
      have hdkA : d3 * k1 = H ^ 3 * m := by
        apply mul_left_cancel₀ hH
        have hdk' := hdk
        rw [hd3] at hdk'
        linear_combination hdk'
      have hQfact := rDivisorDTwo_quotient_factor_68 H A1 b2 c2 d3 e3
        S.alpha S.gamma S.epsilon S.eta
      have hQ3 : rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
          S.alpha S.gamma S.epsilon S.eta = 0 := by
        have hQ0' := hQ0
        rw [hd3] at hQ0'
        have hz : H * rDivisorDTwoQuotient68 H A1 b2 c2 d3 e3
            S.alpha S.gamma S.epsilon S.eta = 0 := by
          rw [← hQfact]
          exact hQ0'
        exact (mul_eq_zero.mp hz).resolve_left hH
      have hd3ne : d3 ≠ 0 := by
        intro h0
        exact hd2ne (by rw [hd3, h0, mul_zero])
      exact ⟨d3, hd3, ⟨d3, hd3⟩, hwdA, hdkA, ⟨m, hdkA⟩, hQfact, hQ3,
        fun a ha => rDivisorDTwo_root_faces_68 H A1 b2 c2 d3 e3 k1 m
          S.alpha S.gamma S.epsilon S.eta hQ3 hdkA a ha (hsimple a ha),
        hd3ne⟩
    · right
      left
      obtain ⟨psi2, hpsi2⟩ := hpsidvd
      have hphi3 : phi1 = H ^ 3 * psi2 := by
        rw [hphi2, hpsi2]
        ring
      have hwdB : w2 * d2 =
          -(C (1 / 6 : k)) * (H ^ 2 * (b2 * psi2)) := by
        rw [hwd, hpsi2]
        ring
      have hpsiroot : ∀ a : k, H.eval a = 0 → psi.eval a = 0 := by
        intro a ha
        rw [hpsi2]
        simp [ha]
      have hbetaface : ∀ a : k, H.eval a = 0 →
          (4 / 3 : k) * e3.eval a - (4 / 81 : k) * A1.eval a ^ 3 +
              2 / 3 * S.gamma * A1.eval a + S.epsilon =
            2 * A1.eval a * w2.eval a := by
        intro a ha
        have hpsieval : psi.eval a =
            2 * ((4 / 3 : k) * e3.eval a -
              (4 / 81 : k) * A1.eval a ^ 3 +
              2 / 3 * S.gamma * A1.eval a + S.epsilon) -
            4 * A1.eval a * w2.eval a := by
          rw [hpsidef, hc2def]
          exact rDivisorLowerZero_psi_eval_68 H A1 b2 e3 w2
            S.gamma S.epsilon a ha
        have h0 := hpsiroot a ha
        rw [hpsieval] at h0
        linear_combination (1 / 2 : k) * h0
      have hgapdvd : H ∣ rDivisorPsiDivisorBetaGap68 A1 e3 w2
          S.gamma S.epsilon := by
        apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
        intro a ha
        simp only [rDivisorPsiDivisorBetaGap68, eval_add, eval_sub,
          eval_mul, eval_pow, eval_C]
        linear_combination hbetaface a ha
      exact ⟨psi2, hpsi2, ⟨psi2, hpsi2⟩, hphi3, ⟨psi2, hphi3⟩, hwdB,
        ⟨-(C (1 / 6 : k)) * (b2 * psi2), by rw [hwdB]; ring⟩, hgapdvd,
        fun a ha => ⟨hpsiroot a ha, hbetaface a ha⟩⟩
    · right
      right
      obtain ⟨a, b, hab, ha, hb, hd2a, hpsia, hd2b, hpsib⟩ := hmix
      have hdfaces := rDivisorDPsiTransverse_dRoot_faces_68
        H b2 w2 d2 psi k1 m a ha hd2a hwd hdk
      have hfb := hfaces b hb
      have hpfaces := rDivisorDPsiTransverse_psiRoot_faces_68
        H b2 w2 d2 psi k1 m b hb hd2b hpsib hfb.1 hfb.2.2 hwd hdk
      have hbetab : (4 / 3 : k) * e3.eval b -
          (4 / 81 : k) * A1.eval b ^ 3 +
          2 / 3 * S.gamma * A1.eval b + S.epsilon = 0 := by
        have hpsieval : psi.eval b =
            2 * ((4 / 3 : k) * e3.eval b -
              (4 / 81 : k) * A1.eval b ^ 3 +
              2 / 3 * S.gamma * A1.eval b + S.epsilon) -
            4 * A1.eval b * w2.eval b := by
          rw [hpsidef, hc2def]
          exact rDivisorLowerZero_psi_eval_68 H A1 b2 e3 w2
            S.gamma S.epsilon b hb
        have h0 := hpsib
        rw [hpsieval] at h0
        linear_combination (1 / 2 : k) * h0 +
          2 * A1.eval b * hpfaces.1
      exact ⟨a, b, hab, ha, hb, hd2a, hpsia, hd2b, hpsib,
        hdfaces.1, hdfaces.2, hpfaces.1, hpfaces.2.1,
        hpfaces.2.2.1, hpfaces.2.2.2, hbetab⟩
  · exact Or.inr (Or.inl hphiDvd)
  · exact Or.inr (Or.inr htrans)

end RDivisorLowerZeroNextSource68

end Max11DegreeRoutes
