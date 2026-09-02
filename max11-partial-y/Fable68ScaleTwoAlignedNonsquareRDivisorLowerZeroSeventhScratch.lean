import Fable68ScaleTwoAlignedNonsquareRDivisorLowerZeroFollowingScratch

/-! # Seventh refinement: one honest face beyond the second-derivative ties

Every surviving allocation of the `H ∣ r` lower-zero branch is advanced by
one genuinely unused derivative/root face, extracted from the retained
`I₄` shape `w₂d₂ = −(1/6)Hb₂ψ`, the cleared-row cofactor relation
`d₂k₁ = H⁴m` and its descended forms, with the two simple core roots used
jointly to globalize double-root zero patterns to core divisibility.

On the `d₂ = H²d₄` grandchild the descended square-cored relation
`d₄k₁ = H²m` yields its first- and loaded second-order faces
(`d₄'k₁ + d₄k₁' = 0` and the unit-loaded `−2jH'²`), and the de-cored `I₄`
face `b₂ψ = −6H(w₂d₄)` differentiates once at every core root.  On the
`k₁ = Hk₂` grandchild the third-order face of `d₃k₂ = H²m` loads the fresh
scalars `H''` and `e₃'` through `m' = H'·(b₂w₂e₃')` at each root.  On the
transverse `d₃/k₁` grandchild the cubic core pins the vanishing orders
exactly: `d₃'''(a)k₁(a) = −6jH'(a)³` and `d₃(b)k₁'''(b) = −6jH'(b)³`, so
`d₃` and `k₁` vanish to order exactly three at their roots, and the joint
double-root zeros globalize to `H ∣ d₃'k₁'` and `H ∣ d₃''k₁''`.

On the `w₂ = Hw₃` grandchild the linear-cored `I₄` face differentiates
once (`w₃'d₂ + w₃d₂' = −(1/6)H'(b₂ψ₂)`), the derivative pin
`w₂' = H'w₃` appears at each root, and the quartic relation contributes
its first face.  On the `d₂ = Hd₃` grandchild inside the `ψ`-divisor
regime the cube-cored relation gives its first and second faces and the
linear-cored `I₄` face differentiates once.  On the transverse `w₂/d₂`
grandchild the quartic core forces `k₁'''(a) = 0` with the exact
fourth-order pin `d₂(a)k₁''''(a) = −24jH'(a)⁴` at the `w₂`-root, the
third-order face `d₂'''k₁ + 3d₂''k₁' = 0` at the `d₂`-root, and the joint
zeros globalize to `H ∣ w₂d₂'` and `H ∣ k₁d₂'`.

On the transverse `d₂/ψ` child the third-order face at the `d₂`-root ties
`d₂'''k₁ + 3d₂''k₁' + 3d₂'k₁''`, the `ψ`-root gains `k₁'''(b) = 0` with
the exact pin `d₂(b)k₁''''(b) = −24jH'(b)⁴`, and the joint zeros
globalize to `H ∣ d₂k₁'` and `H ∣ d₂w₂'`.

No `x`-degree bounds are available, so no allocation is eliminated; every
honest residual is preserved and the `H ∣ φ₁` and outer transverse
siblings are transported literally. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

section RDivisorLowerZeroSeventhAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The two given distinct roots exhaust the roots of a degree-two core
(local replica for the `H ∣ r` lower-zero chain). -/
theorem rDivisorSeventhRootPairExhaust68
    (H : k[X]) (hdeg : H.natDegree = 2) (a b c : k) (hab : a ≠ b)
    (ha : H.eval a = 0) (hb : H.eval b = 0) (hc : H.eval c = 0) :
    c = a ∨ c = b := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hlinA : X - C a ∣ H := by
    rw [dvd_iff_isRoot]
    exact ha
  obtain ⟨H1, hH1⟩ := hlinA
  have hH1b : H1.eval b = 0 := by
    have hev := congrArg (fun P : k[X] => P.eval b) hH1
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hev
    rw [hb] at hev
    exact (mul_eq_zero.mp hev.symm).resolve_left
      (sub_ne_zero.mpr (Ne.symm hab))
  have hlinB : X - C b ∣ H1 := by
    rw [dvd_iff_isRoot]
    exact hH1b
  obtain ⟨H2, hH2⟩ := hlinB
  have hfull : H = (X - C a) * ((X - C b) * H2) := by
    rw [hH1, hH2]
  have hH2ne : H2 ≠ 0 := by
    rintro rfl
    rw [mul_zero, mul_zero] at hfull
    exact hH hfull
  have hH2deg : H2.natDegree = 0 := by
    have hXa : (X - C a : k[X]) ≠ 0 := X_sub_C_ne_zero a
    have hXb : (X - C b : k[X]) ≠ 0 := X_sub_C_ne_zero b
    have hmul : H.natDegree =
        (X - C a : k[X]).natDegree + ((X - C b) * H2).natDegree := by
      rw [hfull]
      exact natDegree_mul hXa (mul_ne_zero hXb hH2ne)
    rw [natDegree_mul hXb hH2ne] at hmul
    simp only [natDegree_X_sub_C] at hmul
    rw [hdeg] at hmul
    omega
  have hH2c : H2.eval c ≠ 0 := by
    intro h0
    apply hH2ne
    have hconst := eq_C_of_natDegree_eq_zero hH2deg
    rw [hconst] at h0
    rw [eval_C] at h0
    rw [hconst, h0, C_0]
  have hev := congrArg (fun P : k[X] => P.eval c) hfull
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hev
  rw [hc] at hev
  rcases mul_eq_zero.mp hev.symm with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inr (sub_eq_zero.mp h')
    · exact absurd h' hH2c

/-- Degree-two simple-root transfer, local replica: one zero evaluation at
each of the two distinct core roots globalizes to core divisibility. -/
theorem rDivisorSeventh_dvd_of_two_root_evals_68
    (H P : k[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ x : k, H.eval x = 0 → H.derivative.eval x ≠ 0)
    (a b : k) (hab : a ≠ b) (ha : H.eval a = 0) (hb : H.eval b = 0)
    (hPa : P.eval a = 0) (hPb : P.eval b = 0) : H ∣ P := by
  apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
  intro c hc
  rcases rDivisorSeventhRootPairExhaust68 H hdeg a b c hab ha hb hc with
    rfl | rfl
  · exact hPa
  · exact hPb

/-- First differentiated face of a linear-cored product relation at a
core root. -/
theorem linearCore_first_face_68 (H w d M : k[X]) (b : k)
    (hb : H.eval b = 0) (hwd : w * d = H * M) :
    w.derivative.eval b * d.eval b + w.eval b * d.derivative.eval b =
      H.derivative.eval b * M.eval b := by
  have h := congrArg (fun P : k[X] => P.derivative.eval b) hwd
  simp only [derivative_mul, eval_add, eval_mul, hb, zero_mul,
    add_zero] at h
  linear_combination h

/-- The third derivative of a square-cored product evaluates to
`6H'H''m + 6H'²m'` at a core root. -/
theorem squareCore_third_derivative_eval_68
    (H m : k[X]) (x : k) (hx : H.eval x = 0) :
    ((H ^ 2 * m).derivative.derivative.derivative).eval x =
      6 * (H.derivative.eval x * H.derivative.derivative.eval x) *
          m.eval x +
        6 * H.derivative.eval x ^ 2 * m.derivative.eval x := by
  have hpow2 : (H ^ 2 : k[X]).derivative = C 2 * H * H.derivative := by
    rw [derivative_pow]
    norm_num
  simp only [derivative_mul, derivative_add, hpow2, derivative_C,
    zero_mul, zero_add, eval_add, eval_mul, eval_pow, eval_C, hx,
    mul_zero, add_zero, zero_pow]
  ring

/-- The third derivative of a cube-cored product evaluates to `6H'³m` at
a core root. -/
theorem cubeCore_third_derivative_eval_68
    (H m : k[X]) (x : k) (hx : H.eval x = 0) :
    ((H ^ 3 * m).derivative.derivative.derivative).eval x =
      6 * H.derivative.eval x ^ 3 * m.eval x := by
  have hpow2 : (H ^ 2 : k[X]).derivative = C 2 * H * H.derivative := by
    rw [derivative_pow]
    norm_num
  have hpow3 : (H ^ 3 : k[X]).derivative = C 3 * H ^ 2 * H.derivative := by
    rw [derivative_pow]
    norm_num
  simp only [derivative_mul, derivative_add, hpow3, hpow2, derivative_C,
    zero_mul, zero_add, eval_add, eval_mul, eval_pow, eval_C, hx,
    mul_zero, add_zero, zero_pow]
  ring

/-- The third derivative of a quartic-cored product vanishes at a core
root. -/
theorem quarticCore_third_derivative_eval_zero_68
    (H m : k[X]) (x : k) (hx : H.eval x = 0) :
    ((H ^ 4 * m).derivative.derivative.derivative).eval x = 0 := by
  have hshape : H ^ 4 * m = H ^ 3 * (H * m) := by
    ring
  rw [hshape, cubeCore_third_derivative_eval_68 H (H * m) x hx]
  simp [hx]

/-- The fourth derivative of a quartic-cored product evaluates to
`24H'⁴m` at a core root. -/
theorem quarticCore_fourth_derivative_eval_68
    (H m : k[X]) (x : k) (hx : H.eval x = 0) :
    ((H ^ 4 * m).derivative.derivative.derivative.derivative).eval x =
      24 * H.derivative.eval x ^ 4 * m.eval x := by
  have hpow2 : (H ^ 2 : k[X]).derivative = C 2 * H * H.derivative := by
    rw [derivative_pow]
    norm_num
  have hpow3 : (H ^ 3 : k[X]).derivative = C 3 * H ^ 2 * H.derivative := by
    rw [derivative_pow]
    norm_num
  have hpow4 : (H ^ 4 : k[X]).derivative = C 4 * H ^ 3 * H.derivative := by
    rw [derivative_pow]
    norm_num
  simp only [derivative_mul, derivative_add, hpow4, hpow3, hpow2,
    derivative_C, zero_mul, zero_add, eval_add, eval_mul, eval_pow,
    eval_C, hx, mul_zero, add_zero, zero_pow]
  ring

/-- Third differentiated face of a square-cored product relation at a
core root: the loaded value `6H'H''m + 6H'²m'` survives. -/
theorem squareCore_third_face_68 (H d ka m : k[X]) (x : k)
    (hdk : d * ka = H ^ 2 * m) (hx : H.eval x = 0) :
    d.derivative.derivative.derivative.eval x * ka.eval x +
      3 * (d.derivative.derivative.eval x * ka.derivative.eval x) +
      3 * (d.derivative.eval x * ka.derivative.derivative.eval x) +
      d.eval x * ka.derivative.derivative.derivative.eval x =
      6 * (H.derivative.eval x * H.derivative.derivative.eval x) *
          m.eval x +
        6 * H.derivative.eval x ^ 2 * m.derivative.eval x := by
  have h3 : ((d * ka).derivative.derivative.derivative).eval x =
      6 * (H.derivative.eval x * H.derivative.derivative.eval x) *
          m.eval x +
        6 * H.derivative.eval x ^ 2 * m.derivative.eval x := by
    rw [hdk]
    exact squareCore_third_derivative_eval_68 H m x hx
  simp only [derivative_mul, derivative_add, eval_add, eval_mul] at h3
  linear_combination h3

/-- Second differentiated face of a cube-cored product relation at a core
root: the face closes to zero. -/
theorem cubeCore_second_face_68 (H d ka m : k[X]) (x : k)
    (hdk : d * ka = H ^ 3 * m) (hx : H.eval x = 0) :
    d.derivative.derivative.eval x * ka.eval x +
      2 * (d.derivative.eval x * ka.derivative.eval x) +
      d.eval x * ka.derivative.derivative.eval x = 0 := by
  have h2 : ((d * ka).derivative.derivative).eval x = 0 := by
    rw [hdk]
    exact cubeCore_second_derivative_eval_zero_68 H m x hx
  simp only [derivative_mul, derivative_add, eval_add, eval_mul] at h2
  linear_combination h2

/-- Third differentiated face of a cube-cored product relation at a core
root: the loaded value `6H'³m` survives. -/
theorem cubeCore_third_face_68 (H d ka m : k[X]) (x : k)
    (hdk : d * ka = H ^ 3 * m) (hx : H.eval x = 0) :
    d.derivative.derivative.derivative.eval x * ka.eval x +
      3 * (d.derivative.derivative.eval x * ka.derivative.eval x) +
      3 * (d.derivative.eval x * ka.derivative.derivative.eval x) +
      d.eval x * ka.derivative.derivative.derivative.eval x =
      6 * H.derivative.eval x ^ 3 * m.eval x := by
  have h3 : ((d * ka).derivative.derivative.derivative).eval x =
      6 * H.derivative.eval x ^ 3 * m.eval x := by
    rw [hdk]
    exact cubeCore_third_derivative_eval_68 H m x hx
  simp only [derivative_mul, derivative_add, eval_add, eval_mul] at h3
  linear_combination h3

/-- Third differentiated face of a quartic-cored product relation at a
core root: the face closes to zero. -/
theorem quarticCore_third_face_68 (H d ka m : k[X]) (x : k)
    (hdk : d * ka = H ^ 4 * m) (hx : H.eval x = 0) :
    d.derivative.derivative.derivative.eval x * ka.eval x +
      3 * (d.derivative.derivative.eval x * ka.derivative.eval x) +
      3 * (d.derivative.eval x * ka.derivative.derivative.eval x) +
      d.eval x * ka.derivative.derivative.derivative.eval x = 0 := by
  have h3 : ((d * ka).derivative.derivative.derivative).eval x = 0 := by
    rw [hdk]
    exact quarticCore_third_derivative_eval_zero_68 H m x hx
  simp only [derivative_mul, derivative_add, eval_add, eval_mul] at h3
  linear_combination h3

/-- Fourth differentiated face of a quartic-cored product relation at a
core root: the loaded value `24H'⁴m` survives. -/
theorem quarticCore_fourth_face_68 (H d ka m : k[X]) (x : k)
    (hdk : d * ka = H ^ 4 * m) (hx : H.eval x = 0) :
    d.derivative.derivative.derivative.derivative.eval x * ka.eval x +
      4 * (d.derivative.derivative.derivative.eval x *
        ka.derivative.eval x) +
      6 * (d.derivative.derivative.eval x *
        ka.derivative.derivative.eval x) +
      4 * (d.derivative.eval x *
        ka.derivative.derivative.derivative.eval x) +
      d.eval x * ka.derivative.derivative.derivative.derivative.eval x =
      24 * H.derivative.eval x ^ 4 * m.eval x := by
  have h4 : ((d * ka).derivative.derivative.derivative.derivative).eval
      x = 24 * H.derivative.eval x ^ 4 * m.eval x := by
    rw [hdk]
    exact quarticCore_fourth_derivative_eval_68 H m x hx
  simp only [derivative_mul, derivative_add, eval_add, eval_mul] at h4
  linear_combination h4

end RDivisorLowerZeroSeventhAlgebra68

section RDivisorLowerZeroSeventhSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Seventh refinement of the `H ∣ r` lower-zero branch: every surviving
allocation gains one honest derivative/root face beyond its recorded
second-derivative ties.  The `d₄` grandchild gains the first and loaded
second faces of `d₄k₁ = H²m` and the differentiated de-cored `I₄` face;
the `k₂` grandchild gains the loaded third face of `d₃k₂ = H²m` through
`m' = H'(b₂w₂e₃')`; the transverse `d₃/k₁` grandchild gains the exact
third-order pins `d₃'''(a)k₁(a) = −6jH'(a)³`, `d₃(b)k₁'''(b) = −6jH'(b)³`
and the joint globalizations `H ∣ d₃'k₁'`, `H ∣ d₃''k₁''`; the `w₃`
grandchild gains the pin `w₂' = H'w₃`, the differentiated linear-cored
`I₄` face and the first quartic face; the `d₃` grandchild in the
`ψ`-regime gains the first and second cube faces and the differentiated
linear-cored `I₄` face; the transverse `w₂/d₂` grandchild gains
`k₁'''(a) = 0`, the exact pin `d₂(a)k₁''''(a) = −24jH'(a)⁴`, the
`d₂`-root third face and `H ∣ w₂d₂'`, `H ∣ k₁d₂'`; the transverse `d₂/ψ`
child gains its third-order faces, `k₁'''(b) = 0`, the exact pin
`d₂(b)k₁''''(b) = −24jH'(b)⁴` and `H ∣ d₂k₁'`, `H ∣ d₂w₂'`.  No
allocation is eliminated; the `H ∣ φ₁` and outer transverse siblings are
transported literally. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneRDivisorLowerZeroSeventhPacket
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
                          (w2.eval a * d4.eval a)))) ∨
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
                            e3.derivative.eval a))) ∨
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
                    k1.derivative.derivative))) ∨
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
                      d2.eval a * k1.derivative.eval a = 0)) ∨
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
                          (b2.eval a * psi2.eval a)))) ∨
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
                  H ∣ k1 * d2.derivative))) ∨
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
    S.terminalAfterLowerOneRDivisorLowerZeroFollowingPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hI4, hrow, ?_⟩
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have h6j : -(6 * j) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, not_or]
    exact ⟨by norm_num, hj⟩
  have h24j : -(24 * j) ≠ 0 := by
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
    · -- `d₂ = H·d₃` child: advance each grandchild.
      left
      obtain ⟨d3, hd3, hd2dvd, hwdA, hdkA, hdk3dvd, hQfact, hQ3,
          hAfaces, hd3ne, hdvd1, hAsplit⟩ := hA
      refine ⟨d3, hd3, hd2dvd, hwdA, hdkA, hdk3dvd, hQfact, hQ3,
        hAfaces, hd3ne, hdvd1, ?_⟩
      rcases hAsplit with hA1 | hA2 | hA3
      · -- `d₃ = H·d₄` grandchild: first and loaded second faces of
        -- `d₄k₁ = H²m` plus the differentiated de-cored `I₄` face.
        left
        obtain ⟨d4, hd4, hd2d4, hd2dvd2, hbpsi, hbpsidvd, hd4k,
            hd4kdvd, hA1faces, hd4ne⟩ := hA1
        refine ⟨d4, hd4, hd2d4, hd2dvd2, hbpsi, hbpsidvd, hd4k,
          hd4kdvd, hA1faces, hd4ne, ?_⟩
        intro a ha
        refine ⟨squareCore_first_face_68 H d4 k1 m a hd4k ha, ?_, ?_⟩
        · have hface := squareCore_second_face_68 H d4 k1 m a hd4k ha
          rw [(hval a ha).1] at hface
          linear_combination hface
        · have hlin : b2 * psi = H * (-(6 : k[X]) * (w2 * d4)) := by
            rw [hbpsi]
            ring
          have hface := linearCore_first_face_68 H b2 psi
            (-(6 : k[X]) * (w2 * d4)) a ha hlin
          simp only [eval_mul, eval_neg, eval_ofNat] at hface
          linear_combination hface
      · -- `k₁ = H·k₂` grandchild: loaded third face of `d₃k₂ = H²m`.
        right
        left
        obtain ⟨k2, hk2, hk1dvdH, hd3k2, hd3k2dvd, hA2faces,
            hk2ne⟩ := hA2
        refine ⟨k2, hk2, hk1dvdH, hd3k2, hd3k2dvd, hA2faces,
          hk2ne, ?_⟩
        intro a ha
        have hface := squareCore_third_face_68 H d3 k2 m a hd3k2 ha
        have hmda : m.derivative.eval a =
            H.derivative.eval a *
              (b2.eval a * w2.eval a * e3.derivative.eval a) := by
          have h := congrArg (fun P : k[X] => P.derivative.eval a) hmdef
          simp only [derivative_sub, derivative_mul, derivative_C,
            sub_zero, eval_sub, eval_add, eval_mul, ha, zero_mul,
            mul_zero, add_zero, zero_add] at h
          linear_combination h
        rw [(hval a ha).1, hmda] at hface
        linear_combination hface
      · -- Transverse `d₃/k₁` grandchild: exact third-order pins and
        -- joint two-root globalizations.
        right
        right
        obtain ⟨x, y, hxy, hx, hy, hd3x, hk1x, hd3y, hk1y, hd3dx,
            hd3ddx, hbpsix, hk1dy, hk1ddy⟩ := hA3
        have hface3x := cubeCore_third_face_68 H d3 k1 m x hdkA hx
        rw [(hval x hx).1] at hface3x
        have hpinx : d3.derivative.derivative.derivative.eval x *
            k1.eval x = -(6 * j) * H.derivative.eval x ^ 3 := by
          linear_combination hface3x -
            3 * k1.derivative.eval x * hd3ddx -
            3 * k1.derivative.derivative.eval x * hd3dx -
            k1.derivative.derivative.derivative.eval x * hd3x
        have hRnex : -(6 * j) * H.derivative.eval x ^ 3 ≠ 0 :=
          mul_ne_zero h6j (pow_ne_zero 3 (hsimple x hx))
        have hd3dddx :
            d3.derivative.derivative.derivative.eval x ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at hpinx
          exact hRnex hpinx.symm
        have hdkA' : k1 * d3 = H ^ 3 * m := by
          rw [mul_comm]
          exact hdkA
        have hface3y := cubeCore_third_face_68 H k1 d3 m y hdkA' hy
        rw [(hval y hy).1] at hface3y
        have hpiny : d3.eval y *
            k1.derivative.derivative.derivative.eval y =
            -(6 * j) * H.derivative.eval y ^ 3 := by
          linear_combination hface3y -
            3 * d3.derivative.eval y * hk1ddy -
            3 * d3.derivative.derivative.eval y * hk1dy -
            d3.derivative.derivative.derivative.eval y * hk1y
        have hRney : -(6 * j) * H.derivative.eval y ^ 3 ≠ 0 :=
          mul_ne_zero h6j (pow_ne_zero 3 (hsimple y hy))
        have hk1dddy :
            k1.derivative.derivative.derivative.eval y ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hpiny
          exact hRney hpiny.symm
        have hdvdD1 : H ∣ d3.derivative * k1.derivative :=
          rDivisorSeventh_dvd_of_two_root_evals_68 H
            (d3.derivative * k1.derivative) hdeg hsimple x y hxy hx hy
            (by rw [eval_mul, hd3dx, zero_mul])
            (by rw [eval_mul, hk1dy, mul_zero])
        have hdvdD2 : H ∣ d3.derivative.derivative *
            k1.derivative.derivative :=
          rDivisorSeventh_dvd_of_two_root_evals_68 H
            (d3.derivative.derivative * k1.derivative.derivative)
            hdeg hsimple x y hxy hx hy
            (by rw [eval_mul, hd3ddx, zero_mul])
            (by rw [eval_mul, hk1ddy, mul_zero])
        exact ⟨x, y, hxy, hx, hy, hd3x, hk1x, hd3y, hk1y, hd3dx,
          hd3ddx, hbpsix, hk1dy, hk1ddy, hpinx, hd3dddx, hpiny,
          hk1dddy, hdvdD1, hdvdD2⟩
    · -- `ψ = H·ψ₂` child: advance each grandchild.
      right
      left
      obtain ⟨psi2, hpsi2, hpsidvdH, hphi3, hphi3dvd, hwdB, hwd2dvd,
          hgapdvd, hBfaces, hBsplit⟩ := hB
      refine ⟨psi2, hpsi2, hpsidvdH, hphi3, hphi3dvd, hwdB, hwd2dvd,
        hgapdvd, hBfaces, ?_⟩
      rcases hBsplit with hB1 | hB2 | hB3
      · -- `w₂ = H·w₃` grandchild: derivative pin, differentiated
        -- linear-cored `I₄` face and first quartic face.
        left
        obtain ⟨w3, hw3, hw2dvdH, hw3d, hw3ddvd, hgapbridge, hbetadvd,
            hB1faces⟩ := hB1
        refine ⟨w3, hw3, hw2dvdH, hw3d, hw3ddvd, hgapbridge, hbetadvd,
          hB1faces, ?_⟩
        intro a ha
        refine ⟨?_, ?_, ?_⟩
        · have h := congrArg (fun P : k[X] => P.derivative.eval a) hw3
          simp only [derivative_mul, eval_add, eval_mul, ha, zero_mul,
            add_zero] at h
          linear_combination h
        · have hlin : w3 * d2 =
              H * (-(C (1 / 6 : k)) * (b2 * psi2)) := by
            rw [hw3d]
            ring
          have hface := linearCore_first_face_68 H w3 d2
            (-(C (1 / 6 : k)) * (b2 * psi2)) a ha hlin
          simp only [eval_mul, eval_neg, eval_C] at hface
          linear_combination hface
        · exact squareCore_first_face_68 H d2 k1 (H ^ 2 * m) a
            (by rw [hdk]; ring) ha
      · -- `d₂ = H·d₃` grandchild in the `ψ`-regime: first and second
        -- cube faces plus the differentiated linear-cored `I₄` face.
        right
        left
        obtain ⟨d3, hd3B, hd2dvdB, hwd3, hwd3dvd, hd3k, hd3kdvd,
            hQfactB, hQ3B, hB2faces, hd3neB⟩ := hB2
        refine ⟨d3, hd3B, hd2dvdB, hwd3, hwd3dvd, hd3k, hd3kdvd,
          hQfactB, hQ3B, hB2faces, hd3neB, ?_⟩
        intro a ha
        refine ⟨?_, cubeCore_second_face_68 H d3 k1 m a hd3k ha, ?_⟩
        · exact squareCore_first_face_68 H d3 k1 (H * m) a
            (by rw [hd3k]; ring) ha
        · have hlin : w2 * d3 =
              H * (-(C (1 / 6 : k)) * (b2 * psi2)) := by
            rw [hwd3]
            ring
          have hface := linearCore_first_face_68 H w2 d3
            (-(C (1 / 6 : k)) * (b2 * psi2)) a ha hlin
          simp only [eval_mul, eval_neg, eval_C] at hface
          linear_combination hface
      · -- Transverse `w₂/d₂` grandchild: exact fourth-order pin at the
        -- `w₂`-root, third face at the `d₂`-root, joint globalizations.
        right
        right
        obtain ⟨x, y, hxy, hx, hy, hw2x, hd2x, hw2y, hd2y, hw2dx,
            hk1x, hk1dx, hk1ddx, hbetax, hd2dy, hd2ddk1y, hI4y⟩ := hB3
        have hface3x := quarticCore_third_face_68 H d2 k1 m x hdk hx
        have hk1dddx :
            k1.derivative.derivative.derivative.eval x = 0 := by
          have hprod : d2.eval x *
              k1.derivative.derivative.derivative.eval x = 0 := by
            linear_combination hface3x -
              d2.derivative.derivative.derivative.eval x * hk1x -
              3 * d2.derivative.derivative.eval x * hk1dx -
              3 * d2.derivative.eval x * hk1ddx
          exact (mul_eq_zero.mp hprod).resolve_left hd2x
        have hface4x := quarticCore_fourth_face_68 H d2 k1 m x hdk hx
        rw [(hval x hx).1] at hface4x
        have hpin4x : d2.eval x *
            k1.derivative.derivative.derivative.derivative.eval x =
            -(24 * j) * H.derivative.eval x ^ 4 := by
          linear_combination hface4x -
            d2.derivative.derivative.derivative.derivative.eval x *
              hk1x -
            4 * d2.derivative.derivative.derivative.eval x * hk1dx -
            6 * d2.derivative.derivative.eval x * hk1ddx -
            4 * d2.derivative.eval x * hk1dddx
        have hk1ddddx :
            k1.derivative.derivative.derivative.derivative.eval x ≠
              0 := by
          intro h0
          rw [h0, mul_zero] at hpin4x
          exact (mul_ne_zero h24j
            (pow_ne_zero 4 (hsimple x hx))) hpin4x.symm
        have hface3y := quarticCore_third_face_68 H d2 k1 m y hdk hy
        have hfacey : d2.derivative.derivative.derivative.eval y *
              k1.eval y +
            3 * (d2.derivative.derivative.eval y *
              k1.derivative.eval y) = 0 := by
          linear_combination hface3y -
            3 * k1.derivative.derivative.eval y * hd2dy -
            k1.derivative.derivative.derivative.eval y * hd2y
        have hdvdWD : H ∣ w2 * d2.derivative :=
          rDivisorSeventh_dvd_of_two_root_evals_68 H
            (w2 * d2.derivative) hdeg hsimple x y hxy hx hy
            (by rw [eval_mul, hw2x, zero_mul])
            (by rw [eval_mul, hd2dy, mul_zero])
        have hdvdKD : H ∣ k1 * d2.derivative :=
          rDivisorSeventh_dvd_of_two_root_evals_68 H
            (k1 * d2.derivative) hdeg hsimple x y hxy hx hy
            (by rw [eval_mul, hk1x, zero_mul])
            (by rw [eval_mul, hd2dy, mul_zero])
        exact ⟨x, y, hxy, hx, hy, hw2x, hd2x, hw2y, hd2y, hw2dx,
          hk1x, hk1dx, hk1ddx, hbetax, hd2dy, hd2ddk1y, hI4y,
          hk1dddx, hpin4x, hk1ddddx, hfacey, hdvdWD, hdvdKD⟩
    · -- Transverse `d₂/ψ` child: third-order faces, exact fourth-order
      -- pin at the `ψ`-root, joint globalizations.
      right
      right
      obtain ⟨a, b, hab, ha, hb, hd2a, hpsia, hd2b, hpsib, hCf1, hCf2,
          hw2b, hk1b, hw2db, hk1db, hbetab, hCsecond, hk1ddb,
          hI4b⟩ := hC
      have hface3a := quarticCore_third_face_68 H d2 k1 m a hdk ha
      have hfacea : d2.derivative.derivative.derivative.eval a *
            k1.eval a +
          3 * (d2.derivative.derivative.eval a *
            k1.derivative.eval a) +
          3 * (d2.derivative.eval a *
            k1.derivative.derivative.eval a) = 0 := by
        linear_combination hface3a -
          k1.derivative.derivative.derivative.eval a * hd2a
      have hface3b := quarticCore_third_face_68 H d2 k1 m b hdk hb
      have hk1dddb :
          k1.derivative.derivative.derivative.eval b = 0 := by
        have hprod : d2.eval b *
            k1.derivative.derivative.derivative.eval b = 0 := by
          linear_combination hface3b -
            d2.derivative.derivative.derivative.eval b * hk1b -
            3 * d2.derivative.derivative.eval b * hk1db -
            3 * d2.derivative.eval b * hk1ddb
        exact (mul_eq_zero.mp hprod).resolve_left hd2b
      have hface4b := quarticCore_fourth_face_68 H d2 k1 m b hdk hb
      rw [(hval b hb).1] at hface4b
      have hpin4b : d2.eval b *
          k1.derivative.derivative.derivative.derivative.eval b =
          -(24 * j) * H.derivative.eval b ^ 4 := by
        linear_combination hface4b -
          d2.derivative.derivative.derivative.derivative.eval b *
            hk1b -
          4 * d2.derivative.derivative.derivative.eval b * hk1db -
          6 * d2.derivative.derivative.eval b * hk1ddb -
          4 * d2.derivative.eval b * hk1dddb
      have hk1ddddb :
          k1.derivative.derivative.derivative.derivative.eval b ≠
            0 := by
        intro h0
        rw [h0, mul_zero] at hpin4b
        exact (mul_ne_zero h24j
          (pow_ne_zero 4 (hsimple b hb))) hpin4b.symm
      have hdvdDK : H ∣ d2 * k1.derivative :=
        rDivisorSeventh_dvd_of_two_root_evals_68 H
          (d2 * k1.derivative) hdeg hsimple a b hab ha hb
          (by rw [eval_mul, hd2a, zero_mul])
          (by rw [eval_mul, hk1db, mul_zero])
      have hdvdDW : H ∣ d2 * w2.derivative :=
        rDivisorSeventh_dvd_of_two_root_evals_68 H
          (d2 * w2.derivative) hdeg hsimple a b hab ha hb
          (by rw [eval_mul, hd2a, zero_mul])
          (by rw [eval_mul, hw2db, mul_zero])
      exact ⟨a, b, hab, ha, hb, hd2a, hpsia, hd2b, hpsib, hCf1, hCf2,
        hw2b, hk1b, hw2db, hk1db, hbetab, hCsecond, hk1ddb, hI4b,
        hfacea, hk1dddb, hpin4b, hk1ddddb, hdvdDK, hdvdDW⟩
  · exact Or.inr (Or.inl hphiDvd)
  · exact Or.inr (Or.inr htrans)

end RDivisorLowerZeroSeventhSource68

end Max11DegreeRoutes
