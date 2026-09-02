import Sol68ScaleTwoAlignedNonsquareAfterLowerOneCoordinateSplitScratch

/-! # Exact divisor cascade on the preserved `H ∣ r` branch

On the coordinate-split packet the first branch keeps the global
divisibility `H ∣ r`.  Writing `r = H·s`, the two lower coordinate rows
`3t − r² = H·X` and `27p₃ − r³ = H·Yd` immediately split off one further
core factor each: `H ∣ t` (hence `H² ∣ p₄`) and `H ∣ p₃`, with exact
cofactors and no primality or degree input.  Substituting the three splits
into the cleared cubic numerators, `A₀` and `C₀` gain one factor of `H`
while `E₀` gains three, so the terminal derivative numerator collapses to
`Ė = H⁴·e₃'` and the cleared last row descends to the exact quotient
cofactor `d₂k₁ = H⁴·(H·b₂w₂e₃' − j)`, whose value at every root of the
core is the nonzero Jacobian scalar `−j`.  In particular `d₂ ≠ 0` and
`k₁ ≠ 0` and the pair `d₂k₁` carries the full fourth core power exactly.
The source records no `x`-degree bounds on these quotient polynomials, so
no honest contradiction is available at this face; the refined residual
is returned instead, with the other two allocation branches transported
unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section RDivisorAlgebra68

variable {k : Type*} [Field k] [CharZero k]

/-- Scalar bridge `3 · C(1/3) = 1` used to divide the first lower row by
the unit `3` exactly. -/
theorem rDivisorThreeUnit68 : (3 : k[X]) * C (1 / 3 : k) = 1 := by
  rw [show (3 : k[X]) = C (3 : k) from (C_ofNat 3).symm, ← map_mul,
    show (3 : k) * (1 / 3 : k) = 1 by norm_num, map_one]

/-- Scalar bridge `27 · C(1/27) = 1` used to divide the second lower row
by the unit `27` exactly. -/
theorem rDivisorTwentySevenUnit68 : (27 : k[X]) * C (1 / 27 : k) = 1 := by
  rw [show (27 : k[X]) = C (27 : k) from (C_ofNat 27).symm, ← map_mul,
    show (27 : k) * (1 / 27 : k) = 1 by norm_num, map_one]

/-- On the `H ∣ r` branch both lower coordinate rows split off one more
core factor: `t = H·t₁` with `3t₁ = Hs² + X`, hence `p₄ = H²·t₁`, and
`p₃ = H·y₁` with `27y₁ = H²s³ + Yd`.  Pure unit division, no primality. -/
theorem rDivisor_coordinate_cascade_68
    (H r t X Yd p3 p4 s : k[X])
    (hs : r = H * s)
    (hp4 : p4 = H * t)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X)
    (hY : (27 : k[X]) * p3 - r ^ 3 = H * Yd) :
    t = H * (C (1 / 3 : k) * (H * s ^ 2 + X)) ∧
      (3 : k[X]) * (C (1 / 3 : k) * (H * s ^ 2 + X)) = H * s ^ 2 + X ∧
      p4 = H ^ 2 * (C (1 / 3 : k) * (H * s ^ 2 + X)) ∧
      p3 = H * (C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)) ∧
      (27 : k[X]) * (C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)) =
        H ^ 2 * s ^ 3 + Yd := by
  have h13 := rDivisorThreeUnit68 (k := k)
  have h127 := rDivisorTwentySevenUnit68 (k := k)
  have ht1 : t = H * (C (1 / 3 : k) * (H * s ^ 2 + X)) := by
    linear_combination C (1 / 3 : k) * hX +
      (C (1 / 3 : k) * (r + H * s)) * hs - t * h13
  have hy1 : p3 = H * (C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)) := by
    linear_combination C (1 / 27 : k) * hY +
      (C (1 / 27 : k) * (r ^ 2 + r * (H * s) + (H * s) ^ 2)) * hs -
      p3 * h127
  refine ⟨ht1, ?_, ?_, hy1, ?_⟩
  · linear_combination (H * s ^ 2 + X) * h13
  · linear_combination hp4 + H * ht1
  · linear_combination (H ^ 2 * s ^ 3 + Yd) * h127

/-- With `r`, `t`, `p₃` all exact core multiples, the `A`, `C`, `E`
numerators gain one, one, and three full factors of `H` respectively. -/
theorem rDivisor_numerator_cascade_68
    (H s t1 y1 p0 p1 p2 : k[X]) :
    cubicANumerator68 (H * t1) (H * s) =
        H * (t1 - C (5 / 12 : k) * H * s ^ 2) ∧
      cubicCNumerator68 H p2 (H * y1) (H * t1) (H * s) =
        H * (p2 - C (1 / 2 : k) * H * y1 * s +
          C (1 / 6 : k) * H ^ 2 * t1 * s ^ 2 -
          C (5 / 144 : k) * H ^ 3 * s ^ 4) ∧
      cubicENumerator68 H p0 p1 p2 (H * y1) (H * t1) (H * s) =
        H ^ 3 * (p0 - C (1 / 6 : k) * p1 * s +
          C (1 / 36 : k) * p2 * s ^ 2 -
          C (1 / 216 : k) * H * y1 * s ^ 3 +
          C (1 / 1296 : k) * H ^ 2 * t1 * s ^ 4 -
          C (5 / 46656 : k) * H ^ 3 * s ^ 6) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [cubicANumerator68, cubicCNumerator68, cubicENumerator68] <;>
    ring

/-- Differentiating a triple core multiple inside the terminal derivative
numerator collapses it to a clean fourth-power multiple. -/
theorem rDivisor_derivative_collapse_68 (H e3 : k[X]) :
    terminalEDerivativeNumerator68 H (H ^ 3 * e3) =
      H ^ 4 * e3.derivative := by
  have hpow : derivative (H ^ 3) = C (3 : k) * H ^ 2 * H.derivative := by
    rw [derivative_pow]
    norm_num
  simp only [terminalEDerivativeNumerator68, derivative_mul, hpow]
  ring

/-- Dividing the cleared last row by the collapsed fourth power isolates
the exact quotient cofactor of `d₂k₁`. -/
theorem rDivisor_row_cofactor_68
    (H b2 w2 d2 k1 e3 : k[X]) (j : k)
    (hrow : H * b2 * w2 * (H ^ 4 * e3.derivative) - d2 * k1 =
      C j * H ^ 4) :
    d2 * k1 = H ^ 4 * (H * b2 * w2 * e3.derivative - C j) := by
  linear_combination -hrow

/-- At every root of the core the quotient cofactor evaluates to the
Jacobian scalar `−j`. -/
theorem rDivisor_cofactor_eval_68
    (H b2 w2 e3 : k[X]) (j a : k) (ha : H.eval a = 0) :
    (H * b2 * w2 * e3.derivative - C j).eval a = -j := by
  simp [ha]

/-- A nonvanishing cofactor value forces both terminal factors of the
cleared row to be nonzero. -/
theorem rDivisor_factors_ne_zero_68
    (H d2 k1 m : k[X]) (j : k) (hj : j ≠ 0) (hH : H ≠ 0)
    (hdk : d2 * k1 = H ^ 4 * m)
    (a : k) (ha : H.eval a = 0) (hval : m.eval a = -j) :
    d2 ≠ 0 ∧ k1 ≠ 0 := by
  have hm : m ≠ 0 := by
    intro h0
    rw [h0, eval_zero] at hval
    exact hj (neg_eq_zero.mp hval.symm)
  have hne : d2 * k1 ≠ 0 := by
    rw [hdk]
    exact mul_ne_zero (pow_ne_zero 4 hH) hm
  exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

end RDivisorAlgebra68

section RDivisorSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Refined source packet on the preserved `H ∣ r` branch of the
coordinate split.  The two lower coordinate rows and the cleared cubic
numerators split off exact core factors — `H ∣ t`, `H² ∣ p₄`, `H ∣ p₃`,
`E₀ = H³e₃`, `Ė = H⁴e₃'` — and the cleared last row descends to the
exact quotient cofactor `d₂k₁ = H⁴(H·b₂w₂e₃' − j)` whose value at every
core root is `−j ≠ 0`; in particular `d₂ ≠ 0` and `k₁ ≠ 0`.  Without
`x`-degree data on the quotient polynomials no contradiction is honest
at this face, so the sharpened residual is returned; the `H ∣ φ₁` and
transverse two-root branches are transported unchanged. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneRDivisorPacket
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
      ((∃ s t1 y1 e3 m : k[X],
          r = H * s ∧
          t = H * t1 ∧
          (3 : k[X]) * t1 = H * s ^ 2 + X ∧
          H ∣ t ∧ H ^ 2 ∣ p.coeff 4 ∧ H ∣ p.coeff 3 ∧
          p.coeff 4 = H ^ 2 * t1 ∧
          p.coeff 3 = H * y1 ∧
          (27 : k[X]) * y1 = H ^ 2 * s ^ 3 + Yd ∧
          cubicANumerator68 t r =
            H * (t1 - C (5 / 12 : k) * H * s ^ 2) ∧
          cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r =
            H * (p.coeff 2 - C (1 / 2 : k) * H * y1 * s +
              C (1 / 6 : k) * H ^ 2 * t1 * s ^ 2 -
              C (5 / 144 : k) * H ^ 3 * s ^ 4) ∧
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
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, hsplit⟩ :=
    S.terminalAfterLowerOneCoordinateSplitPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  refine ⟨r, t, X, Yd, phi1, k1, b2, d2, w2, ht, hX, hY, hI4, hrow, ?_⟩
  rcases hsplit with hr | hphi | htrans
  · left
    obtain ⟨s, hs⟩ := hr
    obtain ⟨ht1, ht1sc, hp4sc, hy1, hy1sc⟩ :=
      rDivisor_coordinate_cascade_68 H r t X Yd (p.coeff 3) (p.coeff 4)
        s hs ht hX hY
    have hnum := rDivisor_numerator_cascade_68 H s
      (C (1 / 3 : k) * (H * s ^ 2 + X))
      (C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd))
      (p.coeff 0) (p.coeff 1) (p.coeff 2)
    have hA : cubicANumerator68 t r =
        H * (C (1 / 3 : k) * (H * s ^ 2 + X) -
          C (5 / 12 : k) * H * s ^ 2) := by
      rw [ht1, hs]
      exact hnum.1
    have hC : cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r =
        H * (p.coeff 2 -
          C (1 / 2 : k) * H * (C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)) * s +
          C (1 / 6 : k) * H ^ 2 * (C (1 / 3 : k) * (H * s ^ 2 + X)) *
            s ^ 2 -
          C (5 / 144 : k) * H ^ 3 * s ^ 4) := by
      rw [ht1, hs, hy1]
      exact hnum.2.1
    have hE : cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r =
        H ^ 3 * (p.coeff 0 - C (1 / 6 : k) * p.coeff 1 * s +
          C (1 / 36 : k) * p.coeff 2 * s ^ 2 -
          C (1 / 216 : k) * H *
            (C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)) * s ^ 3 +
          C (1 / 1296 : k) * H ^ 2 *
            (C (1 / 3 : k) * (H * s ^ 2 + X)) * s ^ 4 -
          C (5 / 46656 : k) * H ^ 3 * s ^ 6) := by
      rw [ht1, hs, hy1]
      exact hnum.2.2
    have heDot : terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) =
        H ^ 4 * (p.coeff 0 - C (1 / 6 : k) * p.coeff 1 * s +
          C (1 / 36 : k) * p.coeff 2 * s ^ 2 -
          C (1 / 216 : k) * H *
            (C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)) * s ^ 3 +
          C (1 / 1296 : k) * H ^ 2 *
            (C (1 / 3 : k) * (H * s ^ 2 + X)) * s ^ 4 -
          C (5 / 46656 : k) * H ^ 3 * s ^ 6).derivative := by
      rw [hE]
      exact rDivisor_derivative_collapse_68 H _
    have hrowE : H * b2 * w2 * terminalEDerivativeNumerator68 H
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) - d2 * k1 = C j * H ^ 4 := hrow
    rw [heDot] at hrowE
    have hdk := rDivisor_row_cofactor_68 H b2 w2 d2 k1 _ j hrowE
    have hval : ∀ a : k, H.eval a = 0 →
        (H * b2 * w2 * (p.coeff 0 - C (1 / 6 : k) * p.coeff 1 * s +
          C (1 / 36 : k) * p.coeff 2 * s ^ 2 -
          C (1 / 216 : k) * H *
            (C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)) * s ^ 3 +
          C (1 / 1296 : k) * H ^ 2 *
            (C (1 / 3 : k) * (H * s ^ 2 + X)) * s ^ 4 -
          C (5 / 46656 : k) * H ^ 3 * s ^ 6).derivative -
            C j).eval a = -j ∧
        (H * b2 * w2 * (p.coeff 0 - C (1 / 6 : k) * p.coeff 1 * s +
          C (1 / 36 : k) * p.coeff 2 * s ^ 2 -
          C (1 / 216 : k) * H *
            (C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd)) * s ^ 3 +
          C (1 / 1296 : k) * H ^ 2 *
            (C (1 / 3 : k) * (H * s ^ 2 + X)) * s ^ 4 -
          C (5 / 46656 : k) * H ^ 3 * s ^ 6).derivative -
            C j).eval a ≠ 0 := by
      intro a ha
      refine ⟨rDivisor_cofactor_eval_68 H b2 w2 _ j a ha, ?_⟩
      rw [rDivisor_cofactor_eval_68 H b2 w2 _ j a ha]
      exact neg_ne_zero.mpr hj
    have hH0 : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH0, hdeg]
      decide
    obtain ⟨a0, ha0⟩ := IsAlgClosed.exists_root H hdegne
    have ha0' : H.eval a0 = 0 := ha0
    have hne := rDivisor_factors_ne_zero_68 H d2 k1 _ j hj hH0 hdk
      a0 ha0' (hval a0 ha0').1
    exact ⟨s, C (1 / 3 : k) * (H * s ^ 2 + X),
      C (1 / 27 : k) * (H ^ 2 * s ^ 3 + Yd), _, _,
      hs, ht1, ht1sc,
      ⟨_, ht1⟩, ⟨_, hp4sc⟩, ⟨_, hy1⟩,
      hp4sc, hy1, hy1sc, hA, hC, rfl, hE, heDot, rfl,
      hdk, ⟨_, hdk⟩, hval, hne.1, hne.2⟩
  · exact Or.inr (Or.inl hphi)
  · exact Or.inr (Or.inr htrans)

end RDivisorSource68

end Max11DegreeRoutes
