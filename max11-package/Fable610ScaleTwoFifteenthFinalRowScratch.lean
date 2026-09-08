import Fable610ScaleTwoFourteenthFaceScratch

/-! # Scale-two fifteenth final row for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the fourteenth-face packet refines both
thirteenth-face alternatives at the last leftover order before the
ground constants: on `p₃₁(a) = 0` the peeled seventh-defect cofactor
obeys `9 χ₂(a) = 16 w₁ (1296 λ p₁ - 1080 p₁ w₁ + 1890 λ p₃₂ w₁²
- 1575 λ a₄₁ w₁³ - 4200 p₃₂ w₁³ + 3500 a₄₁ w₁⁴)`, and on the
complementary factor the peeled sixth-defect cofactor obeys
`ψ₂(a) = 288 (1980 λ a₄₁ w₁³ - 4400 a₄₁ w₁⁴ - 729 λ p₁ - 405 p₁ w₁)`.

The next unused Keller coefficient is the degree-`0` Jacobian row, the
last row of the tower.  It is the literal final row
`W E' - D X' = j`: unlike every higher row it is inhomogeneous — it
equals the nonzero Keller constant — so it is not a first integral and
it clears no defect.  Both cleared defect towers stay exhausted at
their ground constants `η` (order `h³⁵`) and `ζ` (order `h³⁰`); no new
defect order is invented.

This file isolates the final row and the strongest exact source-facing
refinement it induces on both live alternatives.  At the root of `h`
the row evaluates to `E'(a) W(a) - D(a) X'(a) = j`, coupling the fresh
boundary data `E'(a), W(a), X'(a)` — coordinates the `h`-adic jet does
not control — to the Keller constant, and at the normalized source
`j ≠ 0` separates the cross-products: `E'(a) W(a) ≠ D(a) X'(a)`.
Eliminating `p₁(a)` between the final row and each cofactor law gives,
on `p₃₁(a) = 0`,
`16 w₁ (1296 λ - 1080 w₁) (E'(a) W(a) - j) = X'(a) (9 χ₂(a)
- 16 w₁ (1890 λ p₃₂ w₁² - 1575 λ a₄₁ w₁³ - 4200 p₃₂ w₁³
+ 3500 a₄₁ w₁⁴))`, and on the complementary factor
`288 (729 λ + 405 w₁) (E'(a) W(a) - j) = X'(a) (288 (1980 λ a₄₁ w₁³
- 4400 a₄₁ w₁⁴) - ψ₂(a))`.  Neither alternative is contradicted: the
final row lives on the fresh boundary coordinates, so no live branch
closes.

The Jacobian coefficient tower is now fully consumed — there is no
unused row below degree `0`.  The honest residual is the single
inhomogeneous boundary relation `E'(a) W(a) - D(a) X'(a) = j`,
together with everything already open: the aligned face `N = 0` and
the `p₃₁ ≠ 0` sibling remain open, the ground constants `η` and `ζ` of
the seventh- and sixth-defect first integrals are preserved and not
cleared to zero, the degree-`5`, degree-`4`, degree-`3`, degree-`2`,
and degree-`1` first integrals stay uncleared, and no individual
vanishing of `p₂, p₁, p₀, q₃` (nor of `w₁, a₄₁, p₃₂, ω, χ, ψ, χ₂, ψ₂`,
nor of the boundary data `E'(a), W(a), X'(a)`) is claimed.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal final Keller coefficient -/

/-- The degree-`0` Jacobian coefficient for outer degrees `(6,10)` is
the last row of the tower and is inhomogeneous: `W E' - D X' = j`, the
Keller constant itself.  There is no unused row below it. -/
theorem fifteenthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 0).derivative * q.coeff 1 -
      p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 0) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 0 :
      Finset (ℕ × ℕ)) =
      ({(0, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num at hcoeff
  linear_combination hcoeff

/-! ## Scalar eliminations against the fourteenth-face cofactor laws -/

section FifteenthFinalRowScalars610

variable {F : Type*} [Field F] [CharZero F]

/-- On the `p₃₁ = 0` sibling, eliminating `p₁(a)` between the final row
`W E' - D X' = j` and the fourteenth-face `χ₂` law couples the fresh
boundary data to the exhausted seventh-defect tower. -/
theorem fifteenthFinalRow_zeroP31_chi2Elimination610 (w1 a41 p32 p1 chi2
    e1 x1 q1 j : F) (lambda : F)
    (hrow : e1 * q1 - p1 * x1 = j)
    (hChi2 : (9 : F) * chi2 = (16 : F) * w1 *
      ((1296 : F) * lambda * p1 - (1080 : F) * p1 * w1 +
        (1890 : F) * lambda * p32 * w1 ^ 2 -
        (1575 : F) * lambda * a41 * w1 ^ 3 -
        (4200 : F) * p32 * w1 ^ 3 +
        (3500 : F) * a41 * w1 ^ 4)) :
    (16 : F) * w1 * ((1296 : F) * lambda - (1080 : F) * w1) *
        (e1 * q1 - j) =
      x1 * ((9 : F) * chi2 -
        (16 : F) * w1 * ((1890 : F) * lambda * p32 * w1 ^ 2 -
          (1575 : F) * lambda * a41 * w1 ^ 3 -
          (4200 : F) * p32 * w1 ^ 3 +
          (3500 : F) * a41 * w1 ^ 4)) := by
  linear_combination (16 : F) * w1 *
      ((1296 : F) * lambda - (1080 : F) * w1) * hrow - x1 * hChi2

/-- On the complementary factor, eliminating `p₁(a)` between the final
row `W E' - D X' = j` and the fourteenth-face `ψ₂` law couples the
fresh boundary data to the exhausted sixth-defect tower. -/
theorem fifteenthFinalRow_comp_psi2Elimination610 (w1 a41 p1 psi2 e1 x1
    q1 j : F) (lambda : F)
    (hrow : e1 * q1 - p1 * x1 = j)
    (hPsi2 : psi2 = (288 : F) * ((1980 : F) * lambda * a41 * w1 ^ 3 -
      (4400 : F) * a41 * w1 ^ 4 - (729 : F) * lambda * p1 -
      (405 : F) * p1 * w1)) :
    (288 : F) * ((729 : F) * lambda + (405 : F) * w1) *
        (e1 * q1 - j) =
      x1 * ((288 : F) * ((1980 : F) * lambda * a41 * w1 ^ 3 -
          (4400 : F) * a41 * w1 ^ 4) - psi2) := by
  linear_combination (288 : F) * ((729 : F) * lambda + (405 : F) * w1) *
      hrow + x1 * hPsi2

end FifteenthFinalRowScalars610

/-! ## Source-facing fifteenth final-row packet -/

section NonzeroFifteenthFinalRow610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
/-- Finite local fifteenth final-row packet: the fourteenth-face packet
together with the literal degree-`0` Jacobian row `W E' - D X' = j`,
its evaluation at the root, and the elimination of `p₁(a)` against the
`χ₂` and `ψ₂` cofactor laws on the two live alternatives.  The tower
has no unused row below degree `0`. -/
theorem nonzeroFace610_linearRoot_fifteenthFinalRow
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a41 s1 u1 p31 b62 q52 : k[X]),
      p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        (3 : k) * s1.eval a = (5 : k) * a41.eval a ∧
        (3 : k) * u1.eval a = (5 : k) * p31.eval a ∧
        (9 : k) * q52.eval a =
          (10 : k) * a41.eval a * p31.eval a ∧
        (9 : k) * (q.coeff 4).eval a = (5 : k) * (p31.eval a) ^ 2 ∧
        (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a -
            (9 : k) * lambda * p31.eval a +
          (30 : k) * (p.coeff 2).eval a +
            (20 : k) * p31.eval a * w1.eval a = 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j ∧
        ((p31.eval a = 0 ∧
            ∃ (p32 u2 q53 q41 chi chi2 : k[X]),
              p.coeff 3 = h0 ^ 2 * p32 ∧
                q.coeff 7 = h0 ^ 6 * u2 ∧
                q.coeff 5 = h0 ^ 3 * q53 ∧
                q.coeff 4 = h0 * q41 ∧
                (18 : k) * u2.eval a - (30 : k) * p32.eval a -
                    (20 : k) * a41.eval a * w1.eval a +
                  (9 : k) * lambda * a41.eval a = 0 ∧
                (81 : k) * q41.eval a -
                    (90 : k) * a41.eval a * (p.coeff 2).eval a +
                  (5 : k) * (a41.eval a) ^ 3 = 0 ∧
                (216 : k) * q53.eval a +
                    (27 : k) * lambda * (a41.eval a) ^ 2 +
                  (40 : k) * (a41.eval a) ^ 2 * w1.eval a -
                    (240 : k) * a41.eval a * p32.eval a +
                  (108 : k) * lambda * (p.coeff 2).eval a -
                    (240 : k) * (p.coeff 2).eval a * w1.eval a = 0 ∧
                (3888 : k) * (q.coeff 3).eval a -
                    (81 : k) * lambda * (a41.eval a) ^ 3 -
                  (320 : k) * (a41.eval a) ^ 3 * w1.eval a +
                    (720 : k) * (a41.eval a) ^ 2 * p32.eval a +
                  (972 : k) * lambda * a41.eval a *
                      (p.coeff 2).eval a +
                    (1440 : k) * a41.eval a * (p.coeff 2).eval a *
                      w1.eval a -
                  (4320 : k) * (p.coeff 2).eval a * p32.eval a =
                    0 ∧
                (960 : k[X]) * a41 ^ 3 * Polynomial.C lambda +
                    (6400 : k[X]) * a41 ^ 3 * w1 -
                    (9600 : k[X]) * a41 ^ 2 * p32 -
                    (7680 : k[X]) * a41 ^ 2 * s1 * w1 +
                    (2688 : k[X]) * a41 ^ 2 * u2 +
                    (4608 : k[X]) * a41 * b62 * w1 -
                    (2304 : k[X]) * a41 * Polynomial.C lambda *
                      p.coeff 2 -
                    (7680 : k[X]) * a41 * p.coeff 2 * w1 +
                    (6144 : k[X]) * a41 * p32 * s1 -
                    (2560 : k[X]) * a41 * q53 -
                    (3072 : k[X]) * b62 * p32 +
                    (7680 : k[X]) * p.coeff 2 * p32 +
                    (6144 : k[X]) * p.coeff 2 * s1 * w1 -
                    (3584 : k[X]) * p.coeff 2 * u2 +
                    (3072 : k[X]) * q.coeff 3 -
                    (2048 : k[X]) * q41 * w1 = h0 * chi ∧
                (9 : k) * chi.eval a =
                  (17280 : k) * lambda * (a41.eval a) ^ 2 *
                      (w1.eval a) ^ 2 -
                    (54400 : k) * (a41.eval a) ^ 2 *
                      (w1.eval a) ^ 3 -
                    (27648 : k) * lambda * a41.eval a * p32.eval a *
                      w1.eval a -
                    (7680 : k) * a41.eval a * (p.coeff 1).eval a +
                    (99840 : k) * a41.eval a * p32.eval a *
                      (w1.eval a) ^ 2 -
                    (17280 : k) * lambda * (p.coeff 2).eval a *
                      (w1.eval a) ^ 2 +
                    (10368 : k) * lambda * (p32.eval a) ^ 2 +
                    (38400 : k) * (p.coeff 2).eval a *
                      (w1.eval a) ^ 3 -
                    (46080 : k) * (p32.eval a) ^ 2 * w1.eval a ∧
                chi + (-(5040 : k[X]) * a41 ^ 2 * Polynomial.C lambda *
                    w1 ^ 2 +
                  (5760 : k[X]) * a41 * Polynomial.C lambda * p32 *
                    w1 +
                  (7680 : k[X]) * a41 * p.coeff 1 +
                  (4800 : k[X]) * a41 * p32 * w1 ^ 2 +
                  (8960 : k[X]) * a41 * s1 * w1 ^ 3 -
                  (6720 : k[X]) * a41 * u2 * w1 ^ 2 -
                  (1920 : k[X]) * b62 * w1 ^ 3 +
                  (2880 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                    w1 ^ 2 -
                  (1152 : k[X]) * Polynomial.C lambda * p32 ^ 2 -
                  (4096 : k[X]) * p.coeff 1 * s1 -
                  (3200 : k[X]) * p.coeff 2 * w1 ^ 3 -
                  (3840 : k[X]) * p32 ^ 2 * w1 -
                  (7680 : k[X]) * p32 * s1 * w1 ^ 2 +
                  (5376 : k[X]) * p32 * u2 * w1 +
                  (1920 : k[X]) * q53 * w1 ^ 2) = h0 * chi2 ∧
                (9 : k) * chi2.eval a =
                  (16 : k) * w1.eval a *
                    ((1296 : k) * lambda * (p.coeff 1).eval a -
                      (1080 : k) * (p.coeff 1).eval a * w1.eval a +
                      (1890 : k) * lambda * p32.eval a *
                        (w1.eval a) ^ 2 -
                      (1575 : k) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4200 : k) * p32.eval a * (w1.eval a) ^ 3 +
                    (3500 : k) * a41.eval a * (w1.eval a) ^ 4) ∧
                (16 : k) * w1.eval a *
                    ((1296 : k) * lambda - (1080 : k) * w1.eval a) *
                    (((p.coeff 0).derivative).eval a *
                        (q.coeff 1).eval a - j) =
                  ((q.coeff 0).derivative).eval a *
                    ((9 : k) * chi2.eval a -
                      (16 : k) * w1.eval a *
                        ((1890 : k) * lambda * p32.eval a *
                            (w1.eval a) ^ 2 -
                          (1575 : k) * lambda * a41.eval a *
                            (w1.eval a) ^ 3 -
                          (4200 : k) * p32.eval a *
                            (w1.eval a) ^ 3 +
                          (3500 : k) * a41.eval a *
                            (w1.eval a) ^ 4))) ∨
          ((240 : k) * (p.coeff 2).eval a -
                (40 : k) * (a41.eval a) ^ 2 -
              (27 : k) * lambda * p31.eval a -
                (40 : k) * p31.eval a * w1.eval a = 0 ∧
            (144 : k) * b62.eval a - (120 : k) * (a41.eval a) ^ 2 +
                (45 : k) * lambda * p31.eval a -
              (200 : k) * p31.eval a * w1.eval a = 0 ∧
            ∃ (omega psi psi2 : k[X]),
              (583200 : k[X]) * p31 ^ 2 -
                  (489888 : k[X]) * p31 * u1 +
                (419904 : k[X]) * q.coeff 4 = h0 * omega ∧
              omega.eval a =
                (648 : k) * a41.eval a *
                  ((80 : k) * (a41.eval a) ^ 2 +
                      (297 : k) * lambda * p31.eval a -
                    (960 : k) * p31.eval a * w1.eval a) ∧
              omega + (-(518400 : k[X]) * a41 ^ 3 +
                  (466560 : k[X]) * a41 ^ 2 * s1 -
                  (419904 : k[X]) * a41 * b62 -
                  (349920 : k[X]) * a41 * Polynomial.C lambda * p31 +
                  (1166400 : k[X]) * a41 * p.coeff 2 -
                  (1360800 : k[X]) * a41 * p31 * w1 +
                  (816480 : k[X]) * a41 * u1 * w1 -
                  (559872 : k[X]) * p.coeff 2 * s1 +
                  (933120 : k[X]) * p31 * s1 * w1 -
                  (349920 : k[X]) * q52 * w1) = h0 * psi ∧
              psi.eval a =
                (162 : k) * w1.eval a *
                  ((7600 : k) * (a41.eval a) ^ 2 * w1.eval a -
                      (2520 : k) * lambda * (a41.eval a) ^ 2 +
                      (243 : k) * lambda ^ 2 * p31.eval a -
                      (1980 : k) * lambda * p31.eval a * w1.eval a +
                    (3200 : k) * p31.eval a *
                      (w1.eval a) ^ 2) ∧
              psi + ((466560 : k[X]) * a41 ^ 2 * Polynomial.C lambda *
                  w1 +
                (518400 : k[X]) * a41 ^ 2 * w1 ^ 2 -
                (1244160 : k[X]) * a41 * s1 * w1 ^ 2 +
                (349920 : k[X]) * b62 * w1 ^ 2 -
                (349920 : k[X]) * Polynomial.C lambda * p.coeff 2 *
                  w1 +
                (466560 : k[X]) * Polynomial.C lambda * p31 * w1 ^ 2 +
                (194400 : k[X]) * p.coeff 2 * w1 ^ 2 -
                (432000 : k[X]) * p31 * w1 ^ 3 -
                (362880 : k[X]) * u1 * w1 ^ 3) = h0 * psi2 ∧
              psi2.eval a =
                (288 : k) * ((1980 : k) * lambda * a41.eval a *
                    (w1.eval a) ^ 3 -
                  (4400 : k) * a41.eval a * (w1.eval a) ^ 4 -
                  (729 : k) * lambda * (p.coeff 1).eval a -
                  (405 : k) * (p.coeff 1).eval a * w1.eval a) ∧
              (288 : k) * ((729 : k) * lambda +
                    (405 : k) * w1.eval a) *
                  (((p.coeff 0).derivative).eval a *
                      (q.coeff 1).eval a - j) =
                ((q.coeff 0).derivative).eval a *
                  ((288 : k) * ((1980 : k) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4400 : k) * a41.eval a * (w1.eval a) ^ 4) -
                    psi2.eval a))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, hw, ha4s, hp3, hs, hu, hb6s,
    hq5, hMs, hTu, hVq, hWq, hUload, halt⟩ :=
    nonzeroFace610_linearRoot_fourteenthPowerJet p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  have hjac : bivariateJacobian p q =
      Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  have hrow := fifteenthCoefficientJacobianRow_610 hjac
  have hroweval : ((p.coeff 0).derivative).eval a *
      (q.coeff 1).eval a -
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j := by
    have h := congrArg (Polynomial.eval a) hrow
    simpa only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] using h
  refine ⟨w1, a41, s1, u1, p31, b62, q52, hw, ha4s, hp3, hs, hu, hb6s,
    hq5, hMs, hTu, hVq, hWq, hUload, hrow, hroweval, ?_⟩
  rcases halt with ⟨hp31z, ⟨p32, u2, q53, q41, chi, chi2, hp3u, hq7u,
      hq5u, hq4u, hTform, hWform, hVform, hQ3form, hchieq, hchival,
      hchi2eq, hchi2val⟩⟩ |
      ⟨htp, hb62form, omega, psi, psi2, homega, homegaval, hpsieq,
        hpsival, hpsi2eq, hpsi2val⟩
  · exact Or.inl ⟨hp31z, ⟨p32, u2, q53, q41, chi, chi2, hp3u, hq7u,
      hq5u, hq4u, hTform, hWform, hVform, hQ3form, hchieq, hchival,
      hchi2eq, hchi2val,
      fifteenthFinalRow_zeroP31_chi2Elimination610 (w1.eval a)
        (a41.eval a) (p32.eval a) ((p.coeff 1).eval a) (chi2.eval a)
        (((p.coeff 0).derivative).eval a)
        (((q.coeff 0).derivative).eval a) ((q.coeff 1).eval a) j
        lambda hroweval hchi2val⟩⟩
  · exact Or.inr ⟨htp, hb62form, omega, psi, psi2, homega, homegaval,
      hpsieq, hpsival, hpsi2eq, hpsi2val,
      fifteenthFinalRow_comp_psi2Elimination610 (w1.eval a)
        (a41.eval a) ((p.coeff 1).eval a) (psi2.eval a)
        (((p.coeff 0).derivative).eval a)
        (((q.coeff 0).derivative).eval a) ((q.coeff 1).eval a) j
        lambda hroweval hpsi2val⟩

set_option maxHeartbeats 12000000 in
/-- Source-facing fifteenth final-row packet of a normalized scale-two
`(6,10)` nonzero face: the fourteenth-face packet together with the
literal degree-`0` Jacobian row `W E' - D X' = j`, the nonvanishing of
the Keller constant, the separation `E'(a) W(a) ≠ D(a) X'(a)` at the
root, and the `p₁(a)` eliminations against the `χ₂` and `ψ₂` cofactor
laws on the two live alternatives.  The Jacobian coefficient tower is
fully consumed. -/
theorem normalized610ScaleTwo_nonzeroFace_fifteenthFinalRow
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a jK : K)
      (w1 a41 s1 u1 p31 b62 q52 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧
        h0 ∣ p.coeff 3 ∧ h0 ^ 7 ∣ q.coeff 8 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
        h0 ^ 4 ∣ q.coeff 6 ∧ h0 ^ 2 ∣ q.coeff 5 ∧
        (3 : K) * s1.eval a = (5 : K) * a41.eval a ∧
        (3 : K) * u1.eval a = (5 : K) * p31.eval a ∧
        (9 : K) * q52.eval a =
          (10 : K) * a41.eval a * p31.eval a ∧
        (9 : K) * (q.coeff 4).eval a = (5 : K) * (p31.eval a) ^ 2 ∧
        (10 : K) * (a41.eval a) ^ 2 - (18 : K) * b62.eval a -
            (9 : K) * lambda * p31.eval a +
          (30 : K) * (p.coeff 2).eval a +
            (20 : K) * p31.eval a * w1.eval a = 0 ∧
        jK ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C jK ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = jK ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a ∧
        ((p31.eval a = 0 ∧
            ∃ (p32 u2 q53 q41 chi chi2 : K[X]),
              p.coeff 3 = h0 ^ 2 * p32 ∧
                q.coeff 7 = h0 ^ 6 * u2 ∧
                q.coeff 5 = h0 ^ 3 * q53 ∧
                q.coeff 4 = h0 * q41 ∧
                h0 ^ 2 ∣ p.coeff 3 ∧ h0 ^ 6 ∣ q.coeff 7 ∧
                h0 ^ 3 ∣ q.coeff 5 ∧ h0 ∣ q.coeff 4 ∧
                (18 : K) * u2.eval a - (30 : K) * p32.eval a -
                    (20 : K) * a41.eval a * w1.eval a +
                  (9 : K) * lambda * a41.eval a = 0 ∧
                (81 : K) * q41.eval a -
                    (90 : K) * a41.eval a * (p.coeff 2).eval a +
                  (5 : K) * (a41.eval a) ^ 3 = 0 ∧
                (216 : K) * q53.eval a +
                    (27 : K) * lambda * (a41.eval a) ^ 2 +
                  (40 : K) * (a41.eval a) ^ 2 * w1.eval a -
                    (240 : K) * a41.eval a * p32.eval a +
                  (108 : K) * lambda * (p.coeff 2).eval a -
                    (240 : K) * (p.coeff 2).eval a * w1.eval a = 0 ∧
                (3888 : K) * (q.coeff 3).eval a -
                    (81 : K) * lambda * (a41.eval a) ^ 3 -
                  (320 : K) * (a41.eval a) ^ 3 * w1.eval a +
                    (720 : K) * (a41.eval a) ^ 2 * p32.eval a +
                  (972 : K) * lambda * a41.eval a *
                      (p.coeff 2).eval a +
                    (1440 : K) * a41.eval a * (p.coeff 2).eval a *
                      w1.eval a -
                  (4320 : K) * (p.coeff 2).eval a * p32.eval a =
                    0 ∧
                (960 : K[X]) * a41 ^ 3 * Polynomial.C lambda +
                    (6400 : K[X]) * a41 ^ 3 * w1 -
                    (9600 : K[X]) * a41 ^ 2 * p32 -
                    (7680 : K[X]) * a41 ^ 2 * s1 * w1 +
                    (2688 : K[X]) * a41 ^ 2 * u2 +
                    (4608 : K[X]) * a41 * b62 * w1 -
                    (2304 : K[X]) * a41 * Polynomial.C lambda *
                      p.coeff 2 -
                    (7680 : K[X]) * a41 * p.coeff 2 * w1 +
                    (6144 : K[X]) * a41 * p32 * s1 -
                    (2560 : K[X]) * a41 * q53 -
                    (3072 : K[X]) * b62 * p32 +
                    (7680 : K[X]) * p.coeff 2 * p32 +
                    (6144 : K[X]) * p.coeff 2 * s1 * w1 -
                    (3584 : K[X]) * p.coeff 2 * u2 +
                    (3072 : K[X]) * q.coeff 3 -
                    (2048 : K[X]) * q41 * w1 = h0 * chi ∧
                (9 : K) * chi.eval a =
                  (17280 : K) * lambda * (a41.eval a) ^ 2 *
                      (w1.eval a) ^ 2 -
                    (54400 : K) * (a41.eval a) ^ 2 *
                      (w1.eval a) ^ 3 -
                    (27648 : K) * lambda * a41.eval a * p32.eval a *
                      w1.eval a -
                    (7680 : K) * a41.eval a * (p.coeff 1).eval a +
                    (99840 : K) * a41.eval a * p32.eval a *
                      (w1.eval a) ^ 2 -
                    (17280 : K) * lambda * (p.coeff 2).eval a *
                      (w1.eval a) ^ 2 +
                    (10368 : K) * lambda * (p32.eval a) ^ 2 +
                    (38400 : K) * (p.coeff 2).eval a *
                      (w1.eval a) ^ 3 -
                    (46080 : K) * (p32.eval a) ^ 2 * w1.eval a ∧
                chi + (-(5040 : K[X]) * a41 ^ 2 * Polynomial.C lambda *
                    w1 ^ 2 +
                  (5760 : K[X]) * a41 * Polynomial.C lambda * p32 *
                    w1 +
                  (7680 : K[X]) * a41 * p.coeff 1 +
                  (4800 : K[X]) * a41 * p32 * w1 ^ 2 +
                  (8960 : K[X]) * a41 * s1 * w1 ^ 3 -
                  (6720 : K[X]) * a41 * u2 * w1 ^ 2 -
                  (1920 : K[X]) * b62 * w1 ^ 3 +
                  (2880 : K[X]) * Polynomial.C lambda * p.coeff 2 *
                    w1 ^ 2 -
                  (1152 : K[X]) * Polynomial.C lambda * p32 ^ 2 -
                  (4096 : K[X]) * p.coeff 1 * s1 -
                  (3200 : K[X]) * p.coeff 2 * w1 ^ 3 -
                  (3840 : K[X]) * p32 ^ 2 * w1 -
                  (7680 : K[X]) * p32 * s1 * w1 ^ 2 +
                  (5376 : K[X]) * p32 * u2 * w1 +
                  (1920 : K[X]) * q53 * w1 ^ 2) = h0 * chi2 ∧
                (9 : K) * chi2.eval a =
                  (16 : K) * w1.eval a *
                    ((1296 : K) * lambda * (p.coeff 1).eval a -
                      (1080 : K) * (p.coeff 1).eval a * w1.eval a +
                      (1890 : K) * lambda * p32.eval a *
                        (w1.eval a) ^ 2 -
                      (1575 : K) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4200 : K) * p32.eval a * (w1.eval a) ^ 3 +
                    (3500 : K) * a41.eval a * (w1.eval a) ^ 4) ∧
                (16 : K) * w1.eval a *
                    ((1296 : K) * lambda - (1080 : K) * w1.eval a) *
                    (((p.coeff 0).derivative).eval a *
                        (q.coeff 1).eval a - jK) =
                  ((q.coeff 0).derivative).eval a *
                    ((9 : K) * chi2.eval a -
                      (16 : K) * w1.eval a *
                        ((1890 : K) * lambda * p32.eval a *
                            (w1.eval a) ^ 2 -
                          (1575 : K) * lambda * a41.eval a *
                            (w1.eval a) ^ 3 -
                          (4200 : K) * p32.eval a *
                            (w1.eval a) ^ 3 +
                          (3500 : K) * a41.eval a *
                            (w1.eval a) ^ 4))) ∨
          ((240 : K) * (p.coeff 2).eval a -
                (40 : K) * (a41.eval a) ^ 2 -
              (27 : K) * lambda * p31.eval a -
                (40 : K) * p31.eval a * w1.eval a = 0 ∧
            (144 : K) * b62.eval a - (120 : K) * (a41.eval a) ^ 2 +
                (45 : K) * lambda * p31.eval a -
              (200 : K) * p31.eval a * w1.eval a = 0 ∧
            ∃ (omega psi psi2 : K[X]),
              (583200 : K[X]) * p31 ^ 2 -
                  (489888 : K[X]) * p31 * u1 +
                (419904 : K[X]) * q.coeff 4 = h0 * omega ∧
              omega.eval a =
                (648 : K) * a41.eval a *
                  ((80 : K) * (a41.eval a) ^ 2 +
                      (297 : K) * lambda * p31.eval a -
                    (960 : K) * p31.eval a * w1.eval a) ∧
              omega + (-(518400 : K[X]) * a41 ^ 3 +
                  (466560 : K[X]) * a41 ^ 2 * s1 -
                  (419904 : K[X]) * a41 * b62 -
                  (349920 : K[X]) * a41 * Polynomial.C lambda * p31 +
                  (1166400 : K[X]) * a41 * p.coeff 2 -
                  (1360800 : K[X]) * a41 * p31 * w1 +
                  (816480 : K[X]) * a41 * u1 * w1 -
                  (559872 : K[X]) * p.coeff 2 * s1 +
                  (933120 : K[X]) * p31 * s1 * w1 -
                  (349920 : K[X]) * q52 * w1) = h0 * psi ∧
              psi.eval a =
                (162 : K) * w1.eval a *
                  ((7600 : K) * (a41.eval a) ^ 2 * w1.eval a -
                      (2520 : K) * lambda * (a41.eval a) ^ 2 +
                      (243 : K) * lambda ^ 2 * p31.eval a -
                      (1980 : K) * lambda * p31.eval a * w1.eval a +
                    (3200 : K) * p31.eval a *
                      (w1.eval a) ^ 2) ∧
              psi + ((466560 : K[X]) * a41 ^ 2 * Polynomial.C lambda *
                  w1 +
                (518400 : K[X]) * a41 ^ 2 * w1 ^ 2 -
                (1244160 : K[X]) * a41 * s1 * w1 ^ 2 +
                (349920 : K[X]) * b62 * w1 ^ 2 -
                (349920 : K[X]) * Polynomial.C lambda * p.coeff 2 *
                  w1 +
                (466560 : K[X]) * Polynomial.C lambda * p31 * w1 ^ 2 +
                (194400 : K[X]) * p.coeff 2 * w1 ^ 2 -
                (432000 : K[X]) * p31 * w1 ^ 3 -
                (362880 : K[X]) * u1 * w1 ^ 3) = h0 * psi2 ∧
              psi2.eval a =
                (288 : K) * ((1980 : K) * lambda * a41.eval a *
                    (w1.eval a) ^ 3 -
                  (4400 : K) * a41.eval a * (w1.eval a) ^ 4 -
                  (729 : K) * lambda * (p.coeff 1).eval a -
                  (405 : K) * (p.coeff 1).eval a * w1.eval a) ∧
              (288 : K) * ((729 : K) * lambda +
                    (405 : K) * w1.eval a) *
                  (((p.coeff 0).derivative).eval a *
                      (q.coeff 1).eval a - jK) =
                ((q.coeff 0).derivative).eval a *
                  ((288 : K) * ((1980 : K) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4400 : K) * a41.eval a * (w1.eval a) ^ 4) -
                    psi2.eval a))) ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, w1, a41, s1, u1, p31, b62, q52, hh0, hlambda,
    hh0degree, hH, hroot, hw, ha4s, hp3, hs, hu, hb6s, hq5, hq9, hp5d,
    hp4d, hp3d, hq8d, hq7d, hq6d, hq5d, hMs, hTu, hVq, hWq, hUload,
    hXalt, hN'⟩ :=
    normalized610ScaleTwo_nonzeroFace_tenthPowerJet hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨w1', a41', s1', u1', p31', b62', q52', hwN, ha4sN, hp3N, hsN,
    huN, hb6sN, hq5N, hMs', hTu', hVq', hWq', hUload', hrow, hroweval,
    halt⟩ :=
    nonzeroFace610_linearRoot_fifteenthFinalRow p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot hlambda
  have hsep : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
    intro heq
    apply hj
    rw [← hroweval, heq, sub_self]
  refine ⟨h0, lambda, a, j, w1', a41', s1', u1', p31', b62', q52', hh0,
    hlambda, hh0degree, hH, hroot, hwN, ha4sN, hp3N, hsN, huN, hb6sN,
    hq5N, hq9,
    (by rw [hwN]; exact dvd_mul_right _ _),
    (by rw [ha4sN]; exact dvd_mul_right _ _),
    (by rw [hp3N]; exact dvd_mul_right _ _),
    (by rw [hsN]; exact dvd_mul_right _ _),
    (by rw [huN]; exact dvd_mul_right _ _),
    (by rw [hb6sN]; exact dvd_mul_right _ _),
    (by rw [hq5N]; exact dvd_mul_right _ _),
    hMs', hTu', hVq', hWq', hUload', hj, hrow, hroweval, hsep, ?_,
    hN'⟩
  rcases halt with ⟨hp31z, ⟨p32, u2, q53, q41, chi, chi2, hp3u, hq7u,
      hq5u, hq4u, hTform, hWform, hVform, hQ3form, hchieq, hchival,
      hchi2eq, hchi2val, heli⟩⟩ |
      ⟨htp, hb62form, omega, psi, psi2, homega, homegaval, hpsieq,
        hpsival, hpsi2eq, hpsi2val, heli2⟩
  · exact Or.inl ⟨hp31z, ⟨p32, u2, q53, q41, chi, chi2, hp3u, hq7u,
      hq5u, hq4u,
      (by rw [hp3u]; exact dvd_mul_right _ _),
      (by rw [hq7u]; exact dvd_mul_right _ _),
      (by rw [hq5u]; exact dvd_mul_right _ _),
      (by rw [hq4u]; exact dvd_mul_right _ _),
      hTform, hWform, hVform, hQ3form, hchieq, hchival, hchi2eq,
      hchi2val, heli⟩⟩
  · exact Or.inr ⟨htp, hb62form, omega, psi, psi2, homega, homegaval,
      hpsieq, hpsival, hpsi2eq, hpsi2val, heli2⟩

end NonzeroFifteenthFinalRow610

#print axioms fifteenthCoefficientJacobianRow_610
#print axioms fifteenthFinalRow_zeroP31_chi2Elimination610
#print axioms fifteenthFinalRow_comp_psi2Elimination610
#print axioms nonzeroFace610_linearRoot_fifteenthFinalRow
#print axioms normalized610ScaleTwo_nonzeroFace_fifteenthFinalRow

end Max11DegreeRoutes
