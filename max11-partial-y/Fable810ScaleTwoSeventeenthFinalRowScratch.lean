import Fable810ScaleTwoSixteenthFaceScratch

/-! # Scale-two seventeenth final row for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the sixteenth-face packet carries the degree-`1`
Jacobian row and the next-order fourth/fifth refinements of every live
fifteenth-face branch: on the left the `F₁ ∨ F₂` alternative with the
`m₁`/`τ₁`, `g₁`, and `k₁` next-order laws, on the `u₁ = 0` sibling the
`h²` quotients `σ`, `ρ`, `π` with the head law
`k_z(a) = 163840 p₃(a)`, and on the complementary factor the `ρ_c`
quotient law together with `8 a₄ = 3 v₁²`, `8 b₆₂ = 5 v₁²`,
`2 u₁² + v₁³ = 0`, and `32 β(a) + 63 λ v₁² = 0`.

The next unused Keller coefficient is the degree-`0` Jacobian row, the
last row of the tower.  It is the literal final row `W G' - F X' = j`
with `G = p₀`, `F = p₁`, `W = q₁`, `X = q₀` — the raw Lean row is
`p₀' q₁ - p₁ q₀' = j`; this corrects the drifted prose `W G' - G W'`
of the sixteenth-face header.  Unlike every higher row it is
inhomogeneous — it equals the nonzero Keller constant — so it is not a
first integral and it clears no defect.  All four cleared defect
towers stay exhausted at their ground constants `δ` (order `h²⁸`),
`ε` (order `h³⁵`), `ζ` (order `h⁴²`), `η` (order `h⁴⁹`); no new
defect order is invented.

This file isolates the final row and consumes it into the sixteenth
face packet.  At the root of `h` the row evaluates to
`G'(a) W(a) - F(a) X'(a) = j`, coupling the fresh boundary data
`G'(a), F(a), W(a), X'(a)` — coordinates the `h`-adic jet does not
control — to the Keller constant, and at the normalized source `j ≠ 0`
separates the cross-products: `G'(a) W(a) ≠ F(a) X'(a)`.  Unlike the
`(6,10)` lane there is no shared coordinate to eliminate: every
sixteenth-face branch law bottoms out at `p₃, p₄, q₅, q₆`, while the
final row lives entirely on `p₀, p₁, q₀, q₁`.  Consequently no live
branch is contradicted, no per-branch elimination exists, and the
exact terminal boundary relation is retained on both alternatives
verbatim.

The Jacobian coefficient tower is now fully consumed — there is no
unused row below degree `0`.  The honest residual is the single
inhomogeneous boundary relation `G'(a) W(a) - F(a) X'(a) = j`,
together with everything already open: the aligned face `N = 0`
remains open, the left `F₁ ∨ F₂` alternative is unresolved, the
`u₁ = 0` sibling and the complementary factor both survive, the
ground constants `δ`, `ε`, `ζ`, `η` of the fourth- through
seventh-defect first integrals are preserved and not cleared to zero,
the degree-`5`, degree-`4`, degree-`3`, degree-`2`, and degree-`1`
first integrals stay uncleared, and no individual vanishing of
`v₁, u₁, a₄, t₀, t₁, p₃, q₄` (nor of the boundary data
`G'(a), F(a), W(a), X'(a)`) is claimed.  Any further progress on this
lane requires a genuinely new mechanism — the aligned face, clearing
an isolated first integral, or global input — not another row.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal final Keller coefficient -/

/-- The degree-`0` Jacobian coefficient for outer degrees `(8,10)` is
the last row of the tower and is inhomogeneous: `W G' - F X' = j`, the
Keller constant itself.  There is no unused row below it. -/
theorem seventeenthCoefficientJacobianRow_810 {K : Type*}
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

/-! ## Source-facing seventeenth final-row packet -/

section NonzeroSeventeenthFinalRow810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local seventeenth final-row packet: the sixteenth-face packet
together with the literal degree-`0` Jacobian row `W G' - F X' = j` and
its evaluation at the root.  The row lives entirely on the fresh
boundary coordinates `p₀, p₁, q₀, q₁`, which no sixteenth-face branch
law constrains, so both live alternatives are retained verbatim and no
per-branch elimination exists.  The tower has no unused row below
degree `0`. -/
theorem nonzeroFace810_linearRoot_seventeenthFinalRow
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : k[X],
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧ h0 ^ 2 ∣ q.coeff 6 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : k) * s1.eval a - (40 : k) * v1.eval a =
              (5 : k) * (t0.eval a) ^ 2 ∧
            (128 : k) * w1.eval a - (160 : k) * u1.eval a -
                (40 : k) * t0.eval a * v1.eval a +
              (5 : k) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Wred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Xred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7 ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : k[X]),
              (32 : k[X]) * s1 - (40 : k[X]) * v1 -
                    (5 : k[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : k[X]) * w1 - (160 : k[X]) * u1 -
                    (40 : k[X]) * t0 * v1 + (5 : k[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : k) * lambda * t0.eval a = 0 ∧
                (4 : k) * tau1.eval a +
                    (9 : k) * lambda * (t0.eval a) ^ 2 +
                  (144 : k) * lambda * v1.eval a = 0) ∧
            (∃ g1 : k[X],
              (2560 : k[X]) * (p.coeff 4) - (2048 : k[X]) * b62 +
                    (35 : k[X]) * t0 ^ 4 -
                    (240 : k[X]) * t0 ^ 2 * v1 +
                    (640 : k[X]) * t0 * u1 + (320 : k[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : k) * g1.eval a +
                    (3 : k) * lambda *
                      ((7 : k) * (t0.eval a) ^ 3 -
                        (48 : k) * t0.eval a * v1.eval a -
                        (384 : k) * u1.eval a) = 0) ∧
            (∃ k1 : k[X],
              (81920 : k[X]) * (p.coeff 4) * t0 +
                    (131072 : k[X]) * (q.coeff 5) -
                    (98304 : k[X]) * b62 * t0 +
                    (2912 : k[X]) * t0 ^ 5 -
                    (20480 : k[X]) * t0 ^ 3 * v1 +
                    (46080 : k[X]) * t0 ^ 2 * u1 +
                    (30720 : k[X]) * t0 * v1 ^ 2 -
                    (40960 : k[X]) * u1 * v1 =
                  h0 * k1 ∧
                k1.eval a + (9 : k) * lambda *
                    ((4096 : k) * (p.coeff 4).eval a +
                      (91 : k) * (t0.eval a) ^ 4 -
                      (608 : k) * (t0.eval a) ^ 2 * v1.eval a -
                      (2560 : k) * t0.eval a * u1.eval a +
                      (256 : k) * (v1.eval a) ^ 2) = 0) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                  (u1.eval a) →
              (128 : k) * w1.eval a -
                    (5 : k) * t0.eval a *
                      ((24 : k) * v1.eval a -
                        (5 : k) * (t0.eval a) ^ 2) =
                  0 ∧
                (1024 : k) * (q.coeff 5).eval a -
                    (256 : k) * b62.eval a * t0.eval a -
                    (11 : k) * (t0.eval a) ^ 5 +
                  (40 : k) * (t0.eval a) ^ 3 * v1.eval a =
                  0 ∧
                ((3 : k) * (t0.eval a) ^ 2 - (8 : k) * v1.eval a) *
                    ((1024 : k) * b62.eval a +
                      (25 : k) * (t0.eval a) ^ 4 -
                      (320 : k) * (v1.eval a) ^ 2) =
                  0 ∧
                (4177920 : k) * (p.coeff 4).eval a *
                        (t0.eval a) ^ 3 -
                      (11796480 : k) * (p.coeff 4).eval a *
                        t0.eval a * v1.eval a +
                      (10485760 : k) * (p.coeff 4).eval a *
                        u1.eval a +
                      (7208960 : k) * (q.coeff 5).eval a *
                        (t0.eval a) ^ 2 -
                      (10485760 : k) * (q.coeff 5).eval a *
                        v1.eval a -
                      (6848512 : k) * b62.eval a *
                        (t0.eval a) ^ 3 +
                      (17301504 : k) * b62.eval a * t0.eval a *
                        v1.eval a -
                      (12582912 : k) * b62.eval a * u1.eval a +
                      (300960 : k) * (t0.eval a) ^ 7 -
                      (2675200 : k) * (t0.eval a) ^ 5 * v1.eval a +
                      (4561920 : k) * (t0.eval a) ^ 4 * u1.eval a +
                      (7096320 : k) * (t0.eval a) ^ 3 *
                        (v1.eval a) ^ 2 -
                      (15769600 : k) * (t0.eval a) ^ 2 *
                        u1.eval a * v1.eval a +
                      (7208960 : k) * t0.eval a *
                        (u1.eval a) ^ 2 -
                      (5406720 : k) * t0.eval a *
                        (v1.eval a) ^ 3 +
                      (7208960 : k) * u1.eval a *
                        (v1.eval a) ^ 2 +
                    (384 : k) * t0.eval a *
                      ((3 : k) * (t0.eval a) ^ 2 -
                        (8 : k) * v1.eval a) *
                      ((1024 : k) * b62.eval a +
                        (25 : k) * (t0.eval a) ^ 4 -
                        (320 : k) * (v1.eval a) ^ 2) =
                  0)) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s1.eval a = (5 : k) * v1.eval a ∧
            (4 : k) * w1.eval a = (5 : k) * u1.eval a ∧
            (40 : k) * (p.coeff 4).eval a - (32 : k) * b62.eval a +
              (5 : k) * (v1.eval a) ^ 2 = 0 ∧
            (16 : k) * (q.coeff 5).eval a =
              (5 : k) * u1.eval a * v1.eval a ∧
            (16 : k) * b62.eval a * v1.eval a +
                (10 : k) * (u1.eval a) ^ 2 -
              (5 : k) * (v1.eval a) ^ 3 = 0 ∧
            u1.eval a *
                ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a) =
              0 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 4 ∣ p.coeff 6 ∧
            h0 ^ 6 ∣ q.coeff 8 ∧
            ((u1.eval a = 0 ∧
                ∃ (t1 u2 w2 b51 sigma rho pi : k[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    (32 : k[X]) * s1 - (40 : k[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (40 : k[X]) * (p.coeff 4) - (32 : k[X]) * b62 +
                        (5 : k[X]) * v1 ^ 2 =
                      h0 ^ 2 * rho ∧
                    (16 : k[X]) * b62 * v1 -
                        (5 : k[X]) * v1 ^ 3 =
                      h0 ^ 2 * pi ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧ h0 ^ 2 ∣
                      ((32 : k[X]) * s1 - (40 : k[X]) * v1) ∧
                    h0 ^ 2 ∣
                      ((40 : k[X]) * (p.coeff 4) -
                          (32 : k[X]) * b62 +
                        (5 : k[X]) * v1 ^ 2) ∧
                    h0 ^ 2 ∣
                      ((16 : k[X]) * b62 * v1 -
                        (5 : k[X]) * v1 ^ 3) ∧
                    (32 : k) * w2.eval a - (40 : k) * u2.eval a -
                        (10 : k) * t1.eval a * v1.eval a +
                      (9 : k) * lambda * v1.eval a = 0 ∧
                    (2560 : k) * b51.eval a +
                        (576 : k) * lambda * b62.eval a -
                        (640 : k) * t1.eval a * b62.eval a -
                        (45 : k) * lambda * (v1.eval a) ^ 2 +
                        (400 : k) * t1.eval a * (v1.eval a) ^ 2 -
                        (800 : k) * u2.eval a * v1.eval a = 0 ∧
                    (v1.eval a) ^ 3 *
                        ((3 : k) * lambda * v1.eval a +
                          (160 : k) * t1.eval a * v1.eval a -
                          (320 : k) * u2.eval a) =
                      0 ∧
                    (8 : k) * rho.eval a +
                        (8 : k) * sigma.eval a * v1.eval a +
                        (63 : k) * lambda * t1.eval a * v1.eval a -
                        (72 : k) * lambda * u2.eval a -
                        (70 : k) * (t1.eval a) ^ 2 * v1.eval a +
                      (80 : k) * t1.eval a * u2.eval a = 0 ∧
                    ∃ kz : k[X],
                      (81920 : k[X]) * (p.coeff 4) * t1 +
                            (131072 : k[X]) * b51 -
                            (98304 : k[X]) * b62 * t1 +
                            (212992 : k[X]) * s1 * t1 * v1 -
                            (131072 : k[X]) * s1 * u2 -
                            (199680 : k[X]) * t1 * v1 ^ 2 +
                            (266240 : k[X]) * u2 * v1 -
                            (114688 : k[X]) * v1 * w2 +
                            (36864 : k[X]) * Polynomial.C lambda *
                              (p.coeff 4) -
                            (29952 : k[X]) * Polynomial.C lambda *
                              v1 ^ 2 =
                          h0 * kz ∧
                        kz.eval a =
                          (163840 : k) * (p.coeff 3).eval a) ∨
              ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a = 0 ∧
                (8 : k) * (p.coeff 4).eval a -
                    (3 : k) * (v1.eval a) ^ 2 = 0 ∧
                (2 : k) * (u1.eval a) ^ 2 + (v1.eval a) ^ 3 = 0 ∧
                ∃ (t1 omega sigma beta : k[X]),
                  t0 = h0 * t1 ∧
                    (4 : k[X]) * w1 - (5 : k[X]) * u1 =
                      h0 * omega ∧
                    (32 : k[X]) * s1 - (40 : k[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (16 : k[X]) * (q.coeff 5) -
                        (5 : k[X]) * u1 * v1 =
                      h0 * beta ∧
                    h0 ^ 2 ∣ ((32 : k[X]) * s1 - (40 : k[X]) * v1) ∧
                    h0 ∣
                      ((16 : k[X]) * (q.coeff 5) -
                        (5 : k[X]) * u1 * v1) ∧
                    (8 : k) * omega.eval a -
                        (10 : k) * t1.eval a * v1.eval a +
                      (9 : k) * lambda * v1.eval a = 0 ∧
                    (32 : k) * beta.eval a +
                      (63 : k) * lambda * (v1.eval a) ^ 2 =
                      0 ∧
                    ∃ rhoc : k[X],
                      (40 : k[X]) * (p.coeff 4) -
                            (32 : k[X]) * b62 +
                          (5 : k[X]) * v1 ^ 2 =
                        h0 * rhoc ∧
                      rhoc.eval a +
                          (10 : k) * t1.eval a * u1.eval a -
                        (9 : k) * lambda * u1.eval a = 0)))) := by
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
    hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2, hsplit⟩ :=
    nonzeroFace810_linearRoot_sixteenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  have hjac : bivariateJacobian p q =
      Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  have hrow := seventeenthCoefficientJacobianRow_810 hjac
  have hroweval : ((p.coeff 0).derivative).eval a *
      (q.coeff 1).eval a -
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j := by
    have h := congrArg (Polynomial.eval a) hrow
    simpa only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] using h
  exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
    hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2, hrow, hroweval, hsplit⟩

set_option maxHeartbeats 40000000 in
/-- Source-facing seventeenth final-row packet of a normalized scale-two
`(8,10)` nonzero face: the sixteenth-face packet together with the
literal degree-`0` Jacobian row `W G' - F X' = j`, the nonvanishing of
the Keller constant, and the separation `G'(a) W(a) ≠ F(a) X'(a)` at
the root.  The Jacobian coefficient tower is fully consumed; no live
branch is contradicted and no unused row remains. -/
theorem normalized810ScaleTwo_nonzeroFace_seventeenthFinalRow
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a jK : K)
      (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧ h0 ^ 2 ∣ q.coeff 6 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        jK ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C jK ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = jK ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : K) * s1.eval a - (40 : K) * v1.eval a =
              (5 : K) * (t0.eval a) ^ 2 ∧
            (128 : K) * w1.eval a - (160 : K) * u1.eval a -
                (40 : K) * t0.eval a * v1.eval a +
              (5 : K) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Wred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Xred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7 ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                (u1.eval a) ∨
              twelfthFace_leftF2_810 (t0.eval a) (v1.eval a)
                (u1.eval a)) ∧
            (∃ (m1 tau1 : K[X]),
              (32 : K[X]) * s1 - (40 : K[X]) * v1 -
                    (5 : K[X]) * t0 ^ 2 =
                  h0 * m1 ∧
                (128 : K[X]) * w1 - (160 : K[X]) * u1 -
                    (40 : K[X]) * t0 * v1 + (5 : K[X]) * t0 ^ 3 =
                  h0 * tau1 ∧
                m1.eval a + (9 : K) * lambda * t0.eval a = 0 ∧
                (4 : K) * tau1.eval a +
                    (9 : K) * lambda * (t0.eval a) ^ 2 +
                  (144 : K) * lambda * v1.eval a = 0) ∧
            (∃ g1 : K[X],
              (2560 : K[X]) * (p.coeff 4) - (2048 : K[X]) * b62 +
                    (35 : K[X]) * t0 ^ 4 -
                    (240 : K[X]) * t0 ^ 2 * v1 +
                    (640 : K[X]) * t0 * u1 + (320 : K[X]) * v1 ^ 2 =
                  h0 * g1 ∧
                (2 : K) * g1.eval a +
                    (3 : K) * lambda *
                      ((7 : K) * (t0.eval a) ^ 3 -
                        (48 : K) * t0.eval a * v1.eval a -
                        (384 : K) * u1.eval a) = 0) ∧
            (∃ k1 : K[X],
              (81920 : K[X]) * (p.coeff 4) * t0 +
                    (131072 : K[X]) * (q.coeff 5) -
                    (98304 : K[X]) * b62 * t0 +
                    (2912 : K[X]) * t0 ^ 5 -
                    (20480 : K[X]) * t0 ^ 3 * v1 +
                    (46080 : K[X]) * t0 ^ 2 * u1 +
                    (30720 : K[X]) * t0 * v1 ^ 2 -
                    (40960 : K[X]) * u1 * v1 =
                  h0 * k1 ∧
                k1.eval a + (9 : K) * lambda *
                    ((4096 : K) * (p.coeff 4).eval a +
                      (91 : K) * (t0.eval a) ^ 4 -
                      (608 : K) * (t0.eval a) ^ 2 * v1.eval a -
                      (2560 : K) * t0.eval a * u1.eval a +
                      (256 : K) * (v1.eval a) ^ 2) = 0) ∧
            (twelfthFace_leftF1_810 (t0.eval a) (v1.eval a)
                  (u1.eval a) →
              (128 : K) * w1.eval a -
                    (5 : K) * t0.eval a *
                      ((24 : K) * v1.eval a -
                        (5 : K) * (t0.eval a) ^ 2) =
                  0 ∧
                (1024 : K) * (q.coeff 5).eval a -
                    (256 : K) * b62.eval a * t0.eval a -
                    (11 : K) * (t0.eval a) ^ 5 +
                  (40 : K) * (t0.eval a) ^ 3 * v1.eval a =
                  0 ∧
                ((3 : K) * (t0.eval a) ^ 2 - (8 : K) * v1.eval a) *
                    ((1024 : K) * b62.eval a +
                      (25 : K) * (t0.eval a) ^ 4 -
                      (320 : K) * (v1.eval a) ^ 2) =
                  0 ∧
                (4177920 : K) * (p.coeff 4).eval a *
                        (t0.eval a) ^ 3 -
                      (11796480 : K) * (p.coeff 4).eval a *
                        t0.eval a * v1.eval a +
                      (10485760 : K) * (p.coeff 4).eval a *
                        u1.eval a +
                      (7208960 : K) * (q.coeff 5).eval a *
                        (t0.eval a) ^ 2 -
                      (10485760 : K) * (q.coeff 5).eval a *
                        v1.eval a -
                      (6848512 : K) * b62.eval a *
                        (t0.eval a) ^ 3 +
                      (17301504 : K) * b62.eval a * t0.eval a *
                        v1.eval a -
                      (12582912 : K) * b62.eval a * u1.eval a +
                      (300960 : K) * (t0.eval a) ^ 7 -
                      (2675200 : K) * (t0.eval a) ^ 5 * v1.eval a +
                      (4561920 : K) * (t0.eval a) ^ 4 * u1.eval a +
                      (7096320 : K) * (t0.eval a) ^ 3 *
                        (v1.eval a) ^ 2 -
                      (15769600 : K) * (t0.eval a) ^ 2 *
                        u1.eval a * v1.eval a +
                      (7208960 : K) * t0.eval a *
                        (u1.eval a) ^ 2 -
                      (5406720 : K) * t0.eval a *
                        (v1.eval a) ^ 3 +
                      (7208960 : K) * u1.eval a *
                        (v1.eval a) ^ 2 +
                    (384 : K) * t0.eval a *
                      ((3 : K) * (t0.eval a) ^ 2 -
                        (8 : K) * v1.eval a) *
                      ((1024 : K) * b62.eval a +
                        (25 : K) * (t0.eval a) ^ 4 -
                        (320 : K) * (v1.eval a) ^ 2) =
                  0)) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : K) * s1.eval a = (5 : K) * v1.eval a ∧
            (4 : K) * w1.eval a = (5 : K) * u1.eval a ∧
            (40 : K) * (p.coeff 4).eval a - (32 : K) * b62.eval a +
              (5 : K) * (v1.eval a) ^ 2 = 0 ∧
            (16 : K) * (q.coeff 5).eval a =
              (5 : K) * u1.eval a * v1.eval a ∧
            (16 : K) * b62.eval a * v1.eval a +
                (10 : K) * (u1.eval a) ^ 2 -
              (5 : K) * (v1.eval a) ^ 3 = 0 ∧
            u1.eval a *
                ((5 : K) * (v1.eval a) ^ 2 - (8 : K) * b62.eval a) =
              0 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 4 ∣ p.coeff 6 ∧
            h0 ^ 6 ∣ q.coeff 8 ∧
            ((u1.eval a = 0 ∧
                ∃ (t1 u2 w2 b51 sigma rho pi : K[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    (32 : K[X]) * s1 - (40 : K[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (40 : K[X]) * (p.coeff 4) - (32 : K[X]) * b62 +
                        (5 : K[X]) * v1 ^ 2 =
                      h0 ^ 2 * rho ∧
                    (16 : K[X]) * b62 * v1 -
                        (5 : K[X]) * v1 ^ 3 =
                      h0 ^ 2 * pi ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧ h0 ^ 2 ∣
                      ((32 : K[X]) * s1 - (40 : K[X]) * v1) ∧
                    h0 ^ 2 ∣
                      ((40 : K[X]) * (p.coeff 4) -
                          (32 : K[X]) * b62 +
                        (5 : K[X]) * v1 ^ 2) ∧
                    h0 ^ 2 ∣
                      ((16 : K[X]) * b62 * v1 -
                        (5 : K[X]) * v1 ^ 3) ∧
                    (32 : K) * w2.eval a - (40 : K) * u2.eval a -
                        (10 : K) * t1.eval a * v1.eval a +
                      (9 : K) * lambda * v1.eval a = 0 ∧
                    (2560 : K) * b51.eval a +
                        (576 : K) * lambda * b62.eval a -
                        (640 : K) * t1.eval a * b62.eval a -
                        (45 : K) * lambda * (v1.eval a) ^ 2 +
                        (400 : K) * t1.eval a * (v1.eval a) ^ 2 -
                        (800 : K) * u2.eval a * v1.eval a = 0 ∧
                    (v1.eval a) ^ 3 *
                        ((3 : K) * lambda * v1.eval a +
                          (160 : K) * t1.eval a * v1.eval a -
                          (320 : K) * u2.eval a) =
                      0 ∧
                    (8 : K) * rho.eval a +
                        (8 : K) * sigma.eval a * v1.eval a +
                        (63 : K) * lambda * t1.eval a * v1.eval a -
                        (72 : K) * lambda * u2.eval a -
                        (70 : K) * (t1.eval a) ^ 2 * v1.eval a +
                      (80 : K) * t1.eval a * u2.eval a = 0 ∧
                    ∃ kz : K[X],
                      (81920 : K[X]) * (p.coeff 4) * t1 +
                            (131072 : K[X]) * b51 -
                            (98304 : K[X]) * b62 * t1 +
                            (212992 : K[X]) * s1 * t1 * v1 -
                            (131072 : K[X]) * s1 * u2 -
                            (199680 : K[X]) * t1 * v1 ^ 2 +
                            (266240 : K[X]) * u2 * v1 -
                            (114688 : K[X]) * v1 * w2 +
                            (36864 : K[X]) * Polynomial.C lambda *
                              (p.coeff 4) -
                            (29952 : K[X]) * Polynomial.C lambda *
                              v1 ^ 2 =
                          h0 * kz ∧
                        kz.eval a =
                          (163840 : K) * (p.coeff 3).eval a) ∨
              ((5 : K) * (v1.eval a) ^ 2 - (8 : K) * b62.eval a = 0 ∧
                (8 : K) * (p.coeff 4).eval a -
                    (3 : K) * (v1.eval a) ^ 2 = 0 ∧
                (2 : K) * (u1.eval a) ^ 2 +
                  (v1.eval a) ^ 3 = 0 ∧
                ∃ (t1 omega sigma beta : K[X]),
                  t0 = h0 * t1 ∧
                    (4 : K[X]) * w1 - (5 : K[X]) * u1 =
                      h0 * omega ∧
                    (32 : K[X]) * s1 - (40 : K[X]) * v1 =
                      h0 ^ 2 * sigma ∧
                    (16 : K[X]) * (q.coeff 5) -
                        (5 : K[X]) * u1 * v1 =
                      h0 * beta ∧
                    h0 ^ 2 ∣ ((32 : K[X]) * s1 - (40 : K[X]) * v1) ∧
                    h0 ∣
                      ((16 : K[X]) * (q.coeff 5) -
                        (5 : K[X]) * u1 * v1) ∧
                    (8 : K) * omega.eval a -
                        (10 : K) * t1.eval a * v1.eval a +
                      (9 : K) * lambda * v1.eval a = 0 ∧
                    (32 : K) * beta.eval a +
                      (63 : K) * lambda * (v1.eval a) ^ 2 =
                      0 ∧
                    ∃ rhoc : K[X],
                      (40 : K[X]) * (p.coeff 4) -
                            (32 : K[X]) * b62 +
                          (5 : K[X]) * v1 ^ 2 =
                        h0 * rhoc ∧
                      rhoc.eval a +
                          (10 : K) * t1.eval a * u1.eval a -
                        (9 : K) * lambda * u1.eval a = 0)))) := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized810ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨t0', v0', u0', s0', w0', v1', s1', u1', w1', b62', ht0', hv0',
    hu0', hs0', hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6', hrow',
    hroweval', hsplit'⟩ :=
    nonzeroFace810_linearRoot_seventeenthFinalRow p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  have hsep : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
    intro heq
    apply hj
    rw [← hroweval', heq, sub_self]
  exact ⟨h0, lambda, a, j, t0', v0', u0', s0', w0', v1', s1', u1', w1',
    b62', hh0, hlambda, hh0degree, hH, hroot, ht0', hv0', hu0', hs0',
    hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6', hN', hj, hrow',
    hroweval', hsep, hsplit'⟩

end NonzeroSeventeenthFinalRow810

#print axioms seventeenthCoefficientJacobianRow_810
#print axioms nonzeroFace810_linearRoot_seventeenthFinalRow
#print axioms normalized810ScaleTwo_nonzeroFace_seventeenthFinalRow

end Max11DegreeRoutes
