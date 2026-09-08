import Sol610ScaleTwoTerminalIntegralGroundSplitsScratch

/-! # Terminal integral closure for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₅ H² - 3 q₉ = λ h⁹` with
`h.natDegree = 1`, the terminal integral bridge peels the weight-`50`
cleared defect of the degree-`5` first integral `ι` to its order-`44`
head and leaves one factored ground residual on each live branch:
`a₄₁(a) (4 a₄₁⁴ - 35 p₂ a₄₁² + 90 p₂²)(a) = 0` on the `p₃₁(a) = 0`
sibling and `p₃₁(a)² (5 a₄₁² + 2 p₃₁ w₁)(a) = 0` on the complementary
factor.  The imported ground splits normalize both residuals exactly,
without re-expanding the weight-`50` numerator.

This file backwires those exact normal forms into the bridge packet.
On the `p₃₁(a) = 0` sibling the deeper divisibilities `p₃ = h₀² p₃₂`,
`q₇ = h₀⁶ u₂`, `q₅ = h₀³ q₅₃`, `q₄ = h₀ q₄₁` and their source equations
are kept unchanged and the order-`45` residual is replaced by the
honest split `a₄₁(a) = 0 ∨ (4 a₄₁⁴ - 35 p₂ a₄₁² + 90 p₂²)(a) = 0`.  On
the complementary factor the two loaded rows plus the collapsed
cofactor split on `p₃₁(a)`: either `p₃₁(a) = 0` and the rows pin
`6 p₂(a) = a₄₁(a)²` and `6 b₆₂(a) = 5 a₄₁(a)²`, or `p₃₁(a) ≠ 0` and
the peeled `ι` cofactor cancels to the three normalized ground
relations `5 a₄₁² + 2 p₃₁ w₁ = 0`, `80 p₂ - 9 λ p₃₁ - 8 p₃₁ w₁ = 0`,
`144 b₆₂ + 45 λ p₃₁ - 152 p₃₁ w₁ = 0` at the root.  On that
`p₃₁(a) ≠ 0` child the fifteenth final-row packet is re-derived on the
same witnesses — the jet factors `h₀⁵ w₁, h₀³ a₄₁, h₀ p₃₁, h₀⁷ s₁,
h₀⁵ u₁, h₀⁴ b₆₂, h₀² q₅₂` cancel, and the packet's own `p₃₁(a) = 0`
alternative is refuted by `p₃₁(a) ≠ 0` — so the retained `ω/ψ/ψ₂`
tower and the boundary elimination `288 (729 λ + 405 w₁)
(E'(a) W(a) - j) = X'(a) (288 (1980 λ a₄₁ w₁³ - 4400 a₄₁ w₁⁴)
- ψ₂(a))` are forced, not chosen.

No child is closed, because none is contradicted: the quartic child,
the `a₄₁(a) = 0` child, the pinned `p₃₁(a) = 0` child, and the
`p₃₁(a) ≠ 0` child all remain consistent with the final-row boundary
relation `E'(a) W(a) - D(a) X'(a) = j ≠ 0`, which lives on the fresh
boundary coordinates `p₀, p₁, q₀, q₁` no head relation touches.  The
honest residual is that single inhomogeneous boundary relation
together with the preserved ground constants `ζ, η, iotaK` and the
open aligned face `N = 0`.  The Jacobian coefficient tower is fully
consumed (the degree-`0` row is the last) and the degree-`5` integral
`ι` is now spent through both its order-`44` and order-`45` heads and
their exact ground normal forms; the next unused integral row on this
face is the degree-`4` first integral `κ`, which needs the degree-`6`
`θ` tower restated on this chain, and the next unused aligned row on
`N = 0` is the degree-`10` row.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Finite local terminal integral closure packet -/

section NonzeroTerminalIntegralClosure610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local terminal integral closure: the terminal integral
bridge packet with each peeled ground residual replaced by its exact
normal form.  On the `p₃₁(a) = 0` sibling the deeper divisibilities and
source equations are retained and the order-`45` residual splits as
`a₄₁(a) = 0` or the exact quartic `4 a₄₁⁴ - 35 p₂ a₄₁² + 90 p₂² = 0`.
On the complementary factor the two loaded rows and the collapsed
cofactor split on `p₃₁(a)`: if it vanishes the rows pin
`6 p₂(a) = a₄₁(a)²` and `6 b₆₂(a) = 5 a₄₁(a)²`; otherwise the three
normalized ground relations hold and the fifteenth final-row `ω/ψ/ψ₂`
tower with its boundary elimination is forced on the same witnesses.
Neither branch is closed. -/
theorem nonzeroFace610_linearRoot_terminalIntegralClosure
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
    ∃ (w1 a41 s1 u1 p31 b62 q52 : k[X]) (iotaK : k),
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
        terminalClearedIotaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda =
          Polynomial.C iotaK * h0 ^ 50 ∧
        bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 (p.coeff 2)
              (q.coeff 4) (Polynomial.C lambda) +
            h0 * bridgeIotaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
              (Polynomial.C lambda) =
          Polynomial.C iotaK * h0 ^ 6 ∧
        bridgeIotaJetHead610 (w1.eval a) (a41.eval a) (p31.eval a)
            (s1.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
            ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda = 0 ∧
        (p31.eval a) ^ 2 * ((27 : k) * b62.eval a -
            (30 : k) * (a41.eval a) ^ 2 - (5 : k) * (p.coeff 2).eval a +
            (9 : k) * lambda * p31.eval a -
            (40 : k) * p31.eval a * w1.eval a) = 0 ∧
        (p31.eval a) ^ 2 * ((144 : k) * b62.eval a -
            (170 : k) * (a41.eval a) ^ 2 +
            (45 : k) * lambda * p31.eval a -
            (220 : k) * p31.eval a * w1.eval a) = 0 ∧
        ((p31.eval a = 0 ∧
            ∃ (p32 u2 q53 q41 : k[X]),
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
                bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
                    h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                      q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                      (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                      (Polynomial.C lambda) =
                  Polynomial.C iotaK * h0 ^ 5 ∧
                bridgeIotaLeftHead610 (a41.eval a) (s1.eval a)
                    (b62.eval a) ((p.coeff 2).eval a)
                    (q41.eval a) = 0 ∧
                (a41.eval a = 0 ∨
                  (4 : k) * (a41.eval a) ^ 4 -
                      (35 : k) * (p.coeff 2).eval a *
                        (a41.eval a) ^ 2 +
                    (90 : k) * ((p.coeff 2).eval a) ^ 2 = 0)) ∨
          ((240 : k) * (p.coeff 2).eval a -
                (40 : k) * (a41.eval a) ^ 2 -
              (27 : k) * lambda * p31.eval a -
                (40 : k) * p31.eval a * w1.eval a = 0 ∧
            (144 : k) * b62.eval a - (120 : k) * (a41.eval a) ^ 2 +
                (45 : k) * lambda * p31.eval a -
              (200 : k) * p31.eval a * w1.eval a = 0 ∧
            ((p31.eval a = 0 ∧
                (6 : k) * (p.coeff 2).eval a -
                  (a41.eval a) ^ 2 = 0 ∧
                (6 : k) * b62.eval a -
                  (5 : k) * (a41.eval a) ^ 2 = 0) ∨
              (p31.eval a ≠ 0 ∧
                (5 : k) * (a41.eval a) ^ 2 +
                  (2 : k) * p31.eval a * w1.eval a = 0 ∧
                (80 : k) * (p.coeff 2).eval a -
                    (9 : k) * lambda * p31.eval a -
                  (8 : k) * p31.eval a * w1.eval a = 0 ∧
                (144 : k) * b62.eval a +
                    (45 : k) * lambda * p31.eval a -
                  (152 : k) * p31.eval a * w1.eval a = 0 ∧
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
                      (349920 : k[X]) * a41 * Polynomial.C lambda *
                        p31 +
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
                          (1980 : k) * lambda * p31.eval a *
                            w1.eval a +
                        (3200 : k) * p31.eval a *
                          (w1.eval a) ^ 2) ∧
                  psi + ((466560 : k[X]) * a41 ^ 2 *
                      Polynomial.C lambda * w1 +
                    (518400 : k[X]) * a41 ^ 2 * w1 ^ 2 -
                    (1244160 : k[X]) * a41 * s1 * w1 ^ 2 +
                    (349920 : k[X]) * b62 * w1 ^ 2 -
                    (349920 : k[X]) * Polynomial.C lambda *
                      p.coeff 2 * w1 +
                    (466560 : k[X]) * Polynomial.C lambda * p31 *
                      w1 ^ 2 +
                    (194400 : k[X]) * p.coeff 2 * w1 ^ 2 -
                    (432000 : k[X]) * p31 * w1 ^ 3 -
                    (362880 : k[X]) * u1 * w1 ^ 3) = h0 * psi2 ∧
                  psi2.eval a =
                    (288 : k) * ((1980 : k) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4400 : k) * a41.eval a * (w1.eval a) ^ 4 -
                      (729 : k) * lambda * (p.coeff 1).eval a -
                      (405 : k) * (p.coeff 1).eval a *
                        w1.eval a) ∧
                  (288 : k) * ((729 : k) * lambda +
                        (405 : k) * w1.eval a) *
                      (((p.coeff 0).derivative).eval a *
                          (q.coeff 1).eval a - j) =
                    ((q.coeff 0).derivative).eval a *
                      ((288 : k) * ((1980 : k) * lambda *
                            a41.eval a * (w1.eval a) ^ 3 -
                          (4400 : k) * a41.eval a *
                            (w1.eval a) ^ 4) -
                        psi2.eval a))))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, hw, ha4s, hp3, hs, hu,
    hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow, hroweval, hpow, hpeel,
    hheadeval, hres1, hres2, halt⟩ :=
    nonzeroFace610_linearRoot_terminalIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  refine ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, hw, ha4s, hp3, hs, hu,
    hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow, hroweval, hpow, hpeel,
    hheadeval, hres1, hres2, ?_⟩
  rcases halt with ⟨hp31z, p32, u2, q53, q41, hp3u, hq7u, hq5u, hq4u,
      hTform, hWform, hVform, hQ3form, hpeelL, hheadevalL, hresL⟩ |
      ⟨htp, hb62form, hIotaComp⟩
  · exact Or.inl ⟨hp31z, p32, u2, q53, q41, hp3u, hq7u, hq5u, hq4u,
      hTform, hWform, hVform, hQ3form, hpeelL, hheadevalL,
      terminalIotaLeft_groundSplit610 (a41.eval a)
        ((p.coeff 2).eval a) hresL⟩
  · rcases terminalIotaComplement_groundSplit610 (a41.eval a)
        ((p.coeff 2).eval a) (p31.eval a) (w1.eval a) (b62.eval a)
        lambda htp hb62form hIotaComp with
      ⟨hz, hp2pin, hb62pin⟩ | ⟨hnz, hcore, hp2n, hb62n⟩
    · exact Or.inr ⟨htp, hb62form, Or.inl ⟨hz, hp2pin, hb62pin⟩⟩
    · obtain ⟨w1', a41', s1', u1', p31', b62', q52', hw', ha4s', hp3',
        hs', hu', hb6s', hq5', -, -, -, -, -, -, -, halt'⟩ :=
        nonzeroFace610_linearRoot_fifteenthFinalRow p q H h0 j lambda
          a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
      have hw1e : w1' = w1 :=
        mul_left_cancel₀ (pow_ne_zero 5 hh0) (hw'.symm.trans hw)
      have ha41e : a41' = a41 :=
        mul_left_cancel₀ (pow_ne_zero 3 hh0) (ha4s'.symm.trans ha4s)
      have hp31e : p31' = p31 :=
        mul_left_cancel₀ hh0 (hp3'.symm.trans hp3)
      have hs1e : s1' = s1 :=
        mul_left_cancel₀ (pow_ne_zero 7 hh0) (hs'.symm.trans hs)
      have hu1e : u1' = u1 :=
        mul_left_cancel₀ (pow_ne_zero 5 hh0) (hu'.symm.trans hu)
      have hb62e : b62' = b62 :=
        mul_left_cancel₀ (pow_ne_zero 4 hh0) (hb6s'.symm.trans hb6s)
      have hq52e : q52' = q52 :=
        mul_left_cancel₀ (pow_ne_zero 2 hh0) (hq5'.symm.trans hq5)
      rw [hw1e, ha41e, hp31e, hs1e, hu1e, hb62e, hq52e] at halt'
      rcases halt' with ⟨hp31z', -⟩ |
        ⟨-, -, omega, psi, psi2, homega, homegaval, hpsieq, hpsival,
          hpsi2eq, hpsi2val, heli2⟩
      · exact absurd hp31z' hnz
      · exact Or.inr ⟨htp, hb62form, Or.inr ⟨hnz, hcore, hp2n, hb62n,
          omega, psi, psi2, homega, homegaval, hpsieq, hpsival,
          hpsi2eq, hpsi2val, heli2⟩⟩

set_option maxHeartbeats 40000000 in
/-- Source-facing terminal integral closure packet of a normalized
scale-two `(6,10)` nonzero face: the terminal integral bridge packet
with the ground-split normal forms backwired into both live branches —
`a₄₁(a) = 0 ∨ (4 a₄₁⁴ - 35 p₂ a₄₁² + 90 p₂²)(a) = 0` on the
`p₃₁(a) = 0` sibling, and on the complementary factor either
`p₃₁(a) = 0` with the pins `6 p₂(a) = a₄₁(a)²`,
`6 b₆₂(a) = 5 a₄₁(a)²`, or `p₃₁(a) ≠ 0` with the three normalized
ground relations `5 a₄₁² + 2 p₃₁ w₁ = 0`,
`80 p₂ - 9 λ p₃₁ - 8 p₃₁ w₁ = 0`,
`144 b₆₂ + 45 λ p₃₁ - 152 p₃₁ w₁ = 0` at the root and the retained
fifteenth final-row `ω/ψ/ψ₂` packet with its boundary elimination
against `jK`.  The ground constant `iotaK` is preserved, not
cleared, and no branch is closed. -/
theorem normalized610ScaleTwo_nonzeroFace_terminalIntegralClosure
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a jK iotaK : K)
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
        terminalClearedIotaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda =
          Polynomial.C iotaK * h0 ^ 50 ∧
        bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 (p.coeff 2)
              (q.coeff 4) (Polynomial.C lambda) +
            h0 * bridgeIotaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
              (Polynomial.C lambda) =
          Polynomial.C iotaK * h0 ^ 6 ∧
        bridgeIotaJetHead610 (w1.eval a) (a41.eval a) (p31.eval a)
            (s1.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
            ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda = 0 ∧
        (p31.eval a) ^ 2 * ((27 : K) * b62.eval a -
            (30 : K) * (a41.eval a) ^ 2 - (5 : K) * (p.coeff 2).eval a +
            (9 : K) * lambda * p31.eval a -
            (40 : K) * p31.eval a * w1.eval a) = 0 ∧
        (p31.eval a) ^ 2 * ((144 : K) * b62.eval a -
            (170 : K) * (a41.eval a) ^ 2 +
            (45 : K) * lambda * p31.eval a -
            (220 : K) * p31.eval a * w1.eval a) = 0 ∧
        ((p31.eval a = 0 ∧
            ∃ (p32 u2 q53 q41 : K[X]),
              p.coeff 3 = h0 ^ 2 * p32 ∧
                q.coeff 7 = h0 ^ 6 * u2 ∧
                q.coeff 5 = h0 ^ 3 * q53 ∧
                q.coeff 4 = h0 * q41 ∧
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
                bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
                    h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                      q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                      (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                      (Polynomial.C lambda) =
                  Polynomial.C iotaK * h0 ^ 5 ∧
                bridgeIotaLeftHead610 (a41.eval a) (s1.eval a)
                    (b62.eval a) ((p.coeff 2).eval a)
                    (q41.eval a) = 0 ∧
                (a41.eval a = 0 ∨
                  (4 : K) * (a41.eval a) ^ 4 -
                      (35 : K) * (p.coeff 2).eval a *
                        (a41.eval a) ^ 2 +
                    (90 : K) * ((p.coeff 2).eval a) ^ 2 = 0)) ∨
          ((240 : K) * (p.coeff 2).eval a -
                (40 : K) * (a41.eval a) ^ 2 -
              (27 : K) * lambda * p31.eval a -
                (40 : K) * p31.eval a * w1.eval a = 0 ∧
            (144 : K) * b62.eval a - (120 : K) * (a41.eval a) ^ 2 +
                (45 : K) * lambda * p31.eval a -
              (200 : K) * p31.eval a * w1.eval a = 0 ∧
            ((p31.eval a = 0 ∧
                (6 : K) * (p.coeff 2).eval a -
                  (a41.eval a) ^ 2 = 0 ∧
                (6 : K) * b62.eval a -
                  (5 : K) * (a41.eval a) ^ 2 = 0) ∨
              (p31.eval a ≠ 0 ∧
                (5 : K) * (a41.eval a) ^ 2 +
                  (2 : K) * p31.eval a * w1.eval a = 0 ∧
                (80 : K) * (p.coeff 2).eval a -
                    (9 : K) * lambda * p31.eval a -
                  (8 : K) * p31.eval a * w1.eval a = 0 ∧
                (144 : K) * b62.eval a +
                    (45 : K) * lambda * p31.eval a -
                  (152 : K) * p31.eval a * w1.eval a = 0 ∧
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
                      (349920 : K[X]) * a41 * Polynomial.C lambda *
                        p31 +
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
                          (1980 : K) * lambda * p31.eval a *
                            w1.eval a +
                        (3200 : K) * p31.eval a *
                          (w1.eval a) ^ 2) ∧
                  psi + ((466560 : K[X]) * a41 ^ 2 *
                      Polynomial.C lambda * w1 +
                    (518400 : K[X]) * a41 ^ 2 * w1 ^ 2 -
                    (1244160 : K[X]) * a41 * s1 * w1 ^ 2 +
                    (349920 : K[X]) * b62 * w1 ^ 2 -
                    (349920 : K[X]) * Polynomial.C lambda *
                      p.coeff 2 * w1 +
                    (466560 : K[X]) * Polynomial.C lambda * p31 *
                      w1 ^ 2 +
                    (194400 : K[X]) * p.coeff 2 * w1 ^ 2 -
                    (432000 : K[X]) * p31 * w1 ^ 3 -
                    (362880 : K[X]) * u1 * w1 ^ 3) = h0 * psi2 ∧
                  psi2.eval a =
                    (288 : K) * ((1980 : K) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4400 : K) * a41.eval a * (w1.eval a) ^ 4 -
                      (729 : K) * lambda * (p.coeff 1).eval a -
                      (405 : K) * (p.coeff 1).eval a *
                        w1.eval a) ∧
                  (288 : K) * ((729 : K) * lambda +
                        (405 : K) * w1.eval a) *
                      (((p.coeff 0).derivative).eval a *
                          (q.coeff 1).eval a - jK) =
                    ((q.coeff 0).derivative).eval a *
                      ((288 : K) * ((1980 : K) * lambda *
                            a41.eval a * (w1.eval a) ^ 3 -
                          (4400 : K) * a41.eval a *
                            (w1.eval a) ^ 4) -
                        psi2.eval a))))) ∧
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
  obtain ⟨w1', a41', s1', u1', p31', b62', q52', iotaK, hwN, ha4sN,
    hp3N, hsN, huN, hb6sN, hq5N, hMs', hTu', hVq', hWq', hUload',
    hrow, hroweval, hpow, hpeel, hheadeval, hres1, hres2, halt⟩ :=
    nonzeroFace610_linearRoot_terminalIntegralClosure p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot hlambda
  have hsep : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
    intro heq
    apply hj
    rw [← hroweval, heq, sub_self]
  exact ⟨h0, lambda, a, j, iotaK, w1', a41', s1', u1', p31', b62',
    q52', hh0, hlambda, hh0degree, hH, hroot, hwN, ha4sN, hp3N, hsN,
    huN, hb6sN, hq5N, hq9,
    (by rw [hwN]; exact dvd_mul_right _ _),
    (by rw [ha4sN]; exact dvd_mul_right _ _),
    (by rw [hp3N]; exact dvd_mul_right _ _),
    (by rw [hsN]; exact dvd_mul_right _ _),
    (by rw [huN]; exact dvd_mul_right _ _),
    (by rw [hb6sN]; exact dvd_mul_right _ _),
    (by rw [hq5N]; exact dvd_mul_right _ _),
    hMs', hTu', hVq', hWq', hUload', hj, hrow, hroweval, hsep, hpow,
    hpeel, hheadeval, hres1, hres2, halt, hN'⟩

end NonzeroTerminalIntegralClosure610

#print axioms nonzeroFace610_linearRoot_terminalIntegralClosure
#print axioms normalized610ScaleTwo_nonzeroFace_terminalIntegralClosure

end Max11DegreeRoutes
