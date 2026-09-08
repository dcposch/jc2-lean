import Fable610ScaleTwoKappaIntegralBridgeCompatPart19Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section NonzeroKappaIntegralBridge610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Source-facing `κ` integral bridge packet of a normalized scale-two
`(6,10)` nonzero face: the terminal integral closure packet with the
weight-`55` clearing of the degree-`4` first integral `κ`, its
`h₀⁴⁸`-peeled factored head, the chamber-free root split
`a₄₁(a) p₃₁(a)³ = 0` (honestly `a₄₁(a) = 0 ∨ p₃₁(a) = 0`), and the
refined `p₃₁(a) ≠ 0` child carrying `a₄₁(a) = 0`, `w₁(a) = 0`, the
pins `80 p₂(a) = 9 λ p₃₁(a)`, `16 b₆₂(a) = -5 λ p₃₁(a)` and the
collapsed `ψ₂(a) = -209952 λ p₁(a)`.  The ground constants `iotaK` and
`kappaMu` are preserved, not cleared, and no child is closed. -/
theorem normalized610ScaleTwo_nonzeroFace_kappaIntegralBridge
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a jK iotaK kappaMu : K)
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
        bridgeClearedKappaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C kappaMu * h0 ^ 55 ∧
        bridgeKappaJetHead610 a41 p31 s1 u1 q52 (q.coeff 4) +
            h0 * bridgeKappaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C kappaMu * h0 ^ 7 ∧
        bridgeKappaJetHead610 (a41.eval a) (p31.eval a) (s1.eval a)
            (u1.eval a) (q52.eval a) ((q.coeff 4).eval a) = 0 ∧
        a41.eval a * (p31.eval a) ^ 3 = 0 ∧
        (a41.eval a = 0 ∨ p31.eval a = 0) ∧
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
              (p31.eval a ≠ 0 ∧ a41.eval a = 0 ∧ w1.eval a = 0 ∧
                (80 : K) * (p.coeff 2).eval a =
                  (9 : K) * lambda * p31.eval a ∧
                (16 : K) * b62.eval a =
                  -(5 : K) * lambda * p31.eval a ∧
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
                  psi2.eval a =
                    -(209952 : K) * lambda * (p.coeff 1).eval a ∧
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
  obtain ⟨w1', a41', s1', u1', p31', b62', q52', iotaK, kappaMu, hwN,
    ha4sN, hp3N, hsN, huN, hb6sN, hq5N, hMs', hTu', hVq', hWq',
    hUload', hrow, hroweval, hipow, hipeel, hiheadeval, hres1, hres2,
    hkpow, hkpeel, hkheadeval, hksplit0, hksplit, halt⟩ :=
    nonzeroFace610_linearRoot_kappaIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot hlambda
  have hsep : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
    intro heq
    apply hj
    rw [← hroweval, heq, sub_self]
  exact ⟨h0, lambda, a, j, iotaK, kappaMu, w1', a41', s1', u1', p31',
    b62', q52', hh0, hlambda, hh0degree, hH, hroot, hwN, ha4sN, hp3N,
    hsN, huN, hb6sN, hq5N, hq9,
    (by rw [hwN]; exact dvd_mul_right _ _),
    (by rw [ha4sN]; exact dvd_mul_right _ _),
    (by rw [hp3N]; exact dvd_mul_right _ _),
    (by rw [hsN]; exact dvd_mul_right _ _),
    (by rw [huN]; exact dvd_mul_right _ _),
    (by rw [hb6sN]; exact dvd_mul_right _ _),
    (by rw [hq5N]; exact dvd_mul_right _ _),
    hMs', hTu', hVq', hWq', hUload', hj, hrow, hroweval, hsep, hipow,
    hipeel, hiheadeval, hres1, hres2, hkpow, hkpeel, hkheadeval,
    hksplit0, hksplit, halt, hN'⟩

end NonzeroKappaIntegralBridge610

end Max11DegreeRoutes
