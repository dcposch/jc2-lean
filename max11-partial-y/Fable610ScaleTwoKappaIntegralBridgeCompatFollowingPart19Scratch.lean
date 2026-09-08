import Fable610ScaleTwoKappaIntegralBridgeCompatFollowingPart18Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section NonzeroMuIntegralBridge610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Source-facing `μ` integral bridge packet of a normalized scale-two
`(6,10)` nonzero face: the `λ` bridge packet with the weight-`65`
clearing of the degree-`2` first integral, its `h₀⁵⁹`-peeled head and
chamber-free twenty-three-term root reduction, the seven
sibling-child descents with the `h₀⁶¹`-peeled deep head and its
honest split, and the pinned complement child refined by the honest
split `a₄₁(a) = 0 ∨` first `q₃`-tie.  The ground constants `iotaK`,
`kappaMu`, `lambdaNu` and `muXi` are preserved, not cleared, and no
surviving child is closed. -/
theorem normalized610ScaleTwo_nonzeroFace_muIntegralBridge
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a jK iotaK kappaMu lambdaNu muXi : K)
      (w1 a41 s1 u1 p31 b62 q52 p32 u2 q53 q41 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        p.coeff 3 = h0 ^ 2 * p32 ∧ q.coeff 7 = h0 ^ 6 * u2 ∧
        q.coeff 5 = h0 ^ 3 * q53 ∧ q.coeff 4 = h0 * q41 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧
        h0 ^ 2 ∣ p.coeff 3 ∧ h0 ^ 7 ∣ q.coeff 8 ∧ h0 ^ 6 ∣ q.coeff 7 ∧
        h0 ^ 4 ∣ q.coeff 6 ∧ h0 ^ 3 ∣ q.coeff 5 ∧ h0 ∣ q.coeff 4 ∧
        (3 : K) * s1.eval a = (5 : K) * a41.eval a ∧
        (10 : K) * (a41.eval a) ^ 2 - (18 : K) * b62.eval a -
            (9 : K) * lambda * p31.eval a +
          (30 : K) * (p.coeff 2).eval a +
            (20 : K) * p31.eval a * w1.eval a = 0 ∧
        p31.eval a = 0 ∧ u1.eval a = 0 ∧ q52.eval a = 0 ∧
        (q.coeff 4).eval a = 0 ∧
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
        bridgeClearedLambdaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C lambdaNu * h0 ^ 60 ∧
        bridgeLambdaJetHead610 p31 u1 (q.coeff 4) +
            h0 * bridgeLambdaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C lambdaNu * h0 ^ 8 ∧
        bridgeLambdaJetHead610 (p31.eval a) (u1.eval a)
          ((q.coeff 4).eval a) = 0 ∧
        bridgeLambdaDeepHead610 a41 s1 b62 (p.coeff 2) q41 +
            h0 * bridgeLambdaDeepTail610 h0 w1 a41 p32 s1 u2 b62 q53
              (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C lambdaNu * h0 ^ 6 ∧
        bridgeLambdaDeepHead610 (a41.eval a) (s1.eval a) (b62.eval a)
          ((p.coeff 2).eval a) (q41.eval a) = 0 ∧
        (100 : K) * (a41.eval a) ^ 6 -
            (1575 : K) * (a41.eval a) ^ 4 * (p.coeff 2).eval a +
          (810 : K) * (a41.eval a) ^ 3 * q41.eval a +
            (4860 : K) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 -
          (2916 : K) * a41.eval a * (p.coeff 2).eval a * q41.eval a -
            (1620 : K) * ((p.coeff 2).eval a) ^ 3 = 0 ∧
        bridgeClearedMuDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C muXi * h0 ^ 65 ∧
        bridgeMuJetHead610 w1 a41 p32 s1 u2 b62 q53 (p.coeff 2) q41
              (q.coeff 3) (Polynomial.C lambda) +
            h0 * bridgeMuJetTail610 h0 w1 a41 p32 s1 u2 b62 q53
              (p.coeff 2) (p.coeff 1) (p.coeff 0) q41 (q.coeff 3)
              (q.coeff 2) (q.coeff 1) (Polynomial.C lambda) =
          Polynomial.C muXi * h0 ^ 6 ∧
        bridgeMuJetHead610 (w1.eval a) (a41.eval a) (p32.eval a)
          (s1.eval a) (u2.eval a) (b62.eval a) (q53.eval a)
          ((p.coeff 2).eval a) (q41.eval a) ((q.coeff 3).eval a)
          lambda = 0 ∧
        -(1120 : K) * (a41.eval a) ^ 6 * (w1.eval a)
        + (189 : K) * (a41.eval a) ^ 6 * lambda
        + (220 : K) * (a41.eval a) ^ 5 * (p32.eval a)
        + (588 : K) * (a41.eval a) ^ 5 * (u2.eval a)
        + (9200 : K) * (a41.eval a) ^ 4 * ((p.coeff 2).eval a) * (w1.eval a)
        - (1260 : K) * (a41.eval a) ^ 4 * ((p.coeff 2).eval a) * lambda
        - (600 : K) * (a41.eval a) ^ 4 * (q53.eval a)
        - (3360 : K) * (a41.eval a) ^ 3 * ((p.coeff 2).eval a) * (p32.eval a)
        - (3360 : K) * (a41.eval a) ^ 3 * ((p.coeff 2).eval a) * (u2.eval a)
        - (1920 : K) * (a41.eval a) ^ 3 * (q41.eval a) * (w1.eval a)
        + (576 : K) * (a41.eval a) ^ 3 * ((q.coeff 3).eval a)
        - (17280 : K) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 * (w1.eval a)
        + (2160 : K) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) ^ 2 * lambda
        + (2880 : K) * (a41.eval a) ^ 2 * ((p.coeff 2).eval a) * (q53.eval a)
        + (2304 : K) * (a41.eval a) ^ 2 * (p32.eval a) * (q41.eval a)
        + (4800 : K) * (a41.eval a) * ((p.coeff 2).eval a) ^ 2 * (p32.eval a)
        + (4032 : K) * (a41.eval a) * ((p.coeff 2).eval a) ^ 2 * (u2.eval a)
        + (4608 : K) * (a41.eval a) * ((p.coeff 2).eval a) * (q41.eval a) * (w1.eval a)
        - (2304 : K) * (a41.eval a) * ((p.coeff 2).eval a) * ((q.coeff 3).eval a)
        + (3840 : K) * ((p.coeff 2).eval a) ^ 3 * (w1.eval a)
        - (576 : K) * ((p.coeff 2).eval a) ^ 3 * lambda
        - (1920 : K) * ((p.coeff 2).eval a) ^ 2 * (q53.eval a)
        - (3072 : K) * ((p.coeff 2).eval a) * (p32.eval a) * (q41.eval a) = 0 ∧
        ((∃ a42 p21 s2 b63 q54 q42 q31 : K[X],
            (bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
                h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                  q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                  (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                  (Polynomial.C lambda) =
              Polynomial.C iotaK * h0 ^ 5) ∧
            a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
            s1.eval a = 0 ∧ b62.eval a = 0 ∧ q41.eval a = 0 ∧
            q53.eval a = 0 ∧ (q.coeff 3).eval a = 0 ∧
            (3 : K) * u2.eval a = (5 : K) * p32.eval a ∧
            p.coeff 4 = h0 ^ 4 * a42 ∧ p.coeff 2 = h0 * p21 ∧
            q.coeff 8 = h0 ^ 8 * s2 ∧ q.coeff 6 = h0 ^ 5 * b63 ∧
            q.coeff 5 = h0 ^ 4 * q54 ∧ q.coeff 4 = h0 ^ 2 * q42 ∧
            q.coeff 3 = h0 * q31 ∧
            (bridgeMuDeepHead610 w1 p32 u2 b63 p21 q42 q31
                  (Polynomial.C lambda) +
                h0 * bridgeMuDeepTail610 h0 w1 a42 p32 s2 u2 b63 q54
                  p21 (p.coeff 1) (p.coeff 0) q42 q31 (q.coeff 2)
                  (q.coeff 1) (Polynomial.C lambda) =
              Polynomial.C muXi * h0 ^ 4) ∧
            bridgeMuDeepHead610 (w1.eval a) (p32.eval a) (u2.eval a)
              (b63.eval a) (p21.eval a) (q42.eval a) (q31.eval a)
              lambda = 0 ∧
            ((p32.eval a = 0 ∧ u2.eval a = 0) ∨
              (45 : K) * lambda * (p32.eval a) ^ 3 +
                  (144 : K) * b63.eval a * (p32.eval a) ^ 2 +
                  (240 : K) * p21.eval a * (p32.eval a) ^ 2 +
                  (288 : K) * p32.eval a * q42.eval a * w1.eval a -
                (400 : K) * (p32.eval a) ^ 3 * w1.eval a -
                  (144 : K) * p32.eval a * q31.eval a -
                  (384 : K) * p21.eval a * q42.eval a = 0)) ∨
          ((6 : K) * (p.coeff 2).eval a - (a41.eval a) ^ 2 = 0 ∧
            (6 : K) * b62.eval a - (5 : K) * (a41.eval a) ^ 2 = 0 ∧
            ((a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
                b62.eval a = 0) ∨
              (a41.eval a = 0 ∧ (p.coeff 2).eval a = 0 ∧
                b62.eval a = 0 ∧ q41.eval a = 0) ∨
              ((324 : K) * q41.eval a = (35 : K) * (a41.eval a) ^ 3 ∧
                (15552 : K) * (q.coeff 3).eval a =
                  -(2943 : K) * lambda * (a41.eval a) ^ 3 +
                    (14040 : K) * (a41.eval a) ^ 3 * w1.eval a +
                    (1060 : K) * (a41.eval a) ^ 2 * p32.eval a -
                    (11340 : K) * (a41.eval a) ^ 2 * u2.eval a +
                    (14040 : K) * a41.eval a * q53.eval a)))) ∧
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
  obtain ⟨w1', a41', s1', u1', p31', b62', q52', p32', u2', q53',
    q41', iotaK, kappaMu, lambdaNu, muXi, hwN, ha4sN, hp3N, hsN, huN,
    hb6sN, hq5N, hMs', hUload', hrow, hroweval, hipow, hipeel,
    hiheadeval, hkpow, hkpeel, hkheadeval, hlpow, hlpeel, hlheadeval,
    hp31z, hu1z, hq52z, hq4z, hp3deep, hq7deep, hq5deep, hq4deep,
    hldeepPeel, hldeepHeadEval, hG, hmupow, hmupeel, hmuheadeval,
    hmuR22, halt⟩ :=
    nonzeroFace610_linearRoot_muIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot hlambda
  have hsep : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
    intro heq
    apply hj
    rw [← hroweval, heq, sub_self]
  exact ⟨h0, lambda, a, j, iotaK, kappaMu, lambdaNu, muXi, w1', a41',
    s1', u1', p31', b62', q52', p32', u2', q53', q41', hh0, hlambda,
    hh0degree, hH, hroot, hwN, ha4sN, hp3N, hsN, huN, hb6sN, hq5N,
    hp3deep, hq7deep, hq5deep, hq4deep, hq9,
    (by rw [hwN]; exact dvd_mul_right _ _),
    (by rw [ha4sN]; exact dvd_mul_right _ _),
    (by rw [hp3deep]; exact dvd_mul_right _ _),
    (by rw [hsN]; exact dvd_mul_right _ _),
    (by rw [hq7deep]; exact dvd_mul_right _ _),
    (by rw [hb6sN]; exact dvd_mul_right _ _),
    (by rw [hq5deep]; exact dvd_mul_right _ _),
    (by rw [hq4deep]; exact dvd_mul_right _ _),
    hMs', hUload', hp31z, hu1z, hq52z, hq4z, hj, hrow, hroweval, hsep,
    hipow, hipeel, hiheadeval, hkpow, hkpeel, hkheadeval, hlpow,
    hlpeel, hlheadeval, hldeepPeel, hldeepHeadEval, hG, hmupow,
    hmupeel, hmuheadeval, hmuR22, halt, hN'⟩

end NonzeroMuIntegralBridge610

end Max11DegreeRoutes
