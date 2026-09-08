import Fable410ScaleTwoIotaSourceBridgeScratch

/-! # Linear polar branch `λ + 4 t₂(a) = 0` of the `(4,10)` iota bridge

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the iota source bridge proved the polar split at the
root of the degree-one scale: `p₁(a) = 0` or `λ + 4 t₂(a) = 0`.  This
file works the second branch only; the complementary branch
`p₁(a) = 0` is not touched and stays open.

First, the source power relation `8 h³ ι = C c h³` is peeled
`h`-adically to the bottom: exact cofactors `w₁, w₂, w₃` with
`D₃ = h w₁`, `w₁ + D₂ = h w₂`, `w₂ + D₁ = h w₃`, `w₃ + D₀ = C c` on
the four numerator blocks, and the root evaluations
`w₁(a) + D₂(a) = 0`, `w₂(a) + D₁(a) = 0`, `w₃(a) + D₀(a) = c`.
Nothing further remains in the power relation beyond the scalar `c`.

Second, on the branch the exact order-`-2` residual of the bridge loses
`λ`:
`16 w₁(a) + 3 p₁(a)² (-20 a₂₂² + 46 a₂₂ t₂² + 32 s₂₂ t₂² - 9 t₂⁴)(a) = 0`.

Third, the order-`-1` block is reduced on the thirteenth-face jet
(`2 vis = 5 p₁`, `8 w₇₃ = p₁ (30 t₂ - 9 λ)`, and the fifth leftover);
every surviving jet term carries a factor `t₂(a) = -λ/4`, so with the
explicit jet sextic `𝒢` below the next unused source coefficient `q₁`
enters exactly once:
`32 w₂(a) + λ (16 q₁(a) - p₁(a) 𝒢(a)) = 0`.
The coefficient `q₁(a)` is tied, not determined.

Fourth, the last unused Jacobian coefficient — the degree-`0` Keller
row `p₀' q₁ - p₁ q₀' = j`, isolated by the thirteenth face and never an
exact first integral — is evaluated at the root and combined with the
order-`-1` residual to eliminate `q₁(a)`:
`32 p₀'(a) w₂(a) + 16 λ j = λ p₁(a) (𝒢(a) p₀'(a) - 16 q₀'(a))`.
This is the first exact link between the `ι` tower and the literal
Keller constant on this branch.

The branch does not close: no individual vanishing of `p₁(a), t₂(a),
a₂₂, s₂₂, q₁(a), c`, or `j` is claimed, the boundary data
`p₀'(a), q₀'(a)` and the ground constant `c` are fresh unknowns, and
the `θ` first integral of the degree-`4` row (ninth face) remains
uncleared against the thirteenth-face jet.  The ground constants
`α, β, γ, δ` are not touched.  No total-degree or twice-prime theorem
is used.  The aligned face `N = 0` is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Exact `h`-adic peel of the iota power relation -/

section IotaLinearPolarBranch410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-- Full `h`-adic peel of the cleared `ι` power relation: exact
cofactors for the order-`-3`, order-`-2`, and order-`-1` blocks, the
scalar tie of the regular block to the ground constant `c`, and the
three root evaluations.  Nothing beyond `c` is left in the power
relation. -/
theorem iotaBridge_orderOnePeel410 (h t2 a22 s22 vis w73 q54 a1 a0 b42
    b31 b2 b1 b0 : k[X]) (lambda a c : k)
    (hroot : h.eval a = 0)
    (hpow : localClearedIotaResidual410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3) :
    ∃ w1 w2 w3 : k[X],
      iotaPolarThreeNumerator410 t2 vis w73 a1 b42 b31 lambda =
          h * w1 ∧
        w1 + iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42
            b31 b2 lambda =
          h * w2 ∧
        w2 + iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
            lambda =
          h * w3 ∧
        w3 + iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda =
          Polynomial.C c ∧
        w1.eval a +
            (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42
                b31 b2 lambda).eval a =
          0 ∧
        w2.eval a +
            (iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
                lambda).eval a =
          0 ∧
        w3.eval a +
            (iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda).eval a =
          c := by
  have hpow' := hpow
  simp only [localClearedIotaResidual410] at hpow'
  refine ⟨Polynomial.C c * h ^ 2 -
      (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31
          b2 lambda +
        h * (iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
            lambda +
          h * iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda)),
    Polynomial.C c * h -
      (iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
          lambda +
        h * iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda),
    Polynomial.C c - iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination hpow'
  · ring
  · ring
  · ring
  · simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, hroot]
    ring
  · simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, hroot]
    ring
  · simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, hroot]
    ring

/-- On the linear polar branch `λ + 4 t₂(a) = 0` the exact order-`-2`
residual of the bridge loses `λ`: the retained quartic becomes
`-20 a₂₂² + 46 a₂₂ t₂² + 32 s₂₂ t₂² - 9 t₂⁴` at the root.  `w₁(a)` is
tied, not determined. -/
theorem iotaLinearPolarBranch_orderTwoResidual410 (h t2 a22 s22 vis w73
    q54 a1 a0 b42 b31 b2 b1 b0 : k[X]) (lambda a c : k)
    (hroot : h.eval a = 0)
    (hpow : localClearedIotaResidual410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * (a1.eval a) ^ 2)
    (hV : (32 : k) * q54.eval a + (40 : k) * a1.eval a * a22.eval a -
        (64 : k) * a1.eval a * s22.eval a -
        (27 : k) * a1.eval a * lambda * t2.eval a +
        (90 : k) * a1.eval a * (t2.eval a) ^ 2 =
      0)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * (a1.eval a) ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda))
    (hY : (256 : k) * b2.eval a =
      (a1.eval a) ^ 2 *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * (t2.eval a) ^ 2))
    (hbranch : lambda + (4 : k) * t2.eval a = 0) :
    ∃ w1 : k[X],
      iotaPolarThreeNumerator410 t2 vis w73 a1 b42 b31 lambda =
          h * w1 ∧
        (16 : k) * w1.eval a +
            (3 : k) * (a1.eval a) ^ 2 *
              (-(20 : k) * (a22.eval a) ^ 2 +
                (46 : k) * a22.eval a * (t2.eval a) ^ 2 +
                (32 : k) * s22.eval a * (t2.eval a) ^ 2 -
                (9 : k) * (t2.eval a) ^ 4) =
          0 := by
  obtain ⟨w1, hw1, hres⟩ := iotaBridge_orderTwoResidual410 h t2 a22 s22
    vis w73 q54 a1 a0 b42 b31 b2 b1 b0 lambda a c hroot hpow hT hU hW
    hV hX hY
  refine ⟨w1, hw1, ?_⟩
  linear_combination (1 / 8 : k) * hres +
    (27 / 8 : k) * (a1.eval a) ^ 2 * t2.eval a *
      ((3 : k) * (t2.eval a) ^ 2 - (2 : k) * a22.eval a) * hbranch

/-- Jet core of the order-`-1` block on the linear polar branch: the
sextic cofactor of `p₁` left after the thirteenth-face jet
reductions. -/
def iotaOrderOneJetCore410 (a0 a22 s22 t2 : k) : k :=
  -(204 : k) * a0 * a22 - (96 : k) * a0 * s22 +
    (297 : k) * a0 * t2 ^ 2 + (124 : k) * a22 ^ 3 +
    (224 : k) * a22 ^ 2 * s22 - (1265 : k) * a22 ^ 2 * t2 ^ 2 -
    (352 : k) * a22 * s22 * t2 ^ 2 + (1293 : k) * a22 * t2 ^ 4 +
    (96 : k) * s22 * t2 ^ 4 - (297 : k) * t2 ^ 6

set_option maxHeartbeats 4000000 in
/-- Branch residual packet: the full peel together with the
branch-normalized order-`-2` residual and the new exact order-`-1`
residual.  On the jet every order-`-1` term carries `t₂(a) = -λ/4`, so
the next unused source coefficient `q₁ = b₁` enters exactly once:
`32 w₂(a) + λ (16 b₁(a) - p₁(a) 𝒢(a)) = 0`.  Neither `w₂(a)` nor
`b₁(a)` is determined, and the branch is not closed. -/
theorem iotaLinearPolarBranch_residuals410 (h t2 a22 s22 vis w73 q54 a1
    a0 b42 b31 b2 b1 b0 : k[X]) (lambda a c : k)
    (hroot : h.eval a = 0)
    (hpow : localClearedIotaResidual410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * (a1.eval a) ^ 2)
    (hV : (32 : k) * q54.eval a + (40 : k) * a1.eval a * a22.eval a -
        (64 : k) * a1.eval a * s22.eval a -
        (27 : k) * a1.eval a * lambda * t2.eval a +
        (90 : k) * a1.eval a * (t2.eval a) ^ 2 =
      0)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * (a1.eval a) ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda))
    (hY : (256 : k) * b2.eval a =
      (a1.eval a) ^ 2 *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * (t2.eval a) ^ 2))
    (hbranch : lambda + (4 : k) * t2.eval a = 0) :
    ∃ w1 w2 w3 : k[X],
      iotaPolarThreeNumerator410 t2 vis w73 a1 b42 b31 lambda =
          h * w1 ∧
        w1 + iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42
            b31 b2 lambda =
          h * w2 ∧
        w2 + iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
            lambda =
          h * w3 ∧
        w3 + iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda =
          Polynomial.C c ∧
        (16 : k) * w1.eval a +
            (3 : k) * (a1.eval a) ^ 2 *
              (-(20 : k) * (a22.eval a) ^ 2 +
                (46 : k) * a22.eval a * (t2.eval a) ^ 2 +
                (32 : k) * s22.eval a * (t2.eval a) ^ 2 -
                (9 : k) * (t2.eval a) ^ 4) =
          0 ∧
        (32 : k) * w2.eval a +
            lambda *
              ((16 : k) * b1.eval a -
                a1.eval a *
                  iotaOrderOneJetCore410 (a0.eval a) (a22.eval a)
                    (s22.eval a) (t2.eval a)) =
          0 ∧
        w3.eval a +
            (iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda).eval a =
          c := by
  obtain ⟨w1, w2, w3, hw1, hw2, hw3, hwc, he1, he2, he3⟩ :=
    iotaBridge_orderOnePeel410 h t2 a22 s22 vis w73 q54 a1 a0 b42 b31
      b2 b1 b0 lambda a c hroot hpow
  have hlink2 :
      (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31
          b2 lambda).eval a =
        (8 : k) * iotaOrderTwo410 (a0.eval a) (a1.eval a) (t2.eval a)
          (a22.eval a) (s22.eval a) (vis.eval a) (w73.eval a)
          (q54.eval a) (b42.eval a) (b31.eval a) (b2.eval a)
          lambda := by
    simp only [iotaPolarTwoNumerator410, iotaOrderTwo410, eval_add,
      eval_sub, eval_mul, eval_pow, eval_ofNat, eval_C, eval_neg]
    ring
  have hfact2 := terminalIota_orderTwo_onJet410 (a0.eval a)
    (a1.eval a) (t2.eval a) (a22.eval a) (s22.eval a) (vis.eval a)
    (w73.eval a) (q54.eval a) (b42.eval a) (b31.eval a) (b2.eval a)
    lambda hT hU hW hV hX hY
  have hP1val :
      (32 : k) *
          (iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
              lambda).eval a =
        lambda *
          ((16 : k) * b1.eval a -
            a1.eval a *
              iotaOrderOneJetCore410 (a0.eval a) (a22.eval a)
                (s22.eval a) (t2.eval a)) := by
    simp only [iotaPolarOneNumerator410, iotaOrderOneJetCore410,
      eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat, eval_C,
      eval_neg]
    linear_combination
      (-(t2.eval a) *
          ((14 : k) * a0.eval a * a22.eval a -
            (7 : k) * a0.eval a * (t2.eval a) ^ 2 -
            (7 : k) * (a22.eval a) ^ 3 +
            (14 : k) * (a22.eval a) ^ 2 * (t2.eval a) ^ 2 -
            (7 : k) * a22.eval a * (t2.eval a) ^ 4 +
            (t2.eval a) ^ 6)) * hT +
        ((8 : k) *
            ((6 : k) * a0.eval a * a22.eval a -
              (6 : k) * a0.eval a * (t2.eval a) ^ 2 -
              (2 : k) * (a22.eval a) ^ 3 +
              (9 : k) * (a22.eval a) ^ 2 * (t2.eval a) ^ 2 -
              (6 : k) * a22.eval a * (t2.eval a) ^ 4 +
              (t2.eval a) ^ 6)) * hU +
          (-(2 : k) * t2.eval a *
              (-(5 : k) * a0.eval a + (5 : k) * (a22.eval a) ^ 2 -
                (5 : k) * a22.eval a * (t2.eval a) ^ 2 +
                (t2.eval a) ^ 4)) * hV +
            (-(60 : k) * a0.eval a * a1.eval a * a22.eval a -
              (96 : k) * a0.eval a * a1.eval a * s22.eval a +
              (135 : k) * a0.eval a * a1.eval a * (t2.eval a) ^ 2 -
              (20 : k) * a1.eval a * (a22.eval a) ^ 3 +
              (224 : k) * a1.eval a * (a22.eval a) ^ 2 * s22.eval a -
              (455 : k) * a1.eval a * (a22.eval a) ^ 2 *
                (t2.eval a) ^ 2 -
              (352 : k) * a1.eval a * a22.eval a * s22.eval a *
                (t2.eval a) ^ 2 +
              (555 : k) * a1.eval a * a22.eval a * (t2.eval a) ^ 4 +
              (96 : k) * a1.eval a * s22.eval a * (t2.eval a) ^ 4 -
              (135 : k) * a1.eval a * (t2.eval a) ^ 6 -
              (16 : k) * b1.eval a) * hbranch
  refine ⟨w1, w2, w3, hw1, hw2, hw3, hwc, ?_, ?_, he3⟩
  · linear_combination (16 : k) * he1 - (16 : k) * hlink2 -
      (128 : k) * hfact2 +
      (27 / 8 : k) * (a1.eval a) ^ 2 * t2.eval a *
        ((3 : k) * (t2.eval a) ^ 2 - (2 : k) * a22.eval a) * hbranch
  · linear_combination (32 : k) * he2 - hP1val

/-! ## The degree-`0` Keller row at the root -/

/-- The last unused Jacobian coefficient, the degree-`0` Keller row
`p₀' q₁ - p₁ q₀' = j`, evaluated at the root of the degree-one scale.
It is not an exact first integral; only its literal evaluation is
used. -/
theorem kellerRowConstant_eval410 {p q : k[X][X]} {j : k}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) (a : k) :
    ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
        (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  have hrow := thirteenthCoefficientJacobianRow_410 hp hq hjac
  have heval := congrArg (fun r : k[X] => r.eval a) hrow
  simpa only [eval_sub, eval_mul, eval_C] using heval

/-! ## Source-facing branch packet -/

set_option maxHeartbeats 4000000 in
/-- Sharpest exact successor packet on the linear polar branch
`λ + 4 t₂(a) = 0` of the nonzero `(4,10)` face: the peeled power
relation, the branch-normalized order-`-2` residual, the order-`-1`
residual tying the next unused source coefficient `q₁`, the degree-`0`
Keller row at the root, and their combination eliminating `q₁(a)`
against the literal Keller constant `j`.  The complementary branch
`p₁(a) = 0` is untouched, and nothing here closes this branch: `w₁(a)`,
`w₂(a)`, `c`, `q₁(a)`, `p₀'(a)`, `q₀'(a)` are tied, not determined. -/
theorem nonzeroFace410_iotaLinearPolarBranchPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 vis w73 q54 b42 b31 : k[X]) (a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hp3 : p.coeff 3 = h0 ^ 3 * t2) (hp2 : p.coeff 2 = h0 ^ 2 * a22)
    (hq8 : q.coeff 8 = h0 ^ 8 * s22) (hq7 : q.coeff 7 = h0 ^ 6 * vis)
    (hq6 : q.coeff 6 = h0 ^ 5 * w73) (hq5 : q.coeff 5 = h0 ^ 4 * q54)
    (hq4 : q.coeff 4 = h0 ^ 2 * b42) (hq3 : q.coeff 3 = h0 * b31)
    (hroot : h0.eval a = 0)
    (hT : (64 : k) * vis.eval a - (160 : k) * (p.coeff 1).eval a = 0)
    (hU : (8 : k) * w73.eval a =
      (p.coeff 1).eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * ((p.coeff 1).eval a) ^ 2)
    (hV : (32 : k) * q54.eval a +
        (40 : k) * (p.coeff 1).eval a * a22.eval a -
        (64 : k) * (p.coeff 1).eval a * s22.eval a -
        (27 : k) * (p.coeff 1).eval a * lambda * t2.eval a +
        (90 : k) * (p.coeff 1).eval a * (t2.eval a) ^ 2 =
      0)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * ((p.coeff 1).eval a) ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda))
    (hY : (256 : k) * (q.coeff 2).eval a =
      ((p.coeff 1).eval a) ^ 2 *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * (t2.eval a) ^ 2))
    (hbranch : lambda + (4 : k) * t2.eval a = 0) :
    ∃ (c : k) (w1 w2 w3 : k[X]),
      localClearedIotaResidual410 h0 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1) (q.coeff 0)
          lambda =
        Polynomial.C c * h0 ^ 3 ∧
      iotaPolarThreeNumerator410 t2 vis w73 (p.coeff 1) b42 b31
          lambda =
        h0 * w1 ∧
      w1 + iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) b42 b31 (q.coeff 2) lambda =
        h0 * w2 ∧
      w2 + iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) (q.coeff 1) lambda =
        h0 * w3 ∧
      w3 + iotaRegularNumerator410 t2 a22 s22 (p.coeff 0) (q.coeff 0)
          lambda =
        Polynomial.C c ∧
      (16 : k) * w1.eval a +
          (3 : k) * ((p.coeff 1).eval a) ^ 2 *
            (-(20 : k) * (a22.eval a) ^ 2 +
              (46 : k) * a22.eval a * (t2.eval a) ^ 2 +
              (32 : k) * s22.eval a * (t2.eval a) ^ 2 -
              (9 : k) * (t2.eval a) ^ 4) =
        0 ∧
      (32 : k) * w2.eval a +
          lambda *
            ((16 : k) * (q.coeff 1).eval a -
              (p.coeff 1).eval a *
                iotaOrderOneJetCore410 ((p.coeff 0).eval a)
                  (a22.eval a) (s22.eval a) (t2.eval a)) =
        0 ∧
      w3.eval a +
          (iotaRegularNumerator410 t2 a22 s22 (p.coeff 0) (q.coeff 0)
              lambda).eval a =
        c ∧
      ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a =
        j ∧
      (32 : k) * ((p.coeff 0).derivative).eval a * w2.eval a +
          (16 : k) * lambda * j =
        lambda * (p.coeff 1).eval a *
          (iotaOrderOneJetCore410 ((p.coeff 0).eval a) (a22.eval a)
              (s22.eval a) (t2.eval a) *
              ((p.coeff 0).derivative).eval a -
            (16 : k) * ((q.coeff 0).derivative).eval a) := by
  obtain ⟨c, hpow⟩ := nonzeroFace410_iotaResidualPowerRelation p q H h0
    j lambda t2 a22 s22 vis w73 q54 b42 b31 hp hq hh0 hH hp4 hq10 hN
    hD hp3 hp2 hq8 hq7 hq6 hq5 hq4 hq3
  obtain ⟨w1, w2, w3, hw1, hw2, hw3, hwc, hres2, hres1, hreg⟩ :=
    iotaLinearPolarBranch_residuals410 h0 t2 a22 s22 vis w73 q54
      (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
      (q.coeff 0) lambda a c hroot hpow hT hU hW hV hX hY hbranch
  have hkel := kellerRowConstant_eval410 hp hq hD a
  refine ⟨c, w1, w2, w3, hpow, hw1, hw2, hw3, hwc, hres2, hres1, hreg,
    hkel, ?_⟩
  linear_combination ((p.coeff 0).derivative).eval a * hres1 -
    (16 : k) * lambda * hkel

end IotaLinearPolarBranch410

#print axioms iotaBridge_orderOnePeel410
#print axioms iotaLinearPolarBranch_orderTwoResidual410
#print axioms iotaLinearPolarBranch_residuals410
#print axioms kellerRowConstant_eval410
#print axioms nonzeroFace410_iotaLinearPolarBranchPacket

end Max11DegreeRoutes
