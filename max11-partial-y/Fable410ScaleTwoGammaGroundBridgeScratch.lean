import Fable410ScaleTwoBetaGroundBridgeScratch

/-! # Gamma ground bridge for the normalized `(4,10)` nonzero source

The beta ground bridge pinned the row-`10` ground first integral `β`
at exact order `-1` and eliminated `s₂₂` from its solved cofactor
through the global `α` pin.  The next ground first integral is
`γ = R - (5/2) C - (9/4) L B - 2 P A + (25/8) A²` (row `9`,
`gammaResidual410`, fourth face).  On the thirteenth-face jet its
moving letters `B`, `C`, `R` all sit at EXACT order `-1`, so the
cleared defect again has weight one — but the polar residue block is
now jet-loaded: `t₂` and `λ` multiply the residue letters.

First, the clearing (`gammaDefect_eq_cleared410`): `128 h γ` splits as
the polar residue block `128 w₇₃ - 224 t₂ q₇₆ + 80 p₁ t₂ + 144 λ p₁`
plus `h` times the regular block `-525 t₂⁴ + 210 λ t₂³ + 320 s₂₂ t₂² +
400 a₂₂ t₂² - 360 λ a₂₂ t₂ - 256 a₂₂ s₂₂ + 400 a₂₂² - 320 p₀` — the
first ground block seeing the quartic constant `p₀`.

Second, the literal-source trace: the fourth-face power relation pins
the row-`9` integral globally (`nonzeroFace410_fourthDefectPowerRelation`,
weight `14`); substituting the thirteenth-face jet forms and cancelling
`h₀¹³` gives the ground pin at its exact order
(`nonzeroFace410_gammaResidualPowerRelation`):
`polar + h₀ · (regular) = C c_γ h₀`.  Its `h`-adic peel is one step
(`gammaGroundPin_solvePolar410`), and the root evaluation combined
with the `β` pin re-derives the thirteenth-face jet hypothesis `hU`
from the literal source (`gammaGroundPin_rootEval_reDerivesU410`):
`8 w₇₃(a) = p₁(a) (30 t₂(a) - 9 λ)`.

Third, the eliminations: the regular block is linear in `s₂₂` with
cofactor `320 t₂² - 256 a₂₂`, so the global `α` pin eliminates `s₂₂`
exactly (`gammaGroundPin_alphaEliminated410`).  The `β` pin eliminates
the polar letter `q₇₆` from the polar block itself
(`w73GroundPin_betaEliminated410`): `2 γ-pin + 7 t₂ β-pin` collapses to
the `w₇₃` PIN `256 w₇₃ - 960 p₁ t₂ + 288 λ p₁ = h₀ (2 (C c_γ - reg_γ)
+ 7 t₂ (C c_β - reg_β))`; with both `q₇₆` and `s₂₂` eliminated it is
the first global THREE-ground-constant link of the lane
(`w73GroundPin_fullyEliminated410`):
`256 w₇₃ - 960 p₁ t₂ + 288 λ p₁ = h₀ (2 C c_γ + 7 C c_β t₂ +
32 C c_α t₂² + 64 C c_α a₂₂ - 10 t₂⁴ - 15 λ t₂³ + 240 a₂₂ t₂² -
360 λ a₂₂ t₂ + 480 a₂₂² + 640 p₀)`.

Fourth, the combination with the terminal packet: the `w₇₃` pin and
the `β` pin together eliminate BOTH polar letters `q₇₆` and `w₇₃` from
the order-`-3` iota block in factored form
(`iotaFirstPeel_gammaLoaded410`):
`32 p₁ (32 b₄₂ t₂ - 24 b₃₁ - 30 p₁² t₂ - 15 λ p₁²) =
h₀ (128 w₁ + 7 p₁² t₂ (C c_β - reg_β) - 6 p₁² (C c_γ - reg_γ))` —
only the order-`-2` letters `b₄₂, b₃₁` survive on the polar side of
the first `ι` peel step.  (The first `θ` peel carries no `w₇₃`, so `γ`
adds nothing there.)

The sharpest `γ`-loaded residual is one derivative deeper: since
`p₁(a) = q₇₆(a) = 0` on the terminal packet, differentiating the pins
at the root gives
`128 w₇₃'(a) - 224 t₂(a) q₇₆'(a) + 80 t₂(a) p₁'(a) + 144 λ p₁'(a) =
h₀'(a) (c_γ - reg_γ(a))` (`gammaGroundPin_rootDerivativeTie410`) and,
fully eliminated, `256 w₇₃'(a) - 960 t₂(a) p₁'(a) + 288 λ p₁'(a) =
h₀'(a) (2 c_γ + 7 c_β t₂(a) + 32 c_α t₂(a)² + 64 c_α a₂₂(a) -
10 t₂(a)⁴ - 15 λ t₂(a)³ + 240 a₂₂(a) t₂(a)² - 360 λ a₂₂(a) t₂(a) +
480 a₂₂(a)² + 640 p₀(a))`
(`w73Pin_rootDerivativeTie_fullyEliminated410`) — all three ground
constants pinned against the derivative jet through `t₂(a), a₂₂(a),
p₀(a), h₀'(a)` only.

Nothing here closes the face or a branch: `c_γ` is free, so the pin
eliminates no configuration; no root branch is forced (both factors of
the peeled `ι` product already vanish at the root); `t₂(a), a₂₂(a),
q₁(a), q₀(a), c_α, c_β, c_γ, c_θ, c, j, p₀'(a), q₀'(a), w₇₃'(a),
q₇₆'(a), p₁'(a)` remain free or tied-not-determined; the ground
constant `δ` (row `8`, next: its fifth-defect clearing sits at exact
order `-1` with polar block adding the letter `q₅₄`) stays uncleared.
No total-degree or twice-prime theorem is used, and the aligned face
`N = 0` is not touched.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Exact order-`-1` clearing of `γ` on the thirteenth-face jet -/

section GammaGroundClearing410

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- Order-`-1` (polar) numerator block of the cleared `γ` on the
thirteenth-face jet: the residue block of the three order-`-1` letters
`B`, `C`, `R`.  Unlike the `β` polar block it is jet-loaded: `t₂` and
`λ` multiply the residue letters. -/
def gammaGroundPolarNumerator410 (t2 w73 vis a1 : F[X]) (lambda : F) :
    F[X] :=
  (128 : F[X]) * w73 - (224 : F[X]) * t2 * vis +
    (80 : F[X]) * a1 * t2 + (144 : F[X]) * Polynomial.C lambda * a1

/-- Regular (order-`0`) numerator block of the cleared `γ` on the
thirteenth-face jet.  It is linear in `s₂₂` with cofactor
`320 t₂² - 256 a₂₂`, and it is the first ground block seeing the
quartic constant `p₀`. -/
def gammaGroundRegularNumerator410 (t2 a22 s22 a0 : F[X]) (lambda : F) :
    F[X] :=
  -(525 : F[X]) * t2 ^ 4 + (210 : F[X]) * Polynomial.C lambda * t2 ^ 3 +
    (320 : F[X]) * s22 * t2 ^ 2 + (400 : F[X]) * a22 * t2 ^ 2 -
    (360 : F[X]) * Polynomial.C lambda * a22 * t2 -
    (256 : F[X]) * a22 * s22 + (400 : F[X]) * a22 ^ 2 -
    (320 : F[X]) * a0

set_option maxHeartbeats 3200000 in
/-- Exact order-`-1` clearing of the fourth-face residual `γ` on the
thirteenth-face jet substitutions: `128 h γ` is the polar residue block
plus `h` times the regular block, so `γ` sits at exact order `-1`. -/
theorem gammaDefect_eq_cleared410
    (h t2 a22 s22 vis w73 a1 a0 b9 lambda : F) (hh : h ≠ 0)
    (hN : 5 * (h ^ 3 * t2) * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (128 : F) * h *
        gammaResidual410
          (depressedL410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9)
          (depressedA410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22))
          (depressedB410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22) a1)
          (depressedC410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22) a1 a0)
          (depressedP410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22))
          (depressedR410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73)) =
      ((128 : F) * w73 - (224 : F) * t2 * vis + (80 : F) * a1 * t2 +
          (144 : F) * lambda * a1) +
        h * (-(525 : F) * t2 ^ 4 + (210 : F) * lambda * t2 ^ 3 +
          (320 : F) * s22 * t2 ^ 2 + (400 : F) * a22 * t2 ^ 2 -
          (360 : F) * lambda * a22 * t2 - (256 : F) * a22 * s22 +
          (400 : F) * a22 ^ 2 - (320 : F) * a0) := by
  have hL :
      depressedL410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9 =
        -lambda / 2 :=
    depressedL410_eq_of_ninthPower h (h ^ 3 * t2) b9 lambda hh hN
  have hA :
      depressedA410 h (quarticDepressionR410 h (h ^ 3 * t2))
          (h ^ 3 * t2) (h ^ 2 * a22) =
        (8 * a22 - 3 * t2 ^ 2) / 8 := by
    rw [depressedA410_eq_cleared h (h ^ 3 * t2) (h ^ 2 * a22) hh]
    field_simp [hh]
  have hB :
      depressedB410 h (quarticDepressionR410 h (h ^ 3 * t2))
          (h ^ 3 * t2) (h ^ 2 * a22) a1 =
        (8 * a1 - 4 * a22 * h * t2 + h * t2 ^ 3) / (8 * h) := by
    rw [depressedB410_eq_cleared h (h ^ 3 * t2) (h ^ 2 * a22) a1 hh]
    field_simp [hh]
    ring
  have hC :
      depressedC410 h (quarticDepressionR410 h (h ^ 3 * t2))
          (h ^ 3 * t2) (h ^ 2 * a22) a1 a0 =
        (256 * a0 * h - 64 * a1 * t2 + 16 * a22 * t2 ^ 2 * h -
            3 * t2 ^ 4 * h) / (256 * h) := by
    rw [depressedC410_eq_cleared h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0 hh]
    field_simp [hh]
  have hP :
      depressedP410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) =
        (16 * s22 - 45 * t2 ^ 2 + 18 * lambda * t2) / 16 := by
    rw [depressedP410_eq_cleared_ninthPower h (h ^ 3 * t2) b9
      (h ^ 8 * s22) lambda hh hN]
    field_simp [hh]
  have hR :
      depressedR410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) =
        (-(315 : F) * t2 ^ 4 * h + 84 * lambda * t2 ^ 3 * h +
            224 * t2 ^ 2 * s22 * h - 224 * t2 * vis + 128 * w73) /
          (128 * h) := by
    rw [depressedR410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) lambda hh hN]
    field_simp [hh]
  simp only [gammaResidual410, hL, hA, hB, hC, hP, hR]
  field_simp [hh]
  ring

/-- The `γ` ground pin solves the order-`-1` polar block exactly: the
residue block is `h₀` times the explicit ground-loaded cofactor — a
factored `h`-adic quotient identity. -/
theorem gammaGroundPin_solvePolar410
    (h0 t2 a22 s22 vis w73 a1 a0 : F[X]) (lambda cgamma : F)
    (hpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0) :
    gammaGroundPolarNumerator410 t2 w73 vis a1 lambda =
      h0 * (Polynomial.C cgamma -
        gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda) := by
  linear_combination hpin

/-- Root evaluation of the `γ` ground pin: the polar residue block
vanishes at the root of `h₀`. -/
theorem gammaGroundPin_rootEval410
    (h0 t2 a22 s22 vis w73 a1 a0 : F[X]) (lambda cgamma : F) (a : F)
    (hpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0)
    (hroot : h0.eval a = 0) :
    (128 : F) * w73.eval a - (224 : F) * t2.eval a * vis.eval a +
        (80 : F) * a1.eval a * t2.eval a +
        (144 : F) * lambda * a1.eval a = 0 := by
  have h := congrArg (fun r : F[X] => r.eval a) hpin
  simp only [gammaGroundPolarNumerator410, eval_add, eval_sub, eval_mul,
    eval_C, eval_ofNat, hroot, zero_mul, mul_zero, add_zero] at h
  linear_combination h

/-- Root evaluation of the `γ` ground pin combined with the `β` ground
pin: the thirteenth-face tie `8 w₇₃(a) = p₁(a) (30 t₂(a) - 9 λ)` (the
jet hypothesis `hU`) is forced by the literal source through the
row-`10` and row-`9` integrals alone. -/
theorem gammaGroundPin_rootEval_reDerivesU410
    (h0 t2 a22 s22 vis w73 a1 a0 : F[X]) (lambda cbeta cgamma : F)
    (a : F)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0)
    (hroot : h0.eval a = 0) :
    (8 : F) * w73.eval a =
      a1.eval a * ((30 : F) * t2.eval a - (9 : F) * lambda) := by
  have hbe := betaGroundPin_rootEval410 h0 t2 a22 s22 vis a1 lambda
    cbeta a hbpin hroot
  have hge := gammaGroundPin_rootEval410 h0 t2 a22 s22 vis w73 a1 a0
    lambda cgamma a hgpin hroot
  linear_combination (1 / 16 : F) * hge + (7 / 32 : F) * t2.eval a * hbe

/-- Factored elimination of `s₂₂` from the solved polar cofactor by
the global `α` pin: `γ`'s regular block is linear in `s₂₂` with
cofactor `320 t₂² - 256 a₂₂`. -/
theorem gammaGroundPin_alphaEliminated410
    (h0 t2 a22 s22 vis w73 a1 a0 : F[X]) (lambda calpha cgamma : F)
    (halpha : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0) :
    gammaGroundPolarNumerator410 t2 w73 vis a1 lambda =
      h0 * (Polynomial.C cgamma - (75 : F[X]) * t2 ^ 4 +
        (150 : F[X]) * Polynomial.C lambda * t2 ^ 3 -
        (720 : F[X]) * a22 * t2 ^ 2 +
        (72 : F[X]) * Polynomial.C lambda * a22 * t2 +
        (240 : F[X]) * a22 ^ 2 + (320 : F[X]) * a0 -
        (40 : F[X]) * Polynomial.C calpha * t2 ^ 2 +
        (32 : F[X]) * Polynomial.C calpha * a22) := by
  have ha := halpha
  simp only [alphaGroundNumerator410] at ha
  have hg := hgpin
  simp only [gammaGroundPolarNumerator410,
    gammaGroundRegularNumerator410] at hg
  simp only [gammaGroundPolarNumerator410]
  linear_combination hg -
    ((40 : F[X]) * t2 ^ 2 - (32 : F[X]) * a22) * h0 * ha

/-- The `w₇₃` pin: the `β` ground pin eliminates the polar letter
`q₇₆` from the `γ` polar block itself — `2 γ-pin + 7 t₂ β-pin`
collapses to a pin of `w₇₃` alone against the regular blocks, in
factored `h`-adic quotient form. -/
theorem w73GroundPin_betaEliminated410
    (h0 t2 a22 s22 vis w73 a1 a0 : F[X]) (lambda cbeta cgamma : F)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0) :
    (256 : F[X]) * w73 - (960 : F[X]) * a1 * t2 +
        (288 : F[X]) * Polynomial.C lambda * a1 =
      h0 * ((2 : F[X]) * (Polynomial.C cgamma -
          gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda) +
        (7 : F[X]) * t2 * (Polynomial.C cbeta -
          betaGroundRegularNumerator410 t2 a22 s22 lambda)) := by
  have hb := betaGroundPin_solvePolar410 h0 t2 a22 s22 vis a1 lambda
    cbeta hbpin
  have hg := gammaGroundPin_solvePolar410 h0 t2 a22 s22 vis w73 a1 a0
    lambda cgamma hgpin
  simp only [betaGroundPolarNumerator410] at hb
  simp only [gammaGroundPolarNumerator410] at hg
  linear_combination (2 : F[X]) * hg + (7 : F[X]) * t2 * hb

/-- The fully eliminated `w₇₃` pin: with `q₇₆` eliminated by the `β`
pin and `s₂₂` eliminated by the `α` pin, `w₇₃` is pinned against
`t₂, a₂₂, p₀, c_α, c_β, c_γ` only — the first global
three-ground-constant link of the lane. -/
theorem w73GroundPin_fullyEliminated410
    (h0 t2 a22 s22 vis w73 a1 a0 : F[X])
    (lambda calpha cbeta cgamma : F)
    (halpha : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0) :
    (256 : F[X]) * w73 - (960 : F[X]) * a1 * t2 +
        (288 : F[X]) * Polynomial.C lambda * a1 =
      h0 * ((2 : F[X]) * Polynomial.C cgamma +
        (7 : F[X]) * Polynomial.C cbeta * t2 +
        (32 : F[X]) * Polynomial.C calpha * t2 ^ 2 +
        (64 : F[X]) * Polynomial.C calpha * a22 -
        (10 : F[X]) * t2 ^ 4 -
        (15 : F[X]) * Polynomial.C lambda * t2 ^ 3 +
        (240 : F[X]) * a22 * t2 ^ 2 -
        (360 : F[X]) * Polynomial.C lambda * a22 * t2 +
        (480 : F[X]) * a22 ^ 2 + (640 : F[X]) * a0) := by
  have hb := betaGroundPin_alphaEliminated410 h0 t2 a22 s22 vis a1
    lambda calpha cbeta halpha hbpin
  have hg := gammaGroundPin_alphaEliminated410 h0 t2 a22 s22 vis w73
    a1 a0 lambda calpha cgamma halpha hgpin
  simp only [betaGroundPolarNumerator410] at hb
  simp only [gammaGroundPolarNumerator410] at hg
  linear_combination (2 : F[X]) * hg + (7 : F[X]) * t2 * hb

/-- `γ`-loaded first `ι` peel: the `β` and `γ` ground pins eliminate
BOTH polar letters `q₇₆` and `w₇₃` from the order-`-3` iota block in
factored form — only the order-`-2` letters `b₄₂, b₃₁` survive on the
polar side of the first peel step. -/
theorem iotaFirstPeel_gammaLoaded410
    (h0 t2 a22 s22 vis w73 a1 a0 b42 b31 w1 : F[X])
    (lambda cbeta cgamma : F)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0)
    (hpeel : iotaPolarThreeNumerator410 t2 vis w73 a1 b42 b31 lambda =
      h0 * w1) :
    (32 : F[X]) * a1 *
        ((32 : F[X]) * b42 * t2 - (24 : F[X]) * b31 -
          (30 : F[X]) * a1 ^ 2 * t2 -
          (15 : F[X]) * Polynomial.C lambda * a1 ^ 2) =
      h0 * ((128 : F[X]) * w1 +
        (7 : F[X]) * a1 ^ 2 * t2 *
          (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda) -
        (6 : F[X]) * a1 ^ 2 *
          (Polynomial.C cgamma -
            gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda)) := by
  have hb := hbpin
  simp only [betaGroundPolarNumerator410] at hb
  have hg := hgpin
  simp only [gammaGroundPolarNumerator410] at hg
  have hi := hpeel
  simp only [iotaPolarThreeNumerator410] at hi
  linear_combination (128 : F[X]) * hi - (6 : F[X]) * a1 ^ 2 * hg +
    (7 : F[X]) * a1 ^ 2 * t2 * hb

/-- Root derivative of the solved `γ` polar form: since the polar
block is `h₀` times a cofactor, `h₀(a) = 0`, and the residue letters
`q₇₆, p₁` vanish at the root, the derivative combination at the root
sees exactly `h₀'(a)` times the cofactor value. -/
theorem gammaPolar_rootDerivative_of_solved410
    (h0 t2 vis w73 a1 u : F[X]) (lambda : F) (a : F)
    (hsolve : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda =
      h0 * u)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (ha1 : a1.eval a = 0) :
    (128 : F) * (derivative w73).eval a -
        (224 : F) * t2.eval a * (derivative vis).eval a +
        (80 : F) * t2.eval a * (derivative a1).eval a +
        (144 : F) * lambda * (derivative a1).eval a =
      (derivative h0).eval a * u.eval a := by
  have hder := congrArg (fun r : F[X] => derivative r) hsolve
  simp only [gammaGroundPolarNumerator410, derivative_add,
    derivative_sub, derivative_mul, derivative_ofNat, derivative_C,
    zero_mul, mul_zero, zero_add, add_zero] at hder
  have heval := congrArg (fun r : F[X] => r.eval a) hder
  simp only [eval_add, eval_sub, eval_mul, eval_ofNat, eval_C, hroot,
    hvis, ha1, zero_mul, mul_zero, add_zero, zero_add] at heval
  linear_combination heval

/-- Root derivative tie of the `γ` ground pin: the derivative-level
residual pinning the `γ` polar derivative block against `c_γ` and the
root jet. -/
theorem gammaGroundPin_rootDerivativeTie410
    (h0 t2 a22 s22 vis w73 a1 a0 : F[X]) (lambda cgamma : F) (a : F)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (ha1 : a1.eval a = 0) :
    (128 : F) * (derivative w73).eval a -
        (224 : F) * t2.eval a * (derivative vis).eval a +
        (80 : F) * t2.eval a * (derivative a1).eval a +
        (144 : F) * lambda * (derivative a1).eval a =
      (derivative h0).eval a *
        (cgamma -
          (gammaGroundRegularNumerator410 t2 a22 s22 a0
              lambda).eval a) := by
  have hsolve := gammaGroundPin_solvePolar410 h0 t2 a22 s22 vis w73 a1
    a0 lambda cgamma hgpin
  have h := gammaPolar_rootDerivative_of_solved410 h0 t2 vis w73 a1
    (Polynomial.C cgamma -
      gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda) lambda a
    hsolve hroot hvis ha1
  simpa only [eval_sub, eval_C] using h

/-- Root derivative of any solved `w₇₃` pin form: since the pin block
is `h₀` times a cofactor, `h₀(a) = 0`, and `p₁(a) = 0`, the derivative
combination at the root sees exactly `h₀'(a)` times the cofactor. -/
theorem w73Pin_rootDerivative_of_solved410
    (h0 t2 w73 a1 u : F[X]) (lambda : F) (a : F)
    (hsolve : (256 : F[X]) * w73 - (960 : F[X]) * a1 * t2 +
        (288 : F[X]) * Polynomial.C lambda * a1 =
      h0 * u)
    (hroot : h0.eval a = 0) (ha1 : a1.eval a = 0) :
    (256 : F) * (derivative w73).eval a -
        (960 : F) * t2.eval a * (derivative a1).eval a +
        (288 : F) * lambda * (derivative a1).eval a =
      (derivative h0).eval a * u.eval a := by
  have hder := congrArg (fun r : F[X] => derivative r) hsolve
  simp only [derivative_add, derivative_sub, derivative_mul,
    derivative_ofNat, derivative_C, zero_mul, mul_zero, zero_add,
    add_zero] at hder
  have heval := congrArg (fun r : F[X] => r.eval a) hder
  simp only [eval_add, eval_sub, eval_mul, eval_ofNat, eval_C, hroot,
    ha1, zero_mul, mul_zero, add_zero] at heval
  linear_combination heval

/-- Sharpest `γ`-loaded residual: the root derivative tie of the fully
eliminated `w₇₃` pin — all three ground constants pinned against the
derivative jet through `t₂(a), a₂₂(a), p₀(a), h₀'(a)` only. -/
theorem w73Pin_rootDerivativeTie_fullyEliminated410
    (h0 t2 a22 s22 vis w73 a1 a0 : F[X])
    (lambda calpha cbeta cgamma : F) (a : F)
    (halpha : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0)
    (hroot : h0.eval a = 0) (ha1 : a1.eval a = 0) :
    (256 : F) * (derivative w73).eval a -
        (960 : F) * t2.eval a * (derivative a1).eval a +
        (288 : F) * lambda * (derivative a1).eval a =
      (derivative h0).eval a *
        ((2 : F) * cgamma + (7 : F) * cbeta * t2.eval a +
          (32 : F) * calpha * (t2.eval a) ^ 2 +
          (64 : F) * calpha * a22.eval a -
          (10 : F) * (t2.eval a) ^ 4 -
          (15 : F) * lambda * (t2.eval a) ^ 3 +
          (240 : F) * a22.eval a * (t2.eval a) ^ 2 -
          (360 : F) * lambda * a22.eval a * t2.eval a +
          (480 : F) * (a22.eval a) ^ 2 +
          (640 : F) * a0.eval a) := by
  have hsolve := w73GroundPin_fullyEliminated410 h0 t2 a22 s22 vis w73
    a1 a0 lambda calpha cbeta cgamma halpha hbpin hgpin
  have h := w73Pin_rootDerivative_of_solved410 h0 t2 w73 a1
    ((2 : F[X]) * Polynomial.C cgamma +
      (7 : F[X]) * Polynomial.C cbeta * t2 +
      (32 : F[X]) * Polynomial.C calpha * t2 ^ 2 +
      (64 : F[X]) * Polynomial.C calpha * a22 -
      (10 : F[X]) * t2 ^ 4 -
      (15 : F[X]) * Polynomial.C lambda * t2 ^ 3 +
      (240 : F[X]) * a22 * t2 ^ 2 -
      (360 : F[X]) * Polynomial.C lambda * a22 * t2 +
      (480 : F[X]) * a22 ^ 2 + (640 : F[X]) * a0) lambda a hsolve
    hroot ha1
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat,
    eval_C] at h
  linear_combination h

end GammaGroundClearing410

/-! ## Source-facing ground power relation at exact order `-1` -/

section NonzeroGammaGroundBridge410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-- The row-`9` ground first integral `γ` on a square-core ninth-power
source, traced from the literal Keller row through the fourth-face
power relation and expressed at its exact order `-1` on the
thirteenth-face jet: the polar residue block plus `h₀` times the
regular block is GLOBALLY `C c_γ h₀`. -/
theorem nonzeroFace410_gammaResidualPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 vis w73 : k[X])
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
    (hq6 : q.coeff 6 = h0 ^ 5 * w73) :
    ∃ cgamma : k,
      gammaGroundPolarNumerator410 t2 w73 vis (p.coeff 1) lambda +
        h0 * gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
          lambda =
      Polynomial.C cgamma * h0 := by
  obtain ⟨cgamma, hpow⟩ :=
    nonzeroFace410_fourthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  refine ⟨cgamma, ?_⟩
  have h13 : h0 ^ 13 ≠ 0 := pow_ne_zero 13 hh0
  apply mul_left_cancel₀ h13
  calc
    h0 ^ 13 *
          (gammaGroundPolarNumerator410 t2 w73 vis (p.coeff 1) lambda +
            h0 * gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
              lambda) =
        localClearedFourthDefect410 h0 (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          lambda := by
      simp only [localClearedFourthDefect410,
        gammaGroundPolarNumerator410, gammaGroundRegularNumerator410,
        hp3, hp2, hq8, hq7, hq6]
      ring
    _ = Polynomial.C cgamma * h0 ^ 14 := hpow
    _ = h0 ^ 13 * (Polynomial.C cgamma * h0) := by ring

/-! ## Gamma ground bridge packet -/

set_option maxHeartbeats 6400000 in
/-- Sharpest exact successor packet of the `γ` ground bridge on the
nonzero `(4,10)` face: everything from the beta ground bridge packet,
together with the row-`9` ground pin at its exact order `-1`, its
one-step `h`-adic peel, the `α`-eliminated solved cofactor, the `w₇₃`
pin (the `β` pin eliminating the polar letter `q₇₆` from the `γ` polar
block), the fully eliminated `w₇₃` pin — the first global
three-ground-constant link of the lane — the `γ`-loaded factored form
of the first `ι` peel step (both polar letters `q₇₆, w₇₃` eliminated),
and the two root derivative ties — the sharpest `γ`-loaded residuals,
pinning `w₇₃'(a)` against `c_γ` (and `c_α, c_β`) through `t₂(a),
a₂₂(a), p₀(a), h₀'(a)` only.  Nothing here closes the face or a
branch: `c_α, c_β, c_γ` are free, so the pins eliminate no
configuration; no root branch is forced; `t₂(a), a₂₂(a), q₁(a),
q₀(a), c_α, c_β, c_γ, c_θ, c, j, p₀'(a), q₀'(a)` remain free or
tied-not-determined, and the ground constant `δ` stays uncleared. -/
theorem nonzeroFace410_gammaGroundBridgePacket
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
          (540 : k) * (t2.eval a) ^ 2)) :
    ∃ (calpha cbeta cgamma ctheta c : k) (v1 v2 v3 w1 w2 w3 : k[X]),
      alphaGroundNumerator410 t2 a22 s22 lambda =
        Polynomial.C calpha ∧
      (8 : k[X]) * s22 =
        Polynomial.C calpha + (20 : k[X]) * a22 +
          (15 : k[X]) * t2 ^ 2 -
          (9 : k[X]) * Polynomial.C lambda * t2 ∧
      localClearedThetaResidual410 h0 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
          lambda =
        Polynomial.C ctheta * h0 ^ 3 ∧
      thetaPolarThreeNumerator410 vis (p.coeff 1) b42 = h0 * v1 ∧
      v1 + thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) b42 b31 (q.coeff 2) lambda =
        h0 * v2 ∧
      v2 + thetaPolarOneNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) (q.coeff 1) lambda =
        h0 * v3 ∧
      v3 + thetaRegularNumerator410 t2 a22 s22 (p.coeff 0) lambda =
        Polynomial.C ctheta ∧
      localClearedIotaResidual410 h0 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
          (q.coeff 0) lambda =
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
      (8 : k[X]) * v3 +
          (8 : k[X]) *
            thetaRegularNumerator410 t2 a22 0 (p.coeff 0) lambda +
          (Polynomial.C calpha + (20 : k[X]) * a22 +
              (15 : k[X]) * t2 ^ 2 -
              (9 : k[X]) * Polynomial.C lambda * t2) *
            thetaRegularSTwoCofactor410 t2 a22 (p.coeff 0) =
        (8 : k[X]) * Polynomial.C ctheta ∧
      (8 : k[X]) * w3 +
          (8 : k[X]) *
            iotaRegularNumerator410 t2 a22 0 (p.coeff 0) (q.coeff 0)
              lambda +
          (Polynomial.C calpha + (20 : k[X]) * a22 +
              (15 : k[X]) * t2 ^ 2 -
              (9 : k[X]) * Polynomial.C lambda * t2) *
            iotaRegularSTwoCofactor410 t2 a22 (p.coeff 0) =
        (8 : k[X]) * Polynomial.C c ∧
      (p.coeff 1).eval a = 0 ∧
      vis.eval a = 0 ∧
      w73.eval a = 0 ∧
      q54.eval a = 0 ∧
      b42.eval a = 0 ∧
      b31.eval a = 0 ∧
      (q.coeff 2).eval a = 0 ∧
      v1.eval a = 0 ∧
      w1.eval a = 0 ∧
      v2.eval a + (16777216 : k) * (q.coeff 1).eval a = 0 ∧
      w2.eval a = (2 : k) * (q.coeff 1).eval a * t2.eval a ∧
      (8 : k) * s22.eval a =
        calpha + (20 : k) * a22.eval a + (15 : k) * (t2.eval a) ^ 2 -
          (9 : k) * lambda * t2.eval a ∧
      (8 : k) * v3.eval a +
          (8 : k) *
            (thetaRegularNumerator410 t2 a22 0 (p.coeff 0)
                lambda).eval a +
          (calpha + (20 : k) * a22.eval a +
              (15 : k) * (t2.eval a) ^ 2 -
              (9 : k) * lambda * t2.eval a) *
            (thetaRegularSTwoCofactor410 t2 a22 (p.coeff 0)).eval a =
        (8 : k) * ctheta ∧
      (8 : k) * w3.eval a +
          (8 : k) *
            (iotaRegularNumerator410 t2 a22 0 (p.coeff 0) (q.coeff 0)
                lambda).eval a +
          (calpha + (20 : k) * a22.eval a +
              (15 : k) * (t2.eval a) ^ 2 -
              (9 : k) * lambda * t2.eval a) *
            (iotaRegularSTwoCofactor410 t2 a22 (p.coeff 0)).eval a =
        (8 : k) * c ∧
      ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a = j ∧
      ((p.coeff 0).derivative).eval a * v2.eval a +
          (16777216 : k) * j =
        0 ∧
      (lambda + (4 : k) * t2.eval a = 0 →
        (2 : k) * w2.eval a + lambda * (q.coeff 1).eval a = 0 ∧
          (33554432 : k) * w2.eval a = lambda * v2.eval a ∧
          (2 : k) * ((p.coeff 0).derivative).eval a * w2.eval a +
              lambda * j =
            0) ∧
      betaGroundPolarNumerator410 vis (p.coeff 1) +
          h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0 ∧
      betaGroundPolarNumerator410 vis (p.coeff 1) =
        h0 * (Polynomial.C cbeta -
          betaGroundRegularNumerator410 t2 a22 s22 lambda) ∧
      betaGroundPolarNumerator410 vis (p.coeff 1) =
        h0 * (Polynomial.C cbeta + (20 : k[X]) * t2 ^ 3 -
          (45 : k[X]) * Polynomial.C lambda * t2 ^ 2 +
          (240 : k[X]) * a22 * t2 -
          (72 : k[X]) * Polynomial.C lambda * a22 +
          (16 : k[X]) * Polynomial.C calpha * t2) ∧
      (67108864 : k[X]) * p.coeff 1 *
          ((25 : k[X]) * (p.coeff 1) ^ 2 - (16 : k[X]) * b42) =
        h0 * ((64 : k[X]) * v1 -
          (18350080 : k[X]) * (p.coeff 1) ^ 2 *
            (Polynomial.C cbeta -
              betaGroundRegularNumerator410 t2 a22 s22 lambda)) ∧
      (64 : k[X]) * p.coeff 1 *
          ((3 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 -
            (30 : k[X]) * (p.coeff 1) ^ 2 * t2 +
            (6 : k[X]) * p.coeff 1 * w73 +
            (8 : k[X]) * b42 * t2 - (6 : k[X]) * b31) =
        h0 * ((64 : k[X]) * w1 +
          (14 : k[X]) * (p.coeff 1) ^ 2 * t2 *
            (Polynomial.C cbeta -
              betaGroundRegularNumerator410 t2 a22 s22 lambda)) ∧
      (64 : k) * (derivative vis).eval a -
          (160 : k) * (derivative (p.coeff 1)).eval a =
        (derivative h0).eval a *
          (cbeta -
            (betaGroundRegularNumerator410 t2 a22 s22
                lambda).eval a) ∧
      (64 : k) * (derivative vis).eval a -
          (160 : k) * (derivative (p.coeff 1)).eval a =
        (derivative h0).eval a *
          (cbeta + (20 : k) * (t2.eval a) ^ 3 -
            (45 : k) * lambda * (t2.eval a) ^ 2 +
            (240 : k) * a22.eval a * t2.eval a -
            (72 : k) * lambda * a22.eval a +
            (16 : k) * calpha * t2.eval a) ∧
      gammaGroundPolarNumerator410 t2 w73 vis (p.coeff 1) lambda +
          h0 * gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
            lambda =
        Polynomial.C cgamma * h0 ∧
      gammaGroundPolarNumerator410 t2 w73 vis (p.coeff 1) lambda =
        h0 * (Polynomial.C cgamma -
          gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
            lambda) ∧
      gammaGroundPolarNumerator410 t2 w73 vis (p.coeff 1) lambda =
        h0 * (Polynomial.C cgamma - (75 : k[X]) * t2 ^ 4 +
          (150 : k[X]) * Polynomial.C lambda * t2 ^ 3 -
          (720 : k[X]) * a22 * t2 ^ 2 +
          (72 : k[X]) * Polynomial.C lambda * a22 * t2 +
          (240 : k[X]) * a22 ^ 2 + (320 : k[X]) * p.coeff 0 -
          (40 : k[X]) * Polynomial.C calpha * t2 ^ 2 +
          (32 : k[X]) * Polynomial.C calpha * a22) ∧
      (256 : k[X]) * w73 - (960 : k[X]) * p.coeff 1 * t2 +
          (288 : k[X]) * Polynomial.C lambda * p.coeff 1 =
        h0 * ((2 : k[X]) * (Polynomial.C cgamma -
            gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
              lambda) +
          (7 : k[X]) * t2 * (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda)) ∧
      (256 : k[X]) * w73 - (960 : k[X]) * p.coeff 1 * t2 +
          (288 : k[X]) * Polynomial.C lambda * p.coeff 1 =
        h0 * ((2 : k[X]) * Polynomial.C cgamma +
          (7 : k[X]) * Polynomial.C cbeta * t2 +
          (32 : k[X]) * Polynomial.C calpha * t2 ^ 2 +
          (64 : k[X]) * Polynomial.C calpha * a22 -
          (10 : k[X]) * t2 ^ 4 -
          (15 : k[X]) * Polynomial.C lambda * t2 ^ 3 +
          (240 : k[X]) * a22 * t2 ^ 2 -
          (360 : k[X]) * Polynomial.C lambda * a22 * t2 +
          (480 : k[X]) * a22 ^ 2 + (640 : k[X]) * p.coeff 0) ∧
      (32 : k[X]) * p.coeff 1 *
          ((32 : k[X]) * b42 * t2 - (24 : k[X]) * b31 -
            (30 : k[X]) * (p.coeff 1) ^ 2 * t2 -
            (15 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2) =
        h0 * ((128 : k[X]) * w1 +
          (7 : k[X]) * (p.coeff 1) ^ 2 * t2 *
            (Polynomial.C cbeta -
              betaGroundRegularNumerator410 t2 a22 s22 lambda) -
          (6 : k[X]) * (p.coeff 1) ^ 2 *
            (Polynomial.C cgamma -
              gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda)) ∧
      (128 : k) * (derivative w73).eval a -
          (224 : k) * t2.eval a * (derivative vis).eval a +
          (80 : k) * t2.eval a * (derivative (p.coeff 1)).eval a +
          (144 : k) * lambda * (derivative (p.coeff 1)).eval a =
        (derivative h0).eval a *
          (cgamma -
            (gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda).eval a) ∧
      (256 : k) * (derivative w73).eval a -
          (960 : k) * t2.eval a * (derivative (p.coeff 1)).eval a +
          (288 : k) * lambda * (derivative (p.coeff 1)).eval a =
        (derivative h0).eval a *
          ((2 : k) * cgamma + (7 : k) * cbeta * t2.eval a +
            (32 : k) * calpha * (t2.eval a) ^ 2 +
            (64 : k) * calpha * a22.eval a -
            (10 : k) * (t2.eval a) ^ 4 -
            (15 : k) * lambda * (t2.eval a) ^ 3 +
            (240 : k) * a22.eval a * (t2.eval a) ^ 2 -
            (360 : k) * lambda * a22.eval a * t2.eval a +
            (480 : k) * (a22.eval a) ^ 2 +
            (640 : k) * (p.coeff 0).eval a) := by
  obtain ⟨calpha, cbeta, ctheta, c, v1, v2, v3, w1, w2, w3, hpin,
    hsolve, hpowT, htw1, htw2, htw3, htwc, hpowI, hiw1, hiw2, hiw3,
    hiwc, hTglobal, hIglobal, ha1, hvis0, hw730, hq540, hb420, hb310,
    hb20, hv10, hw10, hv2tie, hw2tie, hrootS, hTroot, hIroot, hkelP,
    hcombo, hbr, hbpin, hbsolve, hbalpha, hbtheta, hbiota, hbderiv,
    hbderivA⟩ :=
    nonzeroFace410_betaGroundBridgePacket p q H h0 j lambda t2
      a22 s22 vis w73 q54 b42 b31 a hp hq hh0 hH hp4 hq10 hN hD hp3
      hp2 hq8 hq7 hq6 hq5 hq4 hq3 hroot hT hU hW hV hX hY
  obtain ⟨cgamma, hgpin⟩ := nonzeroFace410_gammaResidualPowerRelation
    p q H h0 j lambda t2 a22 s22 vis w73 hp hq hh0 hH hp4 hq10 hN hD
    hp3 hp2 hq8 hq7 hq6
  have hgsolve := gammaGroundPin_solvePolar410 h0 t2 a22 s22 vis w73
    (p.coeff 1) (p.coeff 0) lambda cgamma hgpin
  have hgalpha := gammaGroundPin_alphaEliminated410 h0 t2 a22 s22 vis
    w73 (p.coeff 1) (p.coeff 0) lambda calpha cgamma hpin hgpin
  have hw73B := w73GroundPin_betaEliminated410 h0 t2 a22 s22 vis w73
    (p.coeff 1) (p.coeff 0) lambda cbeta cgamma hbpin hgpin
  have hw73F := w73GroundPin_fullyEliminated410 h0 t2 a22 s22 vis w73
    (p.coeff 1) (p.coeff 0) lambda calpha cbeta cgamma hpin hbpin
    hgpin
  have hgiota := iotaFirstPeel_gammaLoaded410 h0 t2 a22 s22 vis w73
    (p.coeff 1) (p.coeff 0) b42 b31 w1 lambda cbeta cgamma hbpin hgpin
    hiw1
  have hgderiv := gammaGroundPin_rootDerivativeTie410 h0 t2 a22 s22
    vis w73 (p.coeff 1) (p.coeff 0) lambda cgamma a hgpin hroot hvis0
    ha1
  have hw73deriv := w73Pin_rootDerivativeTie_fullyEliminated410 h0 t2
    a22 s22 vis w73 (p.coeff 1) (p.coeff 0) lambda calpha cbeta cgamma
    a hpin hbpin hgpin hroot ha1
  exact ⟨calpha, cbeta, cgamma, ctheta, c, v1, v2, v3, w1, w2, w3,
    hpin, hsolve, hpowT, htw1, htw2, htw3, htwc, hpowI, hiw1, hiw2,
    hiw3, hiwc, hTglobal, hIglobal, ha1, hvis0, hw730, hq540, hb420,
    hb310, hb20, hv10, hw10, hv2tie, hw2tie, hrootS, hTroot, hIroot,
    hkelP, hcombo, hbr, hbpin, hbsolve, hbalpha, hbtheta, hbiota,
    hbderiv, hbderivA, hgpin, hgsolve, hgalpha, hw73B, hw73F, hgiota,
    hgderiv, hw73deriv⟩

end NonzeroGammaGroundBridge410

#print axioms gammaDefect_eq_cleared410
#print axioms gammaGroundPin_solvePolar410
#print axioms gammaGroundPin_rootEval410
#print axioms gammaGroundPin_rootEval_reDerivesU410
#print axioms gammaGroundPin_alphaEliminated410
#print axioms w73GroundPin_betaEliminated410
#print axioms w73GroundPin_fullyEliminated410
#print axioms iotaFirstPeel_gammaLoaded410
#print axioms gammaPolar_rootDerivative_of_solved410
#print axioms gammaGroundPin_rootDerivativeTie410
#print axioms w73Pin_rootDerivative_of_solved410
#print axioms w73Pin_rootDerivativeTie_fullyEliminated410
#print axioms nonzeroFace410_gammaResidualPowerRelation
#print axioms nonzeroFace410_gammaGroundBridgePacket

end Max11DegreeRoutes
