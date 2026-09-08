import Fable410ScaleTwoGroundConstantsBridgeScratch

/-! # Beta ground bridge for the normalized `(4,10)` nonzero source

The ground constants bridge pinned the row-`11` ground first integral
`α` at weight zero and eliminated `s₂₂` from the terminal cofactor
ties.  The next ground first integral is `β = Q - (5/2) B - (9/4) L A`
(row `10`, `betaResidual410`, third face).  On the thirteenth-face jet
its two moving letters both sit at EXACT order `-1`:
`B = (8 p₁ - 4 a₂₂ h t₂ + h t₂³)/(8h)` and
`Q = (-9 h λ t₂² - 16 h s₂₂ t₂ + 30 h t₂³ + 8 q₇₆)/(8h)`, so the
cleared defect has weight one — the unique next-lowest ground clearing
(`γ, δ` also sit at order `-1` but with deeper polar letters).

First, the clearing (`betaDefect_eq_cleared410`): `64 h β` splits as
the polar residue block `64 q₇₆ - 160 p₁` plus `h` times the regular
block `220 t₂³ - 99 λ t₂² - 128 s₂₂ t₂ + 80 a₂₂ t₂ + 72 λ a₂₂`.

Second, the literal-source trace: the third-face power relation
already pins the row-`10` integral globally against the raw source
coefficients (`nonzeroFace410_thirdDefectPowerRelation`, weight `11`);
substituting the thirteenth-face jet forms and cancelling `h₀¹⁰` gives
the ground pin at its exact order
(`nonzeroFace410_betaResidualPowerRelation`):
`(64 q₇₆ - 160 p₁) + h₀ · (regular) = C c_β h₀`.  Its `h`-adic peel is
one step: the polar block is EXACTLY `h₀` times the solved cofactor
`C c_β - regular` (`betaGroundPin_solvePolar410`) — in particular the
thirteenth-face tie `64 q₇₆(a) = 160 p₁(a)` (the jet hypothesis `hT`)
is re-derived from the literal source (`betaGroundPin_rootEval410`).

Third, the combinations: the regular block is linear in `s₂₂` with
cofactor `-128 t₂`, so the global `α` pin eliminates `s₂₂` exactly
(`betaGroundPin_alphaEliminated410`):
`64 q₇₆ - 160 p₁ = h₀ (C c_β + 20 t₂³ - 45 λ t₂² + 240 a₂₂ t₂ -
72 λ a₂₂ + 16 C c_α t₂)` — the first global two-ground-constant link
of the lane.  The pin then eliminates the polar letter `q₇₆` from the
order-`-3` theta and iota blocks of the terminal packet in factored
form, turning both first peel steps into `β`-loaded `h`-adic quotient
identities (`thetaFirstPeel_betaLoaded410`,
`iotaFirstPeel_betaLoaded410`):
`2²⁶ p₁ (25 p₁² - 16 b₄₂) = h₀ (64 v₁ - 18350080 p₁² (C c_β - reg))`
and `64 p₁ (3 λ p₁² - 30 p₁² t₂ + 6 p₁ w₇₃ + 8 b₄₂ t₂ - 6 b₃₁) =
h₀ (64 w₁ + 14 p₁² t₂ (C c_β - reg))`.

The sharpest `β`-loaded residual is one derivative deeper: since the
polar block is `h₀` times the solved cofactor and every residue letter
vanishes at the root, differentiating and evaluating at the root gives
`64 q₇₆'(a) - 160 p₁'(a) = h₀'(a) (c_β + 20 t₂(a)³ - 45 λ t₂(a)² +
240 a₂₂(a) t₂(a) - 72 λ a₂₂(a) + 16 c_α t₂(a))`
(`betaGroundPin_rootDerivativeTie_alphaEliminated410`) — both ground
constants pinned against the derivative jet through `t₂(a), a₂₂(a),
h₀'(a)` only.

Nothing here closes the face or a branch: `c_β` is free, so the pin
eliminates no configuration; no root branch is forced (both factors of
each peeled product already vanish at the root); `t₂(a), a₂₂(a),
q₁(a), q₀(a), c_α, c_β, c_θ, c, j, p₀'(a), q₀'(a), q₇₆'(a), p₁'(a)`
remain free or tied-not-determined; the ground constants `γ` (row `9`,
next: its order-`-1` residue `8 w₇₃ - 14 t₂ q₇₆ + 5 p₁ t₂ + 9 λ p₁`
adds only the letter `w₇₃`) and `δ` (row `8`, residue also carries
`q₅₄`) stay uncleared.  No total-degree or twice-prime theorem is
used, and the aligned face `N = 0` is not touched.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Exact order-`-1` clearing of `β` on the thirteenth-face jet -/

section BetaGroundClearing410

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- Order-`-1` (polar) numerator block of the cleared `β` on the
thirteenth-face jet: the residue pair of the two order-`-1` letters
`B` and `Q`. -/
def betaGroundPolarNumerator410 (vis a1 : F[X]) : F[X] :=
  (64 : F[X]) * vis - (160 : F[X]) * a1

/-- Regular (order-`0`) numerator block of the cleared `β` on the
thirteenth-face jet.  It is linear in `s₂₂` with cofactor `-128 t₂`. -/
def betaGroundRegularNumerator410 (t2 a22 s22 : F[X]) (lambda : F) :
    F[X] :=
  (220 : F[X]) * t2 ^ 3 - (99 : F[X]) * Polynomial.C lambda * t2 ^ 2 -
    (128 : F[X]) * s22 * t2 + (80 : F[X]) * a22 * t2 +
    (72 : F[X]) * Polynomial.C lambda * a22

set_option maxHeartbeats 1600000 in
/-- Exact order-`-1` clearing of the third-face residual `β` on the
thirteenth-face jet substitutions: `64 h β` is the polar residue block
plus `h` times the regular block, so `β` sits at exact order `-1`. -/
theorem betaDefect_eq_cleared410
    (h t2 a22 s22 vis a1 b9 lambda : F) (hh : h ≠ 0)
    (hN : 5 * (h ^ 3 * t2) * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (64 : F) * h *
        betaResidual410
          (depressedL410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9)
          (depressedA410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22))
          (depressedB410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22) a1)
          (depressedQ410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis)) =
      ((64 : F) * vis - (160 : F) * a1) +
        h * ((220 : F) * t2 ^ 3 - (99 : F) * lambda * t2 ^ 2 -
          (128 : F) * s22 * t2 + (80 : F) * a22 * t2 +
          (72 : F) * lambda * a22) := by
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
  have hQ :
      depressedQ410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) =
        (-(9 : F) * h * lambda * t2 ^ 2 - 16 * h * s22 * t2 +
            30 * h * t2 ^ 3 + 8 * vis) / (8 * h) := by
    rw [depressedQ410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) lambda hh hN]
    field_simp [hh]
    ring
  simp only [betaResidual410, hL, hA, hB, hQ]
  field_simp [hh]
  ring

/-- The `β` ground pin solves the order-`-1` polar block exactly: the
residue pair `64 q₇₆ - 160 p₁` is `h₀` times the explicit
ground-loaded cofactor — a factored `h`-adic quotient identity. -/
theorem betaGroundPin_solvePolar410 (h0 t2 a22 s22 vis a1 : F[X])
    (lambda cbeta : F)
    (hpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0) :
    betaGroundPolarNumerator410 vis a1 =
      h0 * (Polynomial.C cbeta -
        betaGroundRegularNumerator410 t2 a22 s22 lambda) := by
  linear_combination hpin

/-- Root evaluation of the `β` ground pin: the thirteenth-face tie
`64 q₇₆(a) = 160 p₁(a)` (the jet hypothesis `hT`) is forced by the
literal source through the row-`10` integral alone. -/
theorem betaGroundPin_rootEval410 (h0 t2 a22 s22 vis a1 : F[X])
    (lambda cbeta : F) (a : F)
    (hpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hroot : h0.eval a = 0) :
    (64 : F) * vis.eval a - (160 : F) * a1.eval a = 0 := by
  have h := congrArg (fun r : F[X] => r.eval a) hpin
  simp only [betaGroundPolarNumerator410, eval_add, eval_sub, eval_mul,
    eval_C, eval_ofNat, hroot, zero_mul, mul_zero, add_zero] at h
  linear_combination h

/-- Factored elimination of `s₂₂` from the solved polar cofactor by
the global `α` pin: the first exact two-ground-constant link of the
lane, tying `q₇₆` and `p₁` to `t₂, a₂₂, c_α, c_β` only. -/
theorem betaGroundPin_alphaEliminated410
    (h0 t2 a22 s22 vis a1 : F[X]) (lambda calpha cbeta : F)
    (halpha : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha)
    (hpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0) :
    betaGroundPolarNumerator410 vis a1 =
      h0 * (Polynomial.C cbeta + (20 : F[X]) * t2 ^ 3 -
        (45 : F[X]) * Polynomial.C lambda * t2 ^ 2 +
        (240 : F[X]) * a22 * t2 -
        (72 : F[X]) * Polynomial.C lambda * a22 +
        (16 : F[X]) * Polynomial.C calpha * t2) := by
  have ha := halpha
  simp only [alphaGroundNumerator410] at ha
  have hb := hpin
  simp only [betaGroundPolarNumerator410,
    betaGroundRegularNumerator410] at hb
  simp only [betaGroundPolarNumerator410]
  linear_combination hb + (16 : F[X]) * t2 * h0 * ha

/-- `β`-loaded first `θ` peel: the ground pin eliminates the polar
letter `q₇₆` from the order-`-3` theta block in factored form, turning
the first peel step into an exact `h`-adic quotient identity for the
product `p₁ (25 p₁² - 16 b₄₂)`. -/
theorem thetaFirstPeel_betaLoaded410
    (h0 t2 a22 s22 vis a1 b42 v1 : F[X]) (lambda cbeta : F)
    (hpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hpeel : thetaPolarThreeNumerator410 vis a1 b42 = h0 * v1) :
    (67108864 : F[X]) * a1 *
        ((25 : F[X]) * a1 ^ 2 - (16 : F[X]) * b42) =
      h0 * ((64 : F[X]) * v1 -
        (18350080 : F[X]) * a1 ^ 2 *
          (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda)) := by
  have hb := hpin
  simp only [betaGroundPolarNumerator410] at hb
  have ht := hpeel
  simp only [thetaPolarThreeNumerator410] at ht
  linear_combination (64 : F[X]) * ht -
    (18350080 : F[X]) * a1 ^ 2 * hb

/-- `β`-loaded first `ι` peel: the ground pin eliminates the polar
letter `q₇₆` from the order-`-3` iota block in factored form. -/
theorem iotaFirstPeel_betaLoaded410
    (h0 t2 a22 s22 vis w73 a1 b42 b31 w1 : F[X]) (lambda cbeta : F)
    (hpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hpeel : iotaPolarThreeNumerator410 t2 vis w73 a1 b42 b31 lambda =
      h0 * w1) :
    (64 : F[X]) * a1 *
        ((3 : F[X]) * Polynomial.C lambda * a1 ^ 2 -
          (30 : F[X]) * a1 ^ 2 * t2 + (6 : F[X]) * a1 * w73 +
          (8 : F[X]) * b42 * t2 - (6 : F[X]) * b31) =
      h0 * ((64 : F[X]) * w1 +
        (14 : F[X]) * a1 ^ 2 * t2 *
          (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda)) := by
  have hb := hpin
  simp only [betaGroundPolarNumerator410] at hb
  have hi := hpeel
  simp only [iotaPolarThreeNumerator410] at hi
  linear_combination (64 : F[X]) * hi +
    (14 : F[X]) * a1 ^ 2 * t2 * hb

/-- Root derivative of any solved polar form: since the polar block is
`h₀` times a cofactor and `h₀(a) = 0`, the derivative combination at
the root sees exactly `h₀'(a)` times the cofactor value. -/
theorem betaPolar_rootDerivative_of_solved410
    (h0 vis a1 u : F[X]) (a : F)
    (hsolve : betaGroundPolarNumerator410 vis a1 = h0 * u)
    (hroot : h0.eval a = 0) :
    (64 : F) * (derivative vis).eval a -
        (160 : F) * (derivative a1).eval a =
      (derivative h0).eval a * u.eval a := by
  have hder := congrArg (fun r : F[X] => derivative r) hsolve
  simp only [betaGroundPolarNumerator410, derivative_sub,
    derivative_mul, derivative_ofNat, zero_mul, zero_add] at hder
  have heval := congrArg (fun r : F[X] => r.eval a) hder
  simp only [eval_add, eval_sub, eval_mul, eval_ofNat, hroot, zero_mul,
    add_zero] at heval
  linear_combination heval

/-- Root derivative tie of the `β` ground pin: the first
derivative-level residual of the nonzero face, pinning
`64 q₇₆'(a) - 160 p₁'(a)` against `c_β` and the root jet. -/
theorem betaGroundPin_rootDerivativeTie410
    (h0 t2 a22 s22 vis a1 : F[X]) (lambda cbeta : F) (a : F)
    (hpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hroot : h0.eval a = 0) :
    (64 : F) * (derivative vis).eval a -
        (160 : F) * (derivative a1).eval a =
      (derivative h0).eval a *
        (cbeta -
          (betaGroundRegularNumerator410 t2 a22 s22 lambda).eval a) := by
  have hsolve := betaGroundPin_solvePolar410 h0 t2 a22 s22 vis a1
    lambda cbeta hpin
  have h := betaPolar_rootDerivative_of_solved410 h0 vis a1
    (Polynomial.C cbeta -
      betaGroundRegularNumerator410 t2 a22 s22 lambda) a hsolve hroot
  simpa only [eval_sub, eval_C] using h

/-- Sharpest `β`-loaded residual: the root derivative tie with `s₂₂`
eliminated through the `α` pin — both ground constants pinned against
the derivative jet through `t₂(a), a₂₂(a), h₀'(a)` only. -/
theorem betaGroundPin_rootDerivativeTie_alphaEliminated410
    (h0 t2 a22 s22 vis a1 : F[X]) (lambda calpha cbeta : F) (a : F)
    (halpha : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha)
    (hpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hroot : h0.eval a = 0) :
    (64 : F) * (derivative vis).eval a -
        (160 : F) * (derivative a1).eval a =
      (derivative h0).eval a *
        (cbeta + (20 : F) * (t2.eval a) ^ 3 -
          (45 : F) * lambda * (t2.eval a) ^ 2 +
          (240 : F) * a22.eval a * t2.eval a -
          (72 : F) * lambda * a22.eval a +
          (16 : F) * calpha * t2.eval a) := by
  have hsolve := betaGroundPin_alphaEliminated410 h0 t2 a22 s22 vis a1
    lambda calpha cbeta halpha hpin
  have h := betaPolar_rootDerivative_of_solved410 h0 vis a1
    (Polynomial.C cbeta + (20 : F[X]) * t2 ^ 3 -
      (45 : F[X]) * Polynomial.C lambda * t2 ^ 2 +
      (240 : F[X]) * a22 * t2 -
      (72 : F[X]) * Polynomial.C lambda * a22 +
      (16 : F[X]) * Polynomial.C calpha * t2) a hsolve hroot
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat,
    eval_C] at h
  linear_combination h

end BetaGroundClearing410

/-! ## Source-facing ground power relation at exact order `-1` -/

section NonzeroBetaGroundBridge410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-- The row-`10` ground first integral `β` on a square-core
ninth-power source, traced from the literal Keller row through the
third-face power relation and expressed at its exact order `-1` on the
thirteenth-face jet: the polar residue block plus `h₀` times the
regular block is GLOBALLY `C c_β h₀`. -/
theorem nonzeroFace410_betaResidualPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 vis : k[X])
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hp3 : p.coeff 3 = h0 ^ 3 * t2) (hp2 : p.coeff 2 = h0 ^ 2 * a22)
    (hq8 : q.coeff 8 = h0 ^ 8 * s22) (hq7 : q.coeff 7 = h0 ^ 6 * vis) :
    ∃ cbeta : k,
      betaGroundPolarNumerator410 vis (p.coeff 1) +
        h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
      Polynomial.C cbeta * h0 := by
  obtain ⟨cbeta, hpow⟩ :=
    nonzeroFace410_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  refine ⟨cbeta, ?_⟩
  have h10 : h0 ^ 10 ≠ 0 := pow_ne_zero 10 hh0
  apply mul_left_cancel₀ h10
  calc
    h0 ^ 10 *
          (betaGroundPolarNumerator410 vis (p.coeff 1) +
            h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda) =
        localClearedThirdDefect410 h0 (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (q.coeff 8) (q.coeff 7) lambda := by
      simp only [localClearedThirdDefect410,
        betaGroundPolarNumerator410, betaGroundRegularNumerator410,
        hp3, hp2, hq8, hq7]
      ring
    _ = Polynomial.C cbeta * h0 ^ 11 := hpow
    _ = h0 ^ 10 * (Polynomial.C cbeta * h0) := by ring

/-! ## Beta ground bridge packet -/

set_option maxHeartbeats 4000000 in
/-- Sharpest exact successor packet of the `β` ground bridge on the
nonzero `(4,10)` face: everything from the ground-constants bridge
packet, together with the row-`10` ground pin at its exact order `-1`,
its one-step `h`-adic peel solving the polar residue block exactly,
the two-ground-constant link with `s₂₂` eliminated through the global
`α` pin, the `β`-loaded factored forms of the first `θ` and `ι` peel
steps of the terminal packet, and the two root derivative ties — the
sharpest `β`-loaded residuals, pinning `64 q₇₆'(a) - 160 p₁'(a)`
against `c_β` (and `c_α`) through `t₂(a), a₂₂(a), h₀'(a)` only.
Nothing here closes the face or a branch: `c_α, c_β` are free, so the
pins eliminate no configuration; no root branch is forced; `t₂(a),
a₂₂(a), q₁(a), q₀(a), c_α, c_β, c_θ, c, j, p₀'(a), q₀'(a)` remain free
or tied-not-determined, and the ground constants `γ, δ` stay
uncleared. -/
theorem nonzeroFace410_betaGroundBridgePacket
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
    ∃ (calpha cbeta ctheta c : k) (v1 v2 v3 w1 w2 w3 : k[X]),
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
            (16 : k) * calpha * t2.eval a) := by
  obtain ⟨calpha, ctheta, c, v1, v2, v3, w1, w2, w3, hpin, hsolve,
    hpowT, htw1, htw2, htw3, htwc, hpowI, hiw1, hiw2, hiw3, hiwc,
    hTglobal, hIglobal, ha1, hvis0, hw730, hq540, hb420, hb310, hb20,
    hv10, hw10, hv2tie, hw2tie, hrootS, hTroot, hIroot, hkelP, hcombo,
    hbr⟩ :=
    nonzeroFace410_groundConstantsBridgePacket p q H h0 j lambda t2
      a22 s22 vis w73 q54 b42 b31 a hp hq hh0 hH hp4 hq10 hN hD hp3
      hp2 hq8 hq7 hq6 hq5 hq4 hq3 hroot hT hU hW hV hX hY
  obtain ⟨cbeta, hbpin⟩ := nonzeroFace410_betaResidualPowerRelation
    p q H h0 j lambda t2 a22 s22 vis hp hq hh0 hH hp4 hq10 hN hD hp3
    hp2 hq8 hq7
  have hbsolve := betaGroundPin_solvePolar410 h0 t2 a22 s22 vis
    (p.coeff 1) lambda cbeta hbpin
  have hbalpha := betaGroundPin_alphaEliminated410 h0 t2 a22 s22 vis
    (p.coeff 1) lambda calpha cbeta hpin hbpin
  have hbtheta := thetaFirstPeel_betaLoaded410 h0 t2 a22 s22 vis
    (p.coeff 1) b42 v1 lambda cbeta hbpin htw1
  have hbiota := iotaFirstPeel_betaLoaded410 h0 t2 a22 s22 vis w73
    (p.coeff 1) b42 b31 w1 lambda cbeta hbpin hiw1
  have hbderiv := betaGroundPin_rootDerivativeTie410 h0 t2 a22 s22
    vis (p.coeff 1) lambda cbeta a hbpin hroot
  have hbderivA := betaGroundPin_rootDerivativeTie_alphaEliminated410
    h0 t2 a22 s22 vis (p.coeff 1) lambda calpha cbeta a hpin hbpin
    hroot
  exact ⟨calpha, cbeta, ctheta, c, v1, v2, v3, w1, w2, w3, hpin,
    hsolve, hpowT, htw1, htw2, htw3, htwc, hpowI, hiw1, hiw2, hiw3,
    hiwc, hTglobal, hIglobal, ha1, hvis0, hw730, hq540, hb420, hb310,
    hb20, hv10, hw10, hv2tie, hw2tie, hrootS, hTroot, hIroot, hkelP,
    hcombo, hbr, hbpin, hbsolve, hbalpha, hbtheta, hbiota, hbderiv,
    hbderivA⟩

end NonzeroBetaGroundBridge410

#print axioms betaDefect_eq_cleared410
#print axioms betaGroundPin_solvePolar410
#print axioms betaGroundPin_rootEval410
#print axioms betaGroundPin_alphaEliminated410
#print axioms thetaFirstPeel_betaLoaded410
#print axioms iotaFirstPeel_betaLoaded410
#print axioms betaPolar_rootDerivative_of_solved410
#print axioms betaGroundPin_rootDerivativeTie410
#print axioms betaGroundPin_rootDerivativeTie_alphaEliminated410
#print axioms nonzeroFace410_betaResidualPowerRelation
#print axioms nonzeroFace410_betaGroundBridgePacket

end Max11DegreeRoutes
