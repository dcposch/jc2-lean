import Fable410ScaleTwoDeltaGroundBridgeScratch

/-! # Epsilon ground bridge for the normalized `(4,10)` nonzero source

The delta ground bridge pinned the row-`8` ground first integral `δ`
at exact order `-1` and produced the first four-ground-constant link.
The next ground first integral is `ε = T - 2 α C - (7/4) β B -
(3/2) γ A - (15/4) A C - (15/8) B² - (45/16) L A B - α A² - (5/16) A³`
(row `7`, `epsilonResidual410`, sixth face).  On the thirteenth-face
jet it is the FIRST ground integral at exact order `-2`, and the first
seeing the order-`-2` letter `b₄₂`: the clearing needs TWO `h`-adic
peel steps, not one.

First, the clearing (`epsilonDefect_eq_cleared410`): `2048 h² ε`
splits as the order-`-2` polar block `2048 b₄₂ - 3584 p₁ q₇₆ +
5120 p₁²`, plus `h` times the order-`-1` block (every monomial
carries one of the root-vanishing letters `q₇₆, w₇₃, q₅₄, p₁`), plus
`h²` times the regular block (linear in `s₂₂` with quartic cofactor
`4096 (t₂⁴ - 3 a₂₂ t₂² + a₂₂² - p₀)`).

Second, the literal-source trace: the sixth-face power relation pins
the row-`7` integral globally (`nonzeroFace410_sixthDefectPowerRelation`,
weight `20`); substituting the thirteenth-face jet forms and cancelling
`h₀¹⁸` gives the FIRST order-`-2` ground pin of the lane
(`nonzeroFace410_epsilonResidualPowerRelation`):
`polar₂ + h₀ · polar₁ + h₀² · (regular) = C c_ε h₀²`.  Its first
`h`-adic peel step is exact (`epsilonGroundPin_solvePolarTwo410`), and
the root evaluation combined with the `β` pin RE-DERIVES the
thirteenth-face jet hypothesis `hW` from the literal source
(`epsilonGroundPin_rootEval_reDerivesW410`): `8 b₄₂(a) = 15 p₁(a)²` —
rows `10` and `7` alone force it.

Third, the eliminations.  The `β` pin eliminates the polar-`2`
cross-term `p₁ q₇₆` (`b42GroundPin_betaEliminated410`), collapsing the
polar-`2` block to `16384 b₄₂ - 30720 p₁²` — `2048` times the LITERAL
polynomial lift of the jet tie `hW`.  Loading the `δ`, `γ`, `β` pins
at the `h₀`-level and the `α` pin on both depths kills every
order-`-1` letter and `s₂₂` entirely
(`b42GroundPin_fullyEliminated410`): `16384 b₄₂ - 30720 p₁² =
h₀ (F₁ + h₀ F₂)` with `F₁ = 448 C c_β p₁ + 4096 C c_α p₁ t₂ -
23040 λ p₁ a₂₂ + 30720 p₁ a₂₂ t₂ - 2880 λ p₁ t₂² - 2560 p₁ t₂³` and
`F₂ = 8 C c_ε + 5 C c_δ t₂ + 48 C c_γ t₂² + 192 C c_γ a₂₂ +
336 C c_β a₂₂ t₂ - 14 C c_β t₂³ + 4096 C c_α p₀ + 2048 C c_α a₂₂² +
61440 p₀ a₂₂ - 23040 λ p₀ t₂ + 15360 p₀ t₂² + 5120 a₂₂³ -
2880 λ a₂₂² t₂ - 3840 a₂₂² t₂² + 720 λ a₂₂ t₂³ + 960 a₂₂ t₂⁴ -
63 λ t₂⁵ - 80 t₂⁶` — the first FIVE-ground-constant link of the lane
(elimination cofactors `8 ε`, `448 p₁ + h₀ (336 a₂₂ t₂ - 14 t₂³)` on
`β`, `5 h₀ t₂` on `δ`, `h₀ (48 t₂² + 192 a₂₂)` on `γ`,
`h₀ (4096 p₀ h₀ + 4096 p₁ t₂ + 2048 a₂₂² h₀)` on `α`).

Fourth, the combination with the terminal packet: the `b₄₂` pin
eliminates `b₄₂` from the `δ`-loaded second peel steps of BOTH towers
(`thetaSecondPeel_epsilonLoaded410`, `iotaSecondPeel_epsilonLoaded410`)
— only the letters `b₃₁, q₂` survive polar-side.  In the `ι` peel the
`b₄₂`-elimination cancels the `240 p₀ p₁²` and `120 p₁² a₂₂²` blocks
EXACTLY: the `ι` polar side loses its `p₀`-dependence.

The sharpest `ε`-loaded root results are one and two derivatives
deeper.  Since the solved polar-`2` cofactor itself vanishes at the
root (`c_ε h₀(a) - polar₁(a) - h₀(a) reg(a) = 0` — every `polar₁`
monomial dies at `a`), the first derivative of the pin at the root is
CONSTANT-FREE and EXACT (`epsilonPin_rootDerivativeKill410`):
`b₄₂'(a) = 0` — `b₄₂` vanishes doubly at the root, the first
unconditional derivative-level kill of the nonzero face (every earlier
derivative residual carried ground constants).  The honest residual
moves to the second derivative (`epsilonPin_rootSecondDerivativeTie410`):
`2048 b₄₂''(a) - 7168 p₁'(a) q₇₆'(a) + 10240 p₁'(a)² =
2 h₀'(a) (c_ε h₀'(a) - polar₁'(a) - h₀'(a) reg(a))` — the first
second-derivative-level residual of the lane, pinning `c_ε` against
`h₀'(a)²`.

Nothing here closes the face or a branch: `c_ε` is free, so the pin
eliminates no configuration; no root branch is forced (both factors of
every peeled block already vanish at the root); `t₂(a), a₂₂(a),
s₂₂(a), q₁(a), q₀(a), c_α, c_β, c_γ, c_δ, c_ε, c_θ, c, j, p₀'(a),
q₀'(a), p₁'(a), q₇₆'(a), b₄₂''(a)` remain free or
tied-not-determined; the ground constant `ζ` (row `6`, next: its
seventh-defect clearing `localClearedSeventhDefect410 = C · h₀²³`
sits at exact order `-2`, polar-`2` block `131072 (b₃₁ - b₄₂ t₂) -
143360 p₁² t₂ - 129024 λ p₁² + 401408 p₁ t₂ q₇₆ - 196608 p₁ w₇₃` —
the first ground clearing seeing `b₃₁`) stays uncleared.  No
total-degree or twice-prime theorem is used, and the aligned face
`N = 0` is not touched.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Exact order-`-2` clearing of `ε` on the thirteenth-face jet -/

section EpsilonGroundClearing410

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- Order-`-2` (polar) numerator block of the cleared `ε` on the
thirteenth-face jet: the first ground residue block at depth two.  It
is the first ground block seeing `b₄₂`, and it carries the polar-level
cross-term `p₁ q₇₆`. -/
def epsilonGroundPolarTwoNumerator410 (vis a1 b42 : F[X]) : F[X] :=
  (2048 : F[X]) * b42 - (3584 : F[X]) * a1 * vis +
    (5120 : F[X]) * a1 ^ 2

/-- Order-`-1` numerator block of the cleared `ε` on the
thirteenth-face jet.  Every monomial carries one of the root-vanishing
letters `q₇₆, w₇₃, q₅₄, p₁`, so the whole block vanishes at the root
of `h₀`. -/
def epsilonGroundPolarOneNumerator410
    (t2 a22 s22 vis w73 q54 a1 : F[X]) (lambda : F) : F[X] :=
  -(3584 : F[X]) * t2 ^ 3 * vis + (7168 : F[X]) * a22 * t2 * vis +
    (3072 : F[X]) * t2 ^ 2 * w73 - (3072 : F[X]) * a22 * w73 -
    (2560 : F[X]) * t2 * q54 + (8192 : F[X]) * a1 * s22 * t2 -
    (14080 : F[X]) * a1 * t2 ^ 3 +
    (6912 : F[X]) * Polynomial.C lambda * a1 * t2 ^ 2 -
    (7680 : F[X]) * a1 * a22 * t2 -
    (4608 : F[X]) * Polynomial.C lambda * a1 * a22

/-- Regular (order-`0`) numerator block of the cleared `ε` on the
thirteenth-face jet.  It is linear in `s₂₂` with the quartic cofactor
`4096 (t₂⁴ - 3 a₂₂ t₂² + a₂₂² - p₀)`. -/
def epsilonGroundRegularNumerator410 (t2 a22 s22 a0 : F[X])
    (lambda : F) : F[X] :=
  (4096 : F[X]) * s22 * t2 ^ 4 -
    (12288 : F[X]) * a22 * s22 * t2 ^ 2 +
    (4096 : F[X]) * a22 ^ 2 * s22 - (4096 : F[X]) * a0 * s22 -
    (6400 : F[X]) * t2 ^ 6 +
    (2304 : F[X]) * Polynomial.C lambda * t2 ^ 5 +
    (20480 : F[X]) * a22 * t2 ^ 4 -
    (9216 : F[X]) * Polynomial.C lambda * a22 * t2 ^ 3 -
    (3840 : F[X]) * a22 ^ 2 * t2 ^ 2 +
    (6912 : F[X]) * Polynomial.C lambda * a22 ^ 2 * t2 -
    (5120 : F[X]) * a22 ^ 3 + (7680 : F[X]) * a0 * t2 ^ 2 -
    (4608 : F[X]) * Polynomial.C lambda * a0 * t2 +
    (10240 : F[X]) * a0 * a22

set_option maxHeartbeats 12800000 in
/-- Exact order-`-2` clearing of the sixth-face residual `ε` on the
thirteenth-face jet substitutions: `2048 h² ε` is the polar-`2`
residue block plus `h` times the polar-`1` block plus `h²` times the
regular block, so `ε` sits at exact order `-2` — the first ground
integral needing two peel steps. -/
theorem epsilonDefect_eq_cleared410
    (h t2 a22 s22 vis w73 q54 a1 a0 b42 b9 lambda : F) (hh : h ≠ 0)
    (hN : 5 * (h ^ 3 * t2) * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (2048 : F) * h ^ 2 *
        epsilonResidual410
          (depressedL410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9)
          (depressedA410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22))
          (depressedB410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22) a1)
          (depressedC410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22) a1 a0)
          (depressedP410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22))
          (depressedQ410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis))
          (depressedR410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73))
          (depressedT410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
            (h ^ 2 * b42)) =
      ((2048 : F) * b42 - (3584 : F) * a1 * vis +
          (5120 : F) * a1 ^ 2) +
        h * (-(3584 : F) * t2 ^ 3 * vis + (7168 : F) * a22 * t2 * vis +
          (3072 : F) * t2 ^ 2 * w73 - (3072 : F) * a22 * w73 -
          (2560 : F) * t2 * q54 + (8192 : F) * a1 * s22 * t2 -
          (14080 : F) * a1 * t2 ^ 3 +
          (6912 : F) * lambda * a1 * t2 ^ 2 -
          (7680 : F) * a1 * a22 * t2 -
          (4608 : F) * lambda * a1 * a22) +
        h ^ 2 * ((4096 : F) * s22 * t2 ^ 4 -
          (12288 : F) * a22 * s22 * t2 ^ 2 +
          (4096 : F) * a22 ^ 2 * s22 - (4096 : F) * a0 * s22 -
          (6400 : F) * t2 ^ 6 + (2304 : F) * lambda * t2 ^ 5 +
          (20480 : F) * a22 * t2 ^ 4 -
          (9216 : F) * lambda * a22 * t2 ^ 3 -
          (3840 : F) * a22 ^ 2 * t2 ^ 2 +
          (6912 : F) * lambda * a22 ^ 2 * t2 -
          (5120 : F) * a22 ^ 3 + (7680 : F) * a0 * t2 ^ 2 -
          (4608 : F) * lambda * a0 * t2 +
          (10240 : F) * a0 * a22) := by
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
  have hQ :
      depressedQ410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) =
        (-(9 : F) * h * lambda * t2 ^ 2 - 16 * h * s22 * t2 +
            30 * h * t2 ^ 3 + 8 * vis) / (8 * h) := by
    rw [depressedQ410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) lambda hh hN]
    field_simp [hh]
    ring
  have hR :
      depressedR410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) =
        (-(315 : F) * t2 ^ 4 * h + 84 * lambda * t2 ^ 3 * h +
            224 * t2 ^ 2 * s22 * h - 224 * t2 * vis + 128 * w73) /
          (128 * h) := by
    rw [depressedR410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) lambda hh hN]
    field_simp [hh]
  have hT :
      depressedT410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
          (h ^ 2 * b42) =
        ((2048 : F) * b42 - 1120 * h * t2 ^ 3 * vis +
            1920 * h * t2 ^ 2 * w73 - 2560 * h * t2 * q54 +
            560 * h ^ 2 * t2 ^ 4 * s22 - 525 * h ^ 2 * t2 ^ 6 +
            126 * lambda * h ^ 2 * t2 ^ 5) / (2048 * h ^ 2) := by
    rw [depressedT410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) (h ^ 2 * b42) lambda
      hh hN]
    field_simp [hh]
    ring
  simp only [epsilonResidual410, alphaResidual410, betaResidual410,
    gammaResidual410, hL, hA, hB, hC, hP, hQ, hR, hT]
  field_simp [hh]
  ring

/-- The `ε` ground pin solves the order-`-2` polar block exactly: the
polar-`2` residue block is `h₀` times the explicit ground-loaded
cofactor — the first peel step of the order-`-2` pin, in factored
`h`-adic quotient form. -/
theorem epsilonGroundPin_solvePolarTwo410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 : F[X])
    (lambda cepsilon : F)
    (hpin : epsilonGroundPolarTwoNumerator410 vis a1 b42 +
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          a1 lambda +
        h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22 a0
          lambda =
      Polynomial.C cepsilon * h0 ^ 2) :
    epsilonGroundPolarTwoNumerator410 vis a1 b42 =
      h0 * (Polynomial.C cepsilon * h0 -
        epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          lambda -
        h0 * epsilonGroundRegularNumerator410 t2 a22 s22 a0 lambda) := by
  linear_combination hpin

/-- Root evaluation of the `ε` ground pin: the polar-`2` residue block
vanishes at the root of `h₀`. -/
theorem epsilonGroundPin_rootEval410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 : F[X])
    (lambda cepsilon : F) (a : F)
    (hpin : epsilonGroundPolarTwoNumerator410 vis a1 b42 +
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          a1 lambda +
        h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22 a0
          lambda =
      Polynomial.C cepsilon * h0 ^ 2)
    (hroot : h0.eval a = 0) :
    (2048 : F) * b42.eval a - (3584 : F) * a1.eval a * vis.eval a +
        (5120 : F) * (a1.eval a) ^ 2 = 0 := by
  have h := congrArg (fun r : F[X] => r.eval a) hpin
  simp only [epsilonGroundPolarTwoNumerator410, pow_two, eval_add,
    eval_sub, eval_mul, eval_C, eval_ofNat, hroot, zero_mul, mul_zero,
    add_zero] at h
  linear_combination h

/-- Root evaluation of the `ε` ground pin combined with the `β` ground
pin: the thirteenth-face tie `8 b₄₂(a) = 15 p₁(a)²` (the jet
hypothesis `hW`) is forced by the literal source through the row-`10`
and row-`7` integrals alone. -/
theorem epsilonGroundPin_rootEval_reDerivesW410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 : F[X])
    (lambda cbeta cepsilon : F) (a : F)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hepin : epsilonGroundPolarTwoNumerator410 vis a1 b42 +
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          a1 lambda +
        h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22 a0
          lambda =
      Polynomial.C cepsilon * h0 ^ 2)
    (hroot : h0.eval a = 0) :
    (8 : F) * b42.eval a = (15 : F) * (a1.eval a) ^ 2 := by
  have hbe := betaGroundPin_rootEval410 h0 t2 a22 s22 vis a1 lambda
    cbeta a hbpin hroot
  have hee := epsilonGroundPin_rootEval410 h0 t2 a22 s22 vis w73 q54
    a1 a0 b42 lambda cepsilon a hepin hroot
  linear_combination ((1 : F) / 256) * hee +
    ((7 : F) / 32) * a1.eval a * hbe

/-- The `b₄₂` pin, `β`-eliminated: the `β` ground pin eliminates the
polar-`2` cross-term `p₁ q₇₆` from the `ε` polar block, in factored
`h`-adic quotient form.  Its left side is `2048` times the literal
polynomial lift of the thirteenth-face jet tie `hW`: the root tie of
the thirteenth face is the root shadow of this global pin. -/
theorem b42GroundPin_betaEliminated410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 : F[X])
    (lambda cbeta cepsilon : F)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hepin : epsilonGroundPolarTwoNumerator410 vis a1 b42 +
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          a1 lambda +
        h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22 a0
          lambda =
      Polynomial.C cepsilon * h0 ^ 2) :
    (16384 : F[X]) * b42 - (30720 : F[X]) * a1 ^ 2 =
      h0 * ((8 : F[X]) * Polynomial.C cepsilon * h0 +
        (448 : F[X]) * a1 * (Polynomial.C cbeta -
          betaGroundRegularNumerator410 t2 a22 s22 lambda) -
        (8 : F[X]) * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis
          w73 q54 a1 lambda -
        (8 : F[X]) * h0 * epsilonGroundRegularNumerator410 t2 a22 s22
          a0 lambda) := by
  have hb := hbpin
  simp only [betaGroundPolarNumerator410] at hb
  have he := hepin
  simp only [epsilonGroundPolarTwoNumerator410] at he
  linear_combination (8 : F[X]) * he + (448 : F[X]) * a1 * hb

set_option maxHeartbeats 3200000 in
/-- The fully eliminated `b₄₂` pin: the `β` pin kills the polar-`2`
cross-term, the `δ`, `γ`, `β` pins kill every order-`-1` letter at the
`h₀`-level, and the `α` pin (acting at BOTH depths) eliminates `s₂₂`
entirely — `16384 b₄₂ - 30720 p₁²` is pinned against `t₂, a₂₂, p₀,
c_α, c_β, c_γ, c_δ, c_ε` only, the first global FIVE-ground-constant
link of the lane. -/
theorem b42GroundPin_fullyEliminated410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 : F[X])
    (lambda calpha cbeta cgamma cdelta cepsilon : F)
    (halpha : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0)
    (hdpin : deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 a1
        lambda +
      h0 * deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cdelta * h0)
    (hepin : epsilonGroundPolarTwoNumerator410 vis a1 b42 +
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          a1 lambda +
        h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22 a0
          lambda =
      Polynomial.C cepsilon * h0 ^ 2) :
    (16384 : F[X]) * b42 - (30720 : F[X]) * a1 ^ 2 =
      h0 * ((448 : F[X]) * Polynomial.C cbeta * a1 +
        (4096 : F[X]) * Polynomial.C calpha * a1 * t2 -
        (23040 : F[X]) * Polynomial.C lambda * a1 * a22 +
        (30720 : F[X]) * a1 * a22 * t2 -
        (2880 : F[X]) * Polynomial.C lambda * a1 * t2 ^ 2 -
        (2560 : F[X]) * a1 * t2 ^ 3 +
        h0 * ((8 : F[X]) * Polynomial.C cepsilon +
          (5 : F[X]) * Polynomial.C cdelta * t2 +
          (48 : F[X]) * Polynomial.C cgamma * t2 ^ 2 +
          (192 : F[X]) * Polynomial.C cgamma * a22 +
          (336 : F[X]) * Polynomial.C cbeta * a22 * t2 -
          (14 : F[X]) * Polynomial.C cbeta * t2 ^ 3 +
          (4096 : F[X]) * Polynomial.C calpha * a0 +
          (2048 : F[X]) * Polynomial.C calpha * a22 ^ 2 +
          (61440 : F[X]) * a0 * a22 -
          (23040 : F[X]) * Polynomial.C lambda * a0 * t2 +
          (15360 : F[X]) * a0 * t2 ^ 2 +
          (5120 : F[X]) * a22 ^ 3 -
          (2880 : F[X]) * Polynomial.C lambda * a22 ^ 2 * t2 -
          (3840 : F[X]) * a22 ^ 2 * t2 ^ 2 +
          (720 : F[X]) * Polynomial.C lambda * a22 * t2 ^ 3 +
          (960 : F[X]) * a22 * t2 ^ 4 -
          (63 : F[X]) * Polynomial.C lambda * t2 ^ 5 -
          (80 : F[X]) * t2 ^ 6)) := by
  have ha := halpha
  simp only [alphaGroundNumerator410] at ha
  have hb := hbpin
  simp only [betaGroundPolarNumerator410,
    betaGroundRegularNumerator410] at hb
  have hg := hgpin
  simp only [gammaGroundPolarNumerator410,
    gammaGroundRegularNumerator410] at hg
  have hd := hdpin
  simp only [deltaGroundPolarNumerator410,
    deltaGroundRegularNumerator410] at hd
  have he := hepin
  simp only [epsilonGroundPolarTwoNumerator410,
    epsilonGroundPolarOneNumerator410,
    epsilonGroundRegularNumerator410] at he
  linear_combination (8 : F[X]) * he +
    ((448 : F[X]) * a1 +
      h0 * ((336 : F[X]) * a22 * t2 - (14 : F[X]) * t2 ^ 3)) * hb +
    (5 : F[X]) * h0 * t2 * hd +
    h0 * ((48 : F[X]) * t2 ^ 2 + (192 : F[X]) * a22) * hg +
    h0 * ((4096 : F[X]) * a0 * h0 + (4096 : F[X]) * a1 * t2 +
      (2048 : F[X]) * a22 ^ 2 * h0) * ha

set_option maxHeartbeats 1600000 in
/-- `ε`-loaded second `θ` peel: the `b₄₂` pin eliminates the letter
`b₄₂` from the `δ`-loaded order-`-2` theta block — only the
order-`-2` letters `b₃₁, q₂` survive on the polar side. -/
theorem thetaSecondPeel_epsilonLoaded410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 v1 v2 u : F[X])
    (lambda calpha cbeta cgamma cdelta : F)
    (halpha : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0)
    (hdpin : deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 a1
        lambda +
      h0 * deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cdelta * h0)
    (hb42 : (16384 : F[X]) * b42 - (30720 : F[X]) * a1 ^ 2 = h0 * u)
    (hpeel : v1 + thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda =
      h0 * v2) :
    v1 - (8192 : F[X]) *
        ((1200 : F[X]) * a1 ^ 2 * a22 * t2 +
          (2400 : F[X]) * a1 ^ 2 * t2 ^ 3 +
          (1080 : F[X]) * Polynomial.C lambda * a1 ^ 2 * a22 -
          (1575 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 ^ 2 -
          (80 : F[X]) * Polynomial.C calpha * a1 ^ 2 * t2 +
          (1536 : F[X]) * a22 * b31 -
          (960 : F[X]) * b31 * t2 ^ 2 +
          (1024 : F[X]) * b2 * t2) =
      h0 * (v2 - (6400 : F[X]) * a1 * t2 *
          (Polynomial.C cdelta -
            deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda) -
        a1 * ((245760 : F[X]) * a22 + (30720 : F[X]) * t2 ^ 2) *
          (Polynomial.C cgamma -
            gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda) -
        (286720 : F[X]) * a1 * a22 * t2 *
          (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda) -
        ((1280 : F[X]) * a22 * t2 - (480 : F[X]) * t2 ^ 3) * u) := by
  have ha := halpha
  simp only [alphaGroundNumerator410] at ha
  have hb := hbpin
  simp only [betaGroundPolarNumerator410] at hb
  have hg := hgpin
  simp only [gammaGroundPolarNumerator410] at hg
  have hd := hdpin
  simp only [deltaGroundPolarNumerator410] at hd
  have hp := hpeel
  simp only [thetaPolarTwoNumerator410] at hp
  linear_combination hp - (6400 : F[X]) * a1 * t2 * hd -
    a1 * ((245760 : F[X]) * a22 + (30720 : F[X]) * t2 ^ 2) * hg -
    (286720 : F[X]) * a1 * a22 * t2 * hb -
    (655360 : F[X]) * a1 ^ 2 * t2 * ha -
    ((1280 : F[X]) * a22 * t2 - (480 : F[X]) * t2 ^ 3) * hb42

set_option maxHeartbeats 1600000 in
/-- `ε`-loaded second `ι` peel (scaled by `4`): the `b₄₂` pin
eliminates the letter `b₄₂` from the `δ`-loaded order-`-2` iota block
— only `b₃₁, q₂` survive on the polar side, and the elimination
cancels the `240 p₀ p₁²` and `120 p₁² a₂₂²` blocks exactly: the `ι`
polar side loses its `p₀`-dependence. -/
theorem iotaSecondPeel_epsilonLoaded410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 w1 w2 u : F[X])
    (lambda calpha cbeta cgamma cdelta : F)
    (halpha : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0)
    (hdpin : deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 a1
        lambda +
      h0 * deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cdelta * h0)
    (hb42 : (16384 : F[X]) * b42 - (30720 : F[X]) * a1 ^ 2 = h0 * u)
    (hpeel : w1 + iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        a0 b42 b31 b2 lambda =
      h0 * w2) :
    (8192 : F[X]) * w1 + (512 : F[X]) *
        ((8 : F[X]) * Polynomial.C calpha * a1 ^ 2 * a22 +
          (63 : F[X]) * Polynomial.C lambda * a1 ^ 2 * a22 * t2 +
          (270 : F[X]) * a1 ^ 2 * a22 * t2 ^ 2 +
          (8 : F[X]) * Polynomial.C calpha * a1 ^ 2 * t2 ^ 2 -
          (135 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 ^ 3 +
          (150 : F[X]) * a1 ^ 2 * t2 ^ 4 -
          (64 : F[X]) * a22 * b2 +
          (96 : F[X]) * a22 * b31 * t2 +
          (32 : F[X]) * b2 * t2 ^ 2 -
          (32 : F[X]) * b31 * t2 ^ 3) =
      h0 * ((8192 : F[X]) * w2 -
        (20 : F[X]) * a1 * (a22 - t2 ^ 2) *
          (Polynomial.C cdelta -
            deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda) +
        (192 : F[X]) * a1 * t2 * ((3 : F[X]) * a22 + t2 ^ 2) *
          (Polynomial.C cgamma -
            gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda) -
        (56 : F[X]) * a1 *
            ((32 : F[X]) * a0 + (8 : F[X]) * a22 ^ 2 -
              (25 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) *
          (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda) -
        (-(4 : F[X]) * a0 + (2 : F[X]) * a22 ^ 2 -
            (4 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) * u) := by
  have ha := halpha
  simp only [alphaGroundNumerator410] at ha
  have hb := hbpin
  simp only [betaGroundPolarNumerator410] at hb
  have hg := hgpin
  simp only [gammaGroundPolarNumerator410] at hg
  have hd := hdpin
  simp only [deltaGroundPolarNumerator410] at hd
  have hp := hpeel
  simp only [iotaPolarTwoNumerator410] at hp
  linear_combination (8192 : F[X]) * hp -
    (20 : F[X]) * a1 * (a22 - t2 ^ 2) * hd +
    (192 : F[X]) * a1 * t2 * ((3 : F[X]) * a22 + t2 ^ 2) * hg -
    (56 : F[X]) * a1 *
      ((32 : F[X]) * a0 + (8 : F[X]) * a22 ^ 2 -
        (25 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) * hb -
    (4096 : F[X]) * a1 ^ 2 * (a22 + t2 ^ 2) * ha -
    (-(4 : F[X]) * a0 + (2 : F[X]) * a22 ^ 2 -
      (4 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) * hb42

/-- Root evaluation of the `ε` polar-`1` block: every monomial carries
one of the root-vanishing letters `q₇₆, w₇₃, q₅₄, p₁`, so the whole
block dies at the root. -/
theorem epsilonPolarOne_rootEval410
    (t2 a22 s22 vis w73 q54 a1 : F[X]) (lambda : F) (a : F)
    (hvis : vis.eval a = 0) (hw73 : w73.eval a = 0)
    (hq54 : q54.eval a = 0) (ha1 : a1.eval a = 0) :
    (epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
        lambda).eval a = 0 := by
  simp only [epsilonGroundPolarOneNumerator410, eval_add, eval_sub,
    eval_mul, eval_pow, eval_C, eval_ofNat, eval_neg, hvis, hw73,
    hq54, ha1, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    zero_sub, neg_zero]

/-- The exact `ε` derivative kill: since the solved polar-`2` cofactor
itself vanishes at the root (the polar-`1` block dies there), the
derivative of the `ε` pin at the root is constant-free — `b₄₂`
vanishes DOUBLY at the root of `h₀`.  This is the first unconditional
derivative-level kill of the nonzero face: every earlier derivative
residual carried ground constants. -/
theorem epsilonPin_rootDerivativeKill410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 : F[X])
    (lambda cepsilon : F) (a : F)
    (hepin : epsilonGroundPolarTwoNumerator410 vis a1 b42 +
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          a1 lambda +
        h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22 a0
          lambda =
      Polynomial.C cepsilon * h0 ^ 2)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (hw73 : w73.eval a = 0) (hq54 : q54.eval a = 0)
    (ha1 : a1.eval a = 0) :
    (derivative b42).eval a = 0 := by
  have hP1a := epsilonPolarOne_rootEval410 t2 a22 s22 vis w73 q54 a1
    lambda a hvis hw73 hq54 ha1
  have hs : epsilonGroundPolarTwoNumerator410 vis a1 b42 =
      Polynomial.C cepsilon * (h0 * h0) -
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          a1 lambda -
        h0 * (h0 * epsilonGroundRegularNumerator410 t2 a22 s22 a0
          lambda) := by
    linear_combination hepin
  have hd1 := congrArg (fun r : F[X] => derivative r) hs
  simp only [epsilonGroundPolarTwoNumerator410, pow_two,
    derivative_add, derivative_sub, derivative_mul, derivative_ofNat,
    derivative_C, zero_mul, mul_zero, zero_add, add_zero] at hd1
  have heval := congrArg (fun r : F[X] => r.eval a) hd1
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_ofNat, hroot,
    hvis, ha1, hP1a, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    zero_sub, neg_zero] at heval
  linear_combination ((1 : F) / 2048) * heval

set_option maxHeartbeats 3200000 in
/-- Sharpest honest `ε` residual, one derivative below the exact kill:
the second derivative of the `ε` pin at the root ties `b₄₂''(a)` and
the derivative jet against `c_ε` — the first second-derivative-level
residual of the lane, with `c_ε` pinned against `h₀'(a)²`. -/
theorem epsilonPin_rootSecondDerivativeTie410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 : F[X])
    (lambda cepsilon : F) (a : F)
    (hepin : epsilonGroundPolarTwoNumerator410 vis a1 b42 +
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          a1 lambda +
        h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22 a0
          lambda =
      Polynomial.C cepsilon * h0 ^ 2)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (hw73 : w73.eval a = 0) (hq54 : q54.eval a = 0)
    (ha1 : a1.eval a = 0) :
    (2048 : F) * (derivative (derivative b42)).eval a -
        (7168 : F) * (derivative a1).eval a * (derivative vis).eval a +
        (10240 : F) * ((derivative a1).eval a) ^ 2 =
      (2 : F) * (derivative h0).eval a *
        (cepsilon * (derivative h0).eval a -
          (derivative (epsilonGroundPolarOneNumerator410 t2 a22 s22
              vis w73 q54 a1 lambda)).eval a -
          (derivative h0).eval a *
            (epsilonGroundRegularNumerator410 t2 a22 s22 a0
                lambda).eval a) := by
  have hP1a := epsilonPolarOne_rootEval410 t2 a22 s22 vis w73 q54 a1
    lambda a hvis hw73 hq54 ha1
  have hs : epsilonGroundPolarTwoNumerator410 vis a1 b42 =
      Polynomial.C cepsilon * (h0 * h0) -
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          a1 lambda -
        h0 * (h0 * epsilonGroundRegularNumerator410 t2 a22 s22 a0
          lambda) := by
    linear_combination hepin
  have hd2 := congrArg (fun r : F[X] => derivative (derivative r)) hs
  simp only [epsilonGroundPolarTwoNumerator410, pow_two,
    derivative_add, derivative_sub, derivative_mul, derivative_ofNat,
    derivative_C, zero_mul, mul_zero, zero_add, add_zero] at hd2
  have heval := congrArg (fun r : F[X] => r.eval a) hd2
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_ofNat, hroot,
    hvis, hw73, hq54, ha1, hP1a, zero_mul, mul_zero, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero] at heval
  linear_combination heval

end EpsilonGroundClearing410

/-! ## Source-facing ground power relation at exact order `-2` -/

section NonzeroEpsilonGroundBridge410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 3200000 in
/-- The row-`7` ground first integral `ε` on a square-core ninth-power
source, traced from the literal Keller row through the sixth-face
power relation and expressed at its exact order `-2` on the
thirteenth-face jet: the polar-`2` block plus `h₀` times the polar-`1`
block plus `h₀²` times the regular block is GLOBALLY `C c_ε h₀²` —
the first order-`-2` ground pin of the lane. -/
theorem nonzeroFace410_epsilonResidualPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 vis w73 q54 b42 : k[X])
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
    (hq6 : q.coeff 6 = h0 ^ 5 * w73)
    (hq5 : q.coeff 5 = h0 ^ 4 * q54)
    (hq4 : q.coeff 4 = h0 ^ 2 * b42) :
    ∃ cepsilon : k,
      epsilonGroundPolarTwoNumerator410 vis (p.coeff 1) b42 +
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) lambda +
        h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22
          (p.coeff 0) lambda =
      Polynomial.C cepsilon * h0 ^ 2 := by
  obtain ⟨cepsilon, hpow⟩ :=
    nonzeroFace410_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  refine ⟨cepsilon, ?_⟩
  have h18 : h0 ^ 18 ≠ 0 := pow_ne_zero 18 hh0
  apply mul_left_cancel₀ h18
  calc
    h0 ^ 18 *
          (epsilonGroundPolarTwoNumerator410 vis (p.coeff 1) b42 +
            h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73
              q54 (p.coeff 1) lambda +
            h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22
              (p.coeff 0) lambda) =
        localClearedSixthDefect410 h0 (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          (q.coeff 5) (q.coeff 4) lambda := by
      simp only [localClearedSixthDefect410,
        epsilonGroundPolarTwoNumerator410,
        epsilonGroundPolarOneNumerator410,
        epsilonGroundRegularNumerator410, hp3, hp2, hq8, hq7, hq6,
        hq5, hq4]
      ring
    _ = Polynomial.C cepsilon * h0 ^ 20 := hpow
    _ = h0 ^ 18 * (Polynomial.C cepsilon * h0 ^ 2) := by ring

/-! ## Epsilon ground bridge packet -/

set_option maxHeartbeats 12800000 in
/-- Sharpest exact successor packet of the `ε` ground bridge on the
nonzero `(4,10)` face: everything from the delta ground bridge packet,
together with the row-`7` ground pin at its exact order `-2` — the
first order-`-2` ground pin of the lane — its first `h`-adic peel step
in solved form, the `β`-eliminated `b₄₂` pin (whose left side is
`2048` times the global polynomial lift of the jet tie `hW`), the
fully eliminated `b₄₂` pin — the first global FIVE-ground-constant
link of the lane, with cofactor `ueps` bound explicitly — the
`ε`-loaded factored forms of the second `θ` and `ι` peel steps (the
letter `b₄₂` eliminated; only `b₃₁, q₂` survive polar-side, and the
`ι` polar side loses its `p₀`-dependence), the EXACT constant-free
derivative kill `b₄₂'(a) = 0` (`b₄₂` vanishes doubly at the root — the
first unconditional derivative-level kill of the nonzero face), and
the second-derivative root tie — the sharpest honest `ε` residual,
pinning `c_ε` against `h₀'(a)²`.  Nothing here closes the face or a
branch: `c_α, c_β, c_γ, c_δ, c_ε` are free, so the pins eliminate no
configuration; no root branch is forced; `t₂(a), a₂₂(a), s₂₂(a),
q₁(a), q₀(a), c_α, c_β, c_γ, c_δ, c_ε, c_θ, c, j, p₀'(a), q₀'(a)`
remain free or tied-not-determined, and the ground constant `ζ`
(row `6`, seventh defect, exact order `-2`, first seeing `b₃₁`) stays
uncleared. -/
theorem nonzeroFace410_epsilonGroundBridgePacket
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
    ∃ (calpha cbeta cgamma cdelta cepsilon ctheta c : k)
      (v1 v2 v3 w1 w2 w3 ueps : k[X]),
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
            (640 : k) * (p.coeff 0).eval a) ∧
      deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          lambda +
        h0 * deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
          lambda =
        Polynomial.C cdelta * h0 ∧
      deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          lambda =
        h0 * (Polynomial.C cdelta -
          deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
            lambda) ∧
      (4096 : k[X]) * q54 - (6144 : k[X]) * t2 * w73 +
          (8064 : k[X]) * t2 ^ 2 * vis - (7168 : k[X]) * a22 * vis -
          (960 : k[X]) * p.coeff 1 * t2 ^ 2 -
          (1152 : k[X]) * Polynomial.C lambda * p.coeff 1 * t2 +
          (2560 : k[X]) * p.coeff 1 * a22 -
          (1024 : k[X]) * Polynomial.C calpha * p.coeff 1 =
        h0 * (Polynomial.C cdelta + (2808 : k[X]) * t2 ^ 5 -
          (5265 : k[X]) * Polynomial.C lambda * t2 ^ 4 +
          (21600 : k[X]) * a22 * t2 ^ 3 +
          (3888 : k[X]) * Polynomial.C lambda * a22 * t2 ^ 2 -
          (34560 : k[X]) * a22 ^ 2 * t2 +
          (5184 : k[X]) * Polynomial.C lambda * a22 ^ 2 -
          (4608 : k[X]) * Polynomial.C lambda * p.coeff 0 +
          (1248 : k[X]) * Polynomial.C calpha * t2 ^ 3 -
          (2304 : k[X]) * Polynomial.C calpha * a22 * t2) ∧
      (4096 : k[X]) * q54 - (8192 : k[X]) * p.coeff 1 * s22 +
          (11520 : k[X]) * p.coeff 1 * t2 ^ 2 -
          (3456 : k[X]) * Polynomial.C lambda * p.coeff 1 * t2 +
          (5120 : k[X]) * p.coeff 1 * a22 =
        h0 * ((Polynomial.C cdelta -
            deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
              lambda) +
          (48 : k[X]) * t2 * (Polynomial.C cgamma -
            gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
              lambda) +
          ((42 : k[X]) * t2 ^ 2 + (112 : k[X]) * a22) *
            (Polynomial.C cbeta -
              betaGroundRegularNumerator410 t2 a22 s22 lambda)) ∧
      (4096 : k[X]) * q54 -
          (1024 : k[X]) * Polynomial.C calpha * p.coeff 1 -
          (3840 : k[X]) * p.coeff 1 * t2 ^ 2 +
          (5760 : k[X]) * Polynomial.C lambda * p.coeff 1 * t2 -
          (15360 : k[X]) * p.coeff 1 * a22 =
        h0 * (Polynomial.C cdelta +
          (48 : k[X]) * Polynomial.C cgamma * t2 +
          (42 : k[X]) * Polynomial.C cbeta * t2 ^ 2 +
          (112 : k[X]) * Polynomial.C cbeta * a22 +
          (1024 : k[X]) * Polynomial.C calpha * a22 * t2 +
          (48 : k[X]) * t2 ^ 5 +
          (45 : k[X]) * Polynomial.C lambda * t2 ^ 4 -
          (640 : k[X]) * a22 * t2 ^ 3 -
          (720 : k[X]) * Polynomial.C lambda * a22 * t2 ^ 2 +
          (3840 : k[X]) * a22 ^ 2 * t2 -
          (2880 : k[X]) * Polynomial.C lambda * a22 ^ 2 +
          (15360 : k[X]) * p.coeff 0 * t2 -
          (4608 : k[X]) * Polynomial.C lambda * p.coeff 0) ∧
      v1 - (8192 : k[X]) *
          ((6000 : k[X]) * (p.coeff 1) ^ 2 * a22 * t2 +
            (1080 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 *
              a22 +
            (600 : k[X]) * (p.coeff 1) ^ 2 * t2 ^ 3 -
            (1575 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 *
              t2 ^ 2 -
            (80 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 * t2 +
            (1536 : k[X]) * a22 * b31 -
            (2560 : k[X]) * a22 * b42 * t2 +
            (960 : k[X]) * b42 * t2 ^ 3 -
            (960 : k[X]) * b31 * t2 ^ 2 +
            (1024 : k[X]) * q.coeff 2 * t2) =
        h0 * (v2 - (6400 : k[X]) * p.coeff 1 * t2 *
            (Polynomial.C cdelta -
              deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) -
          p.coeff 1 *
              ((245760 : k[X]) * a22 + (30720 : k[X]) * t2 ^ 2) *
            (Polynomial.C cgamma -
              gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) -
          (286720 : k[X]) * p.coeff 1 * a22 * t2 *
            (Polynomial.C cbeta -
              betaGroundRegularNumerator410 t2 a22 s22 lambda)) ∧
      (2048 : k[X]) * w1 + (128 : k[X]) *
          ((240 : k[X]) * p.coeff 0 * (p.coeff 1) ^ 2 -
            (128 : k[X]) * p.coeff 0 * b42 -
            (120 : k[X]) * (p.coeff 1) ^ 2 * a22 ^ 2 +
            (8 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 * a22 +
            (63 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 *
              a22 * t2 +
            (510 : k[X]) * (p.coeff 1) ^ 2 * a22 * t2 ^ 2 +
            (8 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 *
              t2 ^ 2 -
            (135 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 *
              t2 ^ 3 +
            (90 : k[X]) * (p.coeff 1) ^ 2 * t2 ^ 4 +
            (64 : k[X]) * a22 ^ 2 * b42 -
            (64 : k[X]) * a22 * q.coeff 2 +
            (96 : k[X]) * a22 * b31 * t2 -
            (128 : k[X]) * a22 * b42 * t2 ^ 2 +
            (32 : k[X]) * q.coeff 2 * t2 ^ 2 -
            (32 : k[X]) * b31 * t2 ^ 3 +
            (32 : k[X]) * b42 * t2 ^ 4) =
        h0 * ((2048 : k[X]) * w2 -
          (5 : k[X]) * p.coeff 1 * (a22 - t2 ^ 2) *
            (Polynomial.C cdelta -
              deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) +
          (48 : k[X]) * p.coeff 1 * t2 * ((3 : k[X]) * a22 + t2 ^ 2) *
            (Polynomial.C cgamma -
              gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) -
          (14 : k[X]) * p.coeff 1 *
              ((32 : k[X]) * p.coeff 0 + (8 : k[X]) * a22 ^ 2 -
                (25 : k[X]) * a22 * t2 ^ 2 + t2 ^ 4) *
            (Polynomial.C cbeta -
              betaGroundRegularNumerator410 t2 a22 s22 lambda)) ∧
      (4096 : k) * (derivative q54).eval a -
          (6144 : k) * t2.eval a * (derivative w73).eval a +
          (8064 : k) * (t2.eval a) ^ 2 * (derivative vis).eval a -
          (7168 : k) * a22.eval a * (derivative vis).eval a +
          (14400 : k) * (t2.eval a) ^ 2 *
            (derivative (p.coeff 1)).eval a -
          (8192 : k) * s22.eval a * (derivative (p.coeff 1)).eval a -
          (10368 : k) * lambda * t2.eval a *
            (derivative (p.coeff 1)).eval a +
          (23040 : k) * a22.eval a *
            (derivative (p.coeff 1)).eval a =
        (derivative h0).eval a *
          (cdelta -
            (deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda).eval a) ∧
      (4096 : k) * (derivative q54).eval a -
          (1024 : k) * calpha * (derivative (p.coeff 1)).eval a -
          (3840 : k) * (t2.eval a) ^ 2 *
            (derivative (p.coeff 1)).eval a +
          (5760 : k) * lambda * t2.eval a *
            (derivative (p.coeff 1)).eval a -
          (15360 : k) * a22.eval a *
            (derivative (p.coeff 1)).eval a =
        (derivative h0).eval a *
          (cdelta + (48 : k) * cgamma * t2.eval a +
            (42 : k) * cbeta * (t2.eval a) ^ 2 +
            (112 : k) * cbeta * a22.eval a +
            (1024 : k) * calpha * a22.eval a * t2.eval a +
            (48 : k) * (t2.eval a) ^ 5 +
            (45 : k) * lambda * (t2.eval a) ^ 4 -
            (640 : k) * a22.eval a * (t2.eval a) ^ 3 -
            (720 : k) * lambda * a22.eval a * (t2.eval a) ^ 2 +
            (3840 : k) * (a22.eval a) ^ 2 * t2.eval a -
            (2880 : k) * lambda * (a22.eval a) ^ 2 +
            (15360 : k) * (p.coeff 0).eval a * t2.eval a -
            (4608 : k) * lambda * (p.coeff 0).eval a) ∧
      epsilonGroundPolarTwoNumerator410 vis (p.coeff 1) b42 +
          h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73
            q54 (p.coeff 1) lambda +
          h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22
            (p.coeff 0) lambda =
        Polynomial.C cepsilon * h0 ^ 2 ∧
      epsilonGroundPolarTwoNumerator410 vis (p.coeff 1) b42 =
        h0 * (Polynomial.C cepsilon * h0 -
          epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
            (p.coeff 1) lambda -
          h0 * epsilonGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
            lambda) ∧
      (16384 : k[X]) * b42 - (30720 : k[X]) * (p.coeff 1) ^ 2 =
        h0 * ((8 : k[X]) * Polynomial.C cepsilon * h0 +
          (448 : k[X]) * p.coeff 1 * (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda) -
          (8 : k[X]) * epsilonGroundPolarOneNumerator410 t2 a22 s22
            vis w73 q54 (p.coeff 1) lambda -
          (8 : k[X]) * h0 * epsilonGroundRegularNumerator410 t2 a22
            s22 (p.coeff 0) lambda) ∧
      ueps = (448 : k[X]) * Polynomial.C cbeta * p.coeff 1 +
          (4096 : k[X]) * Polynomial.C calpha * p.coeff 1 * t2 -
          (23040 : k[X]) * Polynomial.C lambda * p.coeff 1 * a22 +
          (30720 : k[X]) * p.coeff 1 * a22 * t2 -
          (2880 : k[X]) * Polynomial.C lambda * p.coeff 1 * t2 ^ 2 -
          (2560 : k[X]) * p.coeff 1 * t2 ^ 3 +
          h0 * ((8 : k[X]) * Polynomial.C cepsilon +
            (5 : k[X]) * Polynomial.C cdelta * t2 +
            (48 : k[X]) * Polynomial.C cgamma * t2 ^ 2 +
            (192 : k[X]) * Polynomial.C cgamma * a22 +
            (336 : k[X]) * Polynomial.C cbeta * a22 * t2 -
            (14 : k[X]) * Polynomial.C cbeta * t2 ^ 3 +
            (4096 : k[X]) * Polynomial.C calpha * p.coeff 0 +
            (2048 : k[X]) * Polynomial.C calpha * a22 ^ 2 +
            (61440 : k[X]) * p.coeff 0 * a22 -
            (23040 : k[X]) * Polynomial.C lambda * p.coeff 0 * t2 +
            (15360 : k[X]) * p.coeff 0 * t2 ^ 2 +
            (5120 : k[X]) * a22 ^ 3 -
            (2880 : k[X]) * Polynomial.C lambda * a22 ^ 2 * t2 -
            (3840 : k[X]) * a22 ^ 2 * t2 ^ 2 +
            (720 : k[X]) * Polynomial.C lambda * a22 * t2 ^ 3 +
            (960 : k[X]) * a22 * t2 ^ 4 -
            (63 : k[X]) * Polynomial.C lambda * t2 ^ 5 -
            (80 : k[X]) * t2 ^ 6) ∧
      (16384 : k[X]) * b42 - (30720 : k[X]) * (p.coeff 1) ^ 2 =
        h0 * ueps ∧
      v1 - (8192 : k[X]) *
          ((1200 : k[X]) * (p.coeff 1) ^ 2 * a22 * t2 +
            (2400 : k[X]) * (p.coeff 1) ^ 2 * t2 ^ 3 +
            (1080 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 *
              a22 -
            (1575 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 *
              t2 ^ 2 -
            (80 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 * t2 +
            (1536 : k[X]) * a22 * b31 -
            (960 : k[X]) * b31 * t2 ^ 2 +
            (1024 : k[X]) * q.coeff 2 * t2) =
        h0 * (v2 - (6400 : k[X]) * p.coeff 1 * t2 *
            (Polynomial.C cdelta -
              deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) -
          p.coeff 1 *
              ((245760 : k[X]) * a22 + (30720 : k[X]) * t2 ^ 2) *
            (Polynomial.C cgamma -
              gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) -
          (286720 : k[X]) * p.coeff 1 * a22 * t2 *
            (Polynomial.C cbeta -
              betaGroundRegularNumerator410 t2 a22 s22 lambda) -
          ((1280 : k[X]) * a22 * t2 - (480 : k[X]) * t2 ^ 3) *
            ueps) ∧
      (8192 : k[X]) * w1 + (512 : k[X]) *
          ((8 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 * a22 +
            (63 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 *
              a22 * t2 +
            (270 : k[X]) * (p.coeff 1) ^ 2 * a22 * t2 ^ 2 +
            (8 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 *
              t2 ^ 2 -
            (135 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 *
              t2 ^ 3 +
            (150 : k[X]) * (p.coeff 1) ^ 2 * t2 ^ 4 -
            (64 : k[X]) * a22 * q.coeff 2 +
            (96 : k[X]) * a22 * b31 * t2 +
            (32 : k[X]) * q.coeff 2 * t2 ^ 2 -
            (32 : k[X]) * b31 * t2 ^ 3) =
        h0 * ((8192 : k[X]) * w2 -
          (20 : k[X]) * p.coeff 1 * (a22 - t2 ^ 2) *
            (Polynomial.C cdelta -
              deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) +
          (192 : k[X]) * p.coeff 1 * t2 * ((3 : k[X]) * a22 + t2 ^ 2) *
            (Polynomial.C cgamma -
              gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) -
          (56 : k[X]) * p.coeff 1 *
              ((32 : k[X]) * p.coeff 0 + (8 : k[X]) * a22 ^ 2 -
                (25 : k[X]) * a22 * t2 ^ 2 + t2 ^ 4) *
            (Polynomial.C cbeta -
              betaGroundRegularNumerator410 t2 a22 s22 lambda) -
          (-(4 : k[X]) * p.coeff 0 + (2 : k[X]) * a22 ^ 2 -
              (4 : k[X]) * a22 * t2 ^ 2 + t2 ^ 4) * ueps) ∧
      (derivative b42).eval a = 0 ∧
      (2048 : k) * (derivative (derivative b42)).eval a -
          (7168 : k) * (derivative (p.coeff 1)).eval a *
            (derivative vis).eval a +
          (10240 : k) * ((derivative (p.coeff 1)).eval a) ^ 2 =
        (2 : k) * (derivative h0).eval a *
          (cepsilon * (derivative h0).eval a -
            (derivative (epsilonGroundPolarOneNumerator410 t2 a22 s22
                vis w73 q54 (p.coeff 1) lambda)).eval a -
            (derivative h0).eval a *
              (epsilonGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                  lambda).eval a) := by
  obtain ⟨calpha, cbeta, cgamma, cdelta, ctheta, c, v1, v2, v3, w1, w2,
    w3, hpin, hsolve, hpowT, htw1, htw2, htw3, htwc, hpowI, hiw1, hiw2,
    hiw3, hiwc, hTglobal, hIglobal, ha1, hvis0, hw730, hq540, hb420,
    hb310, hb20, hv10, hw10, hv2tie, hw2tie, hrootS, hTroot, hIroot,
    hkelP, hcombo, hbr, hbpin, hbsolve, hbalpha, hbtheta, hbiota,
    hbderiv, hbderivA, hgpin, hgsolve, hgalpha, hw73B, hw73F, hgiota,
    hgderiv, hw73deriv, hdpin, hdsolve, hdalpha, hq54BG, hq54F,
    hthetaP2, hiotaP2, hdderiv, hq54deriv⟩ :=
    nonzeroFace410_deltaGroundBridgePacket p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 a hp hq hh0 hH hp4 hq10 hN hD hp3 hp2
      hq8 hq7 hq6 hq5 hq4 hq3 hroot hT hU hW hV hX hY
  obtain ⟨cepsilon, hepin⟩ :=
    nonzeroFace410_epsilonResidualPowerRelation p q H h0 j lambda t2
      a22 s22 vis w73 q54 b42 hp hq hh0 hH hp4 hq10 hN hD hp3 hp2 hq8
      hq7 hq6 hq5 hq4
  have hesolve := epsilonGroundPin_solvePolarTwo410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 lambda cepsilon hepin
  have hb42B := b42GroundPin_betaEliminated410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 lambda cbeta cepsilon hbpin hepin
  have hb42pin := b42GroundPin_fullyEliminated410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 lambda calpha cbeta cgamma
    cdelta cepsilon hpin hbpin hgpin hdpin hepin
  have hthetaE := thetaSecondPeel_epsilonLoaded410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) v1 v2 _ lambda
    calpha cbeta cgamma cdelta hpin hbpin hgpin hdpin hb42pin htw2
  have hiotaE := iotaSecondPeel_epsilonLoaded410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) w1 w2 _ lambda
    calpha cbeta cgamma cdelta hpin hbpin hgpin hdpin hb42pin hiw2
  have hb42kill := epsilonPin_rootDerivativeKill410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 lambda cepsilon a hepin hroot
    hvis0 hw730 hq540 ha1
  have h2tie := epsilonPin_rootSecondDerivativeTie410 h0 t2 a22 s22
    vis w73 q54 (p.coeff 1) (p.coeff 0) b42 lambda cepsilon a hepin
    hroot hvis0 hw730 hq540 ha1
  exact ⟨calpha, cbeta, cgamma, cdelta, cepsilon, ctheta, c, v1, v2,
    v3, w1, w2, w3, _, hpin, hsolve, hpowT, htw1, htw2, htw3, htwc,
    hpowI, hiw1, hiw2, hiw3, hiwc, hTglobal, hIglobal, ha1, hvis0,
    hw730, hq540, hb420, hb310, hb20, hv10, hw10, hv2tie, hw2tie,
    hrootS, hTroot, hIroot, hkelP, hcombo, hbr, hbpin, hbsolve,
    hbalpha, hbtheta, hbiota, hbderiv, hbderivA, hgpin, hgsolve,
    hgalpha, hw73B, hw73F, hgiota, hgderiv, hw73deriv, hdpin, hdsolve,
    hdalpha, hq54BG, hq54F, hthetaP2, hiotaP2, hdderiv, hq54deriv,
    hepin, hesolve, hb42B, rfl, hb42pin, hthetaE, hiotaE, hb42kill,
    h2tie⟩

end NonzeroEpsilonGroundBridge410

#print axioms epsilonDefect_eq_cleared410
#print axioms epsilonGroundPin_solvePolarTwo410
#print axioms epsilonGroundPin_rootEval410
#print axioms epsilonGroundPin_rootEval_reDerivesW410
#print axioms b42GroundPin_betaEliminated410
#print axioms b42GroundPin_fullyEliminated410
#print axioms thetaSecondPeel_epsilonLoaded410
#print axioms iotaSecondPeel_epsilonLoaded410
#print axioms epsilonPolarOne_rootEval410
#print axioms epsilonPin_rootDerivativeKill410
#print axioms epsilonPin_rootSecondDerivativeTie410
#print axioms nonzeroFace410_epsilonResidualPowerRelation
#print axioms nonzeroFace410_epsilonGroundBridgePacket

end Max11DegreeRoutes
