import Fable410ScaleTwoEpsilonGroundBridgeScratch

/-! # Zeta ground bridge for the normalized `(4,10)` nonzero source

The epsilon ground bridge pinned the row-`7` ground first integral `ε`
at exact order `-2` and produced the first five-ground-constant link.
The next ground first integral is `ζ = U - (7/4) β C - (3/2) γ B -
(5/4) δ A - (15/4) B C - (15/16) A² B - (45/16) L A C - (45/32) L B² -
(15/128) L A³ - 2 α A B - (21/32) β A²` (row `6`, `zetaResidual410`,
seventh face).  On the thirteenth-face jet it sits at exact order `-2`
and is the FIRST ground clearing seeing the order-`-1` letter `b₃₁`.

First, the clearing (`zetaDefect_eq_cleared410`): `131072 h² ζ` splits
as the order-`-2` polar block `131072 (b₃₁ - b₄₂ t₂) - 143360 p₁² t₂ -
129024 λ p₁² + 401408 p₁ t₂ q₇₆ - 196608 p₁ w₇₃`, plus `h` times the
order-`-1` block (every monomial carries one of the root-vanishing
letters `q₇₆, w₇₃, q₅₄, p₁`), plus `h²` times the regular block.

Second, the literal-source trace: the seventh-face power relation pins
the row-`6` integral globally (`nonzeroFace410_seventhDefectPowerRelation`,
weight `23`); substituting the thirteenth-face jet forms and cancelling
`h₀²¹` gives the second order-`-2` ground pin of the lane
(`nonzeroFace410_zetaResidualPowerRelation`): `polar₂ + h₀ · polar₁ +
h₀² · (regular) = C c_ζ h₀²`.  Its first `h`-adic peel step is exact
(`zetaGroundPin_solvePolarTwo410`), and the root evaluation combined
with the `β`, `γ`, `ε` pins RE-DERIVES the thirteenth-face jet
hypothesis `hX` from the literal source
(`zetaGroundPin_rootEval_reDerivesX410`): `64 b₃₁(a) =
15 p₁(a)² (4 t₂(a) - 3 λ)` — rows `10`, `9`, `7` and `6` alone force
it.

Third, the eliminations.  The `ε`-pin tie kills `b₄₂ t₂`, the `γ` pin
kills `w₇₃`, and the `β` pin kills the `q₇₆` cross-term
(`b31GroundPin_epsilonEliminated410`), collapsing the polar-`2` block
to `131072 b₃₁ - 122880 p₁² t₂ + 92160 λ p₁²` — `2048` times the
LITERAL polynomial lift of the jet tie `hX`.  Loading all six pins
(`δ` with cofactor `h₀ (40 a₂₂ + 5 t₂²)`, `γ` with `1536 p₁ +
h₀ (768 a₂₂ t₂ - 64 t₂³)`, `β` with `2688 p₁ t₂ + h₀ (3584 p₀ +
1344 a₂₂² - 336 a₂₂ t₂² + 35 t₂⁴)`, `ε` with `64 t₂`, `α` with
`h₀ (32768 p₁ a₂₂ + 32768 p₀ h₀ t₂)`) kills every order-`-1` letter
and `s₂₂` entirely (`b31GroundPin_fullyEliminated410`):
`131072 b₃₁ - 122880 p₁² t₂ + 92160 λ p₁² = h₀ (F₁ + h₀ F₂)` with
`F₁ = 128 p₁ (3840 p₀ + 960 a₂₂² + 256 c_α a₂₂ - 360 λ a₂₂ t₂ -
480 a₂₂ t₂² + 21 c_β t₂ + 12 c_γ + 45 λ t₂³ + 60 t₂⁴)` linear in `p₁`
and `F₂` carrying `c_ζ + 64 c_ε t₂ + 5 c_δ t₂² + 40 c_δ a₂₂ + ⋯` —
the first SIX-ground-constant link of the lane.

Fourth, the combination with the terminal packet: the `b₃₁` pin
eliminates `b₃₁` from the `ε`-loaded second peel steps of BOTH towers
(`thetaSecondPeel_zetaLoaded410`, `iotaSecondPeel_zetaLoaded410`) —
only the order-`-2` letter `q₂` survives polar-side, and in the `θ`
peel the elimination cancels the `λ p₁² a₂₂` block EXACTLY: the `θ`
polar side loses its pure-`λ a₂₂` dependence.

The sharpest `ζ`-loaded root results are one and two derivatives
deeper.  Since the solved polar-`2` cofactor itself vanishes at the
root, the first derivative of the pin at the root is CONSTANT-FREE
(`zetaPin_rootDerivativeKill410`): `b₃₁'(a) = t₂(a) b₄₂'(a)`, and
combined with the `ε` kill `b₄₂'(a) = 0` this forces `b₃₁'(a) = 0`
(`zetaPin_rootDerivativeKillFull410`) — `b₃₁` vanishes doubly at the
root, the SECOND unconditional derivative-level kill of the nonzero
face.  The honest residual moves to the second derivative
(`zetaPin_rootSecondDerivativeTie410`): `131072 b₃₁''(a) -
131072 t₂(a) b₄₂''(a) - 262144 t₂'(a) b₄₂'(a) - 286720 t₂(a) p₁'(a)² -
258048 λ p₁'(a)² + 802816 p₁'(a) t₂(a) q₇₆'(a) -
393216 p₁'(a) w₇₃'(a) = 2 h₀'(a) (c_ζ h₀'(a) - polar₁'(a) -
h₀'(a) reg(a))` — the second second-derivative-level residual of the
lane, pinning `c_ζ` against `h₀'(a)²`.

Nothing here closes the face or a branch: `c_ζ` is free, so the pin
eliminates no configuration; no root branch is forced (both factors of
every peeled block already vanish at the root); `t₂(a), a₂₂(a),
s₂₂(a), q₁(a), q₀(a), c_α, c_β, c_γ, c_δ, c_ε, c_ζ, c_θ, c, j,
p₀'(a), q₀'(a), p₁'(a), q₇₆'(a), w₇₃'(a), t₂'(a), b₄₂''(a), b₃₁''(a)`
remain free or tied-not-determined; the ground constant `η` (row `5`,
next: its eighth-defect clearing `localClearedEighthDefect410 =
C · h₀²⁶` sits at exact order `-2`, polar-`2` block `32768 q₂ -
24576 b₃₁ t₂ + 24576 b₄₂ t₂² - 32768 a₂₂ b₄₂ - 153600 p₁² a₂₂ +
69120 λ p₁² t₂ + 49152 p₁² s₂₂ - 76800 p₁² t₂² + 86016 p₁ a₂₂ q₇₆ -
107520 p₁ t₂² q₇₆ + 73728 p₁ t₂ w₇₃ - 40960 p₁ q₅₄` — the first
ground clearing seeing `q₂`, and the first with polar-level `p₁² s₂₂`)
stays uncleared.  No total-degree or twice-prime theorem is used, and
the aligned face `N = 0` is not touched.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Exact order-`-2` clearing of `ζ` on the thirteenth-face jet -/

section ZetaGroundClearing410

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- Order-`-2` (polar) numerator block of the cleared `ζ` on the
thirteenth-face jet: the second ground residue block at depth two, and
the first ground block seeing `b₃₁`.  It carries the polar-level
cross-terms `b₄₂ t₂` and `p₁ q₇₆`. -/
def zetaGroundPolarTwoNumerator410 (t2 vis w73 a1 b42 b31 : F[X])
    (lambda : F) : F[X] :=
  (131072 : F[X]) * b31 - (131072 : F[X]) * b42 * t2 -
    (143360 : F[X]) * a1 ^ 2 * t2 -
    (129024 : F[X]) * Polynomial.C lambda * a1 ^ 2 +
    (401408 : F[X]) * a1 * t2 * vis - (196608 : F[X]) * a1 * w73

/-- Order-`-1` numerator block of the cleared `ζ` on the
thirteenth-face jet.  Every monomial carries one of the root-vanishing
letters `q₇₆, w₇₃, q₅₄, p₁`, so the whole block vanishes at the root
of `h₀`. -/
def zetaGroundPolarOneNumerator410
    (t2 a22 s22 vis w73 q54 a1 a0 : F[X]) (lambda : F) : F[X] :=
  (1047200 : F[X]) * a1 * t2 ^ 4 + (172480 : F[X]) * t2 ^ 4 * vis -
    (443520 : F[X]) * Polynomial.C lambda * a1 * t2 ^ 3 -
    (157696 : F[X]) * t2 ^ 3 * w73 -
    (591360 : F[X]) * a1 * a22 * t2 ^ 2 -
    (551936 : F[X]) * a22 * t2 ^ 2 * vis -
    (630784 : F[X]) * a1 * t2 ^ 2 * s22 +
    (143360 : F[X]) * t2 ^ 2 * q54 +
    (709632 : F[X]) * Polynomial.C lambda * a1 * a22 * t2 +
    (344064 : F[X]) * a22 * t2 * w73 -
    (788480 : F[X]) * a1 * a22 ^ 2 + (200704 : F[X]) * a22 ^ 2 * vis +
    (458752 : F[X]) * a1 * a22 * s22 - (163840 : F[X]) * a22 * q54 +
    (573440 : F[X]) * a0 * a1 - (229376 : F[X]) * a0 * vis

/-- Regular (order-`0`) numerator block of the cleared `ζ` on the
thirteenth-face jet.  It is linear in `s₂₂` with the sextic cofactor
`-187264 t₂⁵ + 788480 a₂₂ t₂³ - 630784 a₂₂² t₂ + 458752 p₀ t₂`. -/
def zetaGroundRegularNumerator410 (t2 a22 s22 a0 : F[X])
    (lambda : F) : F[X] :=
  (288420 : F[X]) * t2 ^ 7 -
    (100947 : F[X]) * Polynomial.C lambda * t2 ^ 6 -
    (1287440 : F[X]) * a22 * t2 ^ 5 - (187264 : F[X]) * t2 ^ 5 * s22 +
    (526680 : F[X]) * Polynomial.C lambda * a22 * t2 ^ 4 +
    (985600 : F[X]) * a22 ^ 2 * t2 ^ 3 +
    (788480 : F[X]) * a22 * t2 ^ 3 * s22 -
    (788480 : F[X]) * a0 * t2 ^ 3 -
    (665280 : F[X]) * Polynomial.C lambda * a22 ^ 2 * t2 ^ 2 +
    (354816 : F[X]) * Polynomial.C lambda * a0 * t2 ^ 2 +
    (394240 : F[X]) * a22 ^ 3 * t2 -
    (630784 : F[X]) * a22 ^ 2 * t2 * s22 -
    (286720 : F[X]) * a0 * a22 * t2 + (458752 : F[X]) * a0 * t2 * s22 +
    (118272 : F[X]) * Polynomial.C lambda * a22 ^ 3 -
    (258048 : F[X]) * Polynomial.C lambda * a0 * a22

set_option maxHeartbeats 25600000 in
/-- Exact order-`-2` clearing of the seventh-face residual `ζ` on the
thirteenth-face jet substitutions: `131072 h² ζ` is the polar-`2`
residue block plus `h` times the polar-`1` block plus `h²` times the
regular block, so `ζ` sits at exact order `-2` — the first ground
clearing seeing `b₃₁`. -/
theorem zetaDefect_eq_cleared410
    (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b9 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * (h ^ 3 * t2) * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (131072 : F) * h ^ 2 *
        zetaResidual410
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
          (depressedS410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54))
          (depressedU410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
            (h ^ 2 * b42) (h * b31)) =
      ((131072 : F) * b31 - (131072 : F) * b42 * t2 -
          (143360 : F) * a1 ^ 2 * t2 - (129024 : F) * lambda * a1 ^ 2 +
          (401408 : F) * a1 * t2 * vis - (196608 : F) * a1 * w73) +
        h * ((1047200 : F) * a1 * t2 ^ 4 +
          (172480 : F) * t2 ^ 4 * vis -
          (443520 : F) * lambda * a1 * t2 ^ 3 -
          (157696 : F) * t2 ^ 3 * w73 -
          (591360 : F) * a1 * a22 * t2 ^ 2 -
          (551936 : F) * a22 * t2 ^ 2 * vis -
          (630784 : F) * a1 * t2 ^ 2 * s22 +
          (143360 : F) * t2 ^ 2 * q54 +
          (709632 : F) * lambda * a1 * a22 * t2 +
          (344064 : F) * a22 * t2 * w73 -
          (788480 : F) * a1 * a22 ^ 2 + (200704 : F) * a22 ^ 2 * vis +
          (458752 : F) * a1 * a22 * s22 - (163840 : F) * a22 * q54 +
          (573440 : F) * a0 * a1 - (229376 : F) * a0 * vis) +
        h ^ 2 * ((288420 : F) * t2 ^ 7 -
          (100947 : F) * lambda * t2 ^ 6 -
          (1287440 : F) * a22 * t2 ^ 5 - (187264 : F) * t2 ^ 5 * s22 +
          (526680 : F) * lambda * a22 * t2 ^ 4 +
          (985600 : F) * a22 ^ 2 * t2 ^ 3 +
          (788480 : F) * a22 * t2 ^ 3 * s22 -
          (788480 : F) * a0 * t2 ^ 3 -
          (665280 : F) * lambda * a22 ^ 2 * t2 ^ 2 +
          (354816 : F) * lambda * a0 * t2 ^ 2 +
          (394240 : F) * a22 ^ 3 * t2 -
          (630784 : F) * a22 ^ 2 * t2 * s22 -
          (286720 : F) * a0 * a22 * t2 +
          (458752 : F) * a0 * t2 * s22 +
          (118272 : F) * lambda * a22 ^ 3 -
          (258048 : F) * lambda * a0 * a22) := by
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
  have hS :
      depressedS410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) =
        ((252 : F) * t2 ^ 5 * h - 63 * lambda * t2 ^ 4 * h -
            224 * t2 ^ 3 * s22 * h + 336 * t2 ^ 2 * vis -
            384 * t2 * w73 + 256 * q54) / (256 * h) := by
    rw [depressedS410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) lambda hh hN]
    field_simp [hh]
  have hU :
      depressedU410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
          (h ^ 2 * b42) (h * b31) =
        ((90 : F) * t2 ^ 7 * h ^ 2 - 21 * lambda * t2 ^ 6 * h ^ 2 -
            112 * t2 ^ 5 * s22 * h ^ 2 + 280 * t2 ^ 4 * vis * h -
            640 * t2 ^ 3 * w73 * h + 1280 * t2 ^ 2 * q54 * h -
            2048 * t2 * b42 + 2048 * b31) / (2048 * h ^ 2) := by
    rw [depressedU410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) (h ^ 2 * b42)
      (h * b31) lambda hh hN]
    field_simp [hh]
  simp only [zetaResidual410, alphaResidual410, betaResidual410,
    gammaResidual410, deltaResidual410, hL, hA, hB, hC, hP, hQ, hR,
    hS, hU]
  field_simp [hh]
  ring

/-- The `ζ` ground pin solves the order-`-2` polar block exactly: the
polar-`2` residue block is `h₀` times the explicit ground-loaded
cofactor — the first peel step of the order-`-2` pin, in factored
`h`-adic quotient form. -/
theorem zetaGroundPin_solvePolarTwo410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 : F[X])
    (lambda czeta : F)
    (hpin : zetaGroundPolarTwoNumerator410 t2 vis w73 a1 b42 b31
        lambda +
        h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * zetaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C czeta * h0 ^ 2) :
    zetaGroundPolarTwoNumerator410 t2 vis w73 a1 b42 b31 lambda =
      h0 * (Polynomial.C czeta * h0 -
        zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0
          lambda -
        h0 * zetaGroundRegularNumerator410 t2 a22 s22 a0 lambda) := by
  linear_combination hpin

/-- Root evaluation of the `ζ` ground pin: the polar-`2` residue block
vanishes at the root of `h₀`. -/
theorem zetaGroundPin_rootEval410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 : F[X])
    (lambda czeta : F) (a : F)
    (hpin : zetaGroundPolarTwoNumerator410 t2 vis w73 a1 b42 b31
        lambda +
        h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * zetaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C czeta * h0 ^ 2)
    (hroot : h0.eval a = 0) :
    (131072 : F) * b31.eval a -
        (131072 : F) * b42.eval a * t2.eval a -
        (143360 : F) * (a1.eval a) ^ 2 * t2.eval a -
        (129024 : F) * lambda * (a1.eval a) ^ 2 +
        (401408 : F) * a1.eval a * t2.eval a * vis.eval a -
        (196608 : F) * a1.eval a * w73.eval a = 0 := by
  have h := congrArg (fun r : F[X] => r.eval a) hpin
  simp only [zetaGroundPolarTwoNumerator410, pow_two, eval_add,
    eval_sub, eval_mul, eval_C, eval_ofNat, hroot, zero_mul, mul_zero,
    add_zero] at h
  linear_combination h

/-- Root evaluation of the `ζ` ground pin combined with the `β`, `γ`
and `ε` ground pins: the thirteenth-face tie `64 b₃₁(a) =
15 p₁(a)² (4 t₂(a) - 3 λ)` (the jet hypothesis `hX`) is forced by the
literal source through the row-`10`, row-`9`, row-`7` and row-`6`
integrals alone. -/
theorem zetaGroundPin_rootEval_reDerivesX410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 : F[X])
    (lambda cbeta cgamma cepsilon czeta : F) (a : F)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0)
    (hepin : epsilonGroundPolarTwoNumerator410 vis a1 b42 +
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          a1 lambda +
        h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22 a0
          lambda =
      Polynomial.C cepsilon * h0 ^ 2)
    (hzpin : zetaGroundPolarTwoNumerator410 t2 vis w73 a1 b42 b31
        lambda +
        h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * zetaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C czeta * h0 ^ 2)
    (hroot : h0.eval a = 0) :
    (64 : F) * b31.eval a =
      (15 : F) * (a1.eval a) ^ 2 *
        ((4 : F) * t2.eval a - (3 : F) * lambda) := by
  have hbe := betaGroundPin_rootEval410 h0 t2 a22 s22 vis a1 lambda
    cbeta a hbpin hroot
  have hge := gammaGroundPin_rootEval410 h0 t2 a22 s22 vis w73 a1 a0
    lambda cgamma a hgpin hroot
  have hee := epsilonGroundPin_rootEval410 h0 t2 a22 s22 vis w73 q54
    a1 a0 b42 lambda cepsilon a hepin hroot
  have hze := zetaGroundPin_rootEval410 h0 t2 a22 s22 vis w73 q54 a1
    a0 b42 b31 lambda czeta a hzpin hroot
  linear_combination ((1 : F) / 2048) * hze +
    ((1 : F) / 32) * t2.eval a * hee +
    ((3 : F) / 4) * a1.eval a * hge +
    ((21 : F) / 16) * a1.eval a * t2.eval a * hbe

/-- The `b₃₁` pin, `ε`-eliminated: the `ε`-pin tie kills the polar-`2`
cross-term `b₄₂ t₂`, the `γ` pin kills `w₇₃`, and the `β` pin kills
the `q₇₆` cross-term, collapsing the `ζ` polar block to
`131072 b₃₁ - 122880 p₁² t₂ + 92160 λ p₁²` — `2048` times the LITERAL
polynomial lift of the jet tie `hX`: the root tie of the thirteenth
face is the root shadow of this global pin. -/
theorem b31GroundPin_epsilonEliminated410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 u : F[X])
    (lambda cbeta cgamma czeta : F)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0)
    (hb42 : (16384 : F[X]) * b42 - (30720 : F[X]) * a1 ^ 2 = h0 * u)
    (hzpin : zetaGroundPolarTwoNumerator410 t2 vis w73 a1 b42 b31
        lambda +
        h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * zetaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C czeta * h0 ^ 2) :
    (131072 : F[X]) * b31 - (122880 : F[X]) * a1 ^ 2 * t2 +
        (92160 : F[X]) * Polynomial.C lambda * a1 ^ 2 =
      h0 * (Polynomial.C czeta * h0 + (8 : F[X]) * t2 * u +
        (1536 : F[X]) * a1 * (Polynomial.C cgamma -
          gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda) -
        (896 : F[X]) * a1 * t2 * (Polynomial.C cbeta -
          betaGroundRegularNumerator410 t2 a22 s22 lambda) -
        zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0
          lambda -
        h0 * zetaGroundRegularNumerator410 t2 a22 s22 a0 lambda) := by
  have hb := hbpin
  simp only [betaGroundPolarNumerator410] at hb
  have hg := hgpin
  simp only [gammaGroundPolarNumerator410] at hg
  have hz := hzpin
  simp only [zetaGroundPolarTwoNumerator410] at hz
  linear_combination hz + (8 : F[X]) * t2 * hb42 +
    (1536 : F[X]) * a1 * hg - (896 : F[X]) * a1 * t2 * hb

set_option maxHeartbeats 6400000 in
/-- The fully eliminated `b₃₁` pin: the `ε` pin kills the `b₄₂ t₂`
cross-term, the `δ`, `γ`, `β` pins kill every order-`-1` letter at the
`h₀`-level, and the `α` pin eliminates `s₂₂` entirely —
`131072 b₃₁ - 122880 p₁² t₂ + 92160 λ p₁²` is pinned against `t₂,
a₂₂, p₀, c_α, c_β, c_γ, c_δ, c_ε, c_ζ` only, the first global
SIX-ground-constant link of the lane. -/
theorem b31GroundPin_fullyEliminated410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 : F[X])
    (lambda calpha cbeta cgamma cdelta cepsilon czeta : F)
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
      Polynomial.C cepsilon * h0 ^ 2)
    (hzpin : zetaGroundPolarTwoNumerator410 t2 vis w73 a1 b42 b31
        lambda +
        h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * zetaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C czeta * h0 ^ 2) :
    (131072 : F[X]) * b31 - (122880 : F[X]) * a1 ^ 2 * t2 +
        (92160 : F[X]) * Polynomial.C lambda * a1 ^ 2 =
      h0 * ((491520 : F[X]) * a0 * a1 +
        (122880 : F[X]) * a1 * a22 ^ 2 +
        (32768 : F[X]) * Polynomial.C calpha * a1 * a22 -
        (46080 : F[X]) * Polynomial.C lambda * a1 * a22 * t2 -
        (61440 : F[X]) * a1 * a22 * t2 ^ 2 +
        (2688 : F[X]) * Polynomial.C cbeta * a1 * t2 +
        (1536 : F[X]) * Polynomial.C cgamma * a1 +
        (5760 : F[X]) * Polynomial.C lambda * a1 * t2 ^ 3 +
        (7680 : F[X]) * a1 * t2 ^ 4 +
        h0 * (Polynomial.C czeta +
          (64 : F[X]) * Polynomial.C cepsilon * t2 +
          (5 : F[X]) * Polynomial.C cdelta * t2 ^ 2 +
          (40 : F[X]) * Polynomial.C cdelta * a22 -
          (64 : F[X]) * Polynomial.C cgamma * t2 ^ 3 +
          (768 : F[X]) * Polynomial.C cgamma * a22 * t2 +
          (35 : F[X]) * Polynomial.C cbeta * t2 ^ 4 -
          (336 : F[X]) * Polynomial.C cbeta * a22 * t2 ^ 2 +
          (1344 : F[X]) * Polynomial.C cbeta * a22 ^ 2 +
          (3584 : F[X]) * Polynomial.C cbeta * a0 +
          (32768 : F[X]) * Polynomial.C calpha * a0 * t2 +
          (245760 : F[X]) * a0 * a22 * t2 -
          (184320 : F[X]) * Polynomial.C lambda * a0 * a22 -
          (23040 : F[X]) * Polynomial.C lambda * a0 * t2 ^ 2 -
          (20480 : F[X]) * a0 * t2 ^ 3 -
          (7680 : F[X]) * Polynomial.C lambda * a22 ^ 3 -
          (20480 : F[X]) * a22 ^ 3 * t2 +
          (8640 : F[X]) * Polynomial.C lambda * a22 ^ 2 * t2 ^ 2 +
          (15360 : F[X]) * a22 ^ 2 * t2 ^ 3 -
          (2520 : F[X]) * Polynomial.C lambda * a22 * t2 ^ 4 -
          (3840 : F[X]) * a22 * t2 ^ 5 +
          (231 : F[X]) * Polynomial.C lambda * t2 ^ 6 +
          (320 : F[X]) * t2 ^ 7)) := by
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
  have hz := hzpin
  simp only [zetaGroundPolarTwoNumerator410,
    zetaGroundPolarOneNumerator410,
    zetaGroundRegularNumerator410] at hz
  linear_combination hz + (64 : F[X]) * t2 * he +
    h0 * ((40 : F[X]) * a22 + (5 : F[X]) * t2 ^ 2) * hd +
    ((1536 : F[X]) * a1 +
      h0 * ((768 : F[X]) * a22 * t2 - (64 : F[X]) * t2 ^ 3)) * hg +
    ((2688 : F[X]) * a1 * t2 +
      h0 * ((3584 : F[X]) * a0 + (1344 : F[X]) * a22 ^ 2 -
        (336 : F[X]) * a22 * t2 ^ 2 + (35 : F[X]) * t2 ^ 4)) * hb +
    h0 * ((32768 : F[X]) * a1 * a22 +
      (32768 : F[X]) * a0 * h0 * t2) * ha

set_option maxHeartbeats 3200000 in
/-- `ζ`-loaded second `θ` peel: the `b₃₁` pin eliminates the letter
`b₃₁` from the `ε`-loaded order-`-2` theta block — only the
order-`-2` letter `q₂` survives on the polar side, and the
elimination cancels the `λ p₁² a₂₂` block EXACTLY. -/
theorem thetaSecondPeel_zetaLoaded410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 v1 v2 u uz : F[X])
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
    (hb31 : (131072 : F[X]) * b31 - (122880 : F[X]) * a1 ^ 2 * t2 +
        (92160 : F[X]) * Polynomial.C lambda * a1 ^ 2 =
      h0 * uz)
    (hpeel : v1 + thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda =
      h0 * v2) :
    v1 - (8192 : F[X]) *
        ((2640 : F[X]) * a1 ^ 2 * a22 * t2 +
          (1500 : F[X]) * a1 ^ 2 * t2 ^ 3 -
          (900 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 ^ 2 -
          (80 : F[X]) * Polynomial.C calpha * a1 ^ 2 * t2 +
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
        ((1280 : F[X]) * a22 * t2 - (480 : F[X]) * t2 ^ 3) * u +
        ((96 : F[X]) * a22 - (60 : F[X]) * t2 ^ 2) * uz) := by
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
    ((1280 : F[X]) * a22 * t2 - (480 : F[X]) * t2 ^ 3) * hb42 +
    ((96 : F[X]) * a22 - (60 : F[X]) * t2 ^ 2) * hb31

set_option maxHeartbeats 3200000 in
/-- `ζ`-loaded second `ι` peel (scaled by `32`): the `b₃₁` pin
eliminates the letter `b₃₁` from the `ε`-loaded order-`-2` iota block
— only `q₂` survives on the polar side of BOTH towers. -/
theorem iotaSecondPeel_zetaLoaded410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 w1 w2 u uz : F[X])
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
    (hb31 : (131072 : F[X]) * b31 - (122880 : F[X]) * a1 ^ 2 * t2 +
        (92160 : F[X]) * Polynomial.C lambda * a1 ^ 2 =
      h0 * uz)
    (hpeel : w1 + iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        a0 b42 b31 b2 lambda =
      h0 * w2) :
    (65536 : F[X]) * w1 + (2048 : F[X]) *
        ((16 : F[X]) * Polynomial.C calpha * a1 ^ 2 * a22 -
          (9 : F[X]) * Polynomial.C lambda * a1 ^ 2 * a22 * t2 +
          (720 : F[X]) * a1 ^ 2 * a22 * t2 ^ 2 +
          (16 : F[X]) * Polynomial.C calpha * a1 ^ 2 * t2 ^ 2 -
          (225 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 ^ 3 +
          (240 : F[X]) * a1 ^ 2 * t2 ^ 4 -
          (128 : F[X]) * a22 * b2 +
          (64 : F[X]) * b2 * t2 ^ 2) =
      h0 * ((65536 : F[X]) * w2 -
        (160 : F[X]) * a1 * (a22 - t2 ^ 2) *
          (Polynomial.C cdelta -
            deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda) +
        (1536 : F[X]) * a1 * t2 * ((3 : F[X]) * a22 + t2 ^ 2) *
          (Polynomial.C cgamma -
            gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda) -
        (448 : F[X]) * a1 *
            ((32 : F[X]) * a0 + (8 : F[X]) * a22 ^ 2 -
              (25 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) *
          (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda) -
        (8 : F[X]) * (-(4 : F[X]) * a0 + (2 : F[X]) * a22 ^ 2 -
            (4 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) * u -
        ((3 : F[X]) * a22 * t2 - t2 ^ 3) * uz) := by
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
  linear_combination (65536 : F[X]) * hp -
    (160 : F[X]) * a1 * (a22 - t2 ^ 2) * hd +
    (1536 : F[X]) * a1 * t2 * ((3 : F[X]) * a22 + t2 ^ 2) * hg -
    (448 : F[X]) * a1 *
      ((32 : F[X]) * a0 + (8 : F[X]) * a22 ^ 2 -
        (25 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) * hb -
    (32768 : F[X]) * a1 ^ 2 * (a22 + t2 ^ 2) * ha -
    (8 : F[X]) * (-(4 : F[X]) * a0 + (2 : F[X]) * a22 ^ 2 -
      (4 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) * hb42 -
    ((3 : F[X]) * a22 * t2 - t2 ^ 3) * hb31

/-- Root evaluation of the `ζ` polar-`1` block: every monomial carries
one of the root-vanishing letters `q₇₆, w₇₃, q₅₄, p₁`, so the whole
block dies at the root. -/
theorem zetaPolarOne_rootEval410
    (t2 a22 s22 vis w73 q54 a1 a0 : F[X]) (lambda : F) (a : F)
    (hvis : vis.eval a = 0) (hw73 : w73.eval a = 0)
    (hq54 : q54.eval a = 0) (ha1 : a1.eval a = 0) :
    (zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0
        lambda).eval a = 0 := by
  simp only [zetaGroundPolarOneNumerator410, eval_add, eval_sub,
    eval_mul, eval_pow, eval_C, eval_ofNat, eval_neg, hvis, hw73,
    hq54, ha1, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    zero_sub, neg_zero]

/-- The constant-free `ζ` derivative tie: since the solved polar-`2`
cofactor itself vanishes at the root (the polar-`1` block dies there),
the derivative of the `ζ` pin at the root is constant-free —
`b₃₁'(a) = t₂(a) b₄₂'(a)`. -/
theorem zetaPin_rootDerivativeKill410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 : F[X])
    (lambda czeta : F) (a : F)
    (hzpin : zetaGroundPolarTwoNumerator410 t2 vis w73 a1 b42 b31
        lambda +
        h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * zetaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C czeta * h0 ^ 2)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (hw73 : w73.eval a = 0) (hq54 : q54.eval a = 0)
    (ha1 : a1.eval a = 0) (hb42 : b42.eval a = 0) :
    (derivative b31).eval a = t2.eval a * (derivative b42).eval a := by
  have hP1a := zetaPolarOne_rootEval410 t2 a22 s22 vis w73 q54 a1 a0
    lambda a hvis hw73 hq54 ha1
  have hs : zetaGroundPolarTwoNumerator410 t2 vis w73 a1 b42 b31
      lambda =
      Polynomial.C czeta * (h0 * h0) -
        h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda -
        h0 * (h0 * zetaGroundRegularNumerator410 t2 a22 s22 a0
          lambda) := by
    linear_combination hzpin
  have hd1 := congrArg (fun r : F[X] => derivative r) hs
  simp only [zetaGroundPolarTwoNumerator410, pow_two, derivative_add,
    derivative_sub, derivative_mul, derivative_ofNat, derivative_C,
    zero_mul, mul_zero, zero_add, add_zero] at hd1
  have heval := congrArg (fun r : F[X] => r.eval a) hd1
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_ofNat, hroot,
    hvis, hw73, ha1, hb42, hP1a, zero_mul, mul_zero, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero] at heval
  linear_combination ((1 : F) / 131072) * heval

/-- The exact `ζ` derivative kill: combining the constant-free `ζ`
derivative tie with the `ε` derivative kill `b₄₂'(a) = 0` forces
`b₃₁'(a) = 0` — `b₃₁` vanishes DOUBLY at the root of `h₀`, the second
unconditional derivative-level kill of the nonzero face. -/
theorem zetaPin_rootDerivativeKillFull410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 : F[X])
    (lambda cepsilon czeta : F) (a : F)
    (hepin : epsilonGroundPolarTwoNumerator410 vis a1 b42 +
        h0 * epsilonGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          a1 lambda +
        h0 ^ 2 * epsilonGroundRegularNumerator410 t2 a22 s22 a0
          lambda =
      Polynomial.C cepsilon * h0 ^ 2)
    (hzpin : zetaGroundPolarTwoNumerator410 t2 vis w73 a1 b42 b31
        lambda +
        h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * zetaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C czeta * h0 ^ 2)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (hw73 : w73.eval a = 0) (hq54 : q54.eval a = 0)
    (ha1 : a1.eval a = 0) :
    (derivative b31).eval a = 0 := by
  have hee := epsilonGroundPin_rootEval410 h0 t2 a22 s22 vis w73 q54
    a1 a0 b42 lambda cepsilon a hepin hroot
  have hb42a : b42.eval a = 0 := by
    linear_combination ((1 : F) / 2048) * hee +
      ((7 : F) / 4) * vis.eval a * ha1 -
      ((5 : F) / 2) * a1.eval a * ha1
  have h1 := zetaPin_rootDerivativeKill410 h0 t2 a22 s22 vis w73 q54
    a1 a0 b42 b31 lambda czeta a hzpin hroot hvis hw73 hq54 ha1 hb42a
  have h2 := epsilonPin_rootDerivativeKill410 h0 t2 a22 s22 vis w73
    q54 a1 a0 b42 lambda cepsilon a hepin hroot hvis hw73 hq54 ha1
  rw [h1, h2, mul_zero]

set_option maxHeartbeats 3200000 in
/-- Sharpest honest `ζ` residual, one derivative below the exact kill:
the second derivative of the `ζ` pin at the root ties `b₃₁''(a)`,
`b₄₂''(a)` and the derivative jet against `c_ζ` — the second
second-derivative-level residual of the lane, with `c_ζ` pinned
against `h₀'(a)²`. -/
theorem zetaPin_rootSecondDerivativeTie410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 : F[X])
    (lambda czeta : F) (a : F)
    (hzpin : zetaGroundPolarTwoNumerator410 t2 vis w73 a1 b42 b31
        lambda +
        h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * zetaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C czeta * h0 ^ 2)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (hw73 : w73.eval a = 0) (hq54 : q54.eval a = 0)
    (ha1 : a1.eval a = 0) (hb42 : b42.eval a = 0) :
    (131072 : F) * (derivative (derivative b31)).eval a -
        (131072 : F) * t2.eval a *
          (derivative (derivative b42)).eval a -
        (262144 : F) * (derivative t2).eval a *
          (derivative b42).eval a -
        (286720 : F) * t2.eval a * ((derivative a1).eval a) ^ 2 -
        (258048 : F) * lambda * ((derivative a1).eval a) ^ 2 +
        (802816 : F) * (derivative a1).eval a * t2.eval a *
          (derivative vis).eval a -
        (393216 : F) * (derivative a1).eval a *
          (derivative w73).eval a =
      (2 : F) * (derivative h0).eval a *
        (czeta * (derivative h0).eval a -
          (derivative (zetaGroundPolarOneNumerator410 t2 a22 s22 vis
              w73 q54 a1 a0 lambda)).eval a -
          (derivative h0).eval a *
            (zetaGroundRegularNumerator410 t2 a22 s22 a0
                lambda).eval a) := by
  have hP1a := zetaPolarOne_rootEval410 t2 a22 s22 vis w73 q54 a1 a0
    lambda a hvis hw73 hq54 ha1
  have hs : zetaGroundPolarTwoNumerator410 t2 vis w73 a1 b42 b31
      lambda =
      Polynomial.C czeta * (h0 * h0) -
        h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda -
        h0 * (h0 * zetaGroundRegularNumerator410 t2 a22 s22 a0
          lambda) := by
    linear_combination hzpin
  have hd2 := congrArg (fun r : F[X] => derivative (derivative r)) hs
  simp only [zetaGroundPolarTwoNumerator410, pow_two, derivative_add,
    derivative_sub, derivative_mul, derivative_ofNat, derivative_C,
    zero_mul, mul_zero, zero_add, add_zero] at hd2
  have heval := congrArg (fun r : F[X] => r.eval a) hd2
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_ofNat, hroot,
    hvis, hw73, hq54, ha1, hb42, hP1a, zero_mul, mul_zero, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero] at heval
  linear_combination heval

end ZetaGroundClearing410

/-! ## Source-facing ground power relation at exact order `-2` -/

section NonzeroZetaGroundBridge410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 6400000 in
/-- The row-`6` ground first integral `ζ` on a square-core ninth-power
source, traced from the literal Keller row through the seventh-face
power relation and expressed at its exact order `-2` on the
thirteenth-face jet: the polar-`2` block plus `h₀` times the polar-`1`
block plus `h₀²` times the regular block is GLOBALLY `C c_ζ h₀²` —
the second order-`-2` ground pin of the lane, and the first seeing
`b₃₁`. -/
theorem nonzeroFace410_zetaResidualPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 vis w73 q54 b42 b31 : k[X])
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
    (hq4 : q.coeff 4 = h0 ^ 2 * b42)
    (hq3 : q.coeff 3 = h0 * b31) :
    ∃ czeta : k,
      zetaGroundPolarTwoNumerator410 t2 vis w73 (p.coeff 1) b42 b31
          lambda +
        h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) lambda +
        h0 ^ 2 * zetaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
          lambda =
      Polynomial.C czeta * h0 ^ 2 := by
  obtain ⟨czeta, hpow⟩ :=
    nonzeroFace410_seventhDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  refine ⟨czeta, ?_⟩
  have h21 : h0 ^ 21 ≠ 0 := pow_ne_zero 21 hh0
  apply mul_left_cancel₀ h21
  calc
    h0 ^ 21 *
          (zetaGroundPolarTwoNumerator410 t2 vis w73 (p.coeff 1) b42
              b31 lambda +
            h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73
              q54 (p.coeff 1) (p.coeff 0) lambda +
            h0 ^ 2 * zetaGroundRegularNumerator410 t2 a22 s22
              (p.coeff 0) lambda) =
        localClearedSeventhDefect410 h0 (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda := by
      simp only [localClearedSeventhDefect410,
        zetaGroundPolarTwoNumerator410,
        zetaGroundPolarOneNumerator410,
        zetaGroundRegularNumerator410, hp3, hp2, hq8, hq7, hq6, hq5,
        hq4, hq3]
      ring
    _ = Polynomial.C czeta * h0 ^ 23 := hpow
    _ = h0 ^ 21 * (Polynomial.C czeta * h0 ^ 2) := by ring

/-! ## Zeta ground bridge packet -/

set_option maxHeartbeats 25600000 in
/-- Sharpest exact successor packet of the `ζ` ground bridge on the
nonzero `(4,10)` face: everything from the epsilon ground bridge
packet, together with the row-`6` ground pin at its exact order `-2` —
the second order-`-2` ground pin of the lane and the first seeing
`b₃₁` — its first `h`-adic peel step in solved form, the
`ε`-eliminated `b₃₁` pin (whose left side is `2048` times the global
polynomial lift of the jet tie `hX`), the fully eliminated `b₃₁` pin —
the first global SIX-ground-constant link of the lane, with cofactor
`uzeta` bound explicitly — the `ζ`-loaded factored forms of the second
`θ` and `ι` peel steps (the letter `b₃₁` eliminated; only `q₂`
survives polar-side in BOTH towers, and the `θ` polar side loses its
`λ p₁² a₂₂` block exactly), the constant-free derivative tie
`b₃₁'(a) = t₂(a) b₄₂'(a)`, the EXACT derivative kill `b₃₁'(a) = 0`
(`b₃₁` vanishes doubly at the root — the second unconditional
derivative-level kill of the nonzero face), and the second-derivative
root tie — the sharpest honest `ζ` residual, pinning `c_ζ` against
`h₀'(a)²`.  Nothing here closes the face or a branch: `c_α, c_β, c_γ,
c_δ, c_ε, c_ζ` are free, so the pins eliminate no configuration; no
root branch is forced; `t₂(a), a₂₂(a), s₂₂(a), q₁(a), q₀(a), c_α,
c_β, c_γ, c_δ, c_ε, c_ζ, c_θ, c, j, p₀'(a), q₀'(a)` remain free or
tied-not-determined, and the ground constant `η` (row `5`, eighth
defect, exact order `-2`, first seeing `q₂`) stays uncleared. -/
theorem nonzeroFace410_zetaGroundBridgePacket
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
    ∃ (calpha cbeta cgamma cdelta cepsilon czeta ctheta c : k)
      (v1 v2 v3 w1 w2 w3 ueps uzeta : k[X]),
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
                  lambda).eval a) ∧
      zetaGroundPolarTwoNumerator410 t2 vis w73 (p.coeff 1) b42 b31
          lambda +
          h0 * zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
            (p.coeff 1) (p.coeff 0) lambda +
          h0 ^ 2 * zetaGroundRegularNumerator410 t2 a22 s22
            (p.coeff 0) lambda =
        Polynomial.C czeta * h0 ^ 2 ∧
      zetaGroundPolarTwoNumerator410 t2 vis w73 (p.coeff 1) b42 b31
          lambda =
        h0 * (Polynomial.C czeta * h0 -
          zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
            (p.coeff 1) (p.coeff 0) lambda -
          h0 * zetaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
            lambda) ∧
      (131072 : k[X]) * b31 - (122880 : k[X]) * (p.coeff 1) ^ 2 * t2 +
          (92160 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 =
        h0 * (Polynomial.C czeta * h0 + (8 : k[X]) * t2 * ueps +
          (1536 : k[X]) * p.coeff 1 * (Polynomial.C cgamma -
            gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
              lambda) -
          (896 : k[X]) * p.coeff 1 * t2 * (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda) -
          zetaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
            (p.coeff 1) (p.coeff 0) lambda -
          h0 * zetaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
            lambda) ∧
      uzeta = (491520 : k[X]) * p.coeff 0 * p.coeff 1 +
          (122880 : k[X]) * p.coeff 1 * a22 ^ 2 +
          (32768 : k[X]) * Polynomial.C calpha * p.coeff 1 * a22 -
          (46080 : k[X]) * Polynomial.C lambda * p.coeff 1 * a22 *
            t2 -
          (61440 : k[X]) * p.coeff 1 * a22 * t2 ^ 2 +
          (2688 : k[X]) * Polynomial.C cbeta * p.coeff 1 * t2 +
          (1536 : k[X]) * Polynomial.C cgamma * p.coeff 1 +
          (5760 : k[X]) * Polynomial.C lambda * p.coeff 1 * t2 ^ 3 +
          (7680 : k[X]) * p.coeff 1 * t2 ^ 4 +
          h0 * (Polynomial.C czeta +
            (64 : k[X]) * Polynomial.C cepsilon * t2 +
            (5 : k[X]) * Polynomial.C cdelta * t2 ^ 2 +
            (40 : k[X]) * Polynomial.C cdelta * a22 -
            (64 : k[X]) * Polynomial.C cgamma * t2 ^ 3 +
            (768 : k[X]) * Polynomial.C cgamma * a22 * t2 +
            (35 : k[X]) * Polynomial.C cbeta * t2 ^ 4 -
            (336 : k[X]) * Polynomial.C cbeta * a22 * t2 ^ 2 +
            (1344 : k[X]) * Polynomial.C cbeta * a22 ^ 2 +
            (3584 : k[X]) * Polynomial.C cbeta * p.coeff 0 +
            (32768 : k[X]) * Polynomial.C calpha * p.coeff 0 * t2 +
            (245760 : k[X]) * p.coeff 0 * a22 * t2 -
            (184320 : k[X]) * Polynomial.C lambda * p.coeff 0 * a22 -
            (23040 : k[X]) * Polynomial.C lambda * p.coeff 0 *
              t2 ^ 2 -
            (20480 : k[X]) * p.coeff 0 * t2 ^ 3 -
            (7680 : k[X]) * Polynomial.C lambda * a22 ^ 3 -
            (20480 : k[X]) * a22 ^ 3 * t2 +
            (8640 : k[X]) * Polynomial.C lambda * a22 ^ 2 * t2 ^ 2 +
            (15360 : k[X]) * a22 ^ 2 * t2 ^ 3 -
            (2520 : k[X]) * Polynomial.C lambda * a22 * t2 ^ 4 -
            (3840 : k[X]) * a22 * t2 ^ 5 +
            (231 : k[X]) * Polynomial.C lambda * t2 ^ 6 +
            (320 : k[X]) * t2 ^ 7) ∧
      (131072 : k[X]) * b31 - (122880 : k[X]) * (p.coeff 1) ^ 2 * t2 +
          (92160 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 =
        h0 * uzeta ∧
      v1 - (8192 : k[X]) *
          ((2640 : k[X]) * (p.coeff 1) ^ 2 * a22 * t2 +
            (1500 : k[X]) * (p.coeff 1) ^ 2 * t2 ^ 3 -
            (900 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 *
              t2 ^ 2 -
            (80 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 * t2 +
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
          ((1280 : k[X]) * a22 * t2 - (480 : k[X]) * t2 ^ 3) * ueps +
          ((96 : k[X]) * a22 - (60 : k[X]) * t2 ^ 2) * uzeta) ∧
      (65536 : k[X]) * w1 + (2048 : k[X]) *
          ((16 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 * a22 -
            (9 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 * a22 *
              t2 +
            (720 : k[X]) * (p.coeff 1) ^ 2 * a22 * t2 ^ 2 +
            (16 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 *
              t2 ^ 2 -
            (225 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 *
              t2 ^ 3 +
            (240 : k[X]) * (p.coeff 1) ^ 2 * t2 ^ 4 -
            (128 : k[X]) * a22 * q.coeff 2 +
            (64 : k[X]) * q.coeff 2 * t2 ^ 2) =
        h0 * ((65536 : k[X]) * w2 -
          (160 : k[X]) * p.coeff 1 * (a22 - t2 ^ 2) *
            (Polynomial.C cdelta -
              deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) +
          (1536 : k[X]) * p.coeff 1 * t2 *
              ((3 : k[X]) * a22 + t2 ^ 2) *
            (Polynomial.C cgamma -
              gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) -
          (448 : k[X]) * p.coeff 1 *
              ((32 : k[X]) * p.coeff 0 + (8 : k[X]) * a22 ^ 2 -
                (25 : k[X]) * a22 * t2 ^ 2 + t2 ^ 4) *
            (Polynomial.C cbeta -
              betaGroundRegularNumerator410 t2 a22 s22 lambda) -
          (8 : k[X]) * (-(4 : k[X]) * p.coeff 0 +
              (2 : k[X]) * a22 ^ 2 - (4 : k[X]) * a22 * t2 ^ 2 +
              t2 ^ 4) * ueps -
          ((3 : k[X]) * a22 * t2 - t2 ^ 3) * uzeta) ∧
      (derivative b31).eval a = t2.eval a * (derivative b42).eval a ∧
      (derivative b31).eval a = 0 ∧
      (131072 : k) * (derivative (derivative b31)).eval a -
          (131072 : k) * t2.eval a *
            (derivative (derivative b42)).eval a -
          (262144 : k) * (derivative t2).eval a *
            (derivative b42).eval a -
          (286720 : k) * t2.eval a *
            ((derivative (p.coeff 1)).eval a) ^ 2 -
          (258048 : k) * lambda *
            ((derivative (p.coeff 1)).eval a) ^ 2 +
          (802816 : k) * (derivative (p.coeff 1)).eval a * t2.eval a *
            (derivative vis).eval a -
          (393216 : k) * (derivative (p.coeff 1)).eval a *
            (derivative w73).eval a =
        (2 : k) * (derivative h0).eval a *
          (czeta * (derivative h0).eval a -
            (derivative (zetaGroundPolarOneNumerator410 t2 a22 s22
                vis w73 q54 (p.coeff 1) (p.coeff 0) lambda)).eval a -
            (derivative h0).eval a *
              (zetaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                  lambda).eval a) := by
  obtain ⟨calpha, cbeta, cgamma, cdelta, cepsilon, ctheta, c, v1, v2,
    v3, w1, w2, w3, ueps, hpin, hsolve, hpowT, htw1, htw2, htw3, htwc,
    hpowI, hiw1, hiw2, hiw3, hiwc, hTglobal, hIglobal, ha1, hvis0,
    hw730, hq540, hb420, hb310, hb20, hv10, hw10, hv2tie, hw2tie,
    hrootS, hTroot, hIroot, hkelP, hcombo, hbr, hbpin, hbsolve,
    hbalpha, hbtheta, hbiota, hbderiv, hbderivA, hgpin, hgsolve,
    hgalpha, hw73B, hw73F, hgiota, hgderiv, hw73deriv, hdpin, hdsolve,
    hdalpha, hq54BG, hq54F, hthetaP2, hiotaP2, hdderiv, hq54deriv,
    hepin, hesolve, hb42B, hueps, hb42tie, hthetaE, hiotaE, hb42kill,
    h2tie⟩ :=
    nonzeroFace410_epsilonGroundBridgePacket p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 a hp hq hh0 hH hp4 hq10 hN hD hp3 hp2
      hq8 hq7 hq6 hq5 hq4 hq3 hroot hT hU hW hV hX hY
  obtain ⟨czeta, hzpin⟩ :=
    nonzeroFace410_zetaResidualPowerRelation p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 hp hq hh0 hH hp4 hq10 hN hD hp3 hp2 hq8
      hq7 hq6 hq5 hq4 hq3
  have hzsolve := zetaGroundPin_solvePolarTwo410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 b31 lambda czeta hzpin
  have hb31B := b31GroundPin_epsilonEliminated410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 b31 ueps lambda cbeta cgamma
    czeta hbpin hgpin hb42tie hzpin
  have hb31full := b31GroundPin_fullyEliminated410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 b31 lambda calpha cbeta cgamma
    cdelta cepsilon czeta hpin hbpin hgpin hdpin hepin hzpin
  have hthetaZ := thetaSecondPeel_zetaLoaded410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) v1 v2 ueps _
    lambda calpha cbeta cgamma cdelta hpin hbpin hgpin hdpin hb42tie
    hb31full htw2
  have hiotaZ := iotaSecondPeel_zetaLoaded410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) w1 w2 ueps _
    lambda calpha cbeta cgamma cdelta hpin hbpin hgpin hdpin hb42tie
    hb31full hiw2
  have hkill1 := zetaPin_rootDerivativeKill410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 b31 lambda czeta a hzpin hroot
    hvis0 hw730 hq540 ha1 hb420
  have hkill0 : (derivative b31).eval a = 0 := by
    rw [hkill1, hb42kill, mul_zero]
  have hz2tie := zetaPin_rootSecondDerivativeTie410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 b31 lambda czeta a hzpin hroot
    hvis0 hw730 hq540 ha1 hb420
  exact ⟨calpha, cbeta, cgamma, cdelta, cepsilon, czeta, ctheta, c,
    v1, v2, v3, w1, w2, w3, ueps, _, hpin, hsolve, hpowT, htw1, htw2,
    htw3, htwc, hpowI, hiw1, hiw2, hiw3, hiwc, hTglobal, hIglobal,
    ha1, hvis0, hw730, hq540, hb420, hb310, hb20, hv10, hw10, hv2tie,
    hw2tie, hrootS, hTroot, hIroot, hkelP, hcombo, hbr, hbpin,
    hbsolve, hbalpha, hbtheta, hbiota, hbderiv, hbderivA, hgpin,
    hgsolve, hgalpha, hw73B, hw73F, hgiota, hgderiv, hw73deriv, hdpin,
    hdsolve, hdalpha, hq54BG, hq54F, hthetaP2, hiotaP2, hdderiv,
    hq54deriv, hepin, hesolve, hb42B, hueps, hb42tie, hthetaE, hiotaE,
    hb42kill, h2tie, hzpin, hzsolve, hb31B, rfl, hb31full, hthetaZ,
    hiotaZ, hkill1, hkill0, hz2tie⟩

end NonzeroZetaGroundBridge410

#print axioms zetaDefect_eq_cleared410
#print axioms zetaGroundPin_solvePolarTwo410
#print axioms zetaGroundPin_rootEval410
#print axioms zetaGroundPin_rootEval_reDerivesX410
#print axioms b31GroundPin_epsilonEliminated410
#print axioms b31GroundPin_fullyEliminated410
#print axioms thetaSecondPeel_zetaLoaded410
#print axioms iotaSecondPeel_zetaLoaded410
#print axioms zetaPolarOne_rootEval410
#print axioms zetaPin_rootDerivativeKill410
#print axioms zetaPin_rootDerivativeKillFull410
#print axioms zetaPin_rootSecondDerivativeTie410
#print axioms nonzeroFace410_zetaResidualPowerRelation
#print axioms nonzeroFace410_zetaGroundBridgePacket

end Max11DegreeRoutes
