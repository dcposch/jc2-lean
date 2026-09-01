import Fable410ScaleTwoNextGroundBridgeScratch

/-! # Eta ground bridge for the normalized `(4,10)` nonzero source

The zeta ground bridge pinned the row-`6` ground first integral `ζ`
at exact order `-2` and produced the first six-ground-constant link.
The LAST unused Keller row of the nonzero face is the degree-`5` row:
its first integral is `η = V + (5/128) A⁴ - (45/128) L A² B -
(15/16) A² C - (3/8) γ A² - (15/16) A B² - (21/16) β A B - 2 α A C -
α B² - (45/16) L B C - ε A - (5/4) δ B - (15/8) C² - (3/2) γ C`
(row `5`, `etaResidual410`, eighth face).  On the thirteenth-face jet
it sits at exact order `-2`; it is the FIRST ground clearing seeing
the letter `q₂` and the first with the polar-level product `p₁² s₂₂`.

First, the clearing (`etaDefect_eq_cleared410`): `32768 h² η` splits
as the order-`-2` polar block `32768 q₂ - 24576 b₃₁ t₂ +
24576 b₄₂ t₂² - 32768 a₂₂ b₄₂ - 153600 p₁² a₂₂ + 69120 λ p₁² t₂ +
49152 p₁² s₂₂ - 76800 p₁² t₂² + 86016 p₁ a₂₂ q₇₆ -
107520 p₁ t₂² q₇₆ + 73728 p₁ t₂ w₇₃ - 40960 p₁ q₅₄`, plus `h` times
the order-`-1` block (every monomial carries one of the
root-vanishing letters `q₇₆, w₇₃, q₅₄, p₁`), plus `h²` times the
regular block.

Second, the literal-source trace: the eighth-face power relation pins
the row-`5` integral globally
(`nonzeroFace410_eighthDefectPowerRelation`, weight `26`);
substituting the thirteenth-face jet forms and cancelling `h₀²⁴`
gives the third order-`-2` ground pin of the lane
(`nonzeroFace410_etaResidualPowerRelation`): `polar₂ + h₀ · polar₁ +
h₀² · (regular) = C c_η h₀²`.  Its first `h`-adic peel step is exact
(`etaGroundPin_solvePolarTwo410`), and the root evaluation combined
with the `β`, `γ`, `δ`, `ε`, `ζ` pins RE-DERIVES the thirteenth-face
jet hypothesis `hY` from the literal source
(`etaGroundPin_rootEval_reDerivesY410`): `256 q₂(a) =
p₁(a)² (256 s₂₂(a) - 400 a₂₂(a) + 243 λ t₂(a) - 540 t₂(a)²)` — rows
`10`, `9`, `8`, `7`, `6` and `5` alone force it.  With `η`, EVERY
thirteenth-face jet hypothesis `hT, hU, hV, hW, hX, hY` is
re-derived from the literal source through the ground rows alone.

Third, the eliminations.  The `ζ`-pin tie kills `b₃₁ t₂`, the
`ε`-pin tie kills both `b₄₂` cross-terms, and the `δ`, `γ`, `β` pins
kill `q₅₄`, `w₇₃` and the `q₇₆` cross-terms
(`q2GroundPin_zetaEliminated410`), collapsing sixteen times the
polar-`2` block to `524288 q₂ - 524288 p₁² s₂₂ + 819200 p₁² a₂₂ -
497664 λ p₁² t₂ + 1105920 p₁² t₂²` — `2048` times the LITERAL
polynomial lift of the jet tie `hY`.  Loading all seven pins (`ζ`
with cofactor `3 t₂`, `ε` with `256 a₂₂`, `δ` with `160 p₁ +
h₀ t₂ (40 a₂₂ - 5 t₂²)`, `γ` with `3072 p₁ t₂ + h₀ (6144 p₀ +
1536 a₂₂² - 768 a₂₂ t₂² + 96 t₂⁴)`, `β` with `10752 p₁ a₂₂ -
1344 p₁ t₂² + h₀ t₂ (10752 p₀ - 1344 a₂₂² + 560 a₂₂ t₂² - 63 t₂⁴)`,
`α` with `65536 p₁² + 131072 p₀ a₂₂ h₀²`) kills every order-`-1`
letter and `s₂₂` entirely (`q2GroundPin_fullyEliminated410`):
`524288 q₂ - 65536 c_α p₁² - 491520 p₁² a₂₂ + 92160 λ p₁² t₂ +
122880 p₁² t₂² = h₀ (F₁ + h₀ F₂)` with `F₁` linear in `p₁` and `F₂`
carrying `16 c_η + 3 c_ζ t₂ + 256 c_ε a₂₂ + 40 c_δ a₂₂ t₂ + ⋯` —
the first SEVEN-ground-constant link of the lane.

Fourth, the combination with the terminal packet: the `q₂` pin
eliminates `q₂` from the `ζ`-loaded second peel steps of BOTH towers
(`thetaSecondPeel_etaLoaded410`, `iotaSecondPeel_etaLoaded410`) — NO
letter survives on the polar side: every residual polar monomial of
the second `θ` and `ι` peels carries `p₁²`.  The ground tower of the
nonzero face is EXHAUSTED: rows `4` and `3` are already pinned at
order `-3` by the `θ`/`ι` source bridges, and rows `2`, `1`, `0` are
consumed by the thirteenth-face jet.

The sharpest `η`-loaded root results are one and two derivatives
deeper.  Since the solved polar-`2` cofactor itself vanishes at the
root, the first derivative of the pin at the root is CONSTANT-FREE
(`etaPin_rootDerivativeKill410`): `4 q₂'(a) = 3 t₂(a) b₃₁'(a) +
(4 a₂₂(a) - 3 t₂(a)²) b₄₂'(a)`, and combined with the `ε` kill
`b₄₂'(a) = 0` and the `ζ` kill `b₃₁'(a) = 0` this forces
`q₂'(a) = 0` (`etaPin_rootDerivativeKillFull410`) — `q₂` vanishes
doubly at the root, the THIRD unconditional derivative-level kill of
the nonzero face.  The honest residual moves to the second
derivative (`etaPin_rootSecondDerivativeTie410`), pinning `c_η`
against `h₀'(a)²`.

Nothing here closes the face or a branch: `c_η` is free, so the pin
eliminates no configuration; no root branch is forced (both factors
of every peeled block already vanish at the root); `t₂(a), a₂₂(a),
s₂₂(a), q₁(a), q₀(a), c_α, c_β, c_γ, c_δ, c_ε, c_ζ, c_η, c_θ, c, j,
p₀'(a), q₀'(a), p₁'(a), q₇₆'(a), w₇₃'(a), t₂'(a), b₄₂''(a),
b₃₁''(a), q₂''(a)` remain free or tied-not-determined.  No unused
ground row remains on the nonzero face; the next unused row of the
lane is the aligned-face degree-`6` row (first seeing `q₃`).  No
total-degree or twice-prime theorem is used, and the aligned face
`N = 0` is not touched.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Exact order-`-2` clearing of `η` on the thirteenth-face jet -/

section EtaGroundClearing410

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- Order-`-2` (polar) numerator block of the cleared `η` on the
thirteenth-face jet: the third ground residue block at depth two, the
first ground block seeing `q₂`, and the first with the polar-level
product `p₁² s₂₂`.  It carries the polar-level cross-terms `b₃₁ t₂`,
`b₄₂ t₂²`, `a₂₂ b₄₂` and `p₁ q₅₄`. -/
def etaGroundPolarTwoNumerator410
    (t2 a22 s22 vis w73 q54 a1 b42 b31 b2 : F[X]) (lambda : F) :
    F[X] :=
  (32768 : F[X]) * b2 -
    (24576 : F[X]) * b31 * t2 +
    (24576 : F[X]) * b42 * t2 ^ 2 -
    (32768 : F[X]) * a22 * b42 -
    (153600 : F[X]) * a1 ^ 2 * a22 +
    (69120 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 +
    (49152 : F[X]) * a1 ^ 2 * s22 -
    (76800 : F[X]) * a1 ^ 2 * t2 ^ 2 +
    (86016 : F[X]) * a1 * a22 * vis -
    (107520 : F[X]) * a1 * t2 ^ 2 * vis +
    (73728 : F[X]) * a1 * t2 * w73 -
    (40960 : F[X]) * a1 * q54

/-- Order-`-1` numerator block of the cleared `η` on the
thirteenth-face jet.  Every monomial carries one of the root-vanishing
letters `q₇₆, w₇₃, q₅₄, p₁`, so the whole block vanishes at the root
of `h₀`. -/
def etaGroundPolarOneNumerator410
    (t2 a22 s22 vis w73 q54 a1 a0 : F[X]) (lambda : F) : F[X] :=
  (86016 : F[X]) * a0 * t2 * vis -
    (30720 : F[X]) * a0 * a1 * t2 -
    (55296 : F[X]) * Polynomial.C lambda * a0 * a1 -
    (49152 : F[X]) * a0 * w73 +
    (192000 : F[X]) * a1 * a22 ^ 2 * t2 +
    (69120 : F[X]) * Polynomial.C lambda * a1 * a22 ^ 2 -
    (245760 : F[X]) * a1 * a22 * s22 * t2 +
    (403200 : F[X]) * a1 * a22 * t2 ^ 3 -
    (241920 : F[X]) * Polynomial.C lambda * a1 * a22 * t2 ^ 2 +
    (143360 : F[X]) * a1 * s22 * t2 ^ 3 -
    (231840 : F[X]) * a1 * t2 ^ 5 +
    (90720 : F[X]) * Polynomial.C lambda * a1 * t2 ^ 4 -
    (107520 : F[X]) * a22 ^ 2 * t2 * vis +
    (36864 : F[X]) * a22 ^ 2 * w73 +
    (125440 : F[X]) * a22 * t2 ^ 3 * vis -
    (92160 : F[X]) * a22 * t2 ^ 2 * w73 +
    (61440 : F[X]) * a22 * t2 * q54 -
    (28224 : F[X]) * t2 ^ 5 * vis +
    (26880 : F[X]) * t2 ^ 4 * w73 -
    (25600 : F[X]) * t2 ^ 3 * q54

/-- Regular (order-`0`) numerator block of the cleared `η` on the
thirteenth-face jet.  It is linear in `s₂₂` with the sextic cofactor
`29568 t₂⁶ - 161280 a₂₂ t₂⁴ + 215040 a₂₂² t₂² - 122880 p₀ t₂² -
40960 a₂₂³ + 98304 p₀ a₂₂`. -/
def etaGroundRegularNumerator410 (t2 a22 s22 a0 : F[X])
    (lambda : F) : F[X] :=
  (61440 : F[X]) * a0 ^ 2 -
    (153600 : F[X]) * a0 * a22 ^ 2 +
    (98304 : F[X]) * a0 * a22 * s22 -
    (153600 : F[X]) * a0 * a22 * t2 ^ 2 +
    (138240 : F[X]) * Polynomial.C lambda * a0 * a22 * t2 -
    (122880 : F[X]) * a0 * s22 * t2 ^ 2 +
    (201600 : F[X]) * a0 * t2 ^ 4 -
    (80640 : F[X]) * Polynomial.C lambda * a0 * t2 ^ 3 +
    (44800 : F[X]) * a22 ^ 4 -
    (40960 : F[X]) * a22 ^ 3 * s22 -
    (80640 : F[X]) * Polynomial.C lambda * a22 ^ 3 * t2 +
    (215040 : F[X]) * a22 ^ 2 * s22 * t2 ^ 2 -
    (352800 : F[X]) * a22 ^ 2 * t2 ^ 4 +
    (181440 : F[X]) * Polynomial.C lambda * a22 ^ 2 * t2 ^ 3 -
    (161280 : F[X]) * a22 * s22 * t2 ^ 4 +
    (258720 : F[X]) * a22 * t2 ^ 6 -
    (99792 : F[X]) * Polynomial.C lambda * a22 * t2 ^ 5 +
    (29568 : F[X]) * s22 * t2 ^ 6 -
    (45045 : F[X]) * t2 ^ 8 +
    (15444 : F[X]) * Polynomial.C lambda * t2 ^ 7

set_option maxHeartbeats 51200000 in
/-- Exact order-`-2` clearing of the eighth-face residual `η` on the
thirteenth-face jet substitutions: `32768 h² η` is the polar-`2`
residue block plus `h` times the polar-`1` block plus `h²` times the
regular block, so `η` sits at exact order `-2` — the first ground
clearing seeing `q₂`. -/
theorem etaDefect_eq_cleared410
    (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 b9 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * (h ^ 3 * t2) * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (32768 : F) * h ^ 2 *
        etaResidual410
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
          (depressedT410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
            (h ^ 2 * b42))
          (depressedV410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
            (h ^ 2 * b42) (h * b31) b2) =
      ((32768 : F) * b2 -
        (24576 : F) * b31 * t2 +
        (24576 : F) * b42 * t2 ^ 2 -
        (32768 : F) * a22 * b42 -
        (153600 : F) * a1 ^ 2 * a22 +
        (69120 : F) * lambda * a1 ^ 2 * t2 +
        (49152 : F) * a1 ^ 2 * s22 -
        (76800 : F) * a1 ^ 2 * t2 ^ 2 +
        (86016 : F) * a1 * a22 * vis -
        (107520 : F) * a1 * t2 ^ 2 * vis +
        (73728 : F) * a1 * t2 * w73 -
        (40960 : F) * a1 * q54) +
        h * ((86016 : F) * a0 * t2 * vis -
          (30720 : F) * a0 * a1 * t2 -
          (55296 : F) * lambda * a0 * a1 -
          (49152 : F) * a0 * w73 +
          (192000 : F) * a1 * a22 ^ 2 * t2 +
          (69120 : F) * lambda * a1 * a22 ^ 2 -
          (245760 : F) * a1 * a22 * s22 * t2 +
          (403200 : F) * a1 * a22 * t2 ^ 3 -
          (241920 : F) * lambda * a1 * a22 * t2 ^ 2 +
          (143360 : F) * a1 * s22 * t2 ^ 3 -
          (231840 : F) * a1 * t2 ^ 5 +
          (90720 : F) * lambda * a1 * t2 ^ 4 -
          (107520 : F) * a22 ^ 2 * t2 * vis +
          (36864 : F) * a22 ^ 2 * w73 +
          (125440 : F) * a22 * t2 ^ 3 * vis -
          (92160 : F) * a22 * t2 ^ 2 * w73 +
          (61440 : F) * a22 * t2 * q54 -
          (28224 : F) * t2 ^ 5 * vis +
          (26880 : F) * t2 ^ 4 * w73 -
          (25600 : F) * t2 ^ 3 * q54) +
        h ^ 2 * ((61440 : F) * a0 ^ 2 -
          (153600 : F) * a0 * a22 ^ 2 +
          (98304 : F) * a0 * a22 * s22 -
          (153600 : F) * a0 * a22 * t2 ^ 2 +
          (138240 : F) * lambda * a0 * a22 * t2 -
          (122880 : F) * a0 * s22 * t2 ^ 2 +
          (201600 : F) * a0 * t2 ^ 4 -
          (80640 : F) * lambda * a0 * t2 ^ 3 +
          (44800 : F) * a22 ^ 4 -
          (40960 : F) * a22 ^ 3 * s22 -
          (80640 : F) * lambda * a22 ^ 3 * t2 +
          (215040 : F) * a22 ^ 2 * s22 * t2 ^ 2 -
          (352800 : F) * a22 ^ 2 * t2 ^ 4 +
          (181440 : F) * lambda * a22 ^ 2 * t2 ^ 3 -
          (161280 : F) * a22 * s22 * t2 ^ 4 +
          (258720 : F) * a22 * t2 ^ 6 -
          (99792 : F) * lambda * a22 * t2 ^ 5 +
          (29568 : F) * s22 * t2 ^ 6 -
          (45045 : F) * t2 ^ 8 +
          (15444 : F) * lambda * t2 ^ 7) := by
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
  have hV :
      depressedV410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
          (h ^ 2 * b42) (h * b31) b2 =
        ((65536 : F) * b2 - 49152 * b31 * t2 + 24576 * b42 * t2 ^ 2 -
            1344 * h * t2 ^ 5 * vis + 3840 * h * t2 ^ 4 * w73 -
            10240 * h * t2 ^ 3 * q54 + 448 * h ^ 2 * t2 ^ 6 * s22 -
            315 * h ^ 2 * t2 ^ 8 + 72 * lambda * h ^ 2 * t2 ^ 7) /
          (65536 * h ^ 2) := by
    rw [depressedV410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) (h ^ 2 * b42)
      (h * b31) b2 lambda hh hN]
    field_simp [hh]
    ring
  simp only [etaResidual410, alphaResidual410, betaResidual410,
    gammaResidual410, deltaResidual410, epsilonResidual410, hL, hA,
    hB, hC, hP, hQ, hR, hS, hT, hV]
  field_simp [hh]
  ring

/-- The `η` ground pin solves the order-`-2` polar block exactly: the
polar-`2` residue block is `h₀` times the explicit ground-loaded
cofactor — the first peel step of the order-`-2` pin, in factored
`h`-adic quotient form. -/
theorem etaGroundPin_solvePolarTwo410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 : F[X])
    (lambda ceta : F)
    (hpin : etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda +
        h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * etaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C ceta * h0 ^ 2) :
    etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 b42 b31
        b2 lambda =
      h0 * (Polynomial.C ceta * h0 -
        etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0
          lambda -
        h0 * etaGroundRegularNumerator410 t2 a22 s22 a0 lambda) := by
  linear_combination hpin

/-- Root evaluation of the `η` ground pin: the polar-`2` residue block
vanishes at the root of `h₀`. -/
theorem etaGroundPin_rootEval410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 : F[X])
    (lambda ceta : F) (a : F)
    (hpin : etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda +
        h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * etaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C ceta * h0 ^ 2)
    (hroot : h0.eval a = 0) :
    (32768 : F) * b2.eval a -
    (24576 : F) * b31.eval a * t2.eval a +
    (24576 : F) * b42.eval a * (t2.eval a) ^ 2 -
    (32768 : F) * a22.eval a * b42.eval a -
    (153600 : F) * (a1.eval a) ^ 2 * a22.eval a +
    (69120 : F) * lambda * (a1.eval a) ^ 2 * t2.eval a +
    (49152 : F) * (a1.eval a) ^ 2 * s22.eval a -
    (76800 : F) * (a1.eval a) ^ 2 * (t2.eval a) ^ 2 +
    (86016 : F) * a1.eval a * a22.eval a * vis.eval a -
    (107520 : F) * a1.eval a * (t2.eval a) ^ 2 * vis.eval a +
    (73728 : F) * a1.eval a * t2.eval a * w73.eval a -
    (40960 : F) * a1.eval a * q54.eval a = 0 := by
  have h := congrArg (fun r : F[X] => r.eval a) hpin
  simp only [etaGroundPolarTwoNumerator410, pow_two, eval_add,
    eval_sub, eval_mul, eval_C, eval_ofNat, hroot, zero_mul, mul_zero,
    add_zero] at h
  linear_combination h

/-- Root evaluation of the `η` ground pin combined with the `β`, `γ`,
`δ`, `ε` and `ζ` ground pins: the thirteenth-face tie `256 q₂(a) =
p₁(a)² (256 s₂₂(a) - 400 a₂₂(a) + 243 λ t₂(a) - 540 t₂(a)²)` (the jet
hypothesis `hY`) is forced by the literal source through the
row-`10`, row-`9`, row-`8`, row-`7`, row-`6` and row-`5` integrals
alone — with `η`, every thirteenth-face jet hypothesis is re-derived
from the literal source. -/
theorem etaGroundPin_rootEval_reDerivesY410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 : F[X])
    (lambda cbeta cgamma cdelta cepsilon czeta ceta : F) (a : F)
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
      Polynomial.C czeta * h0 ^ 2)
    (hnpin : etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda +
        h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * etaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C ceta * h0 ^ 2)
    (hroot : h0.eval a = 0) :
    (256 : F) * b2.eval a =
      (a1.eval a) ^ 2 *
        ((256 : F) * s22.eval a - (400 : F) * a22.eval a +
          (243 : F) * lambda * t2.eval a -
          (540 : F) * (t2.eval a) ^ 2) := by
  have hbe := betaGroundPin_rootEval410 h0 t2 a22 s22 vis a1 lambda
    cbeta a hbpin hroot
  have hge := gammaGroundPin_rootEval410 h0 t2 a22 s22 vis w73 a1 a0
    lambda cgamma a hgpin hroot
  have hde := deltaGroundPin_rootEval410 h0 t2 a22 s22 vis w73 q54 a1
    a0 lambda cdelta a hdpin hroot
  have hee := epsilonGroundPin_rootEval410 h0 t2 a22 s22 vis w73 q54
    a1 a0 b42 lambda cepsilon a hepin hroot
  have hze := zetaGroundPin_rootEval410 h0 t2 a22 s22 vis w73 q54 a1
    a0 b42 b31 lambda czeta a hzpin hroot
  have hne := etaGroundPin_rootEval410 h0 t2 a22 s22 vis w73 q54 a1
    a0 b42 b31 b2 lambda ceta a hnpin hroot
  linear_combination ((1 : F) / 128) * hne +
    ((3 : F) / 2048) * t2.eval a * hze +
    ((1 : F) / 8) * a22.eval a * hee +
    ((5 : F) / 64) * a1.eval a * hde +
    ((3 : F) / 2) * a1.eval a * t2.eval a * hge +
    (((21 : F) / 4) * a1.eval a * a22.eval a -
      ((21 : F) / 32) * a1.eval a * (t2.eval a) ^ 2) * hbe

/-- The `q₂` pin, `ζ`-eliminated: the `ζ`-pin tie kills the polar-`2`
cross-term `b₃₁ t₂`, the `ε`-pin tie kills both `b₄₂` cross-terms,
and the `δ`, `γ`, `β` pins kill `q₅₄`, `w₇₃` and the `q₇₆`
cross-terms, collapsing sixteen times the `η` polar block to
`524288 q₂ - 524288 p₁² s₂₂ + 819200 p₁² a₂₂ - 497664 λ p₁² t₂ +
1105920 p₁² t₂²` — `2048` times the LITERAL polynomial lift of the
jet tie `hY`: the root tie of the thirteenth face is the root shadow
of this global pin. -/
theorem q2GroundPin_zetaEliminated410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 u uz : F[X])
    (lambda cbeta cgamma cdelta ceta : F)
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
    (hnpin : etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda +
        h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * etaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C ceta * h0 ^ 2) :
    (524288 : F[X]) * b2 -
    (524288 : F[X]) * a1 ^ 2 * s22 +
    (819200 : F[X]) * a1 ^ 2 * a22 -
    (497664 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 +
    (1105920 : F[X]) * a1 ^ 2 * t2 ^ 2 =
      h0 * ((16 : F[X]) * Polynomial.C ceta * h0 +
        (3 : F[X]) * t2 * uz +
        ((32 : F[X]) * a22 - (24 : F[X]) * t2 ^ 2) * u +
        (160 : F[X]) * a1 * (Polynomial.C cdelta -
          deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda) -
        (1536 : F[X]) * a1 * t2 * (Polynomial.C cgamma -
          gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda) +
        ((1344 : F[X]) * a1 * t2 ^ 2 - (3584 : F[X]) * a1 * a22) *
          (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda) -
        (16 : F[X]) * etaGroundPolarOneNumerator410 t2 a22 s22 vis
          w73 q54 a1 a0 lambda -
        (16 : F[X]) * h0 * etaGroundRegularNumerator410 t2 a22 s22 a0
          lambda) := by
  have hb := hbpin
  simp only [betaGroundPolarNumerator410] at hb
  have hg := hgpin
  simp only [gammaGroundPolarNumerator410] at hg
  have hd := hdpin
  simp only [deltaGroundPolarNumerator410] at hd
  have hn := hnpin
  simp only [etaGroundPolarTwoNumerator410] at hn
  linear_combination (16 : F[X]) * hn + (3 : F[X]) * t2 * hb31 +
    ((32 : F[X]) * a22 - (24 : F[X]) * t2 ^ 2) * hb42 +
    (160 : F[X]) * a1 * hd - (1536 : F[X]) * a1 * t2 * hg +
    ((1344 : F[X]) * a1 * t2 ^ 2 - (3584 : F[X]) * a1 * a22) * hb

set_option maxHeartbeats 12800000 in
/-- The fully eliminated `q₂` pin: the `ζ` and `ε` pins kill the
`b₃₁`/`b₄₂` cross-terms, the `δ`, `γ`, `β` pins kill every order-`-1`
letter at the `h₀`-level, and the `α` pin eliminates `s₂₂` entirely —
`524288 q₂ - 65536 c_α p₁² - 491520 p₁² a₂₂ + 92160 λ p₁² t₂ +
122880 p₁² t₂²` is pinned against `t₂, a₂₂, p₀, c_α, c_β, c_γ, c_δ,
c_ε, c_ζ, c_η` only, the first global SEVEN-ground-constant link of
the lane. -/
theorem q2GroundPin_fullyEliminated410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 : F[X])
    (lambda calpha cbeta cgamma cdelta cepsilon czeta ceta : F)
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
      Polynomial.C czeta * h0 ^ 2)
    (hnpin : etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda +
        h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * etaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C ceta * h0 ^ 2) :
    (524288 : F[X]) * b2 -
    (65536 : F[X]) * Polynomial.C calpha * a1 ^ 2 -
    (491520 : F[X]) * a1 ^ 2 * a22 +
    (92160 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 +
    (122880 : F[X]) * a1 ^ 2 * t2 ^ 2 =
      h0 * ((983040 : F[X]) * a0 * a1 * t2 -
      (737280 : F[X]) * Polynomial.C lambda * a0 * a1 -
      (245760 : F[X]) * a1 * a22 ^ 2 * t2 -
      (92160 : F[X]) * Polynomial.C lambda * a1 * a22 ^ 2 +
      (122880 : F[X]) * a1 * a22 * t2 ^ 3 +
      (69120 : F[X]) * Polynomial.C lambda * a1 * a22 * t2 ^ 2 +
      (10752 : F[X]) * Polynomial.C cbeta * a1 * a22 -
      (1344 : F[X]) * Polynomial.C cbeta * a1 * t2 ^ 2 +
      (160 : F[X]) * Polynomial.C cdelta * a1 +
      (3072 : F[X]) * Polynomial.C cgamma * a1 * t2 -
      (10080 : F[X]) * Polynomial.C lambda * a1 * t2 ^ 4 -
      (15360 : F[X]) * a1 * t2 ^ 5 +
        h0 * ((16 : F[X]) * Polynomial.C ceta +
        (3 : F[X]) * Polynomial.C czeta * t2 +
        (256 : F[X]) * Polynomial.C cepsilon * a22 +
        (40 : F[X]) * Polynomial.C cdelta * a22 * t2 -
        (5 : F[X]) * Polynomial.C cdelta * t2 ^ 3 +
        (6144 : F[X]) * Polynomial.C cgamma * a0 +
        (1536 : F[X]) * Polynomial.C cgamma * a22 ^ 2 -
        (768 : F[X]) * Polynomial.C cgamma * a22 * t2 ^ 2 +
        (96 : F[X]) * Polynomial.C cgamma * t2 ^ 4 +
        (10752 : F[X]) * Polynomial.C cbeta * a0 * t2 -
        (1344 : F[X]) * Polynomial.C cbeta * a22 ^ 2 * t2 +
        (560 : F[X]) * Polynomial.C cbeta * a22 * t2 ^ 3 -
        (63 : F[X]) * Polynomial.C cbeta * t2 ^ 5 +
        (131072 : F[X]) * Polynomial.C calpha * a0 * a22 +
        (983040 : F[X]) * a0 ^ 2 +
        (491520 : F[X]) * a0 * a22 ^ 2 -
        (245760 : F[X]) * a0 * a22 * t2 ^ 2 -
        (184320 : F[X]) * Polynomial.C lambda * a0 * a22 * t2 +
        (30720 : F[X]) * a0 * t2 ^ 4 +
        (23040 : F[X]) * Polynomial.C lambda * a0 * t2 ^ 3 -
        (20480 : F[X]) * a22 ^ 4 +
        (61440 : F[X]) * a22 ^ 3 * t2 ^ 2 +
        (23040 : F[X]) * Polynomial.C lambda * a22 ^ 3 * t2 -
        (38400 : F[X]) * a22 ^ 2 * t2 ^ 4 -
        (20160 : F[X]) * Polynomial.C lambda * a22 ^ 2 * t2 ^ 3 +
        (8960 : F[X]) * a22 * t2 ^ 6 +
        (5544 : F[X]) * Polynomial.C lambda * a22 * t2 ^ 5 -
        (720 : F[X]) * t2 ^ 8 -
        (495 : F[X]) * Polynomial.C lambda * t2 ^ 7)) := by
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
  have hn := hnpin
  simp only [etaGroundPolarTwoNumerator410,
    etaGroundPolarOneNumerator410,
    etaGroundRegularNumerator410] at hn
  linear_combination (16 : F[X]) * hn + (3 : F[X]) * t2 * hz +
    (256 : F[X]) * a22 * he +
    ((160 : F[X]) * a1 +
      h0 * ((40 : F[X]) * a22 * t2 - (5 : F[X]) * t2 ^ 3)) * hd +
    ((3072 : F[X]) * a1 * t2 +
      h0 * ((6144 : F[X]) * a0 + (1536 : F[X]) * a22 ^ 2 -
        (768 : F[X]) * a22 * t2 ^ 2 + (96 : F[X]) * t2 ^ 4)) * hg +
    ((10752 : F[X]) * a1 * a22 - (1344 : F[X]) * a1 * t2 ^ 2 +
      h0 * ((10752 : F[X]) * a0 * t2 - (1344 : F[X]) * a22 ^ 2 * t2 +
        (560 : F[X]) * a22 * t2 ^ 3 - (63 : F[X]) * t2 ^ 5)) * hb +
    ((65536 : F[X]) * a1 ^ 2 +
      (131072 : F[X]) * a0 * a22 * h0 ^ 2) * ha

set_option maxHeartbeats 6400000 in
/-- `η`-loaded second `θ` peel: the `q₂` pin eliminates the letter
`q₂` from the `ζ`-loaded order-`-2` theta block — NO letter survives
on the polar side: every residual polar monomial carries `p₁²`. -/
theorem thetaSecondPeel_etaLoaded410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 v1 v2 u uz ue : F[X])
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
    (hq2 : (524288 : F[X]) * b2 -
        (65536 : F[X]) * Polynomial.C calpha * a1 ^ 2 -
        (491520 : F[X]) * a1 ^ 2 * a22 +
        (92160 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 +
        (122880 : F[X]) * a1 ^ 2 * t2 ^ 2 =
      h0 * ue)
    (hpeel : v1 + thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda =
      h0 * v2) :
    v1 - (8192 : F[X]) *
        ((3600 : F[X]) * a1 ^ 2 * a22 * t2 +
        (1260 : F[X]) * a1 ^ 2 * t2 ^ 3 -
        (1080 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 ^ 2 +
        (48 : F[X]) * Polynomial.C calpha * a1 ^ 2 * t2) =
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
        ((96 : F[X]) * a22 - (60 : F[X]) * t2 ^ 2) * uz +
        (16 : F[X]) * t2 * ue) := by
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
    ((96 : F[X]) * a22 - (60 : F[X]) * t2 ^ 2) * hb31 +
    (16 : F[X]) * t2 * hq2

set_option maxHeartbeats 6400000 in
/-- `η`-loaded second `ι` peel (scaled by `4`): the `q₂` pin
eliminates the letter `q₂` from the `ζ`-loaded order-`-2` iota block
— NO letter survives on the polar side of EITHER tower. -/
theorem iotaSecondPeel_etaLoaded410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 w1 w2 u uz ue : F[X])
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
    (hq2 : (524288 : F[X]) * b2 -
        (65536 : F[X]) * Polynomial.C calpha * a1 ^ 2 -
        (491520 : F[X]) * a1 ^ 2 * a22 +
        (92160 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 +
        (122880 : F[X]) * a1 ^ 2 * t2 ^ 2 =
      h0 * ue)
    (hpeel : w1 + iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        a0 b42 b31 b2 lambda =
      h0 * w2) :
    (262144 : F[X]) * w1 + (6144 : F[X]) *
        ((1080 : F[X]) * a1 ^ 2 * a22 * t2 ^ 2 +
        (18 : F[X]) * Polynomial.C lambda * a1 ^ 2 * a22 * t2 -
        (160 : F[X]) * a1 ^ 2 * a22 ^ 2 +
        (32 : F[X]) * Polynomial.C calpha * a1 ^ 2 * t2 ^ 2 -
        (315 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 ^ 3 +
        (300 : F[X]) * a1 ^ 2 * t2 ^ 4) =
      h0 * ((262144 : F[X]) * w2 -
        (640 : F[X]) * a1 * (a22 - t2 ^ 2) *
          (Polynomial.C cdelta -
            deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda) +
        (6144 : F[X]) * a1 * t2 * ((3 : F[X]) * a22 + t2 ^ 2) *
          (Polynomial.C cgamma -
            gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda) -
        (1792 : F[X]) * a1 *
            ((32 : F[X]) * a0 + (8 : F[X]) * a22 ^ 2 -
              (25 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) *
          (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda) -
        (32 : F[X]) * (-(4 : F[X]) * a0 + (2 : F[X]) * a22 ^ 2 -
            (4 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) * u -
        ((12 : F[X]) * a22 * t2 - (4 : F[X]) * t2 ^ 3) * uz +
        ((2 : F[X]) * a22 - t2 ^ 2) * ue) := by
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
  linear_combination (262144 : F[X]) * hp -
    (640 : F[X]) * a1 * (a22 - t2 ^ 2) * hd +
    (6144 : F[X]) * a1 * t2 * ((3 : F[X]) * a22 + t2 ^ 2) * hg -
    (1792 : F[X]) * a1 *
      ((32 : F[X]) * a0 + (8 : F[X]) * a22 ^ 2 -
        (25 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) * hb -
    (131072 : F[X]) * a1 ^ 2 * (a22 + t2 ^ 2) * ha -
    (32 : F[X]) * (-(4 : F[X]) * a0 + (2 : F[X]) * a22 ^ 2 -
      (4 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) * hb42 -
    ((12 : F[X]) * a22 * t2 - (4 : F[X]) * t2 ^ 3) * hb31 +
    ((2 : F[X]) * a22 - t2 ^ 2) * hq2

/-- Root evaluation of the `η` polar-`1` block: every monomial carries
one of the root-vanishing letters `q₇₆, w₇₃, q₅₄, p₁`, so the whole
block dies at the root. -/
theorem etaPolarOne_rootEval410
    (t2 a22 s22 vis w73 q54 a1 a0 : F[X]) (lambda : F) (a : F)
    (hvis : vis.eval a = 0) (hw73 : w73.eval a = 0)
    (hq54 : q54.eval a = 0) (ha1 : a1.eval a = 0) :
    (etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0
        lambda).eval a = 0 := by
  simp only [etaGroundPolarOneNumerator410, eval_add, eval_sub,
    eval_mul, eval_pow, eval_C, eval_ofNat, eval_neg, hvis, hw73,
    hq54, ha1, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    zero_sub, neg_zero]

/-- The constant-free `η` derivative tie: since the solved polar-`2`
cofactor itself vanishes at the root (the polar-`1` block dies there),
the derivative of the `η` pin at the root is constant-free —
`4 q₂'(a) = 3 t₂(a) b₃₁'(a) + (4 a₂₂(a) - 3 t₂(a)²) b₄₂'(a)`. -/
theorem etaPin_rootDerivativeKill410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 : F[X])
    (lambda ceta : F) (a : F)
    (hnpin : etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda +
        h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * etaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C ceta * h0 ^ 2)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (hw73 : w73.eval a = 0) (hq54 : q54.eval a = 0)
    (ha1 : a1.eval a = 0) (hb42 : b42.eval a = 0)
    (hb31 : b31.eval a = 0) :
    (4 : F) * (derivative b2).eval a =
      (3 : F) * t2.eval a * (derivative b31).eval a +
        ((4 : F) * a22.eval a - (3 : F) * (t2.eval a) ^ 2) *
          (derivative b42).eval a := by
  have hP1a := etaPolarOne_rootEval410 t2 a22 s22 vis w73 q54 a1 a0
    lambda a hvis hw73 hq54 ha1
  have hs : etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
      b42 b31 b2 lambda =
      Polynomial.C ceta * (h0 * h0) -
        h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda -
        h0 * (h0 * etaGroundRegularNumerator410 t2 a22 s22 a0
          lambda) := by
    linear_combination hnpin
  have hd1 := congrArg (fun r : F[X] => derivative r) hs
  simp only [etaGroundPolarTwoNumerator410, pow_two, derivative_add,
    derivative_sub, derivative_mul, derivative_ofNat, derivative_C,
    zero_mul, mul_zero, zero_add, add_zero] at hd1
  have heval := congrArg (fun r : F[X] => r.eval a) hd1
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_ofNat, hroot,
    hvis, hw73, hq54, ha1, hb42, hb31, hP1a, zero_mul, mul_zero,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero] at heval
  linear_combination ((1 : F) / 8192) * heval

/-- The exact `η` derivative kill: combining the constant-free `η`
derivative tie with the `ε` derivative kill `b₄₂'(a) = 0` and the `ζ`
derivative kill `b₃₁'(a) = 0` forces `q₂'(a) = 0` — `q₂` vanishes
DOUBLY at the root of `h₀`, the third unconditional derivative-level
kill of the nonzero face. -/
theorem etaPin_rootDerivativeKillFull410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 : F[X])
    (lambda cepsilon czeta ceta : F) (a : F)
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
    (hnpin : etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda +
        h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * etaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C ceta * h0 ^ 2)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (hw73 : w73.eval a = 0) (hq54 : q54.eval a = 0)
    (ha1 : a1.eval a = 0) :
    (derivative b2).eval a = 0 := by
  have hee := epsilonGroundPin_rootEval410 h0 t2 a22 s22 vis w73 q54
    a1 a0 b42 lambda cepsilon a hepin hroot
  have hb42a : b42.eval a = 0 := by
    linear_combination ((1 : F) / 2048) * hee +
      ((7 : F) / 4) * vis.eval a * ha1 -
      ((5 : F) / 2) * a1.eval a * ha1
  have hze := zetaGroundPin_rootEval410 h0 t2 a22 s22 vis w73 q54 a1
    a0 b42 b31 lambda czeta a hzpin hroot
  have hb31a : b31.eval a = 0 := by
    linear_combination ((1 : F) / 131072) * hze +
      t2.eval a * hb42a +
      (((35 : F) / 32) * a1.eval a * t2.eval a +
        ((63 : F) / 64) * lambda * a1.eval a -
        ((49 : F) / 16) * t2.eval a * vis.eval a +
        ((3 : F) / 2) * w73.eval a) * ha1
  have hkb42 := epsilonPin_rootDerivativeKill410 h0 t2 a22 s22 vis
    w73 q54 a1 a0 b42 lambda cepsilon a hepin hroot hvis hw73 hq54
    ha1
  have hkb31 := zetaPin_rootDerivativeKillFull410 h0 t2 a22 s22 vis
    w73 q54 a1 a0 b42 b31 lambda cepsilon czeta a hepin hzpin hroot
    hvis hw73 hq54 ha1
  have h1 := etaPin_rootDerivativeKill410 h0 t2 a22 s22 vis w73 q54
    a1 a0 b42 b31 b2 lambda ceta a hnpin hroot hvis hw73 hq54 ha1
    hb42a hb31a
  linear_combination ((1 : F) / 4) * h1 +
    ((3 : F) / 4) * t2.eval a * hkb31 +
    (a22.eval a - ((3 : F) / 4) * (t2.eval a) ^ 2) * hkb42

set_option maxHeartbeats 6400000 in
/-- Sharpest honest `η` residual, one derivative below the exact kill:
the second derivative of the `η` pin at the root ties `q₂''(a)`,
`b₃₁''(a)`, `b₄₂''(a)` and the derivative jet against `c_η` — the
third second-derivative-level residual of the lane, with `c_η` pinned
against `h₀'(a)²`. -/
theorem etaPin_rootSecondDerivativeTie410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 : F[X])
    (lambda ceta : F) (a : F)
    (hnpin : etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda +
        h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda +
        h0 ^ 2 * etaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
      Polynomial.C ceta * h0 ^ 2)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (hw73 : w73.eval a = 0) (hq54 : q54.eval a = 0)
    (ha1 : a1.eval a = 0) (hb42 : b42.eval a = 0)
    (hb31 : b31.eval a = 0) :
    (32768 : F) * (derivative (derivative b2)).eval a -
        (24576 : F) * t2.eval a *
          (derivative (derivative b31)).eval a +
        (24576 : F) * (t2.eval a) ^ 2 *
          (derivative (derivative b42)).eval a -
        (32768 : F) * a22.eval a *
          (derivative (derivative b42)).eval a -
        (49152 : F) * (derivative t2).eval a *
          (derivative b31).eval a +
        (98304 : F) * t2.eval a * (derivative t2).eval a *
          (derivative b42).eval a -
        (65536 : F) * (derivative a22).eval a *
          (derivative b42).eval a -
        (307200 : F) * a22.eval a * ((derivative a1).eval a) ^ 2 +
        (138240 : F) * lambda * t2.eval a *
          ((derivative a1).eval a) ^ 2 +
        (98304 : F) * s22.eval a * ((derivative a1).eval a) ^ 2 -
        (153600 : F) * (t2.eval a) ^ 2 *
          ((derivative a1).eval a) ^ 2 +
        (172032 : F) * (derivative a1).eval a * a22.eval a *
          (derivative vis).eval a -
        (215040 : F) * (derivative a1).eval a * (t2.eval a) ^ 2 *
          (derivative vis).eval a +
        (147456 : F) * (derivative a1).eval a * t2.eval a *
          (derivative w73).eval a -
        (81920 : F) * (derivative a1).eval a *
          (derivative q54).eval a =
      (2 : F) * (derivative h0).eval a *
        (ceta * (derivative h0).eval a -
          (derivative (etaGroundPolarOneNumerator410 t2 a22 s22 vis
              w73 q54 a1 a0 lambda)).eval a -
          (derivative h0).eval a *
            (etaGroundRegularNumerator410 t2 a22 s22 a0
                lambda).eval a) := by
  have hP1a := etaPolarOne_rootEval410 t2 a22 s22 vis w73 q54 a1 a0
    lambda a hvis hw73 hq54 ha1
  have hs : etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
      b42 b31 b2 lambda =
      Polynomial.C ceta * (h0 * h0) -
        h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
          a0 lambda -
        h0 * (h0 * etaGroundRegularNumerator410 t2 a22 s22 a0
          lambda) := by
    linear_combination hnpin
  have hd2 := congrArg (fun r : F[X] => derivative (derivative r)) hs
  simp only [etaGroundPolarTwoNumerator410, pow_two, derivative_add,
    derivative_sub, derivative_mul, derivative_ofNat, derivative_C,
    zero_mul, mul_zero, zero_add, add_zero] at hd2
  have heval := congrArg (fun r : F[X] => r.eval a) hd2
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_ofNat, hroot,
    hvis, hw73, hq54, ha1, hb42, hb31, hP1a, zero_mul, mul_zero,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero] at heval
  linear_combination heval

end EtaGroundClearing410

/-! ## Source-facing ground power relation at exact order `-2` -/

section NonzeroEtaGroundBridge410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 12800000 in
/-- The row-`5` ground first integral `η` on a square-core ninth-power
source, traced from the literal Keller row through the eighth-face
power relation and expressed at its exact order `-2` on the
thirteenth-face jet: the polar-`2` block plus `h₀` times the polar-`1`
block plus `h₀²` times the regular block is GLOBALLY `C c_η h₀²` —
the third order-`-2` ground pin of the lane, the first seeing `q₂`,
and the LAST ground row of the nonzero face. -/
theorem nonzeroFace410_etaResidualPowerRelation
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
    ∃ ceta : k,
      etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) b42 b31 (q.coeff 2) lambda +
        h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) lambda +
        h0 ^ 2 * etaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
          lambda =
      Polynomial.C ceta * h0 ^ 2 := by
  obtain ⟨ceta, hpow⟩ :=
    nonzeroFace410_eighthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  refine ⟨ceta, ?_⟩
  have h24 : h0 ^ 24 ≠ 0 := pow_ne_zero 24 hh0
  apply mul_left_cancel₀ h24
  calc
    h0 ^ 24 *
          (etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54
              (p.coeff 1) b42 b31 (q.coeff 2) lambda +
            h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73
              q54 (p.coeff 1) (p.coeff 0) lambda +
            h0 ^ 2 * etaGroundRegularNumerator410 t2 a22 s22
              (p.coeff 0) lambda) =
        localClearedEighthDefect410 h0 (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2) lambda := by
      simp only [localClearedEighthDefect410,
        etaGroundPolarTwoNumerator410,
        etaGroundPolarOneNumerator410,
        etaGroundRegularNumerator410, hp3, hp2, hq8, hq7, hq6, hq5,
        hq4, hq3]
      ring
    _ = Polynomial.C ceta * h0 ^ 26 := hpow
    _ = h0 ^ 24 * (Polynomial.C ceta * h0 ^ 2) := by ring

/-! ## Eta ground bridge packet -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 51200000 in
/-- Sharpest exact successor packet of the `η` ground bridge on the
nonzero `(4,10)` face: everything from the zeta ground bridge packet,
together with the row-`5` ground pin at its exact order `-2` — the
third order-`-2` ground pin of the lane, the first seeing `q₂`, and
the LAST ground row of the nonzero face — its first `h`-adic peel
step in solved form, the `ζ`-eliminated `q₂` pin (whose left side is
`2048` times the global polynomial lift of the jet tie `hY`), the
fully eliminated `q₂` pin — the first global SEVEN-ground-constant
link of the lane, with cofactor `ueta` bound explicitly — the
`η`-loaded factored forms of the second `θ` and `ι` peel steps (the
letter `q₂` eliminated; NO letter survives polar-side in EITHER
tower: every residual polar monomial carries `p₁²`), the
constant-free derivative tie `4 q₂'(a) = 3 t₂(a) b₃₁'(a) +
(4 a₂₂(a) - 3 t₂(a)²) b₄₂'(a)`, the EXACT derivative kill
`q₂'(a) = 0` (`q₂` vanishes doubly at the root — the third
unconditional derivative-level kill of the nonzero face), and the
second-derivative root tie — the sharpest honest `η` residual,
pinning `c_η` against `h₀'(a)²`.  Nothing here closes the face or a
branch: `c_α, c_β, c_γ, c_δ, c_ε, c_ζ, c_η` are free, so the pins
eliminate no configuration; no root branch is forced; `t₂(a),
a₂₂(a), s₂₂(a), q₁(a), q₀(a), c_α, c_β, c_γ, c_δ, c_ε, c_ζ, c_η,
c_θ, c, j, p₀'(a), q₀'(a)` remain free or tied-not-determined, and
the ground tower of the nonzero face is EXHAUSTED — no unused ground
row remains. -/
theorem nonzeroFace410_etaGroundBridgePacket
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
    ∃ (calpha cbeta cgamma cdelta cepsilon czeta ceta ctheta c : k)
      (v1 v2 v3 w1 w2 w3 ueps uzeta ueta : k[X]),
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
                  lambda).eval a) ∧
      etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) b42 b31 (q.coeff 2) lambda +
          h0 * etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
            (p.coeff 1) (p.coeff 0) lambda +
          h0 ^ 2 * etaGroundRegularNumerator410 t2 a22 s22
            (p.coeff 0) lambda =
        Polynomial.C ceta * h0 ^ 2 ∧
      etaGroundPolarTwoNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) b42 b31 (q.coeff 2) lambda =
        h0 * (Polynomial.C ceta * h0 -
          etaGroundPolarOneNumerator410 t2 a22 s22 vis w73 q54
            (p.coeff 1) (p.coeff 0) lambda -
          h0 * etaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
            lambda) ∧
      (524288 : k[X]) * q.coeff 2 -
      (524288 : k[X]) * (p.coeff 1) ^ 2 * s22 +
      (819200 : k[X]) * (p.coeff 1) ^ 2 * a22 -
      (497664 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 * t2 +
      (1105920 : k[X]) * (p.coeff 1) ^ 2 * t2 ^ 2 =
        h0 * ((16 : k[X]) * Polynomial.C ceta * h0 +
          (3 : k[X]) * t2 * uzeta +
          ((32 : k[X]) * a22 - (24 : k[X]) * t2 ^ 2) * ueps +
          (160 : k[X]) * p.coeff 1 * (Polynomial.C cdelta -
            deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
              lambda) -
          (1536 : k[X]) * p.coeff 1 * t2 * (Polynomial.C cgamma -
            gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
              lambda) +
          ((1344 : k[X]) * p.coeff 1 * t2 ^ 2 -
              (3584 : k[X]) * p.coeff 1 * a22) *
            (Polynomial.C cbeta -
              betaGroundRegularNumerator410 t2 a22 s22 lambda) -
          (16 : k[X]) * etaGroundPolarOneNumerator410 t2 a22 s22 vis
            w73 q54 (p.coeff 1) (p.coeff 0) lambda -
          (16 : k[X]) * h0 * etaGroundRegularNumerator410 t2 a22 s22
            (p.coeff 0) lambda) ∧
      ueta = (983040 : k[X]) * p.coeff 0 * p.coeff 1 * t2 -
        (737280 : k[X]) * Polynomial.C lambda * p.coeff 0 * p.coeff 1 -
        (245760 : k[X]) * p.coeff 1 * a22 ^ 2 * t2 -
        (92160 : k[X]) * Polynomial.C lambda * p.coeff 1 * a22 ^ 2 +
        (122880 : k[X]) * p.coeff 1 * a22 * t2 ^ 3 +
        (69120 : k[X]) * Polynomial.C lambda * p.coeff 1 * a22 * t2 ^ 2 +
        (10752 : k[X]) * Polynomial.C cbeta * p.coeff 1 * a22 -
        (1344 : k[X]) * Polynomial.C cbeta * p.coeff 1 * t2 ^ 2 +
        (160 : k[X]) * Polynomial.C cdelta * p.coeff 1 +
        (3072 : k[X]) * Polynomial.C cgamma * p.coeff 1 * t2 -
        (10080 : k[X]) * Polynomial.C lambda * p.coeff 1 * t2 ^ 4 -
        (15360 : k[X]) * p.coeff 1 * t2 ^ 5 +
          h0 * ((16 : k[X]) * Polynomial.C ceta +
          (3 : k[X]) * Polynomial.C czeta * t2 +
          (256 : k[X]) * Polynomial.C cepsilon * a22 +
          (40 : k[X]) * Polynomial.C cdelta * a22 * t2 -
          (5 : k[X]) * Polynomial.C cdelta * t2 ^ 3 +
          (6144 : k[X]) * Polynomial.C cgamma * p.coeff 0 +
          (1536 : k[X]) * Polynomial.C cgamma * a22 ^ 2 -
          (768 : k[X]) * Polynomial.C cgamma * a22 * t2 ^ 2 +
          (96 : k[X]) * Polynomial.C cgamma * t2 ^ 4 +
          (10752 : k[X]) * Polynomial.C cbeta * p.coeff 0 * t2 -
          (1344 : k[X]) * Polynomial.C cbeta * a22 ^ 2 * t2 +
          (560 : k[X]) * Polynomial.C cbeta * a22 * t2 ^ 3 -
          (63 : k[X]) * Polynomial.C cbeta * t2 ^ 5 +
          (131072 : k[X]) * Polynomial.C calpha * p.coeff 0 * a22 +
          (983040 : k[X]) * (p.coeff 0) ^ 2 +
          (491520 : k[X]) * p.coeff 0 * a22 ^ 2 -
          (245760 : k[X]) * p.coeff 0 * a22 * t2 ^ 2 -
          (184320 : k[X]) * Polynomial.C lambda * p.coeff 0 * a22 * t2 +
          (30720 : k[X]) * p.coeff 0 * t2 ^ 4 +
          (23040 : k[X]) * Polynomial.C lambda * p.coeff 0 * t2 ^ 3 -
          (20480 : k[X]) * a22 ^ 4 +
          (61440 : k[X]) * a22 ^ 3 * t2 ^ 2 +
          (23040 : k[X]) * Polynomial.C lambda * a22 ^ 3 * t2 -
          (38400 : k[X]) * a22 ^ 2 * t2 ^ 4 -
          (20160 : k[X]) * Polynomial.C lambda * a22 ^ 2 * t2 ^ 3 +
          (8960 : k[X]) * a22 * t2 ^ 6 +
          (5544 : k[X]) * Polynomial.C lambda * a22 * t2 ^ 5 -
          (720 : k[X]) * t2 ^ 8 -
          (495 : k[X]) * Polynomial.C lambda * t2 ^ 7) ∧
          (524288 : k[X]) * q.coeff 2 -
          (65536 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 -
          (491520 : k[X]) * (p.coeff 1) ^ 2 * a22 +
          (92160 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 * t2 +
          (122880 : k[X]) * (p.coeff 1) ^ 2 * t2 ^ 2 =
        h0 * ueta ∧
      v1 - (8192 : k[X]) *
          ((3600 : k[X]) * (p.coeff 1) ^ 2 * a22 * t2 +
          (1260 : k[X]) * (p.coeff 1) ^ 2 * t2 ^ 3 -
          (1080 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 * t2 ^ 2 +
          (48 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 * t2) =
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
          ((96 : k[X]) * a22 - (60 : k[X]) * t2 ^ 2) * uzeta +
          (16 : k[X]) * t2 * ueta) ∧
      (262144 : k[X]) * w1 + (6144 : k[X]) *
          ((1080 : k[X]) * (p.coeff 1) ^ 2 * a22 * t2 ^ 2 +
          (18 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 * a22 * t2 -
          (160 : k[X]) * (p.coeff 1) ^ 2 * a22 ^ 2 +
          (32 : k[X]) * Polynomial.C calpha * (p.coeff 1) ^ 2 * t2 ^ 2 -
          (315 : k[X]) * Polynomial.C lambda * (p.coeff 1) ^ 2 * t2 ^ 3 +
          (300 : k[X]) * (p.coeff 1) ^ 2 * t2 ^ 4) =
        h0 * ((262144 : k[X]) * w2 -
          (640 : k[X]) * p.coeff 1 * (a22 - t2 ^ 2) *
            (Polynomial.C cdelta -
              deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) +
          (6144 : k[X]) * p.coeff 1 * t2 *
              ((3 : k[X]) * a22 + t2 ^ 2) *
            (Polynomial.C cgamma -
              gammaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                lambda) -
          (1792 : k[X]) * p.coeff 1 *
              ((32 : k[X]) * p.coeff 0 + (8 : k[X]) * a22 ^ 2 -
                (25 : k[X]) * a22 * t2 ^ 2 + t2 ^ 4) *
            (Polynomial.C cbeta -
              betaGroundRegularNumerator410 t2 a22 s22 lambda) -
          (32 : k[X]) * (-(4 : k[X]) * p.coeff 0 +
              (2 : k[X]) * a22 ^ 2 - (4 : k[X]) * a22 * t2 ^ 2 +
              t2 ^ 4) * ueps -
          ((12 : k[X]) * a22 * t2 - (4 : k[X]) * t2 ^ 3) * uzeta +
          ((2 : k[X]) * a22 - t2 ^ 2) * ueta) ∧
      (4 : k) * (derivative (q.coeff 2)).eval a =
        (3 : k) * t2.eval a * (derivative b31).eval a +
          ((4 : k) * a22.eval a - (3 : k) * (t2.eval a) ^ 2) *
            (derivative b42).eval a ∧
      (derivative (q.coeff 2)).eval a = 0 ∧
      (32768 : k) * (derivative (derivative (q.coeff 2))).eval a -
          (24576 : k) * t2.eval a *
            (derivative (derivative b31)).eval a +
          (24576 : k) * (t2.eval a) ^ 2 *
            (derivative (derivative b42)).eval a -
          (32768 : k) * a22.eval a *
            (derivative (derivative b42)).eval a -
          (49152 : k) * (derivative t2).eval a *
            (derivative b31).eval a +
          (98304 : k) * t2.eval a * (derivative t2).eval a *
            (derivative b42).eval a -
          (65536 : k) * (derivative a22).eval a *
            (derivative b42).eval a -
          (307200 : k) * a22.eval a *
            ((derivative (p.coeff 1)).eval a) ^ 2 +
          (138240 : k) * lambda * t2.eval a *
            ((derivative (p.coeff 1)).eval a) ^ 2 +
          (98304 : k) * s22.eval a *
            ((derivative (p.coeff 1)).eval a) ^ 2 -
          (153600 : k) * (t2.eval a) ^ 2 *
            ((derivative (p.coeff 1)).eval a) ^ 2 +
          (172032 : k) * (derivative (p.coeff 1)).eval a *
            a22.eval a * (derivative vis).eval a -
          (215040 : k) * (derivative (p.coeff 1)).eval a *
            (t2.eval a) ^ 2 * (derivative vis).eval a +
          (147456 : k) * (derivative (p.coeff 1)).eval a *
            t2.eval a * (derivative w73).eval a -
          (81920 : k) * (derivative (p.coeff 1)).eval a *
            (derivative q54).eval a =
        (2 : k) * (derivative h0).eval a *
          (ceta * (derivative h0).eval a -
            (derivative (etaGroundPolarOneNumerator410 t2 a22 s22
                vis w73 q54 (p.coeff 1) (p.coeff 0) lambda)).eval a -
            (derivative h0).eval a *
              (etaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
                  lambda).eval a) := by
  obtain ⟨calpha, cbeta, cgamma, cdelta, cepsilon, czeta, ctheta, c,
    v1, v2, v3, w1, w2, w3, ueps, uzeta, hpin, hsolve, hpowT, htw1,
    htw2, htw3, htwc, hpowI, hiw1, hiw2, hiw3, hiwc, hTglobal,
    hIglobal, ha1, hvis0, hw730, hq540, hb420, hb310, hb20, hv10,
    hw10, hv2tie, hw2tie, hrootS, hTroot, hIroot, hkelP, hcombo, hbr,
    hbpin, hbsolve, hbalpha, hbtheta, hbiota, hbderiv, hbderivA,
    hgpin, hgsolve, hgalpha, hw73B, hw73F, hgiota, hgderiv, hw73deriv,
    hdpin, hdsolve, hdalpha, hq54BG, hq54F, hthetaP2, hiotaP2,
    hdderiv, hq54deriv, hepin, hesolve, hb42B, hueps, hb42tie,
    hthetaE, hiotaE, hb42kill, h2tie, hzpin, hzsolve, hb31B, huzeta,
    hb31full, hthetaZ, hiotaZ, hkill1, hkill0, hz2tie⟩ :=
    nonzeroFace410_zetaGroundBridgePacket p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 a hp hq hh0 hH hp4 hq10 hN hD hp3 hp2
      hq8 hq7 hq6 hq5 hq4 hq3 hroot hT hU hW hV hX hY
  obtain ⟨ceta, hnpin⟩ :=
    nonzeroFace410_etaResidualPowerRelation p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 hp hq hh0 hH hp4 hq10 hN hD hp3 hp2 hq8
      hq7 hq6 hq5 hq4 hq3
  have hnsolve := etaGroundPin_solvePolarTwo410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) lambda ceta hnpin
  have hq2B := q2GroundPin_zetaEliminated410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) ueps uzeta lambda
    cbeta cgamma cdelta ceta hbpin hgpin hdpin hb42tie hb31full hnpin
  have hq2full := q2GroundPin_fullyEliminated410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) lambda calpha
    cbeta cgamma cdelta cepsilon czeta ceta hpin hbpin hgpin hdpin
    hepin hzpin hnpin
  have hthetaN := thetaSecondPeel_etaLoaded410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) v1 v2 ueps uzeta
    _ lambda calpha cbeta cgamma cdelta hpin hbpin hgpin hdpin
    hb42tie hb31full hq2full htw2
  have hiotaN := iotaSecondPeel_etaLoaded410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) w1 w2 ueps uzeta
    _ lambda calpha cbeta cgamma cdelta hpin hbpin hgpin hdpin
    hb42tie hb31full hq2full hiw2
  have hq2dtie := etaPin_rootDerivativeKill410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) lambda ceta a
    hnpin hroot hvis0 hw730 hq540 ha1 hb420 hb310
  have hq2kill : (derivative (q.coeff 2)).eval a = 0 := by
    linear_combination ((1 : k) / 4) * hq2dtie +
      ((3 : k) / 4) * t2.eval a * hkill0 +
      (a22.eval a - ((3 : k) / 4) * (t2.eval a) ^ 2) * hb42kill
  have hn2tie := etaPin_rootSecondDerivativeTie410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) lambda ceta a
    hnpin hroot hvis0 hw730 hq540 ha1 hb420 hb310
  exact ⟨calpha, cbeta, cgamma, cdelta, cepsilon, czeta, ceta,
    ctheta, c, v1, v2, v3, w1, w2, w3, ueps, uzeta, _, hpin, hsolve,
    hpowT, htw1, htw2, htw3, htwc, hpowI, hiw1, hiw2, hiw3, hiwc,
    hTglobal, hIglobal, ha1, hvis0, hw730, hq540, hb420, hb310, hb20,
    hv10, hw10, hv2tie, hw2tie, hrootS, hTroot, hIroot, hkelP,
    hcombo, hbr, hbpin, hbsolve, hbalpha, hbtheta, hbiota, hbderiv,
    hbderivA, hgpin, hgsolve, hgalpha, hw73B, hw73F, hgiota, hgderiv,
    hw73deriv, hdpin, hdsolve, hdalpha, hq54BG, hq54F, hthetaP2,
    hiotaP2, hdderiv, hq54deriv, hepin, hesolve, hb42B, hueps,
    hb42tie, hthetaE, hiotaE, hb42kill, h2tie, hzpin, hzsolve, hb31B,
    huzeta, hb31full, hthetaZ, hiotaZ, hkill1, hkill0, hz2tie, hnpin,
    hnsolve, hq2B, rfl, hq2full, hthetaN, hiotaN, hq2dtie, hq2kill,
    hn2tie⟩

end NonzeroEtaGroundBridge410

#print axioms etaDefect_eq_cleared410
#print axioms etaGroundPin_solvePolarTwo410
#print axioms etaGroundPin_rootEval410
#print axioms etaGroundPin_rootEval_reDerivesY410
#print axioms q2GroundPin_zetaEliminated410
#print axioms q2GroundPin_fullyEliminated410
#print axioms thetaSecondPeel_etaLoaded410
#print axioms iotaSecondPeel_etaLoaded410
#print axioms etaPolarOne_rootEval410
#print axioms etaPin_rootDerivativeKill410
#print axioms etaPin_rootDerivativeKillFull410
#print axioms etaPin_rootSecondDerivativeTie410
#print axioms nonzeroFace410_etaResidualPowerRelation
#print axioms nonzeroFace410_etaGroundBridgePacket

end Max11DegreeRoutes
