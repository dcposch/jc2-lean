import Fable410ScaleTwoGammaGroundBridgeScratch

/-! # Delta ground bridge for the normalized `(4,10)` nonzero source

The gamma ground bridge pinned the row-`9` ground first integral `γ`
at exact order `-1` and produced the first three-ground-constant link.
The next ground first integral is `δ = S - (9/4) L C - 2 α B -
(7/4) β A - (15/4) A B - (45/32) L A²` (row `8`, `deltaResidual410`,
fifth face).  On the thirteenth-face jet it again sits at EXACT order
`-1`, but its polar residue block now carries a CROSS-TERM: the
order-`-1` letter `p₁` multiplies the regular-level letter `s₂₂`.

First, the clearing (`deltaDefect_eq_cleared410`): `4096 h δ` splits
as the polar residue block `4096 q₅₄ - 6144 t₂ w₇₃ + 8064 t₂² q₇₆ -
7168 a₂₂ q₇₆ + 14400 p₁ t₂² - 8192 p₁ s₂₂ - 10368 λ p₁ t₂ +
23040 p₁ a₂₂` plus `h` times the regular block `-9984 t₂³ s₂₂ +
15912 t₂⁵ - 5967 λ t₂⁴ - 31200 a₂₂ t₂³ + 18432 a₂₂ t₂ s₂₂ +
16848 λ a₂₂ t₂² - 11520 a₂₂² t₂ - 5184 λ a₂₂² + 4608 λ p₀`.

Second, the literal-source trace: the fifth-face power relation pins
the row-`8` integral globally (`nonzeroFace410_fifthDefectPowerRelation`,
weight `17`); substituting the thirteenth-face jet forms and cancelling
`h₀¹⁶` gives the ground pin at its exact order
(`nonzeroFace410_deltaResidualPowerRelation`):
`polar + h₀ · (regular) = C c_δ h₀`.  Its `h`-adic peel is one step
(`deltaGroundPin_solvePolar410`), and the root evaluation combined
with the `β` and `γ` pins RE-DERIVES the thirteenth-face jet
hypothesis `hV` from the literal source
(`deltaGroundPin_rootEval_reDerivesV410`): `32 q₅₄(a) +
40 p₁(a) a₂₂(a) - 64 p₁(a) s₂₂(a) - 27 p₁(a) λ t₂(a) +
90 p₁(a) t₂(a)² = 0` — rows `10`, `9`, `8` alone force it.

Third, the eliminations.  The global `α` pin now acts on BOTH blocks:
it eliminates `s₂₂` from the regular block (cofactor
`-9984 t₂³ + 18432 a₂₂ t₂`) AND from the polar cross-term (cofactor
`-8192 p₁`), the first polar-side action of `α` in the lane
(`deltaGroundPin_alphaEliminated410`).  The `β` and `γ` pins eliminate
the polar letters `q₇₆` and `w₇₃` from the `δ` polar block:
`1 δ-pin + 48 t₂ γ-pin + (42 t₂² + 112 a₂₂) β-pin` collapses to the
`q₅₄` PIN (`q54GroundPin_betaGammaEliminated410`)
`4096 q₅₄ - 8192 p₁ s₂₂ + 11520 p₁ t₂² - 3456 λ p₁ t₂ + 5120 p₁ a₂₂ =
h₀ ((C c_δ - reg_δ) + 48 t₂ (C c_γ - reg_γ) + (42 t₂² + 112 a₂₂)
(C c_β - reg_β))` — whose left side is `128` times the LITERAL
polynomial lift of the jet tie `hV`: the root tie of the thirteenth
face is the root shadow of this global pin.  With the cross-term
`α`-eliminated it becomes the first FOUR-ground-constant link of the
lane (`q54GroundPin_fullyEliminated410`):
`4096 q₅₄ - 1024 C c_α p₁ - 3840 p₁ t₂² + 5760 λ p₁ t₂ -
15360 p₁ a₂₂ = h₀ (C c_δ + 48 C c_γ t₂ + 42 C c_β t₂² +
112 C c_β a₂₂ + 1024 C c_α a₂₂ t₂ + 48 t₂⁵ + 45 λ t₂⁴ - 640 a₂₂ t₂³ -
720 λ a₂₂ t₂² + 3840 a₂₂² t₂ - 2880 λ a₂₂² + 15360 p₀ t₂ -
4608 λ p₀)` — the first pin carrying a ground constant (`c_α`) on the
polar side, and the `C c_α t₂³` cofactor cancels exactly in the
combination.

Fourth, the combination with the terminal packet: the first UNUSED
peel steps of both towers are the order-`-2` blocks (the order-`-3`
blocks were `β`/`γ`-loaded by the previous bridges), and they are the
first peel steps seeing `q₅₄`.  The four pins `α, β, γ, δ` eliminate
ALL FOUR polar letters `s₂₂, q₇₆, w₇₃, q₅₄` from them in factored
form — only the order-`-2` letters `b₄₂, b₃₁, q₂` survive polar-side
(`thetaSecondPeel_deltaLoaded410`, `iotaSecondPeel_deltaLoaded410`):
`v₁ - 8192 (6000 p₁² a₂₂ t₂ + 1080 λ p₁² a₂₂ + 600 p₁² t₂³ -
1575 λ p₁² t₂² - 80 C c_α p₁² t₂ + 1536 a₂₂ b₃₁ - 2560 a₂₂ b₄₂ t₂ +
960 b₄₂ t₂³ - 960 b₃₁ t₂² + 1024 q₂ t₂) = h₀ (v₂ - 6400 p₁ t₂
(C c_δ - reg_δ) - p₁ (245760 a₂₂ + 30720 t₂²) (C c_γ - reg_γ) -
286720 p₁ a₂₂ t₂ (C c_β - reg_β))` and the `2048`-scaled `ι` analog
with cofactors `5 p₁ (a₂₂ - t₂²)`, `48 p₁ t₂ (3 a₂₂ + t₂²)`,
`14 p₁ (32 p₀ + 8 a₂₂² - 25 a₂₂ t₂² + t₂⁴)`.

The sharpest `δ`-loaded residuals are one derivative deeper: since
`q₅₄` enters linearly and `q₇₆(a) = w₇₃(a) = p₁(a) = 0`,
differentiating the pins at the root gives
(`deltaGroundPin_rootDerivativeTie410`) and, fully eliminated,
(`q54Pin_rootDerivativeTie_fullyEliminated410`):
`4096 q₅₄'(a) - 1024 c_α p₁'(a) - 3840 t₂(a)² p₁'(a) +
5760 λ t₂(a) p₁'(a) - 15360 a₂₂(a) p₁'(a) = h₀'(a) (c_δ +
48 c_γ t₂(a) + 42 c_β t₂(a)² + 112 c_β a₂₂(a) +
1024 c_α a₂₂(a) t₂(a) + 48 t₂(a)⁵ + 45 λ t₂(a)⁴ - 640 a₂₂(a) t₂(a)³ -
720 λ a₂₂(a) t₂(a)² + 3840 a₂₂(a)² t₂(a) - 2880 λ a₂₂(a)² +
15360 p₀(a) t₂(a) - 4608 λ p₀(a))` — all four ground constants pinned
against the derivative jet through `t₂(a), a₂₂(a), p₀(a), h₀'(a)`
only, with `c_α` now multiplying the derivative letter `p₁'(a)`.

Nothing here closes the face or a branch: `c_δ` is free, so the pin
eliminates no configuration; no root branch is forced (every peeled
block already vanishes at the root); `t₂(a), a₂₂(a), s₂₂(a), q₁(a),
q₀(a), c_α, c_β, c_γ, c_δ, c_θ, c, j, p₀'(a), q₀'(a), q₅₄'(a),
w₇₃'(a), q₇₆'(a), p₁'(a)` remain free or tied-not-determined; the
ground constant `ε` (row `7`, next: its sixth-defect clearing
`localClearedSixthDefect410 = C ζ h₀²⁰` sits at exact order `-2`,
polar-`2` block `2048 b₄₂ - 3584 p₁ q₇₆ + 5120 p₁²` — the first
ground clearing seeing `b₄₂`) stays uncleared.  No total-degree or
twice-prime theorem is used, and the aligned face `N = 0` is not
touched.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Exact order-`-1` clearing of `δ` on the thirteenth-face jet -/

section DeltaGroundClearing410

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- Order-`-1` (polar) numerator block of the cleared `δ` on the
thirteenth-face jet: the residue block of the four order-`-1` letters
`B`, `C`, `Q`, `S`.  It carries the first polar-level CROSS-TERM of
the lane: the order-`-1` letter `p₁` multiplies the regular-level
letter `s₂₂`. -/
def deltaGroundPolarNumerator410 (t2 a22 s22 vis w73 q54 a1 : F[X])
    (lambda : F) : F[X] :=
  (4096 : F[X]) * q54 - (6144 : F[X]) * t2 * w73 +
    (8064 : F[X]) * t2 ^ 2 * vis - (7168 : F[X]) * a22 * vis +
    (14400 : F[X]) * a1 * t2 ^ 2 - (8192 : F[X]) * a1 * s22 -
    (10368 : F[X]) * Polynomial.C lambda * a1 * t2 +
    (23040 : F[X]) * a1 * a22

/-- Regular (order-`0`) numerator block of the cleared `δ` on the
thirteenth-face jet.  It is linear in `s₂₂` with cofactor
`-9984 t₂³ + 18432 a₂₂ t₂`, and it sees the quartic constant `p₀`
only through the pure `λ` term `4608 λ p₀`. -/
def deltaGroundRegularNumerator410 (t2 a22 s22 a0 : F[X])
    (lambda : F) : F[X] :=
  -(9984 : F[X]) * t2 ^ 3 * s22 + (15912 : F[X]) * t2 ^ 5 -
    (5967 : F[X]) * Polynomial.C lambda * t2 ^ 4 -
    (31200 : F[X]) * a22 * t2 ^ 3 +
    (18432 : F[X]) * a22 * t2 * s22 +
    (16848 : F[X]) * Polynomial.C lambda * a22 * t2 ^ 2 -
    (11520 : F[X]) * a22 ^ 2 * t2 -
    (5184 : F[X]) * Polynomial.C lambda * a22 ^ 2 +
    (4608 : F[X]) * Polynomial.C lambda * a0

set_option maxHeartbeats 6400000 in
/-- Exact order-`-1` clearing of the fifth-face residual `δ` on the
thirteenth-face jet substitutions: `4096 h δ` is the polar residue
block plus `h` times the regular block, so `δ` sits at exact order
`-1`. -/
theorem deltaDefect_eq_cleared410
    (h t2 a22 s22 vis w73 q54 a1 a0 b9 lambda : F) (hh : h ≠ 0)
    (hN : 5 * (h ^ 3 * t2) * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (4096 : F) * h *
        deltaResidual410
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
          (depressedS410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73)
            (h ^ 4 * q54)) =
      ((4096 : F) * q54 - (6144 : F) * t2 * w73 +
          (8064 : F) * t2 ^ 2 * vis - (7168 : F) * a22 * vis +
          (14400 : F) * a1 * t2 ^ 2 - (8192 : F) * a1 * s22 -
          (10368 : F) * lambda * a1 * t2 + (23040 : F) * a1 * a22) +
        h * (-(9984 : F) * t2 ^ 3 * s22 + (15912 : F) * t2 ^ 5 -
          (5967 : F) * lambda * t2 ^ 4 - (31200 : F) * a22 * t2 ^ 3 +
          (18432 : F) * a22 * t2 * s22 +
          (16848 : F) * lambda * a22 * t2 ^ 2 -
          (11520 : F) * a22 ^ 2 * t2 -
          (5184 : F) * lambda * a22 ^ 2 +
          (4608 : F) * lambda * a0) := by
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
  have hS :
      depressedS410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) =
        ((252 : F) * t2 ^ 5 * h - 63 * lambda * t2 ^ 4 * h -
            224 * t2 ^ 3 * s22 * h + 336 * t2 ^ 2 * vis -
            384 * t2 * w73 + 256 * q54) / (256 * h) := by
    rw [depressedS410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) lambda hh hN]
    field_simp [hh]
  simp only [deltaResidual410, alphaResidual410, betaResidual410, hL,
    hA, hB, hC, hP, hQ, hS]
  field_simp [hh]
  ring

/-- The `δ` ground pin solves the order-`-1` polar block exactly: the
residue block is `h₀` times the explicit ground-loaded cofactor — a
factored `h`-adic quotient identity. -/
theorem deltaGroundPin_solvePolar410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 : F[X]) (lambda cdelta : F)
    (hpin : deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 a1
        lambda +
      h0 * deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cdelta * h0) :
    deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 a1 lambda =
      h0 * (Polynomial.C cdelta -
        deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda) := by
  linear_combination hpin

/-- Root evaluation of the `δ` ground pin: the polar residue block
vanishes at the root of `h₀`. -/
theorem deltaGroundPin_rootEval410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 : F[X]) (lambda cdelta : F)
    (a : F)
    (hpin : deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 a1
        lambda +
      h0 * deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cdelta * h0)
    (hroot : h0.eval a = 0) :
    (4096 : F) * q54.eval a - (6144 : F) * t2.eval a * w73.eval a +
        (8064 : F) * (t2.eval a) ^ 2 * vis.eval a -
        (7168 : F) * a22.eval a * vis.eval a +
        (14400 : F) * a1.eval a * (t2.eval a) ^ 2 -
        (8192 : F) * a1.eval a * s22.eval a -
        (10368 : F) * lambda * a1.eval a * t2.eval a +
        (23040 : F) * a1.eval a * a22.eval a = 0 := by
  have h := congrArg (fun r : F[X] => r.eval a) hpin
  simp only [deltaGroundPolarNumerator410, eval_add, eval_sub,
    eval_mul, eval_pow, eval_C, eval_ofNat, hroot, zero_mul, mul_zero,
    add_zero] at h
  linear_combination h

/-- Root evaluation of the `δ` ground pin combined with the `β` and
`γ` ground pins: the thirteenth-face tie `32 q₅₄(a) +
40 p₁(a) a₂₂(a) - 64 p₁(a) s₂₂(a) - 27 p₁(a) λ t₂(a) +
90 p₁(a) t₂(a)² = 0` (the jet hypothesis `hV`) is forced by the
literal source through the row-`10`, row-`9` and row-`8` integrals
alone. -/
theorem deltaGroundPin_rootEval_reDerivesV410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 : F[X])
    (lambda cbeta cgamma cdelta : F) (a : F)
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
    (hroot : h0.eval a = 0) :
    (32 : F) * q54.eval a +
        (40 : F) * a1.eval a * a22.eval a -
        (64 : F) * a1.eval a * s22.eval a -
        (27 : F) * a1.eval a * lambda * t2.eval a +
        (90 : F) * a1.eval a * (t2.eval a) ^ 2 = 0 := by
  have hbe := betaGroundPin_rootEval410 h0 t2 a22 s22 vis a1 lambda
    cbeta a hbpin hroot
  have hge := gammaGroundPin_rootEval410 h0 t2 a22 s22 vis w73 a1 a0
    lambda cgamma a hgpin hroot
  have hde := deltaGroundPin_rootEval410 h0 t2 a22 s22 vis w73 q54 a1
    a0 lambda cdelta a hdpin hroot
  linear_combination (1 / 128 : F) * hde +
    (3 / 8 : F) * t2.eval a * hge +
    ((21 : F) * (t2.eval a) ^ 2 + (56 : F) * a22.eval a) / 64 * hbe

/-- Factored elimination of `s₂₂` from BOTH blocks of the `δ` pin by
the global `α` pin: the regular block is linear in `s₂₂` with cofactor
`-9984 t₂³ + 18432 a₂₂ t₂`, and the polar cross-term `-8192 p₁ s₂₂`
is eliminated as well — the first polar-side action of the `α` pin in
the lane. -/
theorem deltaGroundPin_alphaEliminated410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 : F[X])
    (lambda calpha cdelta : F)
    (halpha : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha)
    (hdpin : deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 a1
        lambda +
      h0 * deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cdelta * h0) :
    (4096 : F[X]) * q54 - (6144 : F[X]) * t2 * w73 +
        (8064 : F[X]) * t2 ^ 2 * vis - (7168 : F[X]) * a22 * vis -
        (960 : F[X]) * a1 * t2 ^ 2 -
        (1152 : F[X]) * Polynomial.C lambda * a1 * t2 +
        (2560 : F[X]) * a1 * a22 -
        (1024 : F[X]) * Polynomial.C calpha * a1 =
      h0 * (Polynomial.C cdelta + (2808 : F[X]) * t2 ^ 5 -
        (5265 : F[X]) * Polynomial.C lambda * t2 ^ 4 +
        (21600 : F[X]) * a22 * t2 ^ 3 +
        (3888 : F[X]) * Polynomial.C lambda * a22 * t2 ^ 2 -
        (34560 : F[X]) * a22 ^ 2 * t2 +
        (5184 : F[X]) * Polynomial.C lambda * a22 ^ 2 -
        (4608 : F[X]) * Polynomial.C lambda * a0 +
        (1248 : F[X]) * Polynomial.C calpha * t2 ^ 3 -
        (2304 : F[X]) * Polynomial.C calpha * a22 * t2) := by
  have ha := halpha
  simp only [alphaGroundNumerator410] at ha
  have hd := hdpin
  simp only [deltaGroundPolarNumerator410,
    deltaGroundRegularNumerator410] at hd
  linear_combination hd +
    ((1024 : F[X]) * a1 - (2304 : F[X]) * h0 * a22 * t2 +
      (1248 : F[X]) * h0 * t2 ^ 3) * ha

/-- The `q₅₄` pin: the `β` and `γ` ground pins eliminate the polar
letters `q₇₆` and `w₇₃` from the `δ` polar block —
`1 δ-pin + 48 t₂ γ-pin + (42 t₂² + 112 a₂₂) β-pin` collapses to a pin
of `q₅₄` (and the cross-term `p₁ s₂₂`) alone against the regular
blocks, in factored `h`-adic quotient form.  Its left side is `128`
times the literal polynomial lift of the thirteenth-face jet tie
`hV`. -/
theorem q54GroundPin_betaGammaEliminated410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 : F[X])
    (lambda cbeta cgamma cdelta : F)
    (hbpin : betaGroundPolarNumerator410 vis a1 +
      h0 * betaGroundRegularNumerator410 t2 a22 s22 lambda =
        Polynomial.C cbeta * h0)
    (hgpin : gammaGroundPolarNumerator410 t2 w73 vis a1 lambda +
      h0 * gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cgamma * h0)
    (hdpin : deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 a1
        lambda +
      h0 * deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cdelta * h0) :
    (4096 : F[X]) * q54 - (8192 : F[X]) * a1 * s22 +
        (11520 : F[X]) * a1 * t2 ^ 2 -
        (3456 : F[X]) * Polynomial.C lambda * a1 * t2 +
        (5120 : F[X]) * a1 * a22 =
      h0 * ((Polynomial.C cdelta -
          deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda) +
        (48 : F[X]) * t2 * (Polynomial.C cgamma -
          gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda) +
        ((42 : F[X]) * t2 ^ 2 + (112 : F[X]) * a22) *
          (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda)) := by
  have hb := hbpin
  simp only [betaGroundPolarNumerator410] at hb
  have hg := hgpin
  simp only [gammaGroundPolarNumerator410] at hg
  have hd := hdpin
  simp only [deltaGroundPolarNumerator410] at hd
  linear_combination hd + (48 : F[X]) * t2 * hg +
    ((42 : F[X]) * t2 ^ 2 + (112 : F[X]) * a22) * hb

/-- The fully eliminated `q₅₄` pin: with `q₇₆, w₇₃` eliminated by the
`β` and `γ` pins and `s₂₂` (including the polar cross-term) eliminated
by the `α` pin, `q₅₄` is pinned against `t₂, a₂₂, p₀, c_α, c_β, c_γ,
c_δ` only — the first global FOUR-ground-constant link of the lane,
and the first pin with a ground constant (`c_α`) multiplying a jet
letter (`p₁`) on the polar side.  The `C c_α t₂³` regular cofactor
cancels exactly in the combination. -/
theorem q54GroundPin_fullyEliminated410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 : F[X])
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
        Polynomial.C cdelta * h0) :
    (4096 : F[X]) * q54 -
        (1024 : F[X]) * Polynomial.C calpha * a1 -
        (3840 : F[X]) * a1 * t2 ^ 2 +
        (5760 : F[X]) * Polynomial.C lambda * a1 * t2 -
        (15360 : F[X]) * a1 * a22 =
      h0 * (Polynomial.C cdelta +
        (48 : F[X]) * Polynomial.C cgamma * t2 +
        (42 : F[X]) * Polynomial.C cbeta * t2 ^ 2 +
        (112 : F[X]) * Polynomial.C cbeta * a22 +
        (1024 : F[X]) * Polynomial.C calpha * a22 * t2 +
        (48 : F[X]) * t2 ^ 5 +
        (45 : F[X]) * Polynomial.C lambda * t2 ^ 4 -
        (640 : F[X]) * a22 * t2 ^ 3 -
        (720 : F[X]) * Polynomial.C lambda * a22 * t2 ^ 2 +
        (3840 : F[X]) * a22 ^ 2 * t2 -
        (2880 : F[X]) * Polynomial.C lambda * a22 ^ 2 +
        (15360 : F[X]) * a0 * t2 -
        (4608 : F[X]) * Polynomial.C lambda * a0) := by
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
  linear_combination hd + (48 : F[X]) * t2 * hg +
    ((42 : F[X]) * t2 ^ 2 + (112 : F[X]) * a22) * hb +
    ((1024 : F[X]) * a1 + (1024 : F[X]) * h0 * a22 * t2) * ha

set_option maxHeartbeats 1600000 in
/-- `δ`-loaded second `θ` peel: the four ground pins `α, β, γ, δ`
eliminate ALL FOUR polar letters `s₂₂, q₇₆, w₇₃, q₅₄` from the
order-`-2` theta block — the first unused peel step of the `θ` tower —
in factored form.  Only the order-`-2` letters `b₄₂, b₃₁, q₂` survive
on the polar side. -/
theorem thetaSecondPeel_deltaLoaded410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 v1 v2 : F[X])
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
    (hpeel : v1 + thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        b42 b31 b2 lambda =
      h0 * v2) :
    v1 - (8192 : F[X]) *
        ((6000 : F[X]) * a1 ^ 2 * a22 * t2 +
          (1080 : F[X]) * Polynomial.C lambda * a1 ^ 2 * a22 +
          (600 : F[X]) * a1 ^ 2 * t2 ^ 3 -
          (1575 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 ^ 2 -
          (80 : F[X]) * Polynomial.C calpha * a1 ^ 2 * t2 +
          (1536 : F[X]) * a22 * b31 -
          (2560 : F[X]) * a22 * b42 * t2 +
          (960 : F[X]) * b42 * t2 ^ 3 -
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
            betaGroundRegularNumerator410 t2 a22 s22 lambda)) := by
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
    (655360 : F[X]) * a1 ^ 2 * t2 * ha

set_option maxHeartbeats 1600000 in
/-- `δ`-loaded second `ι` peel (scaled by `2048`): the four ground
pins eliminate ALL FOUR polar letters `s₂₂, q₇₆, w₇₃, q₅₄` from the
order-`-2` iota block — the first unused peel step of the `ι` tower —
in factored form.  Only the order-`-2` letters `b₄₂, b₃₁, q₂` survive
on the polar side. -/
theorem iotaSecondPeel_deltaLoaded410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 w1 w2 : F[X])
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
    (hpeel : w1 + iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1
        a0 b42 b31 b2 lambda =
      h0 * w2) :
    (2048 : F[X]) * w1 + (128 : F[X]) *
        ((240 : F[X]) * a0 * a1 ^ 2 -
          (128 : F[X]) * a0 * b42 -
          (120 : F[X]) * a1 ^ 2 * a22 ^ 2 +
          (8 : F[X]) * Polynomial.C calpha * a1 ^ 2 * a22 +
          (63 : F[X]) * Polynomial.C lambda * a1 ^ 2 * a22 * t2 +
          (510 : F[X]) * a1 ^ 2 * a22 * t2 ^ 2 +
          (8 : F[X]) * Polynomial.C calpha * a1 ^ 2 * t2 ^ 2 -
          (135 : F[X]) * Polynomial.C lambda * a1 ^ 2 * t2 ^ 3 +
          (90 : F[X]) * a1 ^ 2 * t2 ^ 4 +
          (64 : F[X]) * a22 ^ 2 * b42 -
          (64 : F[X]) * a22 * b2 +
          (96 : F[X]) * a22 * b31 * t2 -
          (128 : F[X]) * a22 * b42 * t2 ^ 2 +
          (32 : F[X]) * b2 * t2 ^ 2 -
          (32 : F[X]) * b31 * t2 ^ 3 +
          (32 : F[X]) * b42 * t2 ^ 4) =
      h0 * ((2048 : F[X]) * w2 -
        (5 : F[X]) * a1 * (a22 - t2 ^ 2) *
          (Polynomial.C cdelta -
            deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda) +
        (48 : F[X]) * a1 * t2 * ((3 : F[X]) * a22 + t2 ^ 2) *
          (Polynomial.C cgamma -
            gammaGroundRegularNumerator410 t2 a22 s22 a0 lambda) -
        (14 : F[X]) * a1 *
            ((32 : F[X]) * a0 + (8 : F[X]) * a22 ^ 2 -
              (25 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) *
          (Polynomial.C cbeta -
            betaGroundRegularNumerator410 t2 a22 s22 lambda)) := by
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
  linear_combination (2048 : F[X]) * hp -
    (5 : F[X]) * a1 * (a22 - t2 ^ 2) * hd +
    (48 : F[X]) * a1 * t2 * ((3 : F[X]) * a22 + t2 ^ 2) * hg -
    (14 : F[X]) * a1 *
      ((32 : F[X]) * a0 + (8 : F[X]) * a22 ^ 2 -
        (25 : F[X]) * a22 * t2 ^ 2 + t2 ^ 4) * hb -
    (1024 : F[X]) * a1 ^ 2 * (a22 + t2 ^ 2) * ha

/-- Root derivative of the solved `δ` polar form: since the polar
block is `h₀` times a cofactor, `h₀(a) = 0`, `q₅₄` enters linearly,
and the residue letters `q₇₆, w₇₃, p₁` vanish at the root, the
derivative combination at the root sees exactly `h₀'(a)` times the
cofactor value.  The cross-term contributes `s₂₂(a) p₁'(a)`. -/
theorem deltaPolar_rootDerivative_of_solved410
    (h0 t2 a22 s22 vis w73 q54 a1 u : F[X]) (lambda : F) (a : F)
    (hsolve : deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 a1
        lambda =
      h0 * u)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (hw73 : w73.eval a = 0) (ha1 : a1.eval a = 0) :
    (4096 : F) * (derivative q54).eval a -
        (6144 : F) * t2.eval a * (derivative w73).eval a +
        (8064 : F) * (t2.eval a) ^ 2 * (derivative vis).eval a -
        (7168 : F) * a22.eval a * (derivative vis).eval a +
        (14400 : F) * (t2.eval a) ^ 2 * (derivative a1).eval a -
        (8192 : F) * s22.eval a * (derivative a1).eval a -
        (10368 : F) * lambda * t2.eval a * (derivative a1).eval a +
        (23040 : F) * a22.eval a * (derivative a1).eval a =
      (derivative h0).eval a * u.eval a := by
  have hder := congrArg (fun r : F[X] => derivative r) hsolve
  simp only [deltaGroundPolarNumerator410, derivative_add,
    derivative_sub, derivative_mul, derivative_ofNat, derivative_C,
    zero_mul, mul_zero, zero_add, add_zero] at hder
  have heval := congrArg (fun r : F[X] => r.eval a) hder
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat,
    eval_C, hroot, hvis, hw73, ha1, zero_mul, mul_zero, add_zero,
    zero_add] at heval
  linear_combination heval

/-- Root derivative tie of the `δ` ground pin: the derivative-level
residual pinning the `δ` polar derivative block against `c_δ` and the
root jet. -/
theorem deltaGroundPin_rootDerivativeTie410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 : F[X]) (lambda cdelta : F)
    (a : F)
    (hdpin : deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 a1
        lambda +
      h0 * deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda =
        Polynomial.C cdelta * h0)
    (hroot : h0.eval a = 0) (hvis : vis.eval a = 0)
    (hw73 : w73.eval a = 0) (ha1 : a1.eval a = 0) :
    (4096 : F) * (derivative q54).eval a -
        (6144 : F) * t2.eval a * (derivative w73).eval a +
        (8064 : F) * (t2.eval a) ^ 2 * (derivative vis).eval a -
        (7168 : F) * a22.eval a * (derivative vis).eval a +
        (14400 : F) * (t2.eval a) ^ 2 * (derivative a1).eval a -
        (8192 : F) * s22.eval a * (derivative a1).eval a -
        (10368 : F) * lambda * t2.eval a * (derivative a1).eval a +
        (23040 : F) * a22.eval a * (derivative a1).eval a =
      (derivative h0).eval a *
        (cdelta -
          (deltaGroundRegularNumerator410 t2 a22 s22 a0
              lambda).eval a) := by
  have hsolve := deltaGroundPin_solvePolar410 h0 t2 a22 s22 vis w73
    q54 a1 a0 lambda cdelta hdpin
  have h := deltaPolar_rootDerivative_of_solved410 h0 t2 a22 s22 vis
    w73 q54 a1
    (Polynomial.C cdelta -
      deltaGroundRegularNumerator410 t2 a22 s22 a0 lambda) lambda a
    hsolve hroot hvis hw73 ha1
  simpa only [eval_sub, eval_C] using h

/-- Root derivative of any solved `q₅₄` pin form: since the pin block
is `h₀` times a cofactor, `h₀(a) = 0`, `q₅₄` enters linearly, and
`p₁(a) = 0`, the derivative combination at the root sees exactly
`h₀'(a)` times the cofactor. -/
theorem q54Pin_rootDerivative_of_solved410
    (h0 t2 a22 q54 a1 u : F[X]) (lambda calpha : F) (a : F)
    (hsolve : (4096 : F[X]) * q54 -
        (1024 : F[X]) * Polynomial.C calpha * a1 -
        (3840 : F[X]) * a1 * t2 ^ 2 +
        (5760 : F[X]) * Polynomial.C lambda * a1 * t2 -
        (15360 : F[X]) * a1 * a22 =
      h0 * u)
    (hroot : h0.eval a = 0) (ha1 : a1.eval a = 0) :
    (4096 : F) * (derivative q54).eval a -
        (1024 : F) * calpha * (derivative a1).eval a -
        (3840 : F) * (t2.eval a) ^ 2 * (derivative a1).eval a +
        (5760 : F) * lambda * t2.eval a * (derivative a1).eval a -
        (15360 : F) * a22.eval a * (derivative a1).eval a =
      (derivative h0).eval a * u.eval a := by
  have hder := congrArg (fun r : F[X] => derivative r) hsolve
  simp only [derivative_add, derivative_sub, derivative_mul,
    derivative_ofNat, derivative_C, zero_mul, mul_zero, zero_add,
    add_zero] at hder
  have heval := congrArg (fun r : F[X] => r.eval a) hder
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat,
    eval_C, hroot, ha1, zero_mul, mul_zero, add_zero, zero_add]
    at heval
  linear_combination heval

/-- Sharpest `δ`-loaded residual: the root derivative tie of the fully
eliminated `q₅₄` pin — all four ground constants pinned against the
derivative jet through `t₂(a), a₂₂(a), p₀(a), h₀'(a)` only, with
`c_α` multiplying the derivative letter `p₁'(a)`. -/
theorem q54Pin_rootDerivativeTie_fullyEliminated410
    (h0 t2 a22 s22 vis w73 q54 a1 a0 : F[X])
    (lambda calpha cbeta cgamma cdelta : F) (a : F)
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
    (hroot : h0.eval a = 0) (ha1 : a1.eval a = 0) :
    (4096 : F) * (derivative q54).eval a -
        (1024 : F) * calpha * (derivative a1).eval a -
        (3840 : F) * (t2.eval a) ^ 2 * (derivative a1).eval a +
        (5760 : F) * lambda * t2.eval a * (derivative a1).eval a -
        (15360 : F) * a22.eval a * (derivative a1).eval a =
      (derivative h0).eval a *
        (cdelta + (48 : F) * cgamma * t2.eval a +
          (42 : F) * cbeta * (t2.eval a) ^ 2 +
          (112 : F) * cbeta * a22.eval a +
          (1024 : F) * calpha * a22.eval a * t2.eval a +
          (48 : F) * (t2.eval a) ^ 5 +
          (45 : F) * lambda * (t2.eval a) ^ 4 -
          (640 : F) * a22.eval a * (t2.eval a) ^ 3 -
          (720 : F) * lambda * a22.eval a * (t2.eval a) ^ 2 +
          (3840 : F) * (a22.eval a) ^ 2 * t2.eval a -
          (2880 : F) * lambda * (a22.eval a) ^ 2 +
          (15360 : F) * a0.eval a * t2.eval a -
          (4608 : F) * lambda * a0.eval a) := by
  have hsolve := q54GroundPin_fullyEliminated410 h0 t2 a22 s22 vis w73
    q54 a1 a0 lambda calpha cbeta cgamma cdelta halpha hbpin hgpin
    hdpin
  have h := q54Pin_rootDerivative_of_solved410 h0 t2 a22 q54 a1
    (Polynomial.C cdelta +
      (48 : F[X]) * Polynomial.C cgamma * t2 +
      (42 : F[X]) * Polynomial.C cbeta * t2 ^ 2 +
      (112 : F[X]) * Polynomial.C cbeta * a22 +
      (1024 : F[X]) * Polynomial.C calpha * a22 * t2 +
      (48 : F[X]) * t2 ^ 5 +
      (45 : F[X]) * Polynomial.C lambda * t2 ^ 4 -
      (640 : F[X]) * a22 * t2 ^ 3 -
      (720 : F[X]) * Polynomial.C lambda * a22 * t2 ^ 2 +
      (3840 : F[X]) * a22 ^ 2 * t2 -
      (2880 : F[X]) * Polynomial.C lambda * a22 ^ 2 +
      (15360 : F[X]) * a0 * t2 -
      (4608 : F[X]) * Polynomial.C lambda * a0) lambda calpha a
    hsolve hroot ha1
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat,
    eval_C] at h
  linear_combination h

end DeltaGroundClearing410

/-! ## Source-facing ground power relation at exact order `-1` -/

section NonzeroDeltaGroundBridge410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-- The row-`8` ground first integral `δ` on a square-core ninth-power
source, traced from the literal Keller row through the fifth-face
power relation and expressed at its exact order `-1` on the
thirteenth-face jet: the polar residue block plus `h₀` times the
regular block is GLOBALLY `C c_δ h₀`. -/
theorem nonzeroFace410_deltaResidualPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 vis w73 q54 : k[X])
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
    (hq5 : q.coeff 5 = h0 ^ 4 * q54) :
    ∃ cdelta : k,
      deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          lambda +
        h0 * deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
          lambda =
      Polynomial.C cdelta * h0 := by
  obtain ⟨cdelta, hpow⟩ :=
    nonzeroFace410_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp4 hq10 hN hD
  refine ⟨cdelta, ?_⟩
  have h16 : h0 ^ 16 ≠ 0 := pow_ne_zero 16 hh0
  apply mul_left_cancel₀ h16
  calc
    h0 ^ 16 *
          (deltaGroundPolarNumerator410 t2 a22 s22 vis w73 q54
              (p.coeff 1) lambda +
            h0 * deltaGroundRegularNumerator410 t2 a22 s22 (p.coeff 0)
              lambda) =
        localClearedFifthDefect410 h0 (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          (q.coeff 5) lambda := by
      simp only [localClearedFifthDefect410,
        deltaGroundPolarNumerator410, deltaGroundRegularNumerator410,
        hp3, hp2, hq8, hq7, hq6, hq5]
      ring
    _ = Polynomial.C cdelta * h0 ^ 17 := hpow
    _ = h0 ^ 16 * (Polynomial.C cdelta * h0) := by ring

/-! ## Delta ground bridge packet -/

set_option maxHeartbeats 12800000 in
/-- Sharpest exact successor packet of the `δ` ground bridge on the
nonzero `(4,10)` face: everything from the gamma ground bridge packet,
together with the row-`8` ground pin at its exact order `-1`, its
one-step `h`-adic peel, the `α`-eliminated form (the first polar-side
`α` action, killing the `p₁ s₂₂` cross-term), the `q₅₄` pin (the `β`
and `γ` pins eliminating `q₇₆, w₇₃` from the `δ` polar block — its
left side is the global polynomial lift of the jet tie `hV`), the
fully eliminated `q₅₄` pin — the first global FOUR-ground-constant
link of the lane — the `δ`-loaded factored forms of the second `θ`
and `ι` peel steps (all four polar letters `s₂₂, q₇₆, w₇₃, q₅₄`
eliminated; only `b₄₂, b₃₁, q₂` survive polar-side), and the two root
derivative ties — the sharpest `δ`-loaded residuals, pinning `q₅₄'(a)`
against `c_δ` (and `c_α, c_β, c_γ`) through `t₂(a), a₂₂(a), p₀(a),
h₀'(a)` only.  Nothing here closes the face or a branch: `c_α, c_β,
c_γ, c_δ` are free, so the pins eliminate no configuration; no root
branch is forced; `t₂(a), a₂₂(a), s₂₂(a), q₁(a), q₀(a), c_α, c_β,
c_γ, c_δ, c_θ, c, j, p₀'(a), q₀'(a)` remain free or
tied-not-determined, and the ground constant `ε` (row `7`, sixth
defect, exact order `-2`) stays uncleared. -/
theorem nonzeroFace410_deltaGroundBridgePacket
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
    ∃ (calpha cbeta cgamma cdelta ctheta c : k)
      (v1 v2 v3 w1 w2 w3 : k[X]),
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
            (4608 : k) * lambda * (p.coeff 0).eval a) := by
  obtain ⟨calpha, cbeta, cgamma, ctheta, c, v1, v2, v3, w1, w2, w3,
    hpin, hsolve, hpowT, htw1, htw2, htw3, htwc, hpowI, hiw1, hiw2,
    hiw3, hiwc, hTglobal, hIglobal, ha1, hvis0, hw730, hq540, hb420,
    hb310, hb20, hv10, hw10, hv2tie, hw2tie, hrootS, hTroot, hIroot,
    hkelP, hcombo, hbr, hbpin, hbsolve, hbalpha, hbtheta, hbiota,
    hbderiv, hbderivA, hgpin, hgsolve, hgalpha, hw73B, hw73F, hgiota,
    hgderiv, hw73deriv⟩ :=
    nonzeroFace410_gammaGroundBridgePacket p q H h0 j lambda t2
      a22 s22 vis w73 q54 b42 b31 a hp hq hh0 hH hp4 hq10 hN hD hp3
      hp2 hq8 hq7 hq6 hq5 hq4 hq3 hroot hT hU hW hV hX hY
  obtain ⟨cdelta, hdpin⟩ := nonzeroFace410_deltaResidualPowerRelation
    p q H h0 j lambda t2 a22 s22 vis w73 q54 hp hq hh0 hH hp4 hq10 hN
    hD hp3 hp2 hq8 hq7 hq6 hq5
  have hdsolve := deltaGroundPin_solvePolar410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) lambda cdelta hdpin
  have hdalpha := deltaGroundPin_alphaEliminated410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) lambda calpha cdelta hpin hdpin
  have hq54BG := q54GroundPin_betaGammaEliminated410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) lambda cbeta cgamma cdelta hbpin
    hgpin hdpin
  have hq54F := q54GroundPin_fullyEliminated410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) lambda calpha cbeta cgamma cdelta hpin
    hbpin hgpin hdpin
  have hthetaP2 := thetaSecondPeel_deltaLoaded410 h0 t2 a22 s22 vis
    w73 q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) v1 v2 lambda
    calpha cbeta cgamma cdelta hpin hbpin hgpin hdpin htw2
  have hiotaP2 := iotaSecondPeel_deltaLoaded410 h0 t2 a22 s22 vis w73
    q54 (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) w1 w2 lambda
    calpha cbeta cgamma cdelta hpin hbpin hgpin hdpin hiw2
  have hdderiv := deltaGroundPin_rootDerivativeTie410 h0 t2 a22 s22
    vis w73 q54 (p.coeff 1) (p.coeff 0) lambda cdelta a hdpin hroot
    hvis0 hw730 ha1
  have hq54deriv := q54Pin_rootDerivativeTie_fullyEliminated410 h0 t2
    a22 s22 vis w73 q54 (p.coeff 1) (p.coeff 0) lambda calpha cbeta
    cgamma cdelta a hpin hbpin hgpin hdpin hroot ha1
  exact ⟨calpha, cbeta, cgamma, cdelta, ctheta, c, v1, v2, v3, w1, w2,
    w3, hpin, hsolve, hpowT, htw1, htw2, htw3, htwc, hpowI, hiw1,
    hiw2, hiw3, hiwc, hTglobal, hIglobal, ha1, hvis0, hw730, hq540,
    hb420, hb310, hb20, hv10, hw10, hv2tie, hw2tie, hrootS, hTroot,
    hIroot, hkelP, hcombo, hbr, hbpin, hbsolve, hbalpha, hbtheta,
    hbiota, hbderiv, hbderivA, hgpin, hgsolve, hgalpha, hw73B, hw73F,
    hgiota, hgderiv, hw73deriv, hdpin, hdsolve, hdalpha, hq54BG,
    hq54F, hthetaP2, hiotaP2, hdderiv, hq54deriv⟩

end NonzeroDeltaGroundBridge410

#print axioms deltaDefect_eq_cleared410
#print axioms deltaGroundPin_solvePolar410
#print axioms deltaGroundPin_rootEval410
#print axioms deltaGroundPin_rootEval_reDerivesV410
#print axioms deltaGroundPin_alphaEliminated410
#print axioms q54GroundPin_betaGammaEliminated410
#print axioms q54GroundPin_fullyEliminated410
#print axioms thetaSecondPeel_deltaLoaded410
#print axioms iotaSecondPeel_deltaLoaded410
#print axioms deltaPolar_rootDerivative_of_solved410
#print axioms deltaGroundPin_rootDerivativeTie410
#print axioms q54Pin_rootDerivative_of_solved410
#print axioms q54Pin_rootDerivativeTie_fullyEliminated410
#print axioms nonzeroFace410_deltaResidualPowerRelation
#print axioms nonzeroFace410_deltaGroundBridgePacket

end Max11DegreeRoutes
