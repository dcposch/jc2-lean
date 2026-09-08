import Fable410ScaleTwoAlignedNinthFacePart15Scratch

/-! # Ninth aligned face for the normalized `(4,10)` scale-two leaf

`Fable410ScaleTwoAlignedEighthFaceScratch` consumed the degree-`4`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the squared
weight-`27/2` first integral `M₁₄² = κ₈ H²⁷` of the ninth defect, the
five-deep square peel carrying `s₅` through `s₉`, the nonsquare septic
block tying `q₁` with an `H`-cofactor, and the nonsquare root pin
`g(a) f(a) + 8 p₁(a) = 0`.  This file consumes the next unused aligned
row, the degree-`3` Jacobian coefficient — the FIRST row that sees
`q₀`, and it sees it through `q₀'` ONLY: with `p₄ = H²` the
`p₄'`-pairing of the row carries the Y-weight `0 · q₀`, so the plain
letter `q₀` drops out of the literal row and only `4 p₄ q₀'` survives
(internal names `alignedTenth*`).

At the common source level, modulo the face `N = 0`, the consumed
degree-`11` relation `R = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴ = 0`, and
the consumed degree-`10` through degree-`4` brackets of `M₂`, `M₄`,
`M₆`, `M₈`, `M₁₀`, `M₁₂`, and `M₁₄`, the degree-`3` row is the weighted
derivative of the cleared tenth defect

`M₁₆ = 3932160 p₀ (p₁² + p₀ p₂) H¹⁴ - 4194304 q₀ H¹⁵
  - 983040 p₀² p₃² H¹² - 3932160 p₀ p₁ p₂ p₃ H¹² - 983040 p₁² p₂² H¹²
  - 655360 p₀ p₂³ H¹² - 655360 p₁³ p₃ H¹² + 983040 p₀ p₁ p₃³ H¹⁰
  + 1474560 p₀ p₂² p₃² H¹⁰ + 1474560 p₁² p₂ p₃² H¹⁰
  + 983040 p₁ p₂³ p₃ H¹⁰ + 49152 p₂⁵ H¹⁰ - 614400 p₀ p₂ p₃⁴ H⁸
  - 307200 p₁² p₃⁴ H⁸ - 1228800 p₁ p₂² p₃³ H⁸ - 307200 p₂⁴ p₃² H⁸
  + 71680 p₀ p₃⁶ H⁶ + 430080 p₁ p₂ p₃⁵ H⁶ + 358400 p₂³ p₃⁴ H⁶
  - 46080 p₁ p₃⁷ H⁴ - 161280 p₂² p₃⁶ H⁴ + 31680 p₂ p₃⁸ H² - 2288 p₃¹⁰
  + 524288 κ p₀² H¹⁵
  - p₃ M₁₄ - (16 p₂ H² - 4 p₃²) M₁₂ - (96 p₁ H⁴ - 24 p₂ p₃ H² + 5 p₃³) M₁₀
  - 2048 p₀ H⁶ M₈
  - (2560 p₀ p₃ H⁶ + 2560 p₁ p₂ H⁶ - 960 p₁ p₃² H⁴ - 960 p₂² p₃ H⁴
    + 560 p₂ p₃³ H² - 77 p₃⁵) M₆
  - (24576 p₀ p₂ H⁸ + 12288 p₁² H⁸ - 6144 p₀ p₃² H⁶ - 12288 p₁ p₂ p₃ H⁶
    - 2048 p₂³ H⁶ + 3072 p₁ p₃³ H⁴ + 4608 p₂² p₃² H⁴ - 1920 p₂ p₃⁴ H²
    + 224 p₃⁶) M₄
  - (344064 p₀ p₁ H¹⁰ - 86016 p₀ p₂ p₃ H⁸ - 43008 p₁² p₃ H⁸
    - 43008 p₁ p₂² H⁸ + 17920 p₀ p₃³ H⁶ + 53760 p₁ p₂ p₃² H⁶
    + 17920 p₂³ p₃ H⁶ - 10080 p₁ p₃⁴ H⁴ - 20160 p₂² p₃³ H⁴
    + 6552 p₂ p₃⁵ H² - 663 p₃⁷) M₂`,

kept in factored form through the previous defects — the FIRST aligned
defect whose head `3932160 p₀ (p₁² + p₀ p₂) H¹⁴` factors through `p₀`
times the p-discriminant block `p₁² + p₀ p₂`, the first whose
`κ`-module is the pure-`p₀` square `524288 κ p₀² H¹⁵`, and the first
whose `q`-letter enters at the FULL weight `q₀ H¹⁵` — via the exact
multiplier identity

`1048576 H¹⁴ · row₃[p₄ = H²] = (H M₁₆' - 15 M₁₆ H')
  + 2 p₃ (2 H M₁₄' - 27 M₁₄ H')
  + (8 p₃² + 32 p₂ H²) (H M₁₂' - 12 M₁₂ H')
  + (64 p₁ H⁴ + 48 p₂ p₃ H² - 2 p₃³) (2 H M₁₀' - 21 M₁₀ H')
  + (2048 p₀ H⁶ + 2048 p₁ p₃ H⁴ + 1024 p₂² H⁴) (H M₈' - 9 M₈ H')
  + (5120 p₀ p₃ H⁶ + 5120 p₁ p₂ H⁶ + 640 p₁ p₃² H⁴ + 640 p₂² p₃ H⁴
    - 160 p₂ p₃³ H² + 14 p₃⁵) (2 H M₆' - 15 M₆ H')
  + (49152 p₀ p₂ H⁸ + 24576 p₁² H⁸ + 12288 p₀ p₃² H⁶ + 24576 p₁ p₂ p₃ H⁶
    + 4096 p₂³ H⁶ - 2048 p₁ p₃³ H⁴ - 3072 p₂² p₃² H⁴ + 768 p₂ p₃⁴ H²
    - 64 p₃⁶) (H M₄' - 6 M₄ H')
  + (229376 p₀ p₁ H¹⁰ + 172032 p₀ p₂ p₃ H⁸ + 86016 p₁² p₃ H⁸
    + 86016 p₁ p₂² H⁸ - 7168 p₀ p₃³ H⁶ - 21504 p₁ p₂ p₃² H⁶
    - 7168 p₂³ p₃ H⁶ + 2240 p₁ p₃⁴ H⁴ + 4480 p₂² p₃³ H⁴
    - 1008 p₂ p₃⁵ H² + 78 p₃⁷) (2 H M₂' - 9 M₂ H')`

with multiplier `2²⁰ H¹⁴` (unique solution of the factored cofactor
system, nullspace exactly one).  The correction module is EMPTY for the
FOURTH row in a row: neither the aligned-face residual `N` nor the
degree-`11` relation `R` appears — the row's letters stop at `q₄`, so
no bracket combination can carry `q₈` or `q₉`.  On the aligned face
every previous bracket vanishes, so `H M₁₆' = 15 M₁₆ H'` and the
weight-`15` first integral

`M₁₆ = κ₉ H¹⁵`

holds for a preserved constant `κ₉` — even-type and CHAMBER-FREE, the
FIFTH rung of the even ladder `H⁴, H⁶, H⁹, H¹², H¹⁵`; no parity kill,
`κ₉` is preserved in BOTH chambers.  The chamber core, after cancelling
`h₀²⁰` resp. `H¹⁰`, is a QUARTIC-cofactor cube plus a `p₁`-loaded
square block:

`16 (143 w⁴ - 264 p₂ w² + 48 p₂²) (w² - 4 p₂)³
  + 15360 h p₁ w (3 w² - 4 p₂) (w² - 4 p₂)²`  (`h = h₀²` resp. `H`)

— the first aligned chamber core whose odd cofactor
`143 w⁴ - 264 p₂ w² + 48 p₂²` does not factor against the quadratic
kill (it evaluates to `80 w⁴` on `w² = 4 p₂`).

* square chamber `H = h₀²`, `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
  `M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`,
  `M₁₄ = μ₄ h₀²⁷`, `M₁₆ = κ₉ H¹⁵`: on the consumed divisibility
  `u² - 4 p₂ = h₀ v` the peel is SEVEN deep — the deepest aligned peel
  so far (`q₀` sits ten levels above the core against the
  divisibility's three): the NEW μ-loaded SEPTIC divisibility
  `16 (143 u⁴ - 264 p₂ u² + 48 p₂²) v³ - μ (663 u⁷ - 6552 p₂ u⁵
  + 20160 p₂² u³ - 17920 p₂³ u) = h₀ s₁₀` — self-similar to the
  sixth-, seventh-, and eighth-face divisibilities one level down —
  then the explicit peels producing `s₁₁` through `s₁₆` (`s₁₅` is the
  FIRST peel letter loaded with `μ₄`), and the solved row

  `4194304 q₀ = 524288 κ p₀² - 2048 κ₅ p₀ - κ₉ - s₁₆`

  — the FIRST aligned solved row with NO `h₀`-suppressed tail at all:
  `q₀` carries no `h₀` factor, `κ₉` enters at level ZERO, and every
  higher letter is absorbed into the peel.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = M₆ = M₁₀ = M₁₄ = 0`, `M₄ = κ₃ H⁶`, `M₈ = κ₅ H⁹`,
  `M₁₂ = κ₇ H¹²`, `M₁₆ = κ₉ H¹⁵`: on the consumed divisibility
  `g² - 4 p₂ = H f` the row does NOT solve — the octic block identity
  `16 (143 g⁴ - 264 p₂ g² + 48 p₂²) f³ + 15360 p₁ g (3 g² - 4 p₂) f²
  + 245760 p₁² g² f + 655360 p₁³ g
  = H · (((61440 p₀ - 192 κ₃) g² - 61440 p₁²) f²
  + (983040 p₀ - 3072 κ₃) g p₁ f + (3932160 p₀ - 12288 κ₃) p₁²
  + H · ((10240 p₀ - 32 κ₃) f³ + (6144 κ₃ p₀ + 4 κ₇ - 983040 p₀²) f
  + 524288 κ p₀² - 2048 κ₅ p₀ - κ₉ - 4194304 q₀))` consumes `q₀` with
  an `H²`-cofactor — the first aligned letter tied TWO `H`-levels deep.

The honest new root content at the core root `a` (where
`w(a)² = 4 p₂(a)` from the fifth face): the square chamber gains the
NEW value tie `1280 u(a)⁴ v(a)³ = 5 μ u(a)⁷`, whose clash with the
sixth face's product kill `u(a) (16 v(a)³ - 7 μ u(a)³) = 0` (a
factor-`555` mismatch, `560 μ u⁷` against `5 μ u⁷`) RE-DERIVES the
root dichotomy `(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)`; on it
`s₁₀(a) = 0` unconditionally, and the ties
`s₁₀(a) = -30720 p₁ u³ v²`,
`s₁₁(a) = -245760 p₁² u² v - 672 μ p₁ u⁴ - 3 μ₂ u⁵`,
`s₁₅(a) = (6144 κ₃ p₀ + 4 κ₇ - 983040 p₀²) v - 344064 μ p₀ p₁
- 2560 μ₂ p₀ u - 96 μ₃ p₁ - μ₄ u` — the FIRST aligned root tie loaded
with `μ₄` — and the `q₀` value tie
`4194304 q₀(a) = 524288 κ p₀(a)² - 2048 κ₅ p₀(a) - κ₉ - s₁₆(a)` — the
first aligned root tie that sees `κ₉` — follow.  The nonsquare
chamber's octic block dies at `a` and collapses on the quadratic kill
to the PERFECT-CUBE PRODUCT

`g(a) · (g(a) f(a) + 8 p₁(a))³ = 0`

— an independent re-derivation of the eighth face's root-pin content as
a product kill (this row alone forces `g(a) = 0` or the pin; no new pin
is claimed beyond the eighth face's).  `q₀` itself is `H`-suppressed
twice at the root and stays free there.

Reused architecture: `dvd_of_eval_eq_zero_of_simple_natDegree_two`,
`nonsquare_natDegree_two_derivative_ne_zero`,
`natDegree_one_dvd_of_root_kill_410`, the fourth-face square descent
`p₃ = h₀² u`, the fifth-face divisibilities `u² - 4 p₂ = h₀ v`,
`g² - 4 p₂ = H f`, the sixth-face divisibility carrying `s`, and the
chamber form/kill quotients of the odd rows.  The weight-`15` Wronskian
quotient `fifteenthPowerRelation_of_weightFifteenRow_410` is new but
generic (even-type, distinct from the odd-type
`fifteenthPowerRelation_of_weightFifteenHalfRow_410`).

No closure is claimed.  Both chambers remain open, both dichotomy
branches are preserved, the zero branches (`u = 0`, `g = 0`, `v = 0`,
`f = 0`, `s₁₀ = 0`, `μ = 0` through `μ₄ = 0`, `κ = 0` through
`κ₉ = 0`) are not excluded, and the constants are preserved where not
previously forced (`κ₄ = κ₆ = κ₈ = 0` remain forced in the nonsquare
chamber only; `κ₉` is preserved in both).  `p₀, p₁, p₂` are
constrained only through the solved forms, the divisibilities, and the
root ties.  The aligned Jacobian tower now has TWO unused rows left:
the degree-`2` row (seeing `q₀` and `q₁` through derivatives and
values) and the degree-`1`/degree-`0` tail; the next unused aligned
row is the degree-`2` Jacobian coefficient.  No total-degree or
twice-prime theorem is used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

#print axioms alignedTenthCoefficientJacobianRow_410
#print axioms alignedTenthDefect_weightedDerivative_identity_410
#print axioms alignedTenthDefectRow_eq_zero_410
#print axioms fifteenthPowerRelation_of_weightFifteenRow_410
#print axioms alignedTenthDefectPowerRelation_410
#print axioms alignedSquareTenth_core_410
#print axioms alignedSquareTenth_solved_410
#print axioms alignedNonsquareTenth_core_410
#print axioms alignedNonsquareTenth_solved_410
#print axioms normalized410ScaleTwo_alignedTenthRow_packet
#print axioms normalized410ScaleTwo_alignedTenthRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedTenthRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedTenthRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedTenthRow_rootData

end Max11DegreeRoutes
