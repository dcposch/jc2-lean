import Fable410ScaleTwoAlignedTenthFacePart17Scratch

/-! # Tenth aligned face for the normalized `(4,10)` scale-two leaf

`Fable410ScaleTwoAlignedNinthFaceScratch` consumed the degree-`3`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the
chamber-free weight-`15` first integral `M₁₆ = κ₉ H¹⁵` of the tenth
defect, the seven-deep square peel carrying `s₁₀` through `s₁₆`, and
the solved constant coefficient `q₀`.  This file consumes the next
unused aligned row, the degree-`2` Jacobian coefficient — the LAST
aligned row above the degree-`1`/degree-`0` tail, and the FIRST with
no new letter at all: it sees `q₀` through `q₀'` only (cofactor
`3 p₃`), `q₁` through its value and derivative, and `q₂`, `q₃` through
the derivative pairings, and every one of these letters was already
consumed by a previous face (internal names `alignedEleventh*`).

At the common source level, modulo the face `N = 0` and the consumed
degree-`11` through degree-`3` brackets of `M₂`, `M₄`, `M₆`, `M₈`,
`M₁₀`, `M₁₂`, `M₁₄`, and `M₁₆`, the degree-`2` row is the weighted
derivative of the cleared eleventh defect

`M₁₈ = 125829120 p₀² p₁ H¹⁶ - 62914560 (p₀² p₂ p₃ + p₀ p₁² p₃
  + p₀ p₁ p₂²) H¹⁴ - 20971520 p₁³ p₂ H¹⁴ + 15728640 p₀² p₃³ H¹²
  + 94371840 p₀ p₁ p₂ p₃² H¹² + 31457280 p₀ p₂³ p₃ H¹²
  + 15728640 p₁³ p₃² H¹² + 47185920 p₁² p₂² p₃ H¹²
  + 7864320 p₁ p₂⁴ H¹² - 19660800 p₀ p₁ p₃⁴ H¹⁰
  - 39321600 (p₀ p₂² p₃³ + p₁² p₂ p₃³ + p₁ p₂³ p₃²) H¹⁰
  - 3932160 p₂⁵ p₃ H¹⁰ + 13762560 p₀ p₂ p₃⁵ H⁸ + 6881280 p₁² p₃⁵ H⁸
  + 34406400 p₁ p₂² p₃⁴ H⁸ + 11468800 p₂⁴ p₃³ H⁸ - 1474560 p₀ p₃⁷ H⁶
  - 10321920 p₁ p₂ p₃⁶ H⁶ - 10321920 p₂³ p₃⁵ H⁶ + 1013760 p₁ p₃⁸ H⁴
  + 4055040 p₂² p₃⁷ H⁴ - 732160 p₂ p₃⁹ H² + 49920 p₃¹¹
  - (32 p₂ H² - 12 p₃²) M₁₄ - (512 p₁ H⁴ - 256 p₂ p₃ H² + 64 p₃³) M₁₂
  - (3072 p₀ H⁶ - 768 p₁ p₃ H⁴ - 384 p₂² H⁴ + 480 p₂ p₃² H²
    - 90 p₃⁴) M₁₀
  - (81920 p₀ p₂ H⁸ + 40960 p₁² H⁸ - 30720 p₀ p₃² H⁶
    - 61440 p₁ p₂ p₃ H⁶ - 10240 p₂³ H⁶ + 17920 p₁ p₃³ H⁴
    + 26880 p₂² p₃² H⁴ - 12320 p₂ p₃⁴ H² + 1540 p₃⁶) M₆
  - (786432 p₀ p₁ H¹⁰ - 393216 p₀ p₂ p₃ H⁸ - 196608 p₁² p₃ H⁸
    - 196608 p₁ p₂² H⁸ + 98304 p₀ p₃³ H⁶ + 294912 p₁ p₂ p₃² H⁶
    + 98304 p₂³ p₃ H⁶ - 61440 p₁ p₃⁴ H⁴ - 122880 p₂² p₃³ H⁴
    + 43008 p₂ p₃⁵ H² - 4608 p₃⁷) M₄
  - (5505024 p₀² H¹² - 2752512 p₀ p₁ p₃ H¹⁰ - 1376256 p₀ p₂² H¹⁰
    - 1376256 p₁² p₂ H¹⁰ + 1720320 p₀ p₂ p₃² H⁸ + 860160 p₁² p₃² H⁸
    + 1720320 p₁ p₂² p₃ H⁸ + 143360 p₂⁴ H⁸ - 322560 p₀ p₃⁴ H⁶
    - 1290240 p₁ p₂ p₃³ H⁶ - 645120 p₂³ p₃² H⁶ + 209664 p₁ p₃⁵ H⁴
    + 524160 p₂² p₃⁴ H⁴ - 148512 p₂ p₃⁶ H² + 13923 p₃⁸) M₂`,

kept in factored form through the previous defects — the FIRST aligned
defect whose factored head carries NO `q`-letter and NO `κ`-module at
all (`M₁₆` and `M₈` do not even appear among the corrections:
`d₁₆ = d₈ = 0`, and the whole `q`/`κ`-content of the expanded defect
flows through the corrections `M₂`, `M₄`, `M₆`, `M₁₀`, `M₁₂`, `M₁₄`) —
via the exact multiplier identity

`67108864 H¹⁶ · row₂ = (2 H M₁₈' - 33 M₁₈ H')
  + 48 p₃ (H M₁₆' - 15 M₁₆ H')
  + (96 p₂ H² + 12 p₃²) (2 H M₁₄' - 27 M₁₄ H')
  + (1536 p₁ H⁴ + 768 p₂ p₃ H² - 64 p₃³) (H M₁₂' - 12 M₁₂ H')
  + (3072 p₀ H⁶ + 2304 p₁ p₃ H⁴ + 1152 p₂² H⁴ - 288 p₂ p₃² H²
    + 30 p₃⁴) (2 H M₁₀' - 21 M₁₀ H')
  + (98304 p₀ p₃ H⁶ + 98304 p₁ p₂ H⁶) (H M₈' - 9 M₈ H')
  + (245760 p₀ p₂ H⁸ + 122880 p₁² H⁸ + 30720 p₀ p₃² H⁶
    + 61440 p₁ p₂ p₃ H⁶ + 10240 p₂³ H⁶ - 7680 p₁ p₃³ H⁴
    - 11520 p₂² p₃² H⁴ + 3360 p₂ p₃⁴ H² - 308 p₃⁶)
    (2 H M₆' - 15 M₆ H')
  + (2359296 p₀ p₁ H¹⁰ + 1179648 p₀ p₂ p₃ H⁸ + 589824 p₁² p₃ H⁸
    + 589824 p₁ p₂² H⁸ - 98304 p₀ p₃³ H⁶ - 294912 p₁ p₂ p₃² H⁶
    - 98304 p₂³ p₃ H⁶ + 36864 p₁ p₃⁴ H⁴ + 73728 p₂² p₃³ H⁴
    - 18432 p₂ p₃⁵ H² + 1536 p₃⁷) (H M₄' - 6 M₄ H')
  + (5505024 p₀² H¹² + 8257536 p₀ p₁ p₃ H¹⁰ + 4128768 p₀ p₂² H¹⁰
    + 4128768 p₁² p₂ H¹⁰ - 1032192 p₀ p₂ p₃² H⁸ - 516096 p₁² p₃² H⁸
    - 1032192 p₁ p₂² p₃ H⁸ - 86016 p₂⁴ H⁸ + 107520 p₀ p₃⁴ H⁶
    + 430080 p₁ p₂ p₃³ H⁶ + 215040 p₂³ p₃² H⁶ - 48384 p₁ p₃⁵ H⁴
    - 120960 p₂² p₃⁴ H⁴ + 26208 p₂ p₃⁶ H² - 1989 p₃⁸)
    (2 H M₂' - 9 M₂ H')`

with multiplier `2²⁶ H¹⁶`, `row₂ = p₂' q₁ + 2 p₁' q₂ + 3 p₀' q₃
- (3 p₃ q₀' + 2 p₂ q₁' + p₁ q₂')` (unique solution of the factored
cofactor system: nullspace dimension `12` = the multiplier solution
plus `11` pure re-presentation gauges that leave the expanded defect
unchanged).  The correction module is EMPTY for the FIFTH row in a
row, and the entire `q₀'`-content of the row is carried by the `M₁₆`
bracket with cofactor `48 p₃`.  On the aligned face every previous
bracket vanishes, so `2 H M₁₈' = 33 M₁₈ H'` and the squared
weight-`33/2` first integral

`M₁₈² = κ₁₀ H³³`

holds for a constant `κ₁₀` — the FIFTH regeneration of the odd-power
discriminator shape (`H⁹, H¹⁵, H²¹, H²⁷, H³³`).  The chambers split
honestly on parity.  The chamber core, after cancelling `h₀²²` resp.
`H¹¹`, is a quartic-cofactor cube plus a `p₁`-loaded square:

`1280 w (39 w⁴ - 104 p₂ w² + 48 p₂²) (w² - 4 p₂)³
  + 30720 h p₁ (33 w⁴ - 72 p₂ w² + 16 p₂²) (w² - 4 p₂)²`
  (`h = h₀²` resp. `H`)

and — because every `q`-letter of the row was already solved — the
whole relation is `q`-FREE in both chambers, and `κ`, `κ₅`, `κ₉` drop
out entirely (the first aligned row blind to them).

* square chamber `H = h₀²`, `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
  `M₆ = μ₂ h₀¹⁵`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`, `M₁₄ = μ₄ h₀²⁷`,
  `M₁₈ = μ₅ h₀³³` with `μ₅² = κ₁₀` (honest residual): on the consumed
  divisibility `u² - 4 p₂ = h₀ v` the peel is EIGHT deep — the deepest
  aligned peel: the NEW μ-loaded OCTIC divisibility
  `1280 u (39 u⁴ - 104 p₂ u² + 48 p₂²) v³ - μ (13923 u⁸
  - 148512 p₂ u⁶ + 524160 p₂² u⁴ - 645120 p₂³ u² + 143360 p₂⁴)
  = h₀ s₁₇` — self-similar to the sixth- through ninth-face
  divisibilities one level down — then the explicit peels producing
  `s₁₈` through `s₂₄` (`s₂₂` is loaded with `μ₄`), and — with no
  letter left to solve — the FIRST aligned CONSTANT PIN

  `C μ₅ = s₂₄ - 5505024 μ p₀² - 3072 μ₃ p₀`

  — the row pins the fresh constant `μ₅` (hence `κ₁₀ = μ₅²`) globally
  against the peel letters, forcing the right side to be constant.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = M₆ = M₁₀ = M₁₄ = 0`, `M₄ = κ₃ H⁶`,
  `M₁₂ = κ₇ H¹²`: the odd exponent forces the parity kill `κ₁₀ = 0`
  and `M₁₈ ≡ 0`.  On the consumed divisibility `g² - 4 p₂ = H f` the
  row yields the `q`-free block identity
  `1280 g (39 g⁴ - 104 p₂ g² + 48 p₂²) f³ + 30720 p₁ (33 g⁴
  - 72 p₂ g² + 16 p₂²) f² + 3932160 p₁² g³ f
  + 5242880 p₁³ (3 g² - 4 p₂) = H · (...)` — the first aligned
  nonsquare row consuming NO letter: a pure constraint among the
  descent data.

The honest new root content at the core root `a` (where
`w(a)² = 4 p₂(a)` from the fifth face): the square chamber gains the
NEW value tie `4096 u(a)⁵ v(a)³ = 7 μ u(a)⁸`, whose clash with the
sixth face's product kill `u(a) (16 v(a)³ - 7 μ u(a)³) = 0` (a
factor-`255` mismatch) RE-DERIVES the root dichotomy
`(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)`; on it `s₁₇(a) = 0`
unconditionally, and the ties `s₁₇(a) = -491520 p₁ u⁴ v²`,
`s₁₈(a) = -3932160 p₁² u³ v - 5376 μ p₁ u⁵ - 20 μ₂ u⁶`, the
μ₄-loaded tie `s₂₂(a) = (98304 κ₃ p₀ + 64 κ₇ - 15728640 p₀²) u v
- 2752512 μ p₀ p₁ u - 10240 μ₂ p₀ u² + 40960 μ₂ p₁² - 768 μ₃ p₁ u
- 4 μ₄ u²`, and the `μ₅` value tie
`μ₅ = s₂₄(a) - 5505024 μ p₀(a)² - 3072 μ₃ p₀(a)` — the first aligned
root tie that sees `μ₅` — follow.  The nonsquare chamber's block dies
at `a` and collapses on the quadratic kill to the PERFECT-CUBE PRODUCT

`g(a)² · (g(a) f(a) + 8 p₁(a))³ = 0`

— an independent re-derivation of the eighth face's root-pin content
as a product kill with a `g²`-cofactor (this row alone forces
`g(a) = 0` or the pin; no new pin is claimed beyond the eighth face's).

Reused architecture: `dvd_of_eval_eq_zero_of_simple_natDegree_two`,
`nonsquare_natDegree_two_derivative_ne_zero`, `dvd_of_sq_dvd_sq_poly`,
`natDegree_one_dvd_of_root_kill_410`,
`derivative_eval_eq_zero_of_pow_factor_410`, the fourth-face square
descent `p₃ = h₀² u`, the fifth-face divisibilities `u² - 4 p₂ = h₀ v`,
`g² - 4 p₂ = H f`, the sixth-face divisibility carrying `s`, and the
chamber form/kill quotients of the odd rows.  The weight-`33/2`
Wronskian quotient
`thirtyThirdPowerRelation_of_weightThirtyThreeHalfRow_410` and its
chamber quotients are new but generic.

No closure is claimed.  Both chambers remain open, both dichotomy
branches are preserved, the zero branches (`u = 0`, `g = 0`, `v = 0`,
`f = 0`, `s₁₇ = 0`, `μ = 0` through `μ₅ = 0`, `κ = 0` through
`κ₁₀ = 0`) are not excluded, and the constants are preserved where not
previously forced (`κ₄ = κ₆ = κ₈ = 0` and now `κ₁₀ = 0` are forced in
the nonsquare chamber only; the square chamber pins `μ₅` against the
peel letters but does not clear it).  `p₀, p₁, p₂` are constrained
only through the solved forms, the divisibilities, and the root ties.
The aligned Jacobian tower now has ONLY the degree-`1`/degree-`0`
tail left unused: the degree-`1` row
`p₁' q₁ + 2 p₀' q₂ - (2 p₂ q₀' + p₁ q₁')` and the terminal degree-`0`
row `p₀' q₁ - p₁ q₀'`; the next unused aligned row is the degree-`1`
Jacobian coefficient.  No total-degree or twice-prime theorem is used,
and no finite-root shortcut is taken.
-/
