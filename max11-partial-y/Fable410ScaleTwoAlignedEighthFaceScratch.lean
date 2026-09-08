import Fable410ScaleTwoAlignedEighthFacePart17Scratch

/-! # Eighth aligned face for the normalized `(4,10)` scale-two leaf

`Fable410ScaleTwoAlignedSeventhFaceScratch` consumed the degree-`5`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the
chamber-free weight-`12` first integral `M₁₂ = κ₇ H¹²` of the eighth
defect, the μ-loaded divisibility carrying `s₂`, and the solved
quadratic coefficient `q₂`.  This file consumes the next unused aligned
row, the degree-`4` Jacobian coefficient — the first row that sees
`q₁` — derived here directly from the literal Keller bracket (internal
names `alignedNinth*`).

At the common source level, modulo the face `N = 0`, the consumed
degree-`11` relation `R = 8 q₈ - 20 p₂ H³ - 15 p₃² H - κ H⁴ = 0`, and
the consumed degree-`10` through degree-`5` brackets of `M₂`, `M₄`,
`M₆`, `M₈`, `M₁₀`, and `M₁₂`, the degree-`4` row is the weighted
derivative of the cleared ninth defect

`M₁₄ = 983040 p₀² p₃ H¹² - 1048576 q₁ H¹³ + 1966080 p₀ p₁ p₂ H¹²
  + 327680 p₁³ H¹² - 491520 p₀ p₁ p₃² H¹⁰ - 491520 p₀ p₂² p₃ H¹⁰
  - 491520 p₁² p₂ p₃ H¹⁰ - 163840 p₁ p₂³ H¹⁰ + 245760 p₀ p₂ p₃³ H⁸
  + 122880 p₁² p₃³ H⁸ + 368640 p₁ p₂² p₃² H⁸ + 61440 p₂⁴ p₃ H⁸
  - 30720 p₀ p₃⁵ H⁶ - 153600 p₁ p₂ p₃⁴ H⁶ - 102400 p₂³ p₃³ H⁶
  + 17920 p₁ p₃⁶ H⁴ + 53760 p₂² p₃⁵ H⁴ - 11520 p₂ p₃⁷ H² + 880 p₃⁹
  + 262144 κ p₀ p₁ H¹³
  - 4 p₃ M₁₂ - (24 p₂ H² - 3 p₃²) M₁₀ - 512 p₁ H⁴ M₈
  - (2560 p₀ H⁶ + 640 p₁ p₃ H⁴ + 320 p₂² H⁴ - 240 p₂ p₃² H²
    + 35 p₃⁴) M₆
  - (6144 p₀ p₃ H⁶ + 6144 p₁ p₂ H⁶ - 1536 p₁ p₃² H⁴ - 1536 p₂² p₃ H⁴
    + 768 p₂ p₃³ H² - 96 p₃⁵) M₄
  - (86016 p₀ p₂ H⁸ + 43008 p₁² H⁸ - 10752 p₀ p₃² H⁶
    - 21504 p₁ p₂ p₃ H⁶ - 3584 p₂³ H⁶ + 4480 p₁ p₃³ H⁴
    + 6720 p₂² p₃² H⁴ - 2520 p₂ p₃⁴ H² + 273 p₃⁶) M₂`,

kept in factored form through the previous defects — the FIRST aligned
defect whose head is weighted-CUBIC in the low letters
(`983040 p₀² p₃ + 1966080 p₀ p₁ p₂ + 327680 p₁³
= 327680 (3 p₀² p₃ + 6 p₀ p₁ p₂ + p₁³)`), and the first whose
`κ`-module collapses to a SINGLE term `262144 κ p₀ p₁ H¹³` — via the
exact multiplier identity

`524288 H¹² · row₄[p₄ = H²] = (2 H M₁₄' - 27 M₁₄ H')
  + 20 p₃ (H M₁₂' - 12 M₁₂ H')
  + (40 p₂ H² + 15 p₃²) (2 H M₁₀' - 21 M₁₀ H')
  + (1280 p₁ H⁴ + 1280 p₂ p₃ H²) (H M₈' - 9 M₈ H')
  + (2560 p₀ H⁶ + 3200 p₁ p₃ H⁴ + 1600 p₂² H⁴ + 400 p₂ p₃² H²
    - 25 p₃⁴) (2 H M₆' - 15 M₆ H')
  + (30720 p₀ p₃ H⁶ + 30720 p₁ p₂ H⁶ + 7680 p₁ p₃² H⁴ + 7680 p₂² p₃ H⁴
    - 1280 p₂ p₃³ H² + 96 p₃⁵) (H M₄' - 6 M₄ H')
  + (143360 p₀ p₂ H⁸ + 71680 p₁² H⁸ + 53760 p₀ p₃² H⁶
    + 107520 p₁ p₂ p₃ H⁶ + 17920 p₂³ H⁶ - 4480 p₁ p₃³ H⁴
    - 6720 p₂² p₃² H⁴ + 1400 p₂ p₃⁴ H² - 105 p₃⁶) (2 H M₂' - 9 M₂ H')`.

The correction module is EMPTY for the third row in a row: neither the
aligned-face residual `N` nor the degree-`11` relation `R` appears —
the row's letters stop at `q₅`, so no bracket combination can carry
`q₈` or `q₉`, and the identity is exact in the free letters (unique
solution of the cofactor system, multiplier `2¹⁹ H¹²`).  On the aligned
face every previous bracket vanishes, so `2 H M₁₄' = 27 M₁₄ H'` and the
squared weight-`27/2` first integral

`M₁₄² = κ₈ H²⁷`

holds for a preserved constant `κ₈` — the FOURTH regeneration of the
odd-power discriminator shape (`M₂² = κ₂ H⁹`, `M₆² = κ₄ H¹⁵`,
`M₁₀² = κ₆ H²¹`, `M₁₄² = κ₈ H²⁷`).  The chambers split honestly on
parity.  The chamber core, after cancelling `h₀¹⁸` resp. `H⁹`, is the
fifth face's cube times a NEW odd cofactor plus a `p₁`-loaded square:

`80 w (11 w² - 12 p₂) (w² - 4 p₂)³
  + 2560 h p₁ (7 w² - 4 p₂) (w² - 4 p₂)²`  (`h = h₀²` resp. `H`).

* square chamber `H = h₀²`, `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
  `M₆ = μ₂ h₀¹⁵`, `M₈ = κ₅ H⁹`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`,
  `M₁₄ = μ₄ h₀²⁷` with `μ₄² = κ₈` (honest residual): on the consumed
  divisibility `u² - 4 p₂ = h₀ v` the peel is FIVE deep (`q₁` sits
  eight levels above the core against the divisibility's three): the
  NEW μ-loaded divisibility
  `80 u (11 u² - 12 p₂) v³ - μ (273 u⁶ - 2520 p₂ u⁴ + 6720 p₂² u²
  - 3584 p₂³) = h₀ s₅` — self-similar to the sixth and seventh face
  divisibilities one level down — then the explicit peels producing
  `s₆`, `s₇`, `s₈`, `s₉`, and the solved linear row with no `h₀` factor
  on `q₁` and κ₇ entering at level ZERO (the first solved aligned row
  where an even-row constant is not `h₀`-suppressed):
  `1048576 q₁ = s₉ - 4 κ₇ u - 512 κ₅ p₁ - 6144 κ₃ p₀ u + 983040 p₀² u
  + 262144 κ p₀ p₁ - h₀ (μ₄ + 2560 μ₂ p₀)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = 0`, `M₆ = 0`, `M₁₀ = 0`, `M₄ = κ₃ H⁶`,
  `M₈ = κ₅ H⁹`, `M₁₂ = κ₇ H¹²`: the odd exponent forces the parity
  kill `κ₈ = 0` and `M₁₄ ≡ 0`.  On the consumed divisibility
  `g² - 4 p₂ = H f` the row does NOT solve outright: for the first
  time the NONSQUARE chamber needs its own descent — the septic block
  identity
  `80 g (11 g² - 12 p₂) f³ + 2560 p₁ (7 g² - 4 p₂) f²
  + 122880 p₁² g f + 327680 p₁³ = H · ((30720 p₀ - 96 κ₃) g f²
  + (491520 p₀ - 1536 κ₃) p₁ f + 1048576 q₁ + 4 κ₇ g + 512 κ₅ p₁
  + 6144 κ₃ p₀ g - 983040 p₀² g - 262144 κ p₀ p₁)` — `q₁` is consumed
  with an `H`-cofactor (tied, not solved).

The honest new root content at the core root `a` (where
`w(a)² = 4 p₂(a)` from the fifth face): the square chamber gains the
tie `640 u(a)³ v(a)³ = 7 μ u(a)⁶`, whose clash with the sixth face's
product kill `u(a) (16 v(a)³ - 7 μ u(a)³) = 0` (a factor-`273`
mismatch) RE-DERIVES the root dichotomy
`(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)`; on it `s₅(a) = 0`
unconditionally, and the ties `s₅(a) = -15360 p₁ u² v²`,
`s₆(a) = -5 μ₂ u⁴ - 896 μ p₁ u³ - 122880 p₁² u v`, and the `q₁` value
tie `1048576 q₁(a) = s₉(a) - 4 κ₇ u - 512 κ₅ p₁ - 6144 κ₃ p₀ u
+ 983040 p₀² u + 262144 κ p₀ p₁` — the first aligned root tie that
sees `κ₇` — follow.  The nonsquare chamber's septic block dies at `a`
and collapses on the quadratic kill to the PERFECT CUBE
`640 (g(a) f(a) + 8 p₁(a))³ = 0`, forcing the NEW ROOT PIN

`g(a) f(a) + 8 p₁(a) = 0`

— the first aligned root pin on `p₁` in the nonsquare chamber; `q₁`
itself is `H`-suppressed at the root and stays free there.

Reused architecture: `dvd_of_eval_eq_zero_of_simple_natDegree_two`,
`nonsquare_natDegree_two_derivative_ne_zero`, `dvd_of_sq_dvd_sq_poly`,
`natDegree_one_dvd_of_root_kill_410`,
`derivative_eval_eq_zero_of_pow_factor_410`, the fourth-face square
descent `p₃ = h₀² u`, the fifth-face divisibilities `u² - 4 p₂ = h₀ v`,
`g² - 4 p₂ = H f`, and the sixth-face divisibility carrying `s`.  The
weight-`27/2` Wronskian quotient
`twentySeventhPowerRelation_of_weightTwentySevenHalfRow_410` and its
chamber quotients are new but generic.

No closure is claimed.  Both chambers remain open, both dichotomy
branches are preserved, the zero branches (`u = 0`, `g = 0`, `v = 0`,
`f = 0`, `s₅ = 0`, `μ = 0`, `μ₂ = 0`, `μ₃ = 0`, `μ₄ = 0`, `κ = 0`
through `κ₈ = 0`) are not excluded, and the constants are preserved
where not previously forced (`κ₈ = 0` and `M₁₄ ≡ 0` are forced in the
nonsquare chamber only).  `p₀, p₁, p₂` are constrained only through
the solved forms, the divisibilities, and the root pin.  The next
unused Keller row on the aligned face is the degree-`3` Jacobian
coefficient, the first row that sees `q₀` (through `q₀'`).  No
total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

#print axioms alignedNinthCoefficientJacobianRow_410
#print axioms alignedNinthDefect_weightedDerivative_identity_410
#print axioms alignedNinthDefectRow_eq_zero_410
#print axioms twentySeventhPowerRelation_of_weightTwentySevenHalfRow_410
#print axioms alignedNinthDefectPowerRelation_410
#print axioms twentySeventhPower_squareChamber_form_410
#print axioms twentySeventhPower_nonsquareChamber_kill_410
#print axioms alignedSquareNinth_core_410
#print axioms alignedSquareNinth_solved_410
#print axioms alignedNonsquareNinth_core_410
#print axioms alignedNonsquareNinth_solved_410
#print axioms normalized410ScaleTwo_alignedNinthRow_packet
#print axioms normalized410ScaleTwo_alignedNinthRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedNinthRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedNinthRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedNinthRow_rootData

end Max11DegreeRoutes
