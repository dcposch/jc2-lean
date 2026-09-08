import Fable410ScaleTwoAlignedEleventhFacePart15Scratch

/-! # Eleventh aligned face for the normalized `(4,10)` scale-two leaf

`Fable410ScaleTwoAlignedTenthFaceScratch` consumed the degree-`2`
Keller row on the aligned face `N = 5 p₃ H³ - 2 q₉ = 0`: the squared
weight-`33/2` first integral `M₁₈² = κ₁₀ H³³`, the eight-deep square
peel carrying `s₁₇` through `s₂₄`, and the constant pin
`C μ₅ = s₂₄ - 5505024 μ p₀² - 3072 μ₃ p₀`.  This file consumes the
next unused aligned row, the degree-`1` Jacobian coefficient
`p₁' q₁ + 2 p₀' q₂ - (2 p₂ q₀' + p₁ q₁')` — the LAST aligned row above
the terminal degree-`0` Keller-constant row, and the second in a row
with no new letter: `q₀` enters through `q₀'` only (cofactor `2 p₂`),
`q₁` through its value and derivative, and `q₂` through `2 p₀' q₂`,
and every one of these letters was already consumed by a previous face
(internal names `alignedTwelfth*`).

At the common source level, modulo the face `N = 0` and the consumed
degree-`11` through degree-`2` brackets of `M₂` through `M₁₈`, the
degree-`1` row is the weighted derivative of the cleared twelfth
defect `M₂₀` (weight `18`, co-degree `12`), kept in factored form
through the previous defects: the head is the first weighted
p₀-CUBIC block `838860800 p₀³ H¹⁸ - 629145600 (p₀² p₁ p₃ + p₀² p₂²
+ 2 p₀ p₁² p₂) H¹⁶ - 104857600 p₁⁴ H¹⁶ + ...` with NO `q`-letter and
NO `κ`-module at all (the SECOND pure-`p` head), and neither `M₈` nor
`M₁₆` nor `M₁₈` appears among the corrections — the `q`-content flows
through `M₂`, `M₄`, `M₆`, `M₁₀`, `M₁₂`, `M₁₄` alone (`q₀` and `q₄`
drop out of the defect entirely).  The exact multiplier identity is

`671088640 H¹⁸ · row₁ = (H M₂₀' - 18 M₂₀ H')
  + 5 p₃ (2 H M₁₈' - 33 M₁₈ H') + 320 p₂ H² (H M₁₆' - 15 M₁₆ H')
  + (640 p₁ H⁴ + 160 p₂ p₃ H² - 20 p₃³) (2 H M₁₄' - 27 M₁₄ H')
  + (10240 p₀ H⁶ + 5120 p₁ p₃ H⁴ + 2560 p₂² H⁴ - 1280 p₂ p₃² H²
    + 160 p₃⁴) (H M₁₂' - 12 M₁₂ H')
  + (15360 p₀ p₃ H⁶ + 15360 p₁ p₂ H⁶ - 1920 p₁ p₃² H⁴
    - 1920 p₂² p₃ H⁴ + 800 p₂ p₃³ H² - 90 p₃⁵) (2 H M₁₀' - 21 M₁₀ H')
  + (655360 p₀ p₂ H⁸ + 327680 p₁² H⁸) (H M₈' - 9 M₈ H')
  + c₆ (2 H M₆' - 15 M₆ H') + c₄ (H M₄' - 6 M₄ H')
  + c₂ (2 H M₂' - 9 M₂ H')`

with multiplier `2²⁷·5·H¹⁸` — the first aligned multiplier that is
not a pure power of two — and an EMPTY correction module for the
SIXTH row in a row; the row's entire `q₀'`-content is carried by the
`M₁₆` bracket with cofactor `320 p₂ H²`.  On the aligned face every
previous bracket vanishes, so `H M₂₀' = 18 M₂₀ H'` and the
weight-`18` first integral

`M₂₀ = κ₁₁ H¹⁸`

holds for a preserved constant `κ₁₁` — even-type and CHAMBER-FREE,
the SIXTH rung of the even ladder `H⁴, H⁶, H⁹, H¹², H¹⁵, H¹⁸`; no
parity kill, `κ₁₁` is preserved in BOTH chambers.  The chamber core,
after cancelling `h₀²⁴` resp. `H¹²`, is a SEXTIC-cofactor cube plus a
`p₁`-loaded quintic square block:

`3200 (143 w⁶ - 572 p₂ w⁴ + 528 p₂² w² - 64 p₂³) (w² - 4 p₂)³
  + 51200 h p₁ w (187 w⁴ - 664 p₂ w² + 432 p₂²) (w² - 4 p₂)²`
  (`h = h₀²` resp. `H`)

and — because every `q`-letter of the row was already solved — the
whole relation is `q`-FREE in both chambers, and `κ`, `κ₅`, `κ₉` drop
out entirely.  The `μ`-block of the quotient factors through
`(u² - 4 p₂)` for the first time, so the leading peel is μ-FREE.

* square chamber `H = h₀²`, `p₃ = h₀² u`, `M₂ = μ h₀⁹`, `M₄ = κ₃ H⁶`,
  `M₆ = μ₂ h₀¹⁵`, `M₁₀ = μ₃ h₀²¹`, `M₁₂ = κ₇ H¹²`, `M₁₄ = μ₄ h₀²⁷`,
  `M₂₀ = κ₁₁ H¹⁸`: on the consumed divisibility `u² - 4 p₂ = h₀ v`
  the peel is NINE deep — the deepest aligned peel: the NEW μ-FREE
  leading divisibility

  `3200 (143 u⁶ - 572 p₂ u⁴ + 528 p₂² u² - 64 p₂³) v³ = h₀ s₂₅`

  — the first aligned peel whose head carries no constant at all —
  then the explicit peels producing `s₂₆` through `s₃₃` (`s₃₁` is
  loaded with `μ₄`), and the SECOND aligned CONSTANT PIN, now a
  `p₀`-CUBIC:

  `C κ₁₁ = 838860800 p₀³ - 7864320 κ₃ p₀² - 10240 κ₇ p₀ - s₃₃`

  — the row pins the even constant `κ₁₁` globally against the peel
  letters.  Combining the pin with the ninth face's solved row
  `4194304 q₀ = 524288 κ p₀² - 2048 κ₅ p₀ - κ₉ - s₁₆` eliminates the
  `p₀`-cubic and yields the GLOBAL `q₀`-backwire cross-tie

  `C κ C κ₁₁ = 6710886400 p₀ q₀ + 3276800 κ₅ p₀² + 1600 κ₉ p₀
    + 1600 p₀ s₁₆ - 7864320 κ κ₃ p₀² - 10240 κ κ₇ p₀ - κ s₃₃`

  — the FIRST global cross-face link between two aligned pins.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots),
  `p₃ = H g`, `M₂ = M₆ = M₁₀ = M₁₄ = M₁₈ = 0`, `M₄ = κ₃ H⁶`,
  `M₁₂ = κ₇ H¹²`, `M₂₀ = κ₁₁ H¹⁸`: on the consumed divisibility
  `g² - 4 p₂ = H f` the row yields the `q`-free block identity whose
  `H²`-part carries `κ₁₁ + 7864320 κ₃ p₀² + 10240 κ₇ p₀
  - 838860800 p₀³` — `κ₁₁` is TIED two `H`-levels deep (like the
  ninth face's `q₀`), not solved, and no parity kill occurs.

The honest new root content at the core root `a` (where
`w(a)² = 4 p₂(a)` from the fifth face): the square chamber gains the
NEW value tie as a PURE PRODUCT KILL `u(a)⁶ v(a)³ = 0` (the sextic
cofactor evaluates to `32 u⁶` on the kill and the μ-block dies), so
the root dichotomy `(u(a) = 0 ∧ p₂(a) = 0) ∨ (v(a) = 0 ∧ μ = 0)` is
derived DIRECTLY — `u = 0` or `v = 0` splits against the sixth face's
product kill `u (16 v³ - 7 μ u³) = 0` — plus `s₂₅(a) = 0` AND
`s₂₆(a) = 0` unconditionally (the first aligned double peel kill),
the μ₄-loaded tie `s₃₂(a) = -1638400 μ₂ p₀ p₁ - 640 μ₄ p₁`, the
`κ₁₁` value tie, and — combining with the eighth face's `q₁`-solve to
eliminate `κ₇` — the `q₁`-backwire root tie

`u κ₁₁ = 2684354560 p₀ q₁ - 1677721600 p₀³ u + 7864320 κ₃ p₀² u
  + 1310720 κ₅ p₀ p₁ - 671088640 κ p₀² p₁ - 2560 p₀ s₉ - s₃₃ u` at `a`.

The nonsquare chamber's block dies at `a` and collapses on the
quadratic kill to the PERFECT-CUBE PRODUCT

`g(a)³ · (g(a) f(a) + 8 p₁(a))³ = 0`

— an independent re-derivation of the eighth face's root-pin content
with a `g³`-cofactor (no new pin is claimed).

No closure is claimed.  Both chambers remain open, both dichotomy
branches are preserved, the zero branches are not excluded, and the
constants are preserved where not previously forced (`κ₁₁` is pinned
globally in the square chamber against the peel letters and tied two
`H`-levels deep in the nonsquare chamber, but not cleared).  The
aligned Jacobian tower now has ONLY the terminal degree-`0` row
`p₀' q₁ - p₁ q₀' = C j` — the inhomogeneous Keller-constant row —
left unused.  No total-degree or twice-prime theorem is used, and no
finite-root shortcut is taken.
-/

/-! Proofs are isolated in one-declaration Part modules for bounded elaboration memory. -/

namespace Max11DegreeRoutes

#print axioms alignedTwelfthCoefficientJacobianRow_410
#print axioms alignedTwelfthDefect_weightedDerivative_identity_410
#print axioms alignedTwelfthDefectRow_eq_zero_410
#print axioms eighteenthPowerRelation_of_weightEighteenRow_410
#print axioms alignedTwelfthDefectPowerRelation_410
#print axioms alignedSquareTwelfth_core_410
#print axioms alignedSquareTwelfth_solved_410
#print axioms alignedNonsquareTwelfth_core_410
#print axioms alignedNonsquareTwelfth_solved_410
#print axioms normalized410ScaleTwo_alignedTwelfthRow_packet
#print axioms normalized410ScaleTwo_alignedTwelfthRow_squareChamber_packet
#print axioms normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
#print axioms normalized410ScaleTwo_alignedTwelfthRow_chamberDichotomy
#print axioms normalized410ScaleTwo_alignedTwelfthRow_rootData

end Max11DegreeRoutes
