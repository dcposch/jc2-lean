import Fable610ScaleTwoAlignedEleventhFacePart101Scratch
import Fable610ScaleTwoAlignedEleventhFacePart03Scratch
import Fable610ScaleTwoAlignedEleventhFacePart102Scratch
import Fable610ScaleTwoAlignedEleventhFacePart09Scratch
import Fable610ScaleTwoAlignedEleventhFacePart13Scratch
import Fable610ScaleTwoAlignedEleventhFacePart16Scratch
import Fable610ScaleTwoAlignedEleventhFacePart17Scratch

/-! # Eleventh aligned face row for the normalized `(6,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable610ScaleTwoAlignedTenthFaceScratch` consumed the degree-`5`
Keller row on the aligned face `N = 5 p₅ H² - 3 q₉ = 0` into the
chamber-free weight-`25` integral `Ω = κ₉ H²⁵`, transferring the NEW
μ-loaded divisibility `2048 e₁³ w₁⁴ - μ w₁⁷ = h₀ s₂` (square chamber)
and solving `q₀` outright through the NEW divisibility
`243 p₁ - g₁ u = H v` (nonsquare chamber).  This file consumes the
next unused aligned row, the degree-`4` Jacobian coefficient — the
first aligned row whose antidiagonal has lost the leading coefficient
`p₆ = H³` (pairs `(0,5), (1,4), (2,3), (3,2), (4,1), (5,0)`), seeing
`q₀` through `q₀'` only (via `5 p₅ q₀'`) and NO new Jacobian
coefficient: the `q`-jet is exhausted at `q₀`.

At the source level, modulo the face and the consumed degree-`13`
through degree-`5` rows, the degree-`4` row is the weighted derivative
of the cleared eleventh defect

`Λ = 522427760640 p₀ p₁ H²⁷ - 174142586880 (p₀ p₂ + p₁² / 2) p₅ H²⁴
  - 174142586880 (p₀ p₃ + p₁ p₂) p₄ H²⁴ - 87071293440 (p₁ p₃² + p₂² p₃) H²⁴ / …
  + partitions-of-11 monomials - 404684800 p₅¹¹ + κ-block
  - (1128701952 (p₀ p₄ + p₁ p₃) H¹⁸ + 564350976 p₂² H¹⁸ - …) D
  - (67184640 p₀ H¹⁵ - …) F - (2985984 p₁ H¹² - …) G
  - (93312 p₂ H⁹ - …) I - (10368 p₃ H⁶ - 6912 p₄ p₅ H³ + 1920 p₅³) J
  - (48 p₄ H³ - 20 p₅²) L`,

kept in factored form through the third, fifth, sixth, seventh,
eighth, and ninth defects — in the minimal gauge the fourth defect `E`
and the tenth defect `Ω` do NOT enter the defect at all — via the
exact multiplier identity

`156728328192 H²⁶ · row₄ = (2 H Λ' - 55 Λ H')
  + (5643509760 (p₀ p₄ + p₁ p₃) H¹⁸ + 2821754880 p₂² H¹⁸ + …) rowD
  + 1612431360 (p₀ p₅ + p₁ p₄ + p₂ p₃) H¹⁵ rowE
  + (67184640 p₀ H¹⁵ + 55987200 (p₁ p₅ + p₂ p₄) H¹² + …) rowF
  + (7464960 p₁ H¹² + …) rowG + (155520 p₂ H⁹ + …) rowI
  + (51840 p₃ H⁶ + 17280 p₄ p₅ H³ - 1920 p₅³) rowJ
  + (240 p₄ H³ + 20 p₅²) rowL + 80 p₅ rowΩ`.

The row sees neither `q₉` nor `q₈` — the THIRD aligned row in sequence
with an EMPTY source-correction module: no `N`-correction and no
`C`-correction of any kind.  On the aligned face every correction
vanishes, so `2 H Λ' = 55 Λ H'` and the squared weight-`55/2` first
integral `Λ² = κ₁₀ H⁵⁵` holds — ODD exponent, chambered like `D`,
`F`, `I`, `L`.

* Square chamber (`H = h₀²`, `p₅ = h₀⁴ w₁`, `p₄ = h₀² f₂`,
  `D = μ h₀¹⁵`, `F = ν h₀²⁵`, `G = κ₅ H¹⁵`, `I = ν₂ h₀³⁵`,
  `J = κ₇ H²⁰`, `L = μ₃ h₀⁴⁵`): the square root exists,
  `Λ = μ₄ h₀⁵⁵` with `μ₄² = κ₁₀`.  Cancelling `h₀⁴⁴` leaves the core
  `= μ₄ h₀¹¹` whose `h₀`-free undecic head has every term of total
  `(α,β)`-degree at least two in `α = 27 p₃ - w₁³`, `β = 3 f₂ - w₁²`,
  `z = w₁`, with degree-two part `-1474560 z⁵ (α - 3 β z)²`.
  Substituting `e₁, e₂` peels `h₀²` onto the head
  `-1474560 w₁⁵ (3 e₁ w₁ - e₂)²`, reducing along the eighth-face
  product divisor `u₂` peels one more `h₀` onto the μ-loaded head
  `-135 w₁⁵ (7 μ w₁³ - 32768 e₁³)`, and substituting the carried
  tenth-face divisor `s₂` collapses the head to the PURE MONOMIAL
  `1215 μ w₁⁸`: the row pins `μ w₁(a)⁸ = 0` at the root outright —
  rederiving the tenth-face residual branch — and transfers to the
  NEW divisibility `μ w₁⁸ = h₀ s₄`.  Substituting `s₄` peels one more
  `h₀` into the peeled row `= μ₄ h₀⁷` — the FIRST aligned
  square-chamber row carrying NO `q`-coefficient at all (a pure
  `p`-jet/witness constraint; `κ₃` and `κ₉` are also absent).  At the
  root the peeled head, the carried facts `e₂(a) = 0`, the `u₂` root
  product, and the tenth-face tie
  `135 s₂(a) = 92160 w₁(a)² (81 p₂(a) - u₂(a))²` force the exact
  vanishing `s₄(a) = 0`, deepening the new divisor to
  `μ w₁⁸ = h₀² s₅`.
* Nonsquare chamber (`H` a degree-two nonsquare, simple roots,
  `p₅ = H² g₁`, `p₄ = H f`, `D = 0`, `F = 0`, `I = 0`, `L = 0`,
  `G = κ₅ H¹⁵`, `J = κ₇ H²⁰`): the odd exponent FORCES `κ₁₀ = 0` and
  `Λ ≡ 0`, exactly as for `D`, `F`, `I`, `L`.  Cancelling `H²²` and
  substituting `t₁, t₂` peels `H²` onto the head
  `-1474560 g₁³ (81 p₂ + 3 g₁² t₁ - g₁ t₂)²` — the carried eighth-face
  `p₂` divisor squared — so substituting `u` peels one more `H` onto
  the cubic head `163840 g₁² (6 g₁ t₁ - t₂)³` — the carried ninth-face
  `t₃` divisor cubed — so substituting `t₃` peels one more `H` onto
  the head `-1474560 g₁ (243 p₁ - g₁ u)²` — the carried TENTH-face `v`
  divisor squared — so substituting `v` peels `H²` more and the row
  bottoms out WITHOUT introducing any new witness: the residue

  `1280 g₁² t₃³ - 9216 κ g₁ t₁ t₃² + 9216 κ g₁ t₃ v + 23040 g₁ t₁² t₃²
  - 23040 g₁ t₁ t₃ v - 3840 g₁ t₃² u + 11520 g₁ v² - 96 κ₅ t₁ t₃
  + 96 κ₅ v + 3 κ₇ t₃ - 6718464 κ p₀ t₃ - 46080 κ t₁³ t₃
  + 27648 κ t₁² v + 18432 κ t₁ t₃ u - 9216 κ u v + 16796160 p₀ t₁ t₃
  - 16796160 p₀ v + 80640 t₁⁴ t₃ - 46080 t₁³ v - 46080 t₁² t₃ u
  + 23040 t₁ u v + 3840 t₃ u² + H (1024 κ t₃³ - 5120 t₁ t₃³
  + 3840 t₃² v) = 0`

  — an inhomogeneous relation on the CARRIED witnesses whose root
  evaluation is the FIRST `p₀`-loaded root relation of the aligned
  nonsquare tower (`p₀` enters through `16796160 p₀ (t₁ t₃ - v) -
  6718464 κ p₀ t₃`).  No `q`-coefficient is solved — none is left.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`,
`dvd_of_sq_dvd_sq_poly`, and
`linearPolynomial_dvd_of_eval_eq_zero_810`.

No closure is claimed.  Both chambers remain open, the zero branches
(`w₁ = 0`, `f₂ = 0`, `e₁ = 0`, `e₂ = 0`, `e₃ = 0`, `u₂ = 0`, `s₂ = 0`,
`s₄ = 0`, `s₅ = 0`, `g₁ = 0`, `f = 0`, `t₁ = 0`, `t₂ = 0`, `t₃ = 0`,
`u = 0`, `v = 0`, `κ = 0`, `μ = 0`, `κ₃ = 0`, `ν = 0`, `κ₅ = 0`,
`κ₆ = 0`, `ν₂ = 0`, `κ₇ = 0`, `κ₈ = 0`, `μ₃ = 0`, `κ₉ = 0`,
`κ₁₀ = 0`, `μ₄ = 0`) are not excluded, and the constants `κ`,
`κ₂ = μ²`, `κ₃`, `κ₄ = ν²`, `κ₅`, `κ₆ = ν₂²`, `κ₇`, `κ₈ = μ₃²`, `κ₉`,
`κ₁₀ = μ₄²` are preserved where not forced (`κ₁₀ = 0` is FORCED in the
nonsquare chamber).  The square residual branch
`w₁(a) = 0 ∨ (μ = 0 ∧ e₁(a) = 0)` keeps both alternatives; no
individual vanishing of `p₀, p₁, p₂, p₃` is claimed.  The next unused
Keller row on the aligned face is the degree-`3` Jacobian coefficient
(pairs `(0,4), (1,3), (2,2), (3,1), (4,0)`; expected weight-`30`
defect, even exponent, chamber-free like `E`, `G`, `J`, `Ω`).  No
total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken. -/
/-! ## Literal degree-`4` Keller coefficient on the aligned face -/

namespace Max11DegreeRoutes

#print axioms alignedEleventhCoefficientJacobianRow_610
#print axioms alignedEleventhDefect_weightedDerivative_identity_610
#print axioms alignedEleventhDefectRow_eq_zero_610
#print axioms alignedEleventhDefectPowerRelation_610
#print axioms alignedSquareEleventh_sqrt_610
#print axioms alignedEleventhSquareTieResolve_610
#print axioms alignedSquareEleventh_descent_610
#print axioms alignedNonsquareEleventh_defect_eq_zero_610
#print axioms alignedNonsquareEleventh_descent_610
#print axioms normalized610ScaleTwo_alignedEleventhFace_packet
#print axioms normalized610ScaleTwo_alignedEleventhFace_squareChamber_packet
#print axioms normalized610ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
#print axioms normalized610ScaleTwo_alignedEleventhFace_chamberDichotomy
#print axioms normalized610ScaleTwo_alignedEleventhFace_rootData

end Max11DegreeRoutes
