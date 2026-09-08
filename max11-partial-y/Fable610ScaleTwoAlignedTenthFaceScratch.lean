import Fable610ScaleTwoAlignedTenthFacePart01Scratch
import Fable610ScaleTwoAlignedTenthFacePart02Scratch
import Fable610ScaleTwoAlignedTenthFacePart03Scratch
import Fable610ScaleTwoAlignedTenthFacePart04Scratch
import Fable610ScaleTwoAlignedTenthFacePart05Scratch
import Fable610ScaleTwoAlignedTenthFacePart06Scratch
import Fable610ScaleTwoAlignedTenthFacePart07Scratch
import Fable610ScaleTwoAlignedTenthFacePart08Scratch
import Fable610ScaleTwoAlignedTenthFacePart09Scratch
import Fable610ScaleTwoAlignedTenthFacePart10Scratch
import Fable610ScaleTwoAlignedTenthFacePart11Scratch
import Fable610ScaleTwoAlignedTenthFacePart12Scratch
import Fable610ScaleTwoAlignedTenthFacePart13Scratch
import Fable610ScaleTwoAlignedTenthFacePart14Scratch
import Fable610ScaleTwoAlignedTenthFacePart15Scratch

/-! # Tenth aligned face row for the normalized `(6,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable610ScaleTwoAlignedNinthFaceScratch` consumed the degree-`6`
Keller row on the aligned face `N = 5 p₅ H² - 3 q₉ = 0` into the
chambered squared weight-`45/2` integral `L² = κ₈ H⁴⁵`, resolving the
eighth-face residual branch to `e₂(a) = 0` and deepening the
seventh-face divisor to `27 p₃ - w₁³ = h₀² e₃` (square chamber), and
solving `q₁` outright through the new divisibility `t₂ - 6 g₁ t₁ =
H t₃` (nonsquare chamber).  This file consumes the next unused aligned
row, the degree-`5` Jacobian coefficient — the first row that sees
`q₀` (through `q₀'` only; pairs `(0,6), (1,5), (2,4), (3,3), (4,2),
(5,1), (6,0)`).

At the source level, modulo the face and the consumed degree-`13`
through degree-`6` rows, the degree-`5` row is the weighted derivative
of the cleared tenth defect

`Ω = 10883911680 p₀ p₂ H²⁴ + 5441955840 p₁² H²⁴ - 9795520512 q₀ H²⁵
  - 3627970560 (p₀ p₃ + p₁ p₂) p₅ H²¹ - 1813985280 p₀ p₄² H²¹
  - 3627970560 p₁ p₃ p₄ H²¹ - 1813985280 (p₂² p₄ + p₂ p₃²) H²¹
  + partitions-of-10 monomials + κ-block
  - (23514624 (p₀ p₅ + p₁ p₄ + p₂ p₃) H¹⁵ + …) D - 20155392 p₀ H¹⁵ E
  - (1399680 p₁ H¹² - …) F - (62208 p₂ H⁹ - …) G
  - (1944 p₃ H⁶ - 972 p₄ p₅ H³ + 243 p₅³) I - (216 p₄ H³ - 72 p₅²) J
  - p₅ L`,

kept in factored form through the third–ninth defects, via the exact
multiplier identity

`1632586752 H²³ · row₅[p₆ = H³] = (H Ω' - 25 Ω H')
  + (70543872 (p₀ p₅ + p₁ p₄ + p₂ p₃) H¹⁵ + …) rowD
  + (20155392 (p₀ H³ + p₁ p₅ + p₂ p₄) H¹² + 10077696 p₃² H¹²) rowE
  + (839808 p₁ H¹² + …) rowF + (93312 p₂ H⁹ + …) rowG
  + (1944 p₃ H⁶ + 972 p₄ p₅ H³ - 81 p₅³) rowI
  + (648 p₄ H³ + 108 p₅²) rowJ + 3 p₅ rowL`.

The row sees neither `q₉` nor `q₈` — the second aligned row in
sequence with an EMPTY source-correction module: no `N`-correction and
no `C`-correction of any kind.  On the aligned face every correction
vanishes, so `H Ω' = 25 Ω H'` and the weight-`25` first integral
`Ω = κ₉ H²⁵` holds for a preserved constant `κ₉` in BOTH chambers —
EVEN exponent, chamber-free like `E`, `G`, `J`.

* Square chamber (`H = h₀²`, `p₅ = h₀⁴ w₁`, `p₄ = h₀² f₂`,
  `D = μ h₀¹⁵`, `E = κ₃ H¹⁰`, `F = ν h₀²⁵`, `G = κ₅ H¹⁵`,
  `I = ν₂ h₀³⁵`, `J = κ₇ H²⁰`, `L = μ₃ h₀⁴⁵`): cancelling `h₀⁴⁰`
  leaves the core `= κ₉ h₀¹⁰` whose `h₀`-free decic head has every
  term of total `(α,β)`-degree at least two in `α = 27 p₃ - w₁³`,
  `β = 3 f₂ - w₁²`, `z = w₁`, with degree-two part
  `92160 z⁴ (α - 3 β z)²`.  Substituting `e₁, e₂` peels `h₀²` onto the
  head `92160 w₁⁴ (3 e₁ w₁ - e₂)²` and reducing along the eighth-face
  product divisor `u₂` peels one more `h₀`, giving the μ-loaded head
  `-135 (2048 e₁³ w₁⁴ - μ w₁⁷)` with `q₀` tied at `h₀⁷`.  At the root
  the head transfers to the NEW divisibility
  `2048 e₁³ w₁⁴ - μ w₁⁷ = h₀ s₂` — the first aligned μ-loaded
  divisibility — and substituting `s₂` peels one more `h₀` into the
  peeled row `= κ₉ h₀⁶` with `q₀` tied at `h₀⁶`, the first
  square-chamber row whose head sees `p₂`.  At the root the peeled
  head, `e₂(a) = 0` (ninth-face deepening), and the `u₂` root product
  force the exact tie
  `135 s₂(a) = 92160 w₁(a)² (81 p₂(a) - u₂(a))²` — the new witness is
  pinned by the carried `p₂`-block, whose discriminant is a perfect
  square.
* Nonsquare chamber (`H` a degree-two nonsquare, simple roots,
  `p₅ = H² g₁`, `p₄ = H f`, `D = 0`, `F = 0`, `I = 0`, `L = 0`,
  `E = κ₃ H¹⁰`, `G = κ₅ H¹⁵`, `J = κ₇ H²⁰`): `Ω = κ₉ H²⁵` SURVIVES
  (chamber-free — nothing is forced).  Cancelling `H²⁰` and
  substituting `t₁, t₂` peels `H²` with head
  `92160 g₁² (81 p₂ + 3 g₁² t₁ - g₁ t₂)²` — the carried eighth-face
  `p₂` divisor squared — so substituting `u` peels one more `H` onto
  the cubic head `-10240 g₁ (6 g₁ t₁ - t₂)³` — the carried ninth-face
  `t₃` divisor cubed — so substituting `t₃` peels one more `H` onto
  the PERFECT-SQUARE head `92160 (243 p₁ - g₁ u)²`, which vanishes at
  BOTH simple roots and transfers to the NEW divisibility
  `243 p₁ - g₁ u = H v` — the FIRST `p₁` constraint of the aligned
  nonsquare tower, pinning `243 p₁(a) = g₁(a) u(a)` at every root.
  Substituting `v` peels the last `H` and `q₀` is solved OUTRIGHT with
  `κ₉` entering at level ZERO:
  `9795520512 q₀ = -387072 t₁⁵ + 368640 t₁³ u - 92160 t₁ u²
  - 201553920 p₀ t₁² + 134369280 p₀ u + κ(…) - 20155392 κ₃ p₀
  + κ₅(1152 t₁² - 768 u) - 72 κ₇ t₁ + H(…) - κ₉`.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`, and
`linearPolynomial_dvd_of_eval_eq_zero_810`.

No closure is claimed.  Both chambers remain open, the zero branches
(`w₁ = 0`, `f₂ = 0`, `e₁ = 0`, `e₂ = 0`, `e₃ = 0`, `u₂ = 0`, `s₂ = 0`,
`g₁ = 0`, `f = 0`, `t₁ = 0`, `t₂ = 0`, `t₃ = 0`, `u = 0`, `v = 0`,
`κ = 0`, `μ = 0`, `κ₃ = 0`, `ν = 0`, `κ₅ = 0`, `κ₆ = 0`, `ν₂ = 0`,
`κ₇ = 0`, `κ₈ = 0`, `μ₃ = 0`, `κ₉ = 0`) are not excluded, and the
constants `κ`, `κ₂ = μ²`, `κ₃`, `κ₄ = ν²`, `κ₅`, `κ₆ = ν₂²`, `κ₇`,
`κ₈ = μ₃²`, `κ₉` are preserved where not forced.  The square residual
branch `w₁(a) = 0 ∨ (μ = 0 ∧ e₁(a) = 0)` keeps both alternatives; no
individual vanishing of `p₀, p₁, p₂, p₃, q₀, q₁, q₂` is claimed.  The
next unused Keller row on the aligned face is the degree-`4` Jacobian
coefficient (pairs `(0,5), (1,4), (2,3), (3,2), (4,1), (5,0)`; it sees
no new Jacobian coefficient — the `q`-jet is exhausted at `q₀` —
expected weight-`55/2` defect, odd exponent, chambered like `D`, `F`,
`I`, `L`).  No total-degree or twice-prime theorem is used, and no
finite-root shortcut is taken. -/
/-! ## Literal degree-`5` Keller coefficient on the aligned face -/

namespace Max11DegreeRoutes

#print axioms alignedTenthCoefficientJacobianRow_610
#print axioms alignedTenthDefect_weightedDerivative_identity_610
#print axioms alignedTenthDefectRow_eq_zero_610
#print axioms alignedTenthDefectPowerRelation_610
#print axioms alignedSquareTenth_descent_610
#print axioms alignedTenthSquareTieResolve_610
#print axioms alignedNonsquareTenth_descent_610
#print axioms normalized610ScaleTwo_alignedTenthFace_packet
#print axioms normalized610ScaleTwo_alignedTenthFace_squareChamber_packet
#print axioms normalized610ScaleTwo_alignedTenthFace_nonsquareChamber_packet
#print axioms normalized610ScaleTwo_alignedTenthFace_chamberDichotomy
#print axioms normalized610ScaleTwo_alignedTenthFace_rootData

end Max11DegreeRoutes
