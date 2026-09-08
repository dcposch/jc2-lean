import Fable610ScaleTwoAlignedNinthFacePart01Scratch
import Fable610ScaleTwoAlignedNinthFacePart02Scratch
import Fable610ScaleTwoAlignedNinthFacePart03Scratch
import Fable610ScaleTwoAlignedNinthFacePart04Scratch
import Fable610ScaleTwoAlignedNinthFacePart05Scratch
import Fable610ScaleTwoAlignedNinthFacePart06Scratch
import Fable610ScaleTwoAlignedNinthFacePart07Scratch
import Fable610ScaleTwoAlignedNinthFacePart08Scratch
import Fable610ScaleTwoAlignedNinthFacePart09Scratch
import Fable610ScaleTwoAlignedNinthFacePart10Scratch
import Fable610ScaleTwoAlignedNinthFacePart11Scratch
import Fable610ScaleTwoAlignedNinthFacePart12Scratch
import Fable610ScaleTwoAlignedNinthFacePart13Scratch
import Fable610ScaleTwoAlignedNinthFacePart14Scratch
import Fable610ScaleTwoAlignedNinthFacePart15Scratch
import Fable610ScaleTwoAlignedNinthFacePart16Scratch
import Fable610ScaleTwoAlignedNinthFacePart17Scratch

/-! # Ninth aligned face row for the normalized `(6,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable610ScaleTwoAlignedEighthFaceScratch` consumed the degree-`7`
Keller row on the aligned face `N = 5 p₅ H² - 3 q₉ = 0` into the
chamber-free weight-twenty integral `J = κ₇ H²⁰`, with the
square-chamber product divisibility `w₁ (e₂ - 3 e₁ w₁) = h₀ u₂` and
the nonsquare-chamber divisor `81 p₂ + 3 g₁² t₁ - g₁ t₂ = H u` (the
first `p₂` constraint of the aligned tower) with `q₂` solved outright.
This file consumes the next unused aligned row, the degree-`6`
Jacobian coefficient — the first row that sees `q₁` (pairs
`(0,7), (1,6), (2,5), (3,4), (4,3), (5,2), (6,1)`).

At the source level, modulo the face and the consumed degree-`13`
through degree-`7` rows, the degree-`6` row is the weighted derivative
of the cleared ninth defect

`L = 1813985280 (p₀ p₃ + p₁ p₂) H²¹ - 1632586752 q₁ H²²
  - 604661760 (p₀ p₄ p₅ + p₁ p₃ p₅ + p₂ p₃ p₄) H¹⁸
  - 302330880 (p₁ p₄² + p₂² p₅) H¹⁸ - 100776960 p₃³ H¹⁸
  + partitions-of-9 monomials + κ-block
  - (23514624 p₀ H¹⁵ + …) D - 3359232 p₁ H¹² E - (233280 p₂ H⁹ + …) F
  - (10368 p₃ H⁶ - …) G - (324 p₄ H³ - 81 p₅²) I - 36 p₅ J`,

kept in factored form through the third–eighth defects, via the exact
multiplier identity

`544195584 H²⁰ · row₆[p₆ = H³] = (2 H L' - 45 L H')
  + (23514624 p₀ H¹⁵ + …) rowD
  + 7838208 (p₁ H¹² + p₂ p₅ H⁹ + p₃ p₄ H⁹) rowE
  + (326592 p₂ H⁹ + …) rowF + (36288 p₃ H⁶ + …) rowG
  + (756 p₄ H³ + 189 p₅²) rowI + 252 p₅ rowJ`.

The row sees neither `q₉` nor `q₈` at all — the first aligned row with
an EMPTY source-correction module: there is no `N`-correction and no
`C`-correction of any kind.  On the aligned face every correction
vanishes, so `2 H L' = 45 L H'` and the weight-`45/2` first integral
`L² = κ₈ H⁴⁵` holds — ODD exponent, chambered like `D`, `F`, `I`.

* Square chamber (`H = h₀²`, `p₅ = h₀⁴ w₁`, `p₄ = h₀² f₂`,
  `D = μ h₀¹⁵`, `E = κ₃ H¹⁰`, `F = ν h₀²⁵`, `G = κ₅ H¹⁵`,
  `I = ν₂ h₀³⁵`, `J = κ₇ H²⁰`): `L = μ₃ h₀⁴⁵` with `μ₃² = κ₈`.
  Cancelling `h₀³⁶` leaves the core `= μ₃ h₀⁹` whose `h₀`-free nonic
  head is
  `-5120 (α³ - 36 α² β z + 9 α² z³ - 36 α β³ + 270 α β² z² - 54 α β z⁴
  + 189 β⁴ z - 540 β³ z³ + 81 β² z⁵)`
  in `α = 27 p₃ - w₁³`, `β = 3 f₂ - w₁²`, `z = w₁` — every term of
  total `(α,β)`-degree at least two, with degree-two part
  `9 z³ (α - 3 β z)²`.  Substituting `e₁, e₂` and reducing along the
  eighth-face product divisor `u₂` peels `h₀³` to the peeled row
  `= μ₃ h₀⁶` with head `27 w₁³ (10240 e₁³ - 7 μ w₁³) - 5120 e₂³` and
  `q₁` tied at `h₀⁵`.  At the root the head, the `u₂` root product,
  and the eighth-face combined-row cubic RESOLVE the eighth-face
  residual branch: `e₂(a) = 0` holds UNCONDITIONALLY, refined by
  `w₁(a) = 0 ∨ (μ = 0 ∧ e₁(a) = 0)` — so the seventh-face divisor
  DEEPENS to `27 p₃ - w₁³ = h₀² e₃`, the first `h₀²`-deep
  divisibility of the aligned tower.
* Nonsquare chamber (`H` a degree-two nonsquare, simple roots,
  `p₅ = H² g₁`, `p₄ = H f`, `D = 0`, `F = 0`, `I = 0`, `E = κ₃ H¹⁰`,
  `G = κ₅ H¹⁵`, `J = κ₇ H²⁰`): the odd exponent forces `κ₈ = 0` and
  `L ≡ 0`.  Cancelling `H¹⁸` and substituting `t₁, t₂` peels `H²`
  with head `-46080 g₁ (81 p₂ + 3 g₁² t₁ - g₁ t₂)²` — the CARRIED
  eighth-face `p₂` divisor squared — so substituting `u` peels one
  more `H`, leaving the cubic head `-5120 (t₂ - 6 g₁ t₁)³`, which
  vanishes at BOTH simple roots and transfers to the NEW divisibility
  `t₂ - 6 g₁ t₁ = H t₃` with root pin `t₂(a) = 6 g₁(a) t₁(a)` (hence
  `27 p₂(a) = g₁(a)² t₁(a)`, refining the carried eighth-face `p₂`
  pin).  Substituting `t₃` peels the last `H` and `q₁` is solved
  OUTRIGHT: `1632586752 q₁ = … - 5120 H² t₃³`.

The generic transfer lemmas are reused unchanged:
`nonsquare_natDegree_two_derivative_ne_zero`,
`dvd_of_eval_eq_zero_of_simple_natDegree_two`,
`dvd_of_sq_dvd_sq_poly`, and
`linearPolynomial_dvd_of_eval_eq_zero_810`.

No closure is claimed.  Both chambers remain open, the zero branches
(`w₁ = 0`, `f₂ = 0`, `e₁ = 0`, `e₂ = 0`, `e₃ = 0`, `u₂ = 0`,
`g₁ = 0`, `f = 0`, `t₁ = 0`, `t₂ = 0`, `t₃ = 0`, `u = 0`, `κ = 0`,
`μ = 0`, `κ₃ = 0`, `ν = 0`, `κ₅ = 0`, `κ₆ = 0`, `ν₂ = 0`, `κ₇ = 0`,
`κ₈ = 0`, `μ₃ = 0`) are not excluded, and the constants `κ`,
`κ₂ = μ²`, `κ₃`, `κ₄ = ν²`, `κ₅`, `κ₆ = ν₂²`, `κ₇`, `κ₈ = μ₃²` are
preserved where not forced.  The square residual branch keeps both
alternatives; no individual vanishing of `p₀, p₁, p₂, p₃, q₁, q₂, q₃`
is claimed.  The next unused Keller row on the aligned face is the
degree-`5` Jacobian coefficient, the first row that sees `q₀` (pairs
`(0,6), (1,5), (2,4), (3,3), (4,2), (5,1), (6,0)`; expected
weight-`25` defect, even exponent, chamber-free like `E`, `G`, `J`).
No total-degree or twice-prime theorem is used, and no finite-root
shortcut is taken. -/
/-! ## Literal degree-`6` Keller coefficient on the aligned face -/

namespace Max11DegreeRoutes

#print axioms alignedNinthCoefficientJacobianRow_610
#print axioms alignedNinthDefect_weightedDerivative_identity_610
#print axioms alignedNinthDefectRow_eq_zero_610
#print axioms alignedNinthDefectPowerRelation_610
#print axioms alignedSquareNinth_sqrt_610
#print axioms alignedNinthSquareResolve_610
#print axioms alignedSquareNinth_descent_610
#print axioms alignedNonsquareNinth_defect_eq_zero_610
#print axioms alignedNonsquareNinth_descent_610
#print axioms normalized610ScaleTwo_alignedNinthFace_packet
#print axioms normalized610ScaleTwo_alignedNinthFace_squareChamber_packet
#print axioms normalized610ScaleTwo_alignedNinthFace_nonsquareChamber_packet
#print axioms normalized610ScaleTwo_alignedNinthFace_chamberDichotomy
#print axioms normalized610ScaleTwo_alignedNinthFace_rootData

end Max11DegreeRoutes
