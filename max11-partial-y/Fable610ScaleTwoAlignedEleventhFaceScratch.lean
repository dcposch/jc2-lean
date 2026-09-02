import Fable610ScaleTwoAlignedTenthFaceScratch

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

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`4` Keller coefficient on the aligned face -/

/-- The eleventh row below the leading weighted-Wronskian row for
outer degrees `(6,10)`: the degree-`4` Jacobian coefficient, the first
aligned row with no `p₆`-term — the leading coefficient has left the
antidiagonal — seeing `q₀` through `q₀'` only. -/
theorem alignedEleventhCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : K)) -
      ((p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 4) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (4 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 4 :
      Finset (ℕ × ℕ)) =
      ({(0, 4), (1, 3), (2, 2), (3, 1),
        (4, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  rw [hC2, hC3, hC4, hC5]
  linear_combination hcoeff

/-! ## Aligned eleventh defect -/

set_option maxHeartbeats 1600000000 in
/-- Cleared eleventh defect of the degree-`4` aligned `(6,10)` row,
kept in factored form through the third defect `D`, the fifth defect
`F`, the sixth defect `G`, the seventh defect `I`, the eighth defect
`J`, and the ninth defect `L` — in the minimal gauge the fourth defect
`E` and the tenth defect `Ω` do not enter, and the raw head carries no
`q`-coefficient at all.  On the aligned face it is a squared
polynomial first integral of weight `55/2`. -/
def alignedEleventhDefect610 {K : Type*} [CommRing K]
    (H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    K[X] :=
  ((522427760640 : K[X]) * a0 * a1 * H ^ 27 - (174142586880 : K[X]) * a0
    * a2 * a5 * H ^ 24 - (174142586880 : K[X]) * a0 * a3 * a4 * H ^ 24 +
    (116095057920 : K[X]) * a0 * a3 * a5 ^ 2 * H ^ 21 + (116095057920 :
    K[X]) * a0 * a4 ^ 2 * a5 * H ^ 21 - (90296156160 : K[X]) * a0 * a4 *
    a5 ^ 3 * H ^ 18 + (15049359360 : K[X]) * a0 * a5 ^ 5 * H ^ 15 -
    (87071293440 : K[X]) * a1 ^ 2 * a5 * H ^ 24 - (174142586880 : K[X]) *
    a1 * a2 * a4 * H ^ 24 + (116095057920 : K[X]) * a1 * a2 * a5 ^ 2 * H ^
    21 - (87071293440 : K[X]) * a1 * a3 ^ 2 * H ^ 24 + (232190115840 :
    K[X]) * a1 * a3 * a4 * a5 * H ^ 21 - (90296156160 : K[X]) * a1 * a3 *
    a5 ^ 3 * H ^ 18 + (38698352640 : K[X]) * a1 * a4 ^ 3 * H ^ 21 -
    (135444234240 : K[X]) * a1 * a4 ^ 2 * a5 ^ 2 * H ^ 18 + (75246796800 :
    K[X]) * a1 * a4 * a5 ^ 4 * H ^ 15 - (10868981760 : K[X]) * a1 * a5 ^ 6
    * H ^ 12 - (87071293440 : K[X]) * a2 ^ 2 * a3 * H ^ 24 + (116095057920
    : K[X]) * a2 ^ 2 * a4 * a5 * H ^ 21 - (45148078080 : K[X]) * a2 ^ 2 *
    a5 ^ 3 * H ^ 18 + (116095057920 : K[X]) * a2 * a3 ^ 2 * a5 * H ^ 21 +
    (116095057920 : K[X]) * a2 * a3 * a4 ^ 2 * H ^ 21 - (270888468480 :
    K[X]) * a2 * a3 * a4 * a5 ^ 2 * H ^ 18 + (75246796800 : K[X]) * a2 *
    a3 * a5 ^ 4 * H ^ 15 - (90296156160 : K[X]) * a2 * a4 ^ 3 * a5 * H ^
    18 + (150493593600 : K[X]) * a2 * a4 ^ 2 * a5 ^ 3 * H ^ 15 -
    (65213890560 : K[X]) * a2 * a4 * a5 ^ 5 * H ^ 12 + (8281128960 : K[X])
    * a2 * a5 ^ 7 * H ^ 9 + (38698352640 : K[X]) * a3 ^ 3 * a4 * H ^ 21 -
    (45148078080 : K[X]) * a3 ^ 3 * a5 ^ 2 * H ^ 18 - (135444234240 :
    K[X]) * a3 ^ 2 * a4 ^ 2 * a5 * H ^ 18 + (150493593600 : K[X]) * a3 ^ 2
    * a4 * a5 ^ 3 * H ^ 15 - (32606945280 : K[X]) * a3 ^ 2 * a5 ^ 5 * H ^
    12 - (22574039040 : K[X]) * a3 * a4 ^ 4 * H ^ 18 + (150493593600 :
    K[X]) * a3 * a4 ^ 3 * a5 ^ 2 * H ^ 15 - (163034726400 : K[X]) * a3 *
    a4 ^ 2 * a5 ^ 4 * H ^ 12 + (57967902720 : K[X]) * a3 * a4 * a5 ^ 6 * H
    ^ 9 - (6555893760 : K[X]) * a3 * a5 ^ 8 * H ^ 6 + (15049359360 : K[X])
    * a4 ^ 5 * a5 * H ^ 15 - (54344908800 : K[X]) * a4 ^ 4 * a5 ^ 3 * H ^
    12 + (57967902720 : K[X]) * a4 ^ 3 * a5 ^ 5 * H ^ 9 - (26223575040 :
    K[X]) * a4 ^ 2 * a5 ^ 7 * H ^ 6 + (5341839360 : K[X]) * a4 * a5 ^ 9 *
    H ^ 3 - (404684800 : K[X]) * a5 ^ 11 + Polynomial.C κ * ((23219011584
    : K[X]) * a0 * a3 * H ^ 26 - (15479341056 : K[X]) * a0 * a4 * a5 * H ^
    23 + (4299816960 : K[X]) * a0 * a5 ^ 3 * H ^ 20 + (23219011584 : K[X])
    * a1 * a2 * H ^ 26 - (15479341056 : K[X]) * a1 * a3 * a5 * H ^ 23 -
    (7739670528 : K[X]) * a1 * a4 ^ 2 * H ^ 23 + (12899450880 : K[X]) * a1
    * a4 * a5 ^ 2 * H ^ 20 - (2866544640 : K[X]) * a1 * a5 ^ 4 * H ^ 17 -
    (7739670528 : K[X]) * a2 ^ 2 * a5 * H ^ 23 - (15479341056 : K[X]) * a2
    * a3 * a4 * H ^ 23 + (12899450880 : K[X]) * a2 * a3 * a5 ^ 2 * H ^ 20
    + (12899450880 : K[X]) * a2 * a4 ^ 2 * a5 * H ^ 20 - (11466178560 :
    K[X]) * a2 * a4 * a5 ^ 3 * H ^ 17 + (2102132736 : K[X]) * a2 * a5 ^ 5
    * H ^ 14 - (2579890176 : K[X]) * a3 ^ 3 * H ^ 23 + (12899450880 :
    K[X]) * a3 ^ 2 * a4 * a5 * H ^ 20 - (5733089280 : K[X]) * a3 ^ 2 * a5
    ^ 3 * H ^ 17 + (4299816960 : K[X]) * a3 * a4 ^ 3 * H ^ 20 -
    (17199267840 : K[X]) * a3 * a4 ^ 2 * a5 ^ 2 * H ^ 17 + (10510663680 :
    K[X]) * a3 * a4 * a5 ^ 4 * H ^ 14 - (1634992128 : K[X]) * a3 * a5 ^ 6
    * H ^ 11 - (2866544640 : K[X]) * a4 ^ 4 * a5 * H ^ 17 + (7007109120 :
    K[X]) * a4 ^ 3 * a5 ^ 3 * H ^ 14 - (4904976384 : K[X]) * a4 ^ 2 * a5 ^
    5 * H ^ 11 + (1323565056 : K[X]) * a4 * a5 ^ 7 * H ^ 8 - (122552320 :
    K[X]) * a5 ^ 9 * H ^ 5)) - ((1128701952 : K[X]) * a0 * a4 * H ^ 18 -
    (470292480 : K[X]) * a0 * a5 ^ 2 * H ^ 15 + (1128701952 : K[X]) * a1 *
    a3 * H ^ 18 - (940584960 : K[X]) * a1 * a4 * a5 * H ^ 15 + (287400960
    : K[X]) * a1 * a5 ^ 3 * H ^ 12 + (564350976 : K[X]) * a2 ^ 2 * H ^ 18
    - (940584960 : K[X]) * a2 * a3 * a5 * H ^ 15 - (470292480 : K[X]) * a2
    * a4 ^ 2 * H ^ 15 + (862202880 : K[X]) * a2 * a4 * a5 ^ 2 * H ^ 12 -
    (203575680 : K[X]) * a2 * a5 ^ 4 * H ^ 9 - (470292480 : K[X]) * a3 ^ 2
    * a4 * H ^ 15 + (431101440 : K[X]) * a3 ^ 2 * a5 ^ 2 * H ^ 12 +
    (862202880 : K[X]) * a3 * a4 ^ 2 * a5 * H ^ 12 - (814302720 : K[X]) *
    a3 * a4 * a5 ^ 3 * H ^ 9 + (156074688 : K[X]) * a3 * a5 ^ 5 * H ^ 6 +
    (71850240 : K[X]) * a4 ^ 4 * H ^ 12 - (407151360 : K[X]) * a4 ^ 3 * a5
    ^ 2 * H ^ 9 + (390186720 : K[X]) * a4 ^ 2 * a5 ^ 4 * H ^ 6 -
    (125726832 : K[X]) * a4 * a5 ^ 6 * H ^ 3 + (13096545 : K[X]) * a5 ^ 8)
    * alignedThirdDefect610 H a3 a4 a5 b7 κ - ((67184640 : K[X]) * a0 * H
    ^ 15 - (11197440 : K[X]) * a1 * a5 * H ^ 12 - (11197440 : K[X]) * a2 *
    a4 * H ^ 12 + (6531840 : K[X]) * a2 * a5 ^ 2 * H ^ 9 - (5598720 :
    K[X]) * a3 ^ 2 * H ^ 12 + (13063680 : K[X]) * a3 * a4 * a5 * H ^ 9 -
    (4717440 : K[X]) * a3 * a5 ^ 3 * H ^ 6 + (2177280 : K[X]) * a4 ^ 3 * H
    ^ 9 - (7076160 : K[X]) * a4 ^ 2 * a5 ^ 2 * H ^ 6 + (3734640 : K[X]) *
    a4 * a5 ^ 4 * H ^ 3 - (518700 : K[X]) * a5 ^ 6) *
    alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ - ((2985984 : K[X])
    * a1 * H ^ 12 - (995328 : K[X]) * a2 * a5 * H ^ 9 - (995328 : K[X]) *
    a3 * a4 * H ^ 9 + (663552 : K[X]) * a3 * a5 ^ 2 * H ^ 6 + (663552 :
    K[X]) * a4 ^ 2 * a5 * H ^ 6 - (516096 : K[X]) * a4 * a5 ^ 3 * H ^ 3 +
    (86016 : K[X]) * a5 ^ 5) * alignedSixthDefect610 H a0 a1 a2 a3 a4 a5
    b4 b5 b6 b7 κ - ((93312 : K[X]) * a2 * H ^ 9 - (46656 : K[X]) * a3 *
    a5 * H ^ 6 - (23328 : K[X]) * a4 ^ 2 * H ^ 6 + (34992 : K[X]) * a4 *
    a5 ^ 2 * H ^ 3 - (7290 : K[X]) * a5 ^ 4) * alignedSeventhDefect610 H
    a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ - ((10368 : K[X]) * a3 * H ^ 6 -
    (6912 : K[X]) * a4 * a5 * H ^ 3 + (1920 : K[X]) * a5 ^ 3) *
    alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7 κ - ((48
    : K[X]) * a4 * H ^ 3 - (20 : K[X]) * a5 ^ 2) * alignedNinthDefect610 H
    a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ

set_option maxHeartbeats 12800000000 in
/-- Exact combination of the degree-`4` Jacobian expression with the
weighted derivative of `Λ`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`13` through
degree-`5` rows.  The row sees neither `q₉` nor `q₈`, so there is no
`N`-correction and no `C`-correction — the source-correction module is
EMPTY, as for the ninth and tenth faces.  The corrections run through
the TENTH defect `Ω` (with cofactor `80 p₅`) even though `Ω` does not
enter the defect itself. -/
theorem alignedEleventhDefect_weightedDerivative_identity_610 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    (156728328192 : K[X]) * H ^ 26 * (a4.derivative * b1 + a3.derivative
      * (b2 * (2 : K[X])) + a2.derivative * (b3 * (3 : K[X])) +
      a1.derivative * (b4 * (4 : K[X])) + a0.derivative * (b5 * (5 :
      K[X])) - ((a5 * (5 : K[X])) * b0.derivative + (a4 * (4 : K[X])) *
      b1.derivative + (a3 * (3 : K[X])) * b2.derivative + (a2 * (2 :
      K[X])) * b3.derivative + a1 * b4.derivative)) = ((2 : K[X]) * H *
      (alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
      κ).derivative - (55 : K[X]) * alignedEleventhDefect610 H a0 a1 a2 a3
      a4 a5 b1 b2 b3 b4 b5 b6 b7 κ * H.derivative) + ((5643509760 : K[X])
      * a0 * a4 * H ^ 18 + (470292480 : K[X]) * a0 * a5 ^ 2 * H ^ 15 +
      (5643509760 : K[X]) * a1 * a3 * H ^ 18 + (940584960 : K[X]) * a1 *
      a4 * a5 * H ^ 15 - (130636800 : K[X]) * a1 * a5 ^ 3 * H ^ 12 +
      (2821754880 : K[X]) * a2 ^ 2 * H ^ 18 + (940584960 : K[X]) * a2 * a3
      * a5 * H ^ 15 + (470292480 : K[X]) * a2 * a4 ^ 2 * H ^ 15 -
      (391910400 : K[X]) * a2 * a4 * a5 ^ 2 * H ^ 12 + (59875200 : K[X]) *
      a2 * a5 ^ 4 * H ^ 9 + (470292480 : K[X]) * a3 ^ 2 * a4 * H ^ 15 -
      (195955200 : K[X]) * a3 ^ 2 * a5 ^ 2 * H ^ 12 - (391910400 : K[X]) *
      a3 * a4 ^ 2 * a5 * H ^ 12 + (239500800 : K[X]) * a3 * a4 * a5 ^ 3 *
      H ^ 9 - (33929280 : K[X]) * a3 * a5 ^ 5 * H ^ 6 - (32659200 : K[X])
      * a4 ^ 4 * H ^ 12 + (119750400 : K[X]) * a4 ^ 3 * a5 ^ 2 * H ^ 9 -
      (84823200 : K[X]) * a4 ^ 2 * a5 ^ 4 * H ^ 6 + (21677040 : K[X]) * a4
      * a5 ^ 6 * H ^ 3 - (1870935 : K[X]) * a5 ^ 8) * ((2 : K[X]) * H *
      (alignedThirdDefect610 H a3 a4 a5 b7 κ).derivative - (15 : K[X]) *
      alignedThirdDefect610 H a3 a4 a5 b7 κ * H.derivative) + ((1612431360
      : K[X]) * a0 * a5 * H ^ 15 + (1612431360 : K[X]) * a1 * a4 * H ^ 15
      + (1612431360 : K[X]) * a2 * a3 * H ^ 15) * (H *
      (alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ).derivative - (10 :
      K[X]) * alignedFourthDefect610 H a2 a3 a4 a5 b6 b7 κ * H.derivative)
      + ((67184640 : K[X]) * a0 * H ^ 15 + (55987200 : K[X]) * a1 * a5 * H
      ^ 12 + (55987200 : K[X]) * a2 * a4 * H ^ 12 - (4665600 : K[X]) * a2
      * a5 ^ 2 * H ^ 9 + (27993600 : K[X]) * a3 ^ 2 * H ^ 12 - (9331200 :
      K[X]) * a3 * a4 * a5 * H ^ 9 + (1814400 : K[X]) * a3 * a5 ^ 3 * H ^
      6 - (1555200 : K[X]) * a4 ^ 3 * H ^ 9 + (2721600 : K[X]) * a4 ^ 2 *
      a5 ^ 2 * H ^ 6 - (982800 : K[X]) * a4 * a5 ^ 4 * H ^ 3 + (103740 :
      K[X]) * a5 ^ 6) * ((2 : K[X]) * H * (alignedFifthDefect610 H a1 a2
      a3 a4 a5 b5 b6 b7 κ).derivative - (25 : K[X]) *
      alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ * H.derivative) +
      ((7464960 : K[X]) * a1 * H ^ 12 + (4976640 : K[X]) * a2 * a5 * H ^ 9
      + (4976640 : K[X]) * a3 * a4 * H ^ 9 - (829440 : K[X]) * a3 * a5 ^ 2
      * H ^ 6 - (829440 : K[X]) * a4 ^ 2 * a5 * H ^ 6 + (368640 : K[X]) *
      a4 * a5 ^ 3 * H ^ 3 - (43008 : K[X]) * a5 ^ 5) * (H *
      (alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ).derivative
      - (15 : K[X]) * alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6
      b7 κ * H.derivative) + ((155520 : K[X]) * a2 * H ^ 9 + (77760 :
      K[X]) * a3 * a5 * H ^ 6 + (38880 : K[X]) * a4 ^ 2 * H ^ 6 - (19440 :
      K[X]) * a4 * a5 ^ 2 * H ^ 3 + (2430 : K[X]) * a5 ^ 4) * ((2 : K[X])
      * H * (alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7
      κ).derivative - (35 : K[X]) * alignedSeventhDefect610 H a0 a1 a2 a3
      a4 a5 b3 b4 b5 b6 b7 κ * H.derivative) + ((51840 : K[X]) * a3 * H ^
      6 + (17280 : K[X]) * a4 * a5 * H ^ 3 - (1920 : K[X]) * a5 ^ 3) * (H
      * (alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
      κ).derivative - (20 : K[X]) * alignedEighthDefect610 H a0 a1 a2 a3
      a4 a5 b2 b3 b4 b5 b6 b7 κ * H.derivative) + ((240 : K[X]) * a4 * H ^
      3 + (20 : K[X]) * a5 ^ 2) * ((2 : K[X]) * H * (alignedNinthDefect610
      H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ).derivative - (45 : K[X])
      * alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ *
      H.derivative) + ((80 : K[X]) * a5) * (H * (alignedTenthDefect610 H
      a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6 b7 κ).derivative - (25 :
      K[X]) * alignedTenthDefect610 H a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5
      b6 b7 κ * H.derivative) := by
  simp only [alignedEleventhDefect610, alignedTenthDefect610,
    alignedNinthDefect610, alignedEighthDefect610, alignedSeventhDefect610,
    alignedSixthDefect610, alignedFifthDefect610, alignedFourthDefect610,
    alignedThirdDefect610, Polynomial.derivative_sub,
    Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_ofNat,
    Polynomial.derivative_C, nsmul_eq_mul, zero_mul, mul_zero, zero_add,
    add_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

set_option maxHeartbeats 3200000000 in
/-- On the aligned face, with the consumed degree-`13` through
degree-`5` rows, the degree-`4` row is the weighted derivative
`2 H Λ' - 55 Λ H' = 0`. -/
theorem alignedEleventhDefectRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    (2 : K[X]) * H * (alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ).derivative -
      (55 : K[X]) * alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedEleventhCoefficientJacobianRow_610 hp hq hjac
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5] at hrow
  have hDrow :=
    alignedThirdDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hErow :=
    alignedFourthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hFrow :=
    alignedFifthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hGrow :=
    alignedSixthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hIrow :=
    alignedSeventhDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hJrow :=
    alignedEighthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hLrow :=
    alignedNinthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hOrow :=
    alignedTenthDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hid := alignedEleventhDefect_weightedDerivative_identity_610
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
    (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  rw [hrow, hDrow, hErow, hFrow, hGrow, hIrow, hJrow, hLrow, hOrow] at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

set_option maxHeartbeats 8000000 in
/-- Squared weight-`55/2` polynomial first integral of the aligned
`(6,10)` eleventh defect: `Λ² = κ₁₀ H⁵⁵`.  The odd exponent forces a
square/nonsquare chamber split exactly as for `D`, `F`, `I`, and
`L`. -/
theorem alignedEleventhDefectPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5) :
    ∃ κ₁₀ : K,
      alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
      Polynomial.C κ₁₀ * H ^ 55 := by
  let L : K[X] :=
    alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
    3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * L.derivative -
        (55 : K[X]) * L * H.derivative = 0 := by
    simpa only [L] using
      alignedEleventhDefectRow_eq_zero_610 hp hq hjac hp6 hq10 haligned hM
  have hC55 : Polynomial.C (55 : K) = (55 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (L ^ 2) (H ^ 55) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      L ^ 2 * (Polynomial.C (55 : K) * H ^ (55 - 1) * H.derivative) -
          Polynomial.C (2 : K) * L ^ (2 - 1) * L.derivative * H ^ 55 =
          L * H ^ 54 *
            (Polynomial.C (55 : K) * L * H.derivative -
              Polynomial.C (2 : K) * H * L.derivative) := by
        ring
      _ = 0 := by
        rw [hC55, hC2]
        have hfac :
            (55 : K[X]) * L * H.derivative -
              (2 : K[X]) * H * L.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 55 hH) hW

/-! ## Square chamber -/

/-- In the square chamber the squared weight-`55/2` integral has a
polynomial square root: `Λ = μ₄ h₀⁵⁵` with `μ₄² = κ₁₀`.  The constant
`μ₄` is preserved, not cleared. -/
theorem alignedSquareEleventh_sqrt_610 {K : Type*} [Field K] [CharZero K]
    {H h0 a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₁₀ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hL2 :
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ ^ 2 =
        Polynomial.C κ₁₀ * H ^ 55) :
    ∃ μ₄ : K, μ₄ ^ 2 = κ₁₀ ∧
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ =
        Polynomial.C μ₄ * h0 ^ 55 := by
  set L : K[X] :=
    alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ
  have hdvd : (h0 ^ 55) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₁₀, ?_⟩
    rw [hL2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₁₀ := by
    have h110 := hL2
    rw [hG, hHsq] at h110
    apply mul_left_cancel₀ (pow_ne_zero 110 hh0)
    linear_combination h110
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₁₀
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨μ₄, hμ⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨μ₄, ?_, ?_⟩
  · have hCμ : Polynomial.C (μ₄ ^ 2) = Polynomial.C κ₁₀ := by
      rw [Polynomial.C_pow, hμ, hG2]
    exact Polynomial.C_injective hCμ
  · rw [hG, ← hμ]
    ring

/-- Scalar resolution of the eleventh-row peeled head at the root
against `e₂(a) = 0`, the `u₂` root product, and the carried tenth-face
tie `135 s = 92160 x² (81 p - y)²`: the head equation forces the exact
vanishing `t = 0` of the new μ-loaded witness. -/
theorem alignedEleventhSquareTieResolve_610 {K : Type*} [Field K]
    [CharZero K] {x u v y p s t m : K}
    (h1 : x * (v - 3 * u * x) = 0)
    (h2 : v = 0)
    (htie : 135 * s = 92160 * x ^ 2 * (81 * p - y) ^ 2)
    (hhead : -61931520 * u ^ 4 * x ^ 3 + 1433272320 * u ^ 2 * p * x ^ 3 -
      22118400 * u ^ 2 * y * x ^ 3 + 655360 * u * v ^ 3 - 21168 * u * m *
      x ^ 6 - 9674588160 * p ^ 2 * x ^ 3 + 238878720 * p * y * x ^ 3 +
      2160 * s * x + 1215 * t - 1474560 * y ^ 2 * x ^ 3 = 0) :
    t = 0 := by
  have hux2 : u * x ^ 2 = 0 := by
    linear_combination (-(3 : K)⁻¹) * h1 + ((3 : K)⁻¹ * x) * h2
  have hux : u * x = 0 := by
    rcases mul_eq_zero.mp hux2 with hu | hx2
    · rw [hu, zero_mul]
    · rw [(pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hx2, mul_zero]
  linear_combination ((1215 : K)⁻¹) * hhead -
    ((1215 : K)⁻¹ * 16 * x) * htie +
    ((1215 : K)⁻¹ * (21168 * m * x ^ 5 - 1433272320 * p * u * x ^ 2 +
      61931520 * u ^ 3 * x ^ 2 + 22118400 * u * x ^ 2 * y)) * hux -
    ((1215 : K)⁻¹ * 655360 * u * v ^ 2) * h2

set_option maxHeartbeats 1600000000 in
/-- Peeled square-chamber form of the consumed degree-`4` row
(`h₀⁴⁴ · h₀² · h₀ · h₀` cancelled along the seventh-face
divisibilities, the eighth-face product divisor `u₂`, the tenth-face
μ-loaded divisor `s₂`, and the NEW divisor `s₄`): the FIRST aligned
square-chamber row with no `q`-coefficient at all.  On the face it
equals `μ₄ h₀⁷`. -/
def alignedEleventhSquarePeeledRow610 {K : Type*} [CommRing K]
    (h0 w1 e1 e2 u2 s2 s4 a0 a1 a2 : K[X])
    (κ μ ν κ₅ ν₂ κ₇ μ₃ : K) : K[X] :=
  (-((61931520 : K[X]) * e1 ^ 4 * w1 ^ 3) - (22118400 : K[X]) * e1 ^ 2 *
    u2 * w1 ^ 3 + (1433272320 : K[X]) * e1 ^ 2 * w1 ^ 3 * a2 + (655360 :
    K[X]) * e1 * e2 ^ 3 - (1474560 : K[X]) * u2 ^ 2 * w1 ^ 3 + (238878720
    : K[X]) * u2 * w1 ^ 3 * a2 + (2160 : K[X]) * s2 * w1 + (1215 : K[X]) *
    s4 - (9674588160 : K[X]) * w1 ^ 3 * a2 ^ 2 - Polynomial.C μ * ((21168
    : K[X]) * e1 * w1 ^ 6)) + h0 * ((61931520 : K[X]) * e1 ^ 5 * w1 -
    (10321920 : K[X]) * e1 ^ 4 * e2 + (103219200 : K[X]) * e1 ^ 3 * u2 *
    w1 - (3344302080 : K[X]) * e1 ^ 3 * w1 * a2 - (20643840 : K[X]) * e1 ^
    2 * e2 * u2 + (477757440 : K[X]) * e1 ^ 2 * e2 * a2 + (19660800 :
    K[X]) * e1 * u2 ^ 2 * w1 - (1911029760 : K[X]) * e1 * u2 * w1 * a2 +
    (38698352640 : K[X]) * e1 * w1 * a2 ^ 2 - (1638400 : K[X]) * e2 * u2 ^
    2 + (159252480 : K[X]) * e2 * u2 * a2 - (3224862720 : K[X]) * e2 * a2
    ^ 2 + Polynomial.C ν * ((540 : K[X]) * w1 ^ 6) - Polynomial.C μ *
    ((211680 : K[X]) * e1 ^ 2 * w1 ^ 4) - Polynomial.C μ * ((28224 : K[X])
    * u2 * w1 ^ 4) + Polynomial.C μ * ((3265920 : K[X]) * w1 ^ 4 * a2) +
    Polynomial.C κ * ((17694720 : K[X]) * e1 ^ 3 * w1 ^ 3) + Polynomial.C
    κ * ((3538944 : K[X]) * e1 * u2 * w1 ^ 3) - Polynomial.C κ *
    ((286654464 : K[X]) * e1 * w1 ^ 3 * a2) - Polynomial.C κ * ((131072 :
    K[X]) * e2 ^ 3)) + h0 ^ 2 * (-((2149908480 : K[X]) * e1 ^ 2 * w1 ^ 2 *
    a1) - (119439360 : K[X]) * e2 ^ 2 * a1 - (716636160 : K[X]) * u2 * w1
    ^ 2 * a1 + (58047528960 : K[X]) * w1 ^ 2 * a1 * a2 + Polynomial.C ν *
    ((10800 : K[X]) * e1 * w1 ^ 4) + Polynomial.C μ * ((887040 : K[X]) *
    e1 ^ 3 * w1 ^ 2) + Polynomial.C μ * ((215040 : K[X]) * e1 * e2 ^ 2) +
    Polynomial.C μ * ((1128960 : K[X]) * e1 * u2 * w1 ^ 2) - Polynomial.C
    μ * ((78382080 : K[X]) * e1 * w1 ^ 2 * a2) - Polynomial.C κ *
    ((35389440 : K[X]) * e1 ^ 4 * w1) + Polynomial.C κ * ((5898240 : K[X])
    * e1 ^ 3 * e2) - Polynomial.C κ * ((35389440 : K[X]) * e1 ^ 2 * u2 *
    w1) + Polynomial.C κ * ((1433272320 : K[X]) * e1 ^ 2 * w1 * a2) +
    Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 * u2) - Polynomial.C κ *
    ((191102976 : K[X]) * e1 * e2 * a2) - Polynomial.C κ * ((2359296 :
    K[X]) * u2 ^ 2 * w1) + Polynomial.C κ * ((286654464 : K[X]) * u2 * w1
    * a2) - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) + h0 ^ 3
    * ((1433272320 : K[X]) * e1 ^ 3 * a1 + (2866544640 : K[X]) * e1 * u2 *
    a1 - (58047528960 : K[X]) * e1 * a1 * a2 - Polynomial.C ν₂ * ((54 :
    K[X]) * w1 ^ 4) + Polynomial.C ν * ((60480 : K[X]) * e1 ^ 2 * w1 ^ 2)
    + Polynomial.C ν * ((7680 : K[X]) * e2 ^ 2) + Polynomial.C ν * ((28800
    : K[X]) * u2 * w1 ^ 2) - Polynomial.C ν * ((2799360 : K[X]) * w1 ^ 2 *
    a2) - Polynomial.C μ * ((887040 : K[X]) * e1 ^ 4) - Polynomial.C μ *
    ((3548160 : K[X]) * e1 ^ 2 * u2) + Polynomial.C μ * ((52254720 : K[X])
    * e1 ^ 2 * a2) - Polynomial.C μ * ((376320 : K[X]) * u2 ^ 2) +
    Polynomial.C μ * ((34836480 : K[X]) * u2 * a2) - Polynomial.C μ *
    ((15676416 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ * ((564350976 :
    K[X]) * a2 ^ 2) + Polynomial.C κ * ((859963392 : K[X]) * e1 * w1 ^ 2 *
    a1)) + h0 ^ 4 * ((12899450880 : K[X]) * e1 ^ 2 * w1 * a0 - (2149908480
    : K[X]) * e1 * e2 * a0 + (2149908480 : K[X]) * u2 * w1 * a0 -
    (174142586880 : K[X]) * w1 * a0 * a2 - (87071293440 : K[X]) * w1 * a1
    ^ 2 - Polynomial.C ν₂ * ((1296 : K[X]) * e1 * w1 ^ 2) - Polynomial.C
    κ₅ * ((73728 : K[X]) * e1 ^ 2 * w1) + Polynomial.C κ₅ * ((12288 :
    K[X]) * e1 * e2) - Polynomial.C κ₅ * ((12288 : K[X]) * u2 * w1) +
    Polynomial.C κ₅ * ((995328 : K[X]) * w1 * a2) - Polynomial.C ν *
    ((80640 : K[X]) * e1 ^ 3) - Polynomial.C ν * ((161280 : K[X]) * e1 *
    u2) + Polynomial.C ν * ((3732480 : K[X]) * e1 * a2) + Polynomial.C μ *
    ((313528320 : K[X]) * e1 * w1 * a1) - Polynomial.C μ * ((41803776 :
    K[X]) * e2 * a1) - Polynomial.C κ * ((859963392 : K[X]) * e1 ^ 2 * a1)
    - Polynomial.C κ * ((573308928 : K[X]) * u2 * a1) + Polynomial.C κ *
    ((23219011584 : K[X]) * a1 * a2)) + h0 ^ 5 * (Polynomial.C μ₃ * ((4 :
    K[X]) * w1 ^ 2) + Polynomial.C κ₇ * ((2304 : K[X]) * e1 * w1) -
    Polynomial.C κ₇ * ((384 : K[X]) * e2) + Polynomial.C ν₂ * ((2592 :
    K[X]) * e1 ^ 2) + Polynomial.C ν₂ * ((1728 : K[X]) * u2) -
    Polynomial.C ν₂ * ((93312 : K[X]) * a2) + Polynomial.C ν * ((11197440
    : K[X]) * w1 * a1) + Polynomial.C μ * ((94058496 : K[X]) * w1 ^ 2 *
    a0) - Polynomial.C κ * ((5159780352 : K[X]) * e1 * w1 * a0) +
    Polynomial.C κ * ((859963392 : K[X]) * e2 * a0)) + h0 ^ 6 *
    ((522427760640 : K[X]) * a0 * a1 - Polynomial.C μ₃ * ((16 : K[X]) *
    e1) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) - Polynomial.C μ *
    ((376233984 : K[X]) * e1 * a0)) + h0 ^ 7 * (-(Polynomial.C ν *
    ((67184640 : K[X]) * a0)))

set_option maxHeartbeats 6400000000 in
/-- Descent of the consumed degree-`4` row in the square chamber: the
`h₀⁴⁴`-peeled core absorbs the undecic head through the seventh-face
divisibilities and the eighth-face product divisor `u₂`, and the
carried tenth-face divisor `s₂` collapses the head to the pure
monomial `1215 μ w₁⁸`; at the root of `h₀` the head transfers to the
NEW divisibility `μ w₁⁸ = h₀ s₄`, and substituting `s₄` peels one more
`h₀` into the peeled row `= μ₄ h₀⁷`.  At the root the peeled head, the
carried facts `e₂(a) = 0` and the `u₂` root product, and the
tenth-face tie force `s₄(a) = 0`, deepening the new divisor to
`μ w₁⁸ = h₀² s₅`. -/
theorem alignedSquareEleventh_descent_610 {K : Type*} [Field K]
    [CharZero K]
    {H h0 w1 f2 e1 e2 e3 u2 s2 a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 b6
      b7 : K[X]}
    {κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ κ₉ μ₄ : K}
    (hh0 : h0 ≠ 0) (hdeg1 : h0.natDegree = 1) (hHsq : H = h0 ^ 2)
    (hp5 : a5 = h0 ^ 4 * w1) (hp4 : a4 = h0 ^ 2 * f2)
    (hD : alignedThirdDefect610 H a3 a4 a5 b7 κ =
      Polynomial.C μ * h0 ^ 15)
    (hF : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ =
      Polynomial.C ν * h0 ^ 25)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15)
    (hI : alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ =
      Polynomial.C ν₂ * h0 ^ 35)
    (hJ : alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₇ * H ^ 20)
    (hL : alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6
        b7 κ = Polynomial.C μ₃ * h0 ^ 45)
    (hLam : alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5
        b6 b7 κ = Polynomial.C μ₄ * h0 ^ 55)
    (he1 : (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1)
    (he2 : (27 : K[X]) * a3 - w1 ^ 3 = h0 * e2)
    (hu2 : w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2)
    (hs2 : (2048 : K[X]) * e1 ^ 3 * w1 ^ 4 - Polynomial.C μ * w1 ^ 7 =
      h0 * s2)
    (he3 : e2 = h0 * e3)
    (hR10 : alignedTenthSquarePeeledRow610 h0 w1 e1 e2 u2 s2 a0 a1 a2
        b0 κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ = Polynomial.C κ₉ * h0 ^ 6) :
    ∃ s4 s5 : K[X],
      Polynomial.C μ * w1 ^ 8 = h0 * s4 ∧
      alignedEleventhSquarePeeledRow610 h0 w1 e1 e2 u2 s2 s4 a0 a1 a2
          κ μ ν κ₅ ν₂ κ₇ μ₃ = Polynomial.C μ₄ * h0 ^ 7 ∧
      s4 = h0 * s5 ∧
      Polynomial.C μ * w1 ^ 8 = h0 ^ 2 * s5 := by
  have hL' := hLam
  simp only [alignedEleventhDefect610] at hL'
  rw [hD, hF, hG, hI, hJ, hL, hHsq, hp5, hp4] at hL'
  have hcore :
      ((15049359360 : K[X]) * f2 ^ 5 * w1 - (22574039040 : K[X]) * f2 ^ 4
      * a3 - (54344908800 : K[X]) * f2 ^ 4 * w1 ^ 3 + (150493593600 :
      K[X]) * f2 ^ 3 * a3 * w1 ^ 2 + (57967902720 : K[X]) * f2 ^ 3 * w1 ^
      5 - (135444234240 : K[X]) * f2 ^ 2 * a3 ^ 2 * w1 - (163034726400 :
      K[X]) * f2 ^ 2 * a3 * w1 ^ 4 - (26223575040 : K[X]) * f2 ^ 2 * w1 ^
      7 + (38698352640 : K[X]) * f2 * a3 ^ 3 + (150493593600 : K[X]) * f2
      * a3 ^ 2 * w1 ^ 3 + (57967902720 : K[X]) * f2 * a3 * w1 ^ 6 +
      (5341839360 : K[X]) * f2 * w1 ^ 9 - (45148078080 : K[X]) * a3 ^ 3 *
      w1 ^ 2 - (32606945280 : K[X]) * a3 ^ 2 * w1 ^ 5 - (6555893760 :
      K[X]) * a3 * w1 ^ 8 - (404684800 : K[X]) * w1 ^ 11) + h0 ^ 2 *
      (-((90296156160 : K[X]) * f2 ^ 3 * w1 * a2) + (116095057920 : K[X])
      * f2 ^ 2 * a3 * a2 + (150493593600 : K[X]) * f2 ^ 2 * w1 ^ 3 * a2 -
      (270888468480 : K[X]) * f2 * a3 * w1 ^ 2 * a2 - (65213890560 : K[X])
      * f2 * w1 ^ 5 * a2 + (116095057920 : K[X]) * a3 ^ 2 * w1 * a2 +
      (75246796800 : K[X]) * a3 * w1 ^ 4 * a2 + (8281128960 : K[X]) * w1 ^
      7 * a2 - Polynomial.C κ * ((2866544640 : K[X]) * f2 ^ 4 * w1) +
      Polynomial.C κ * ((4299816960 : K[X]) * f2 ^ 3 * a3) + Polynomial.C
      κ * ((7007109120 : K[X]) * f2 ^ 3 * w1 ^ 3) - Polynomial.C κ *
      ((17199267840 : K[X]) * f2 ^ 2 * a3 * w1 ^ 2) - Polynomial.C κ *
      ((4904976384 : K[X]) * f2 ^ 2 * w1 ^ 5) + Polynomial.C κ *
      ((12899450880 : K[X]) * f2 * a3 ^ 2 * w1) + Polynomial.C κ *
      ((10510663680 : K[X]) * f2 * a3 * w1 ^ 4) + Polynomial.C κ *
      ((1323565056 : K[X]) * f2 * w1 ^ 7) - Polynomial.C κ * ((2579890176
      : K[X]) * a3 ^ 3) - Polynomial.C κ * ((5733089280 : K[X]) * a3 ^ 2 *
      w1 ^ 3) - Polynomial.C κ * ((1634992128 : K[X]) * a3 * w1 ^ 6) -
      Polynomial.C κ * ((122552320 : K[X]) * w1 ^ 9)) + h0 ^ 3 *
      (-(Polynomial.C μ * ((71850240 : K[X]) * f2 ^ 4)) + Polynomial.C μ *
      ((407151360 : K[X]) * f2 ^ 3 * w1 ^ 2) - Polynomial.C μ *
      ((862202880 : K[X]) * f2 ^ 2 * a3 * w1) - Polynomial.C μ *
      ((390186720 : K[X]) * f2 ^ 2 * w1 ^ 4) + Polynomial.C μ *
      ((470292480 : K[X]) * f2 * a3 ^ 2) + Polynomial.C μ * ((814302720 :
      K[X]) * f2 * a3 * w1 ^ 3) + Polynomial.C μ * ((125726832 : K[X]) *
      f2 * w1 ^ 6) - Polynomial.C μ * ((431101440 : K[X]) * a3 ^ 2 * w1 ^
      2) - Polynomial.C μ * ((156074688 : K[X]) * a3 * w1 ^ 5) -
      Polynomial.C μ * ((13096545 : K[X]) * w1 ^ 8)) + h0 ^ 4 *
      ((38698352640 : K[X]) * f2 ^ 3 * a1 - (135444234240 : K[X]) * f2 ^ 2
      * w1 ^ 2 * a1 + (232190115840 : K[X]) * f2 * a3 * w1 * a1 +
      (75246796800 : K[X]) * f2 * w1 ^ 4 * a1 + (116095057920 : K[X]) * f2
      * w1 * a2 ^ 2 - (87071293440 : K[X]) * a3 ^ 2 * a1 - (90296156160 :
      K[X]) * a3 * w1 ^ 3 * a1 - (87071293440 : K[X]) * a3 * a2 ^ 2 -
      (10868981760 : K[X]) * w1 ^ 6 * a1 - (45148078080 : K[X]) * w1 ^ 3 *
      a2 ^ 2 + Polynomial.C κ * ((12899450880 : K[X]) * f2 ^ 2 * w1 * a2)
      - Polynomial.C κ * ((15479341056 : K[X]) * f2 * a3 * a2) -
      Polynomial.C κ * ((11466178560 : K[X]) * f2 * w1 ^ 3 * a2) +
      Polynomial.C κ * ((12899450880 : K[X]) * a3 * w1 ^ 2 * a2) +
      Polynomial.C κ * ((2102132736 : K[X]) * w1 ^ 5 * a2)) + h0 ^ 5 *
      (-(Polynomial.C ν * ((2177280 : K[X]) * f2 ^ 3)) + Polynomial.C ν *
      ((7076160 : K[X]) * f2 ^ 2 * w1 ^ 2) - Polynomial.C ν * ((13063680 :
      K[X]) * f2 * a3 * w1) - Polynomial.C ν * ((3734640 : K[X]) * f2 * w1
      ^ 4) + Polynomial.C ν * ((5598720 : K[X]) * a3 ^ 2) + Polynomial.C ν
      * ((4717440 : K[X]) * a3 * w1 ^ 3) + Polynomial.C ν * ((518700 :
      K[X]) * w1 ^ 6) + Polynomial.C μ * ((470292480 : K[X]) * f2 ^ 2 *
      a2) - Polynomial.C μ * ((862202880 : K[X]) * f2 * w1 ^ 2 * a2) +
      Polynomial.C μ * ((940584960 : K[X]) * a3 * w1 * a2) + Polynomial.C
      μ * ((203575680 : K[X]) * w1 ^ 4 * a2)) + h0 ^ 6 * ((116095057920 :
      K[X]) * f2 ^ 2 * w1 * a0 - (174142586880 : K[X]) * f2 * a3 * a0 -
      (90296156160 : K[X]) * f2 * w1 ^ 3 * a0 - (174142586880 : K[X]) * f2
      * a1 * a2 + (116095057920 : K[X]) * a3 * w1 ^ 2 * a0 + (15049359360
      : K[X]) * w1 ^ 5 * a0 + (116095057920 : K[X]) * w1 ^ 2 * a1 * a2 -
      Polynomial.C κ₅ * ((663552 : K[X]) * f2 ^ 2 * w1) + Polynomial.C κ₅
      * ((995328 : K[X]) * f2 * a3) + Polynomial.C κ₅ * ((516096 : K[X]) *
      f2 * w1 ^ 3) - Polynomial.C κ₅ * ((663552 : K[X]) * a3 * w1 ^ 2) -
      Polynomial.C κ₅ * ((86016 : K[X]) * w1 ^ 5) - Polynomial.C κ *
      ((7739670528 : K[X]) * f2 ^ 2 * a1) + Polynomial.C κ * ((12899450880
      : K[X]) * f2 * w1 ^ 2 * a1) - Polynomial.C κ * ((15479341056 : K[X])
      * a3 * w1 * a1) - Polynomial.C κ * ((2866544640 : K[X]) * w1 ^ 4 *
      a1) - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) + h0 ^ 7
      * (Polynomial.C ν₂ * ((23328 : K[X]) * f2 ^ 2) - Polynomial.C ν₂ *
      ((34992 : K[X]) * f2 * w1 ^ 2) + Polynomial.C ν₂ * ((46656 : K[X]) *
      a3 * w1) + Polynomial.C ν₂ * ((7290 : K[X]) * w1 ^ 4) + Polynomial.C
      ν * ((11197440 : K[X]) * f2 * a2) - Polynomial.C ν * ((6531840 :
      K[X]) * w1 ^ 2 * a2) + Polynomial.C μ * ((940584960 : K[X]) * f2 *
      w1 * a1) - Polynomial.C μ * ((1128701952 : K[X]) * a3 * a1) -
      Polynomial.C μ * ((287400960 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ
      * ((564350976 : K[X]) * a2 ^ 2)) + h0 ^ 8 * (-((174142586880 : K[X])
      * w1 * a0 * a2) - (87071293440 : K[X]) * w1 * a1 ^ 2 + Polynomial.C
      κ₇ * ((6912 : K[X]) * f2 * w1) - Polynomial.C κ₇ * ((10368 : K[X]) *
      a3) - Polynomial.C κ₇ * ((1920 : K[X]) * w1 ^ 3) + Polynomial.C κ₅ *
      ((995328 : K[X]) * w1 * a2) - Polynomial.C κ * ((15479341056 : K[X])
      * f2 * w1 * a0) + Polynomial.C κ * ((23219011584 : K[X]) * a3 * a0)
      + Polynomial.C κ * ((4299816960 : K[X]) * w1 ^ 3 * a0) +
      Polynomial.C κ * ((23219011584 : K[X]) * a1 * a2)) + h0 ^ 9 *
      (-(Polynomial.C μ₃ * ((48 : K[X]) * f2)) + Polynomial.C μ₃ * ((20 :
      K[X]) * w1 ^ 2) - Polynomial.C ν₂ * ((93312 : K[X]) * a2) +
      Polynomial.C ν * ((11197440 : K[X]) * w1 * a1) - Polynomial.C μ *
      ((1128701952 : K[X]) * f2 * a0) + Polynomial.C μ * ((470292480 :
      K[X]) * w1 ^ 2 * a0)) + h0 ^ 10 * ((522427760640 : K[X]) * a0 * a1 -
      Polynomial.C κ₅ * ((2985984 : K[X]) * a1)) + h0 ^ 11 *
      (-(Polynomial.C ν * ((67184640 : K[X]) * a0))) = Polynomial.C μ₄ *
      h0 ^ 11 := by
    apply mul_left_cancel₀ (pow_ne_zero 44 hh0)
    linear_combination hL'
  have hcs2 :
      (-((13271040 : K[X]) * e1 ^ 2 * w1 ^ 7) + (8847360 : K[X]) * e1 * e2
      * w1 ^ 6 - (1474560 : K[X]) * e2 ^ 2 * w1 ^ 5) + h0 * ((247726080 :
      K[X]) * e1 ^ 3 * w1 ^ 5 - (154828800 : K[X]) * e1 ^ 2 * e2 * w1 ^ 4
      + (29491200 : K[X]) * e1 * e2 ^ 2 * w1 ^ 3 - (716636160 : K[X]) * e1
      * w1 ^ 5 * a2 - (1638400 : K[X]) * e2 ^ 3 * w1 ^ 2 + (238878720 :
      K[X]) * e2 * w1 ^ 4 * a2 - Polynomial.C μ * ((945 : K[X]) * w1 ^ 8))
      + h0 ^ 2 * (-((371589120 : K[X]) * e1 ^ 4 * w1 ^ 3) + (165150720 :
      K[X]) * e1 ^ 3 * e2 * w1 ^ 2 - (20643840 : K[X]) * e1 ^ 2 * e2 ^ 2 *
      w1 + (7166361600 : K[X]) * e1 ^ 2 * w1 ^ 3 * a2 + (655360 : K[X]) *
      e1 * e2 ^ 3 - (2388787200 : K[X]) * e1 * e2 * w1 ^ 2 * a2 +
      (159252480 : K[X]) * e2 ^ 2 * w1 * a2 - (9674588160 : K[X]) * w1 ^ 3
      * a2 ^ 2 + Polynomial.C μ * ((63504 : K[X]) * e1 * w1 ^ 6) -
      Polynomial.C μ * ((28224 : K[X]) * e2 * w1 ^ 5) - Polynomial.C κ *
      ((31850496 : K[X]) * e1 ^ 2 * w1 ^ 5) + Polynomial.C κ * ((17694720
      : K[X]) * e1 * e2 * w1 ^ 4) - Polynomial.C κ * ((2359296 : K[X]) *
      e2 ^ 2 * w1 ^ 3)) + h0 ^ 3 * ((61931520 : K[X]) * e1 ^ 5 * w1 -
      (10321920 : K[X]) * e1 ^ 4 * e2 - (3344302080 : K[X]) * e1 ^ 3 * w1
      * a2 + (477757440 : K[X]) * e1 ^ 2 * e2 * a2 + (2149908480 : K[X]) *
      e1 * w1 ^ 4 * a1 + (38698352640 : K[X]) * e1 * w1 * a2 ^ 2 -
      (716636160 : K[X]) * e2 * w1 ^ 3 * a1 - (3224862720 : K[X]) * e2 *
      a2 ^ 2 + Polynomial.C ν * ((540 : K[X]) * w1 ^ 6) - Polynomial.C μ *
      ((6985440 : K[X]) * e1 ^ 2 * w1 ^ 4) + Polynomial.C μ * ((3386880 :
      K[X]) * e1 * e2 * w1 ^ 3) - Polynomial.C μ * ((376320 : K[X]) * e2 ^
      2 * w1 ^ 2) + Polynomial.C μ * ((3265920 : K[X]) * w1 ^ 4 * a2) +
      Polynomial.C κ * ((123863040 : K[X]) * e1 ^ 3 * w1 ^ 3) -
      Polynomial.C κ * ((53084160 : K[X]) * e1 ^ 2 * e2 * w1 ^ 2) +
      Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 ^ 2 * w1) -
      Polynomial.C κ * ((1146617856 : K[X]) * e1 * w1 ^ 3 * a2) -
      Polynomial.C κ * ((131072 : K[X]) * e2 ^ 3) + Polynomial.C κ *
      ((286654464 : K[X]) * e2 * w1 ^ 2 * a2)) + h0 ^ 4 * (-((10749542400
      : K[X]) * e1 ^ 2 * w1 ^ 2 * a1) + (2866544640 : K[X]) * e1 * e2 * w1
      * a1 - (119439360 : K[X]) * e2 ^ 2 * a1 + (58047528960 : K[X]) * w1
      ^ 2 * a1 * a2 - Polynomial.C ν * ((75600 : K[X]) * e1 * w1 ^ 4) +
      Polynomial.C ν * ((28800 : K[X]) * e2 * w1 ^ 3) + Polynomial.C μ *
      ((11531520 : K[X]) * e1 ^ 3 * w1 ^ 2) - Polynomial.C μ * ((3548160 :
      K[X]) * e1 ^ 2 * e2 * w1) + Polynomial.C μ * ((215040 : K[X]) * e1 *
      e2 ^ 2) - Polynomial.C μ * ((182891520 : K[X]) * e1 * w1 ^ 2 * a2) +
      Polynomial.C μ * ((34836480 : K[X]) * e2 * w1 * a2) - Polynomial.C κ
      * ((35389440 : K[X]) * e1 ^ 4 * w1) + Polynomial.C κ * ((5898240 :
      K[X]) * e1 ^ 3 * e2) + Polynomial.C κ * ((1433272320 : K[X]) * e1 ^
      2 * w1 * a2) - Polynomial.C κ * ((191102976 : K[X]) * e1 * e2 * a2)
      - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) + h0 ^ 5 *
      ((1433272320 : K[X]) * e1 ^ 3 * a1 - (6449725440 : K[X]) * e1 * w1 ^
      3 * a0 - (58047528960 : K[X]) * e1 * a1 * a2 + (2149908480 : K[X]) *
      e2 * w1 ^ 2 * a0 - Polynomial.C ν₂ * ((54 : K[X]) * w1 ^ 4) +
      Polynomial.C κ₅ * ((36864 : K[X]) * e1 * w1 ^ 3) - Polynomial.C κ₅ *
      ((12288 : K[X]) * e2 * w1 ^ 2) + Polynomial.C ν * ((544320 : K[X]) *
      e1 ^ 2 * w1 ^ 2) - Polynomial.C ν * ((161280 : K[X]) * e1 * e2 * w1)
      + Polynomial.C ν * ((7680 : K[X]) * e2 ^ 2) - Polynomial.C ν *
      ((2799360 : K[X]) * w1 ^ 2 * a2) - Polynomial.C μ * ((887040 : K[X])
      * e1 ^ 4) + Polynomial.C μ * ((52254720 : K[X]) * e1 ^ 2 * a2) -
      Polynomial.C μ * ((15676416 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ
      * ((564350976 : K[X]) * a2 ^ 2) + Polynomial.C κ * ((2579890176 :
      K[X]) * e1 * w1 ^ 2 * a1) - Polynomial.C κ * ((573308928 : K[X]) *
      e2 * w1 * a1)) + h0 ^ 6 * ((12899450880 : K[X]) * e1 ^ 2 * w1 * a0 -
      (2149908480 : K[X]) * e1 * e2 * a0 - (174142586880 : K[X]) * w1 * a0
      * a2 - (87071293440 : K[X]) * w1 * a1 ^ 2 - Polynomial.C ν₂ * ((6480
      : K[X]) * e1 * w1 ^ 2) + Polynomial.C ν₂ * ((1728 : K[X]) * e2 * w1)
      - Polynomial.C κ₅ * ((73728 : K[X]) * e1 ^ 2 * w1) + Polynomial.C κ₅
      * ((12288 : K[X]) * e1 * e2) + Polynomial.C κ₅ * ((995328 : K[X]) *
      w1 * a2) - Polynomial.C ν * ((80640 : K[X]) * e1 ^ 3) + Polynomial.C
      ν * ((3732480 : K[X]) * e1 * a2) + Polynomial.C μ * ((313528320 :
      K[X]) * e1 * w1 * a1) - Polynomial.C μ * ((41803776 : K[X]) * e2 *
      a1) - Polynomial.C κ * ((859963392 : K[X]) * e1 ^ 2 * a1) +
      Polynomial.C κ * ((23219011584 : K[X]) * a1 * a2)) + h0 ^ 7 *
      (Polynomial.C μ₃ * ((4 : K[X]) * w1 ^ 2) + Polynomial.C κ₇ * ((2304
      : K[X]) * e1 * w1) - Polynomial.C κ₇ * ((384 : K[X]) * e2) +
      Polynomial.C ν₂ * ((2592 : K[X]) * e1 ^ 2) - Polynomial.C ν₂ *
      ((93312 : K[X]) * a2) + Polynomial.C ν * ((11197440 : K[X]) * w1 *
      a1) + Polynomial.C μ * ((94058496 : K[X]) * w1 ^ 2 * a0) -
      Polynomial.C κ * ((5159780352 : K[X]) * e1 * w1 * a0) + Polynomial.C
      κ * ((859963392 : K[X]) * e2 * a0)) + h0 ^ 8 * ((522427760640 :
      K[X]) * a0 * a1 - Polynomial.C μ₃ * ((16 : K[X]) * e1) -
      Polynomial.C κ₅ * ((2985984 : K[X]) * a1) - Polynomial.C μ *
      ((376233984 : K[X]) * e1 * a0)) + h0 ^ 9 * (-(Polynomial.C ν *
      ((67184640 : K[X]) * a0))) = Polynomial.C μ₄ * h0 ^ 9 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    linear_combination hcore + (-((61931520 : K[X]) * e1 ^ 4 * w1 * h0 ^ 4 - (423198720 : K[X]) * e1 ^
      3 * w1 ^ 3 * h0 ^ 3 + (185794560 : K[X]) * e1 ^ 3 * w1 * f2 * h0 ^ 3
      - (278691840 : K[X]) * e1 ^ 3 * a3 * h0 ^ 3 + (505774080 : K[X]) *
      e1 ^ 2 * w1 ^ 5 * h0 ^ 2 - (1455390720 : K[X]) * e1 ^ 2 * w1 ^ 3 *
      f2 * h0 ^ 2 + (4737761280 : K[X]) * e1 ^ 2 * w1 ^ 2 * a3 * h0 ^ 2 +
      (557383680 : K[X]) * e1 ^ 2 * w1 * f2 ^ 2 * h0 ^ 2 - (3344302080 :
      K[X]) * e1 ^ 2 * w1 * a2 * h0 ^ 4 - (836075520 : K[X]) * e1 ^ 2 * f2
      * a3 * h0 ^ 2 + (1433272320 : K[X]) * e1 ^ 2 * a1 * h0 ^ 6 -
      (384860160 : K[X]) * e1 * w1 ^ 7 * h0 + (2972712960 : K[X]) * e1 *
      w1 ^ 5 * f2 * h0 - (7803371520 : K[X]) * e1 * w1 ^ 4 * a3 * h0 -
      (4923555840 : K[X]) * e1 * w1 ^ 3 * f2 ^ 2 * h0 + (10032906240 :
      K[X]) * e1 * w1 ^ 3 * a2 * h0 ^ 3 + (15049359360 : K[X]) * e1 * w1 ^
      2 * f2 * a3 * h0 - (12182814720 : K[X]) * e1 * w1 ^ 2 * a1 * h0 ^ 5
      + (1672151040 : K[X]) * e1 * w1 * f2 ^ 3 * h0 - (10032906240 : K[X])
      * e1 * w1 * f2 * a2 * h0 ^ 3 - (15049359360 : K[X]) * e1 * w1 * a3 ^
      2 * h0 + (12899450880 : K[X]) * e1 * w1 * a0 * h0 ^ 7 - (2508226560
      : K[X]) * e1 * f2 ^ 2 * a3 * h0 + (4299816960 : K[X]) * e1 * f2 * a1
      * h0 ^ 5 + (12899450880 : K[X]) * e1 * a3 * a2 * h0 ^ 3 + (404848640
      : K[X]) * w1 ^ 9 - (4127293440 : K[X]) * w1 ^ 7 * f2 + (6502809600 :
      K[X]) * w1 ^ 6 * a3 + (13841694720 : K[X]) * w1 ^ 5 * f2 ^ 2 -
      (8360755200 : K[X]) * w1 ^ 5 * a2 * h0 ^ 2 - (38459473920 : K[X]) *
      w1 ^ 4 * f2 * a3 + (11466178560 : K[X]) * w1 ^ 4 * a1 * h0 ^ 4 -
      (16442818560 : K[X]) * w1 ^ 3 * f2 ^ 3 + (40131624960 : K[X]) * w1 ^
      3 * f2 * a2 * h0 ^ 2 + (35115171840 : K[X]) * w1 ^ 3 * a3 ^ 2 -
      (17199267840 : K[X]) * w1 ^ 3 * a0 * h0 ^ 6 + (47656304640 : K[X]) *
      w1 ^ 2 * f2 ^ 2 * a3 - (40848261120 : K[X]) * w1 ^ 2 * f2 * a1 * h0
      ^ 4 - (77396705280 : K[X]) * w1 ^ 2 * a3 * a2 * h0 ^ 2 + (5016453120
      : K[X]) * w1 * f2 ^ 4 - (30098718720 : K[X]) * w1 * f2 ^ 2 * a2 * h0
      ^ 2 - (45148078080 : K[X]) * w1 * f2 * a3 ^ 2 + (38698352640 : K[X])
      * w1 * f2 * a0 * h0 ^ 6 + (77396705280 : K[X]) * w1 * a3 * a1 * h0 ^
      4 + (38698352640 : K[X]) * w1 * a2 ^ 2 * h0 ^ 4 - (7524679680 :
      K[X]) * f2 ^ 3 * a3 + (12899450880 : K[X]) * f2 ^ 2 * a1 * h0 ^ 4 +
      (38698352640 : K[X]) * f2 * a3 * a2 * h0 ^ 2 + (12899450880 : K[X])
      * a3 ^ 3 - (58047528960 : K[X]) * a3 * a0 * h0 ^ 6 - (58047528960 :
      K[X]) * a1 * a2 * h0 ^ 6 - Polynomial.C μ₃ * ((16 : K[X]) * h0 ^ 9)
      + Polynomial.C κ₇ * ((2304 : K[X]) * w1 * h0 ^ 8) + Polynomial.C ν₂
      * ((2592 : K[X]) * e1 * h0 ^ 8) - Polynomial.C ν₂ * ((9072 : K[X]) *
      w1 ^ 2 * h0 ^ 7) + Polynomial.C ν₂ * ((7776 : K[X]) * f2 * h0 ^ 7) -
      Polynomial.C κ₅ * ((73728 : K[X]) * e1 * w1 * h0 ^ 7) + Polynomial.C
      κ₅ * ((98304 : K[X]) * w1 ^ 3 * h0 ^ 6) - Polynomial.C κ₅ * ((221184
      : K[X]) * w1 * f2 * h0 ^ 6) + Polynomial.C κ₅ * ((331776 : K[X]) *
      a3 * h0 ^ 6) - Polynomial.C ν * ((80640 : K[X]) * e1 ^ 2 * h0 ^ 7) +
      Polynomial.C ν * ((624960 : K[X]) * e1 * w1 ^ 2 * h0 ^ 6) -
      Polynomial.C ν * ((241920 : K[X]) * e1 * f2 * h0 ^ 6) - Polynomial.C
      ν * ((539280 : K[X]) * w1 ^ 4 * h0 ^ 5) + Polynomial.C ν * ((2116800
      : K[X]) * w1 ^ 2 * f2 * h0 ^ 5) - Polynomial.C ν * ((4354560 : K[X])
      * w1 * a3 * h0 ^ 5) - Polynomial.C ν * ((725760 : K[X]) * f2 ^ 2 *
      h0 ^ 5) + Polynomial.C ν * ((3732480 : K[X]) * a2 * h0 ^ 7) -
      Polynomial.C μ * ((887040 : K[X]) * e1 ^ 3 * h0 ^ 6) + Polynomial.C
      μ * ((12418560 : K[X]) * e1 ^ 2 * w1 ^ 2 * h0 ^ 5) - Polynomial.C μ
      * ((2661120 : K[X]) * e1 ^ 2 * f2 * h0 ^ 5) - Polynomial.C μ *
      ((15855840 : K[X]) * e1 * w1 ^ 4 * h0 ^ 4) + Polynomial.C μ *
      ((39916800 : K[X]) * e1 * w1 ^ 2 * f2 * h0 ^ 4) - Polynomial.C μ *
      ((95800320 : K[X]) * e1 * w1 * a3 * h0 ^ 4) - Polynomial.C μ *
      ((7983360 : K[X]) * e1 * f2 ^ 2 * h0 ^ 4) + Polynomial.C μ *
      ((52254720 : K[X]) * e1 * a2 * h0 ^ 6) + Polynomial.C μ * ((12747504
      : K[X]) * w1 ^ 6 * h0 ^ 3) - Polynomial.C μ * ((87484320 : K[X]) *
      w1 ^ 4 * f2 * h0 ^ 3) + Polynomial.C μ * ((175633920 : K[X]) * w1 ^
      3 * a3 * h0 ^ 3) + Polynomial.C μ * ((127733760 : K[X]) * w1 ^ 2 *
      f2 ^ 2 * h0 ^ 3) - Polynomial.C μ * ((235146240 : K[X]) * w1 ^ 2 *
      a2 * h0 ^ 5) - Polynomial.C μ * ((287400960 : K[X]) * w1 * f2 * a3 *
      h0 ^ 3) + Polynomial.C μ * ((313528320 : K[X]) * w1 * a1 * h0 ^ 7) -
      Polynomial.C μ * ((23950080 : K[X]) * f2 ^ 3 * h0 ^ 3) +
      Polynomial.C μ * ((156764160 : K[X]) * f2 * a2 * h0 ^ 5) +
      Polynomial.C μ * ((156764160 : K[X]) * a3 ^ 2 * h0 ^ 3) -
      Polynomial.C μ * ((376233984 : K[X]) * a0 * h0 ^ 9) - Polynomial.C κ
      * ((35389440 : K[X]) * e1 ^ 3 * w1 * h0 ^ 5) + Polynomial.C κ *
      ((153354240 : K[X]) * e1 ^ 2 * w1 ^ 3 * h0 ^ 4) - Polynomial.C κ *
      ((106168320 : K[X]) * e1 ^ 2 * w1 * f2 * h0 ^ 4) + Polynomial.C κ *
      ((159252480 : K[X]) * e1 ^ 2 * a3 * h0 ^ 4) - Polynomial.C κ *
      ((132120576 : K[X]) * e1 * w1 ^ 5 * h0 ^ 3) + Polynomial.C κ *
      ((566231040 : K[X]) * e1 * w1 ^ 3 * f2 * h0 ^ 3) - Polynomial.C κ *
      ((1592524800 : K[X]) * e1 * w1 ^ 2 * a3 * h0 ^ 3) - Polynomial.C κ *
      ((318504960 : K[X]) * e1 * w1 * f2 ^ 2 * h0 ^ 3) + Polynomial.C κ *
      ((1433272320 : K[X]) * e1 * w1 * a2 * h0 ^ 5) + Polynomial.C κ *
      ((477757440 : K[X]) * e1 * f2 * a3 * h0 ^ 3) - Polynomial.C κ *
      ((859963392 : K[X]) * e1 * a1 * h0 ^ 7) + Polynomial.C κ *
      ((120324096 : K[X]) * w1 ^ 7 * h0 ^ 2) - Polynomial.C κ *
      ((962592768 : K[X]) * w1 ^ 5 * f2 * h0 ^ 2) + Polynomial.C κ *
      ((1751777280 : K[X]) * w1 ^ 4 * a3 * h0 ^ 2) + Polynomial.C κ *
      ((2017198080 : K[X]) * w1 ^ 3 * f2 ^ 2 * h0 ^ 2) - Polynomial.C κ *
      ((2388787200 : K[X]) * w1 ^ 3 * a2 * h0 ^ 4) - Polynomial.C κ *
      ((5255331840 : K[X]) * w1 ^ 2 * f2 * a3 * h0 ^ 2) + Polynomial.C κ *
      ((3439853568 : K[X]) * w1 ^ 2 * a1 * h0 ^ 6) - Polynomial.C κ *
      ((955514880 : K[X]) * w1 * f2 ^ 3 * h0 ^ 2) + Polynomial.C κ *
      ((4299816960 : K[X]) * w1 * f2 * a2 * h0 ^ 4) + Polynomial.C κ *
      ((4299816960 : K[X]) * w1 * a3 ^ 2 * h0 ^ 2) - Polynomial.C κ *
      ((5159780352 : K[X]) * w1 * a0 * h0 ^ 8) + Polynomial.C κ *
      ((1433272320 : K[X]) * f2 ^ 2 * a3 * h0 ^ 2) - Polynomial.C κ *
      ((2579890176 : K[X]) * f2 * a1 * h0 ^ 6) - Polynomial.C κ *
      ((5159780352 : K[X]) * a3 * a2 * h0 ^ 4))) * he1 + (-(-((10321920 :
      K[X]) * e1 ^ 4 * h0 ^ 4) + (165150720 : K[X]) * e1 ^ 3 * w1 ^ 2 * h0
      ^ 3 - (20643840 : K[X]) * e1 ^ 2 * e2 * w1 * h0 ^ 3 - (134184960 :
      K[X]) * e1 ^ 2 * w1 ^ 4 * h0 ^ 2 - (557383680 : K[X]) * e1 ^ 2 * w1
      * a3 * h0 ^ 2 + (477757440 : K[X]) * e1 ^ 2 * a2 * h0 ^ 4 + (655360
      : K[X]) * e1 * e2 ^ 2 * h0 ^ 3 + (28835840 : K[X]) * e1 * e2 * w1 ^
      3 * h0 ^ 2 + (17694720 : K[X]) * e1 * e2 * a3 * h0 ^ 2 - (19988480 :
      K[X]) * e1 * w1 ^ 6 * h0 + (760872960 : K[X]) * e1 * w1 ^ 3 * a3 *
      h0 - (2388787200 : K[X]) * e1 * w1 ^ 2 * a2 * h0 ^ 3 + (2866544640 :
      K[X]) * e1 * w1 * a1 * h0 ^ 5 + (477757440 : K[X]) * e1 * a3 ^ 2 *
      h0 - (2149908480 : K[X]) * e1 * a0 * h0 ^ 7 - (1638400 : K[X]) * e2
      ^ 2 * w1 ^ 2 * h0 ^ 2 + (163840 : K[X]) * e2 * w1 ^ 5 * h0 -
      (44236800 : K[X]) * e2 * w1 ^ 2 * a3 * h0 + (159252480 : K[X]) * e2
      * w1 * a2 * h0 ^ 3 - (119439360 : K[X]) * e2 * a1 * h0 ^ 5 - (163840
      : K[X]) * w1 ^ 8 + (48660480 : K[X]) * w1 ^ 5 * a3 + (79626240 :
      K[X]) * w1 ^ 4 * a2 * h0 ^ 2 - (597196800 : K[X]) * w1 ^ 3 * a1 * h0
      ^ 4 - (1194393600 : K[X]) * w1 ^ 2 * a3 ^ 2 + (2149908480 : K[X]) *
      w1 ^ 2 * a0 * h0 ^ 6 + (4299816960 : K[X]) * w1 * a3 * a2 * h0 ^ 2 -
      (3224862720 : K[X]) * a3 * a1 * h0 ^ 4 - (3224862720 : K[X]) * a2 ^
      2 * h0 ^ 4 - Polynomial.C κ₇ * ((384 : K[X]) * h0 ^ 8) +
      Polynomial.C ν₂ * ((1728 : K[X]) * w1 * h0 ^ 7) + Polynomial.C κ₅ *
      ((12288 : K[X]) * e1 * h0 ^ 7) - Polynomial.C κ₅ * ((12288 : K[X]) *
      w1 ^ 2 * h0 ^ 6) - Polynomial.C ν * ((161280 : K[X]) * e1 * w1 * h0
      ^ 6) + Polynomial.C ν * ((7680 : K[X]) * e2 * h0 ^ 6) + Polynomial.C
      ν * ((21120 : K[X]) * w1 ^ 3 * h0 ^ 5) + Polynomial.C ν * ((207360 :
      K[X]) * a3 * h0 ^ 5) - Polynomial.C μ * ((3548160 : K[X]) * e1 ^ 2 *
      w1 * h0 ^ 5) + Polynomial.C μ * ((215040 : K[X]) * e1 * e2 * h0 ^ 5)
      + Polynomial.C μ * ((3171840 : K[X]) * e1 * w1 ^ 3 * h0 ^ 4) +
      Polynomial.C μ * ((5806080 : K[X]) * e1 * a3 * h0 ^ 4) -
      Polynomial.C μ * ((376320 : K[X]) * e2 * w1 ^ 2 * h0 ^ 4) +
      Polynomial.C μ * ((348096 : K[X]) * w1 ^ 5 * h0 ^ 3) - Polynomial.C
      μ * ((10160640 : K[X]) * w1 ^ 2 * a3 * h0 ^ 3) + Polynomial.C μ *
      ((34836480 : K[X]) * w1 * a2 * h0 ^ 5) - Polynomial.C μ * ((41803776
      : K[X]) * a1 * h0 ^ 7) + Polynomial.C κ * ((5898240 : K[X]) * e1 ^ 3
      * h0 ^ 5) - Polynomial.C κ * ((53084160 : K[X]) * e1 ^ 2 * w1 ^ 2 *
      h0 ^ 4) + Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 * w1 * h0 ^
      4) + Polynomial.C κ * ((11796480 : K[X]) * e1 * w1 ^ 4 * h0 ^ 3) +
      Polynomial.C κ * ((159252480 : K[X]) * e1 * w1 * a3 * h0 ^ 3) -
      Polynomial.C κ * ((191102976 : K[X]) * e1 * a2 * h0 ^ 5) -
      Polynomial.C κ * ((131072 : K[X]) * e2 ^ 2 * h0 ^ 4) - Polynomial.C
      κ * ((2228224 : K[X]) * e2 * w1 ^ 3 * h0 ^ 3) - Polynomial.C κ *
      ((3538944 : K[X]) * e2 * a3 * h0 ^ 3) + Polynomial.C κ * ((2228224 :
      K[X]) * w1 ^ 6 * h0 ^ 2) - Polynomial.C κ * ((56623104 : K[X]) * w1
      ^ 3 * a3 * h0 ^ 2) + Polynomial.C κ * ((286654464 : K[X]) * w1 ^ 2 *
      a2 * h0 ^ 4) - Polynomial.C κ * ((573308928 : K[X]) * w1 * a1 * h0 ^
      6) - Polynomial.C κ * ((95551488 : K[X]) * a3 ^ 2 * h0 ^ 2) +
      Polynomial.C κ * ((859963392 : K[X]) * a0 * h0 ^ 8))) * he2
  have hRq :
      ((4423680 : K[X]) * e1 ^ 3 * w1 ^ 5 - Polynomial.C μ * ((945 : K[X])
      * w1 ^ 8)) + h0 * (-((61931520 : K[X]) * e1 ^ 4 * w1 ^ 3) -
      (22118400 : K[X]) * e1 ^ 2 * u2 * w1 ^ 3 + (1433272320 : K[X]) * e1
      ^ 2 * w1 ^ 3 * a2 + (655360 : K[X]) * e1 * e2 ^ 3 - (1474560 : K[X])
      * u2 ^ 2 * w1 ^ 3 + (238878720 : K[X]) * u2 * w1 ^ 3 * a2 -
      (9674588160 : K[X]) * w1 ^ 3 * a2 ^ 2 - Polynomial.C μ * ((21168 :
      K[X]) * e1 * w1 ^ 6)) + h0 ^ 2 * ((61931520 : K[X]) * e1 ^ 5 * w1 -
      (10321920 : K[X]) * e1 ^ 4 * e2 + (103219200 : K[X]) * e1 ^ 3 * u2 *
      w1 - (3344302080 : K[X]) * e1 ^ 3 * w1 * a2 - (20643840 : K[X]) * e1
      ^ 2 * e2 * u2 + (477757440 : K[X]) * e1 ^ 2 * e2 * a2 + (19660800 :
      K[X]) * e1 * u2 ^ 2 * w1 - (1911029760 : K[X]) * e1 * u2 * w1 * a2 +
      (38698352640 : K[X]) * e1 * w1 * a2 ^ 2 - (1638400 : K[X]) * e2 * u2
      ^ 2 + (159252480 : K[X]) * e2 * u2 * a2 - (3224862720 : K[X]) * e2 *
      a2 ^ 2 + Polynomial.C ν * ((540 : K[X]) * w1 ^ 6) - Polynomial.C μ *
      ((211680 : K[X]) * e1 ^ 2 * w1 ^ 4) - Polynomial.C μ * ((28224 :
      K[X]) * u2 * w1 ^ 4) + Polynomial.C μ * ((3265920 : K[X]) * w1 ^ 4 *
      a2) + Polynomial.C κ * ((17694720 : K[X]) * e1 ^ 3 * w1 ^ 3) +
      Polynomial.C κ * ((3538944 : K[X]) * e1 * u2 * w1 ^ 3) -
      Polynomial.C κ * ((286654464 : K[X]) * e1 * w1 ^ 3 * a2) -
      Polynomial.C κ * ((131072 : K[X]) * e2 ^ 3)) + h0 ^ 3 *
      (-((2149908480 : K[X]) * e1 ^ 2 * w1 ^ 2 * a1) - (119439360 : K[X])
      * e2 ^ 2 * a1 - (716636160 : K[X]) * u2 * w1 ^ 2 * a1 + (58047528960
      : K[X]) * w1 ^ 2 * a1 * a2 + Polynomial.C ν * ((10800 : K[X]) * e1 *
      w1 ^ 4) + Polynomial.C μ * ((887040 : K[X]) * e1 ^ 3 * w1 ^ 2) +
      Polynomial.C μ * ((215040 : K[X]) * e1 * e2 ^ 2) + Polynomial.C μ *
      ((1128960 : K[X]) * e1 * u2 * w1 ^ 2) - Polynomial.C μ * ((78382080
      : K[X]) * e1 * w1 ^ 2 * a2) - Polynomial.C κ * ((35389440 : K[X]) *
      e1 ^ 4 * w1) + Polynomial.C κ * ((5898240 : K[X]) * e1 ^ 3 * e2) -
      Polynomial.C κ * ((35389440 : K[X]) * e1 ^ 2 * u2 * w1) +
      Polynomial.C κ * ((1433272320 : K[X]) * e1 ^ 2 * w1 * a2) +
      Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 * u2) - Polynomial.C κ
      * ((191102976 : K[X]) * e1 * e2 * a2) - Polynomial.C κ * ((2359296 :
      K[X]) * u2 ^ 2 * w1) + Polynomial.C κ * ((286654464 : K[X]) * u2 *
      w1 * a2) - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) +
      h0 ^ 4 * ((1433272320 : K[X]) * e1 ^ 3 * a1 + (2866544640 : K[X]) *
      e1 * u2 * a1 - (58047528960 : K[X]) * e1 * a1 * a2 - Polynomial.C ν₂
      * ((54 : K[X]) * w1 ^ 4) + Polynomial.C ν * ((60480 : K[X]) * e1 ^ 2
      * w1 ^ 2) + Polynomial.C ν * ((7680 : K[X]) * e2 ^ 2) + Polynomial.C
      ν * ((28800 : K[X]) * u2 * w1 ^ 2) - Polynomial.C ν * ((2799360 :
      K[X]) * w1 ^ 2 * a2) - Polynomial.C μ * ((887040 : K[X]) * e1 ^ 4) -
      Polynomial.C μ * ((3548160 : K[X]) * e1 ^ 2 * u2) + Polynomial.C μ *
      ((52254720 : K[X]) * e1 ^ 2 * a2) - Polynomial.C μ * ((376320 :
      K[X]) * u2 ^ 2) + Polynomial.C μ * ((34836480 : K[X]) * u2 * a2) -
      Polynomial.C μ * ((15676416 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ
      * ((564350976 : K[X]) * a2 ^ 2) + Polynomial.C κ * ((859963392 :
      K[X]) * e1 * w1 ^ 2 * a1)) + h0 ^ 5 * ((12899450880 : K[X]) * e1 ^ 2
      * w1 * a0 - (2149908480 : K[X]) * e1 * e2 * a0 + (2149908480 : K[X])
      * u2 * w1 * a0 - (174142586880 : K[X]) * w1 * a0 * a2 - (87071293440
      : K[X]) * w1 * a1 ^ 2 - Polynomial.C ν₂ * ((1296 : K[X]) * e1 * w1 ^
      2) - Polynomial.C κ₅ * ((73728 : K[X]) * e1 ^ 2 * w1) + Polynomial.C
      κ₅ * ((12288 : K[X]) * e1 * e2) - Polynomial.C κ₅ * ((12288 : K[X])
      * u2 * w1) + Polynomial.C κ₅ * ((995328 : K[X]) * w1 * a2) -
      Polynomial.C ν * ((80640 : K[X]) * e1 ^ 3) - Polynomial.C ν *
      ((161280 : K[X]) * e1 * u2) + Polynomial.C ν * ((3732480 : K[X]) *
      e1 * a2) + Polynomial.C μ * ((313528320 : K[X]) * e1 * w1 * a1) -
      Polynomial.C μ * ((41803776 : K[X]) * e2 * a1) - Polynomial.C κ *
      ((859963392 : K[X]) * e1 ^ 2 * a1) - Polynomial.C κ * ((573308928 :
      K[X]) * u2 * a1) + Polynomial.C κ * ((23219011584 : K[X]) * a1 *
      a2)) + h0 ^ 6 * (Polynomial.C μ₃ * ((4 : K[X]) * w1 ^ 2) +
      Polynomial.C κ₇ * ((2304 : K[X]) * e1 * w1) - Polynomial.C κ₇ *
      ((384 : K[X]) * e2) + Polynomial.C ν₂ * ((2592 : K[X]) * e1 ^ 2) +
      Polynomial.C ν₂ * ((1728 : K[X]) * u2) - Polynomial.C ν₂ * ((93312 :
      K[X]) * a2) + Polynomial.C ν * ((11197440 : K[X]) * w1 * a1) +
      Polynomial.C μ * ((94058496 : K[X]) * w1 ^ 2 * a0) - Polynomial.C κ
      * ((5159780352 : K[X]) * e1 * w1 * a0) + Polynomial.C κ *
      ((859963392 : K[X]) * e2 * a0)) + h0 ^ 7 * ((522427760640 : K[X]) *
      a0 * a1 - Polynomial.C μ₃ * ((16 : K[X]) * e1) - Polynomial.C κ₅ *
      ((2985984 : K[X]) * a1) - Polynomial.C μ * ((376233984 : K[X]) * e1
      * a0)) + h0 ^ 8 * (-(Polynomial.C ν * ((67184640 : K[X]) * a0))) =
      Polynomial.C μ₄ * h0 ^ 8 := by
    apply mul_left_cancel₀ hh0
    linear_combination hcs2 + (-((103219200 : K[X]) * e1 ^ 3 * w1 * h0 ^ 2 - (20643840 : K[X]) * e1 ^
      2 * e2 * h0 ^ 2 - (81100800 : K[X]) * e1 ^ 2 * w1 ^ 3 * h0 +
      (24576000 : K[X]) * e1 * e2 * w1 ^ 2 * h0 + (19660800 : K[X]) * e1 *
      u2 * w1 * h0 ^ 2 + (4423680 : K[X]) * e1 * w1 ^ 5 - (1911029760 :
      K[X]) * e1 * w1 * a2 * h0 ^ 2 + (2866544640 : K[X]) * e1 * a1 * h0 ^
      4 - (1638400 : K[X]) * e2 ^ 2 * w1 * h0 - (1638400 : K[X]) * e2 * u2
      * h0 ^ 2 - (1474560 : K[X]) * e2 * w1 ^ 4 + (159252480 : K[X]) * e2
      * a2 * h0 ^ 2 - (1474560 : K[X]) * u2 * w1 ^ 3 * h0 + (238878720 :
      K[X]) * w1 ^ 3 * a2 * h0 - (716636160 : K[X]) * w1 ^ 2 * a1 * h0 ^ 3
      + (2149908480 : K[X]) * w1 * a0 * h0 ^ 5 + Polynomial.C ν₂ * ((1728
      : K[X]) * h0 ^ 6) - Polynomial.C κ₅ * ((12288 : K[X]) * w1 * h0 ^ 5)
      - Polynomial.C ν * ((161280 : K[X]) * e1 * h0 ^ 5) + Polynomial.C ν
      * ((28800 : K[X]) * w1 ^ 2 * h0 ^ 4) - Polynomial.C μ * ((3548160 :
      K[X]) * e1 ^ 2 * h0 ^ 4) + Polynomial.C μ * ((2257920 : K[X]) * e1 *
      w1 ^ 2 * h0 ^ 3) - Polynomial.C μ * ((376320 : K[X]) * e2 * w1 * h0
      ^ 3) - Polynomial.C μ * ((376320 : K[X]) * u2 * h0 ^ 4) -
      Polynomial.C μ * ((28224 : K[X]) * w1 ^ 4 * h0 ^ 2) + Polynomial.C μ
      * ((34836480 : K[X]) * a2 * h0 ^ 4) - Polynomial.C κ * ((35389440 :
      K[X]) * e1 ^ 2 * w1 * h0 ^ 3) + Polynomial.C κ * ((5898240 : K[X]) *
      e1 * e2 * h0 ^ 3) + Polynomial.C κ * ((10616832 : K[X]) * e1 * w1 ^
      3 * h0 ^ 2) - Polynomial.C κ * ((2359296 : K[X]) * e2 * w1 ^ 2 * h0
      ^ 2) - Polynomial.C κ * ((2359296 : K[X]) * u2 * w1 * h0 ^ 3) +
      Polynomial.C κ * ((286654464 : K[X]) * w1 * a2 * h0 ^ 3) -
      Polynomial.C κ * ((573308928 : K[X]) * a1 * h0 ^ 5))) * hu2
  have hR2q :
      (Polynomial.C μ * ((1215 : K[X]) * w1 ^ 8)) + h0 * (-((61931520 :
      K[X]) * e1 ^ 4 * w1 ^ 3) - (22118400 : K[X]) * e1 ^ 2 * u2 * w1 ^ 3
      + (1433272320 : K[X]) * e1 ^ 2 * w1 ^ 3 * a2 + (655360 : K[X]) * e1
      * e2 ^ 3 - (1474560 : K[X]) * u2 ^ 2 * w1 ^ 3 + (238878720 : K[X]) *
      u2 * w1 ^ 3 * a2 + (2160 : K[X]) * s2 * w1 - (9674588160 : K[X]) *
      w1 ^ 3 * a2 ^ 2 - Polynomial.C μ * ((21168 : K[X]) * e1 * w1 ^ 6)) +
      h0 ^ 2 * ((61931520 : K[X]) * e1 ^ 5 * w1 - (10321920 : K[X]) * e1 ^
      4 * e2 + (103219200 : K[X]) * e1 ^ 3 * u2 * w1 - (3344302080 : K[X])
      * e1 ^ 3 * w1 * a2 - (20643840 : K[X]) * e1 ^ 2 * e2 * u2 +
      (477757440 : K[X]) * e1 ^ 2 * e2 * a2 + (19660800 : K[X]) * e1 * u2
      ^ 2 * w1 - (1911029760 : K[X]) * e1 * u2 * w1 * a2 + (38698352640 :
      K[X]) * e1 * w1 * a2 ^ 2 - (1638400 : K[X]) * e2 * u2 ^ 2 +
      (159252480 : K[X]) * e2 * u2 * a2 - (3224862720 : K[X]) * e2 * a2 ^
      2 + Polynomial.C ν * ((540 : K[X]) * w1 ^ 6) - Polynomial.C μ *
      ((211680 : K[X]) * e1 ^ 2 * w1 ^ 4) - Polynomial.C μ * ((28224 :
      K[X]) * u2 * w1 ^ 4) + Polynomial.C μ * ((3265920 : K[X]) * w1 ^ 4 *
      a2) + Polynomial.C κ * ((17694720 : K[X]) * e1 ^ 3 * w1 ^ 3) +
      Polynomial.C κ * ((3538944 : K[X]) * e1 * u2 * w1 ^ 3) -
      Polynomial.C κ * ((286654464 : K[X]) * e1 * w1 ^ 3 * a2) -
      Polynomial.C κ * ((131072 : K[X]) * e2 ^ 3)) + h0 ^ 3 *
      (-((2149908480 : K[X]) * e1 ^ 2 * w1 ^ 2 * a1) - (119439360 : K[X])
      * e2 ^ 2 * a1 - (716636160 : K[X]) * u2 * w1 ^ 2 * a1 + (58047528960
      : K[X]) * w1 ^ 2 * a1 * a2 + Polynomial.C ν * ((10800 : K[X]) * e1 *
      w1 ^ 4) + Polynomial.C μ * ((887040 : K[X]) * e1 ^ 3 * w1 ^ 2) +
      Polynomial.C μ * ((215040 : K[X]) * e1 * e2 ^ 2) + Polynomial.C μ *
      ((1128960 : K[X]) * e1 * u2 * w1 ^ 2) - Polynomial.C μ * ((78382080
      : K[X]) * e1 * w1 ^ 2 * a2) - Polynomial.C κ * ((35389440 : K[X]) *
      e1 ^ 4 * w1) + Polynomial.C κ * ((5898240 : K[X]) * e1 ^ 3 * e2) -
      Polynomial.C κ * ((35389440 : K[X]) * e1 ^ 2 * u2 * w1) +
      Polynomial.C κ * ((1433272320 : K[X]) * e1 ^ 2 * w1 * a2) +
      Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 * u2) - Polynomial.C κ
      * ((191102976 : K[X]) * e1 * e2 * a2) - Polynomial.C κ * ((2359296 :
      K[X]) * u2 ^ 2 * w1) + Polynomial.C κ * ((286654464 : K[X]) * u2 *
      w1 * a2) - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) +
      h0 ^ 4 * ((1433272320 : K[X]) * e1 ^ 3 * a1 + (2866544640 : K[X]) *
      e1 * u2 * a1 - (58047528960 : K[X]) * e1 * a1 * a2 - Polynomial.C ν₂
      * ((54 : K[X]) * w1 ^ 4) + Polynomial.C ν * ((60480 : K[X]) * e1 ^ 2
      * w1 ^ 2) + Polynomial.C ν * ((7680 : K[X]) * e2 ^ 2) + Polynomial.C
      ν * ((28800 : K[X]) * u2 * w1 ^ 2) - Polynomial.C ν * ((2799360 :
      K[X]) * w1 ^ 2 * a2) - Polynomial.C μ * ((887040 : K[X]) * e1 ^ 4) -
      Polynomial.C μ * ((3548160 : K[X]) * e1 ^ 2 * u2) + Polynomial.C μ *
      ((52254720 : K[X]) * e1 ^ 2 * a2) - Polynomial.C μ * ((376320 :
      K[X]) * u2 ^ 2) + Polynomial.C μ * ((34836480 : K[X]) * u2 * a2) -
      Polynomial.C μ * ((15676416 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ
      * ((564350976 : K[X]) * a2 ^ 2) + Polynomial.C κ * ((859963392 :
      K[X]) * e1 * w1 ^ 2 * a1)) + h0 ^ 5 * ((12899450880 : K[X]) * e1 ^ 2
      * w1 * a0 - (2149908480 : K[X]) * e1 * e2 * a0 + (2149908480 : K[X])
      * u2 * w1 * a0 - (174142586880 : K[X]) * w1 * a0 * a2 - (87071293440
      : K[X]) * w1 * a1 ^ 2 - Polynomial.C ν₂ * ((1296 : K[X]) * e1 * w1 ^
      2) - Polynomial.C κ₅ * ((73728 : K[X]) * e1 ^ 2 * w1) + Polynomial.C
      κ₅ * ((12288 : K[X]) * e1 * e2) - Polynomial.C κ₅ * ((12288 : K[X])
      * u2 * w1) + Polynomial.C κ₅ * ((995328 : K[X]) * w1 * a2) -
      Polynomial.C ν * ((80640 : K[X]) * e1 ^ 3) - Polynomial.C ν *
      ((161280 : K[X]) * e1 * u2) + Polynomial.C ν * ((3732480 : K[X]) *
      e1 * a2) + Polynomial.C μ * ((313528320 : K[X]) * e1 * w1 * a1) -
      Polynomial.C μ * ((41803776 : K[X]) * e2 * a1) - Polynomial.C κ *
      ((859963392 : K[X]) * e1 ^ 2 * a1) - Polynomial.C κ * ((573308928 :
      K[X]) * u2 * a1) + Polynomial.C κ * ((23219011584 : K[X]) * a1 *
      a2)) + h0 ^ 6 * (Polynomial.C μ₃ * ((4 : K[X]) * w1 ^ 2) +
      Polynomial.C κ₇ * ((2304 : K[X]) * e1 * w1) - Polynomial.C κ₇ *
      ((384 : K[X]) * e2) + Polynomial.C ν₂ * ((2592 : K[X]) * e1 ^ 2) +
      Polynomial.C ν₂ * ((1728 : K[X]) * u2) - Polynomial.C ν₂ * ((93312 :
      K[X]) * a2) + Polynomial.C ν * ((11197440 : K[X]) * w1 * a1) +
      Polynomial.C μ * ((94058496 : K[X]) * w1 ^ 2 * a0) - Polynomial.C κ
      * ((5159780352 : K[X]) * e1 * w1 * a0) + Polynomial.C κ *
      ((859963392 : K[X]) * e2 * a0)) + h0 ^ 7 * ((522427760640 : K[X]) *
      a0 * a1 - Polynomial.C μ₃ * ((16 : K[X]) * e1) - Polynomial.C κ₅ *
      ((2985984 : K[X]) * a1) - Polynomial.C μ * ((376233984 : K[X]) * e1
      * a0)) + h0 ^ 8 * (-(Polynomial.C ν * ((67184640 : K[X]) * a0))) =
      Polynomial.C μ₄ * h0 ^ 8 := by
    linear_combination hRq + (-((2160 : K[X]) * w1)) * hs2
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have hev := congrArg (fun t : K[X] => t.eval (-(d / c))) hR2q
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hev
  rw [hroot] at hev
  have hzero :
      (Polynomial.C μ * w1 ^ 8).eval (-(d / c)) = 0 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C]
    linear_combination ((1215 : K)⁻¹) * hev
  obtain ⟨s4, hs4⟩ := linearPolynomial_dvd_of_eval_eq_zero_810 h0
    (Polynomial.C μ * w1 ^ 8) (-(d / c)) hdeg1 hroot hzero
  have hR3q :
      (-((61931520 : K[X]) * e1 ^ 4 * w1 ^ 3) - (22118400 : K[X]) * e1 ^ 2
      * u2 * w1 ^ 3 + (1433272320 : K[X]) * e1 ^ 2 * w1 ^ 3 * a2 + (655360
      : K[X]) * e1 * e2 ^ 3 - (1474560 : K[X]) * u2 ^ 2 * w1 ^ 3 +
      (238878720 : K[X]) * u2 * w1 ^ 3 * a2 + (2160 : K[X]) * s2 * w1 +
      (1215 : K[X]) * s4 - (9674588160 : K[X]) * w1 ^ 3 * a2 ^ 2 -
      Polynomial.C μ * ((21168 : K[X]) * e1 * w1 ^ 6)) + h0 * ((61931520 :
      K[X]) * e1 ^ 5 * w1 - (10321920 : K[X]) * e1 ^ 4 * e2 + (103219200 :
      K[X]) * e1 ^ 3 * u2 * w1 - (3344302080 : K[X]) * e1 ^ 3 * w1 * a2 -
      (20643840 : K[X]) * e1 ^ 2 * e2 * u2 + (477757440 : K[X]) * e1 ^ 2 *
      e2 * a2 + (19660800 : K[X]) * e1 * u2 ^ 2 * w1 - (1911029760 : K[X])
      * e1 * u2 * w1 * a2 + (38698352640 : K[X]) * e1 * w1 * a2 ^ 2 -
      (1638400 : K[X]) * e2 * u2 ^ 2 + (159252480 : K[X]) * e2 * u2 * a2 -
      (3224862720 : K[X]) * e2 * a2 ^ 2 + Polynomial.C ν * ((540 : K[X]) *
      w1 ^ 6) - Polynomial.C μ * ((211680 : K[X]) * e1 ^ 2 * w1 ^ 4) -
      Polynomial.C μ * ((28224 : K[X]) * u2 * w1 ^ 4) + Polynomial.C μ *
      ((3265920 : K[X]) * w1 ^ 4 * a2) + Polynomial.C κ * ((17694720 :
      K[X]) * e1 ^ 3 * w1 ^ 3) + Polynomial.C κ * ((3538944 : K[X]) * e1 *
      u2 * w1 ^ 3) - Polynomial.C κ * ((286654464 : K[X]) * e1 * w1 ^ 3 *
      a2) - Polynomial.C κ * ((131072 : K[X]) * e2 ^ 3)) + h0 ^ 2 *
      (-((2149908480 : K[X]) * e1 ^ 2 * w1 ^ 2 * a1) - (119439360 : K[X])
      * e2 ^ 2 * a1 - (716636160 : K[X]) * u2 * w1 ^ 2 * a1 + (58047528960
      : K[X]) * w1 ^ 2 * a1 * a2 + Polynomial.C ν * ((10800 : K[X]) * e1 *
      w1 ^ 4) + Polynomial.C μ * ((887040 : K[X]) * e1 ^ 3 * w1 ^ 2) +
      Polynomial.C μ * ((215040 : K[X]) * e1 * e2 ^ 2) + Polynomial.C μ *
      ((1128960 : K[X]) * e1 * u2 * w1 ^ 2) - Polynomial.C μ * ((78382080
      : K[X]) * e1 * w1 ^ 2 * a2) - Polynomial.C κ * ((35389440 : K[X]) *
      e1 ^ 4 * w1) + Polynomial.C κ * ((5898240 : K[X]) * e1 ^ 3 * e2) -
      Polynomial.C κ * ((35389440 : K[X]) * e1 ^ 2 * u2 * w1) +
      Polynomial.C κ * ((1433272320 : K[X]) * e1 ^ 2 * w1 * a2) +
      Polynomial.C κ * ((5898240 : K[X]) * e1 * e2 * u2) - Polynomial.C κ
      * ((191102976 : K[X]) * e1 * e2 * a2) - Polynomial.C κ * ((2359296 :
      K[X]) * u2 ^ 2 * w1) + Polynomial.C κ * ((286654464 : K[X]) * u2 *
      w1 * a2) - Polynomial.C κ * ((7739670528 : K[X]) * w1 * a2 ^ 2)) +
      h0 ^ 3 * ((1433272320 : K[X]) * e1 ^ 3 * a1 + (2866544640 : K[X]) *
      e1 * u2 * a1 - (58047528960 : K[X]) * e1 * a1 * a2 - Polynomial.C ν₂
      * ((54 : K[X]) * w1 ^ 4) + Polynomial.C ν * ((60480 : K[X]) * e1 ^ 2
      * w1 ^ 2) + Polynomial.C ν * ((7680 : K[X]) * e2 ^ 2) + Polynomial.C
      ν * ((28800 : K[X]) * u2 * w1 ^ 2) - Polynomial.C ν * ((2799360 :
      K[X]) * w1 ^ 2 * a2) - Polynomial.C μ * ((887040 : K[X]) * e1 ^ 4) -
      Polynomial.C μ * ((3548160 : K[X]) * e1 ^ 2 * u2) + Polynomial.C μ *
      ((52254720 : K[X]) * e1 ^ 2 * a2) - Polynomial.C μ * ((376320 :
      K[X]) * u2 ^ 2) + Polynomial.C μ * ((34836480 : K[X]) * u2 * a2) -
      Polynomial.C μ * ((15676416 : K[X]) * w1 ^ 3 * a1) - Polynomial.C μ
      * ((564350976 : K[X]) * a2 ^ 2) + Polynomial.C κ * ((859963392 :
      K[X]) * e1 * w1 ^ 2 * a1)) + h0 ^ 4 * ((12899450880 : K[X]) * e1 ^ 2
      * w1 * a0 - (2149908480 : K[X]) * e1 * e2 * a0 + (2149908480 : K[X])
      * u2 * w1 * a0 - (174142586880 : K[X]) * w1 * a0 * a2 - (87071293440
      : K[X]) * w1 * a1 ^ 2 - Polynomial.C ν₂ * ((1296 : K[X]) * e1 * w1 ^
      2) - Polynomial.C κ₅ * ((73728 : K[X]) * e1 ^ 2 * w1) + Polynomial.C
      κ₅ * ((12288 : K[X]) * e1 * e2) - Polynomial.C κ₅ * ((12288 : K[X])
      * u2 * w1) + Polynomial.C κ₅ * ((995328 : K[X]) * w1 * a2) -
      Polynomial.C ν * ((80640 : K[X]) * e1 ^ 3) - Polynomial.C ν *
      ((161280 : K[X]) * e1 * u2) + Polynomial.C ν * ((3732480 : K[X]) *
      e1 * a2) + Polynomial.C μ * ((313528320 : K[X]) * e1 * w1 * a1) -
      Polynomial.C μ * ((41803776 : K[X]) * e2 * a1) - Polynomial.C κ *
      ((859963392 : K[X]) * e1 ^ 2 * a1) - Polynomial.C κ * ((573308928 :
      K[X]) * u2 * a1) + Polynomial.C κ * ((23219011584 : K[X]) * a1 *
      a2)) + h0 ^ 5 * (Polynomial.C μ₃ * ((4 : K[X]) * w1 ^ 2) +
      Polynomial.C κ₇ * ((2304 : K[X]) * e1 * w1) - Polynomial.C κ₇ *
      ((384 : K[X]) * e2) + Polynomial.C ν₂ * ((2592 : K[X]) * e1 ^ 2) +
      Polynomial.C ν₂ * ((1728 : K[X]) * u2) - Polynomial.C ν₂ * ((93312 :
      K[X]) * a2) + Polynomial.C ν * ((11197440 : K[X]) * w1 * a1) +
      Polynomial.C μ * ((94058496 : K[X]) * w1 ^ 2 * a0) - Polynomial.C κ
      * ((5159780352 : K[X]) * e1 * w1 * a0) + Polynomial.C κ *
      ((859963392 : K[X]) * e2 * a0)) + h0 ^ 6 * ((522427760640 : K[X]) *
      a0 * a1 - Polynomial.C μ₃ * ((16 : K[X]) * e1) - Polynomial.C κ₅ *
      ((2985984 : K[X]) * a1) - Polynomial.C μ * ((376233984 : K[X]) * e1
      * a0)) + h0 ^ 7 * (-(Polynomial.C ν * ((67184640 : K[X]) * a0))) =
      Polynomial.C μ₄ * h0 ^ 7 := by
    apply mul_left_cancel₀ hh0
    linear_combination hR2q + (-((1215 : K[X]))) * hs4
  have h1ev := congrArg (fun t : K[X] => t.eval (-(d / c))) hu2
  simp only [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_ofNat] at h1ev
  rw [hroot, zero_mul] at h1ev
  have h1 : w1.eval (-(d / c)) *
      (e2.eval (-(d / c)) - 3 * e1.eval (-(d / c)) * w1.eval (-(d / c)))
      = 0 := by
    linear_combination h1ev
  have hv0 : e2.eval (-(d / c)) = 0 := by
    have hev3 := congrArg (fun t : K[X] => t.eval (-(d / c))) he3
    simp only [Polynomial.eval_mul] at hev3
    rw [hroot, zero_mul] at hev3
    exact hev3
  have hevR10 := congrArg (fun t : K[X] => t.eval (-(d / c))) hR10
  simp only [alignedTenthSquarePeeledRow610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hevR10
  rw [hroot] at hevR10
  have hhead10 :
      184320 * e1.eval (-(d / c)) ^ 2 * e2.eval (-(d / c)) ^ 2 - 44789760
      * e1.eval (-(d / c)) ^ 2 * a2.eval (-(d / c)) * w1.eval (-(d / c)) ^
      2 + 737280 * e1.eval (-(d / c)) ^ 2 * u2.eval (-(d / c)) * w1.eval
      (-(d / c)) ^ 2 + 2268 * e1.eval (-(d / c)) * μ * w1.eval (-(d / c))
      ^ 5 - 2488320 * e2.eval (-(d / c)) ^ 2 * a2.eval (-(d / c)) + 40960
      * e2.eval (-(d / c)) ^ 2 * u2.eval (-(d / c)) + 604661760 * a2.eval
      (-(d / c)) ^ 2 * w1.eval (-(d / c)) ^ 2 - 14929920 * a2.eval (-(d /
      c)) * u2.eval (-(d / c)) * w1.eval (-(d / c)) ^ 2 - 135 * s2.eval
      (-(d / c)) + 92160 * u2.eval (-(d / c)) ^ 2 * w1.eval (-(d / c)) ^ 2
      = 0 := by
    linear_combination hevR10
  have htie := alignedTenthSquareTieResolve_610 h1 hv0 hhead10
  have hevR3 := congrArg (fun t : K[X] => t.eval (-(d / c))) hR3q
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_neg,
    Polynomial.eval_ofNat] at hevR3
  rw [hroot] at hevR3
  have hhead11 :
      -61931520 * e1.eval (-(d / c)) ^ 4 * w1.eval (-(d / c)) ^ 3 +
      1433272320 * e1.eval (-(d / c)) ^ 2 * a2.eval (-(d / c)) * w1.eval
      (-(d / c)) ^ 3 - 22118400 * e1.eval (-(d / c)) ^ 2 * u2.eval (-(d /
      c)) * w1.eval (-(d / c)) ^ 3 + 655360 * e1.eval (-(d / c)) * e2.eval
      (-(d / c)) ^ 3 - 21168 * e1.eval (-(d / c)) * μ * w1.eval (-(d / c))
      ^ 6 - 9674588160 * a2.eval (-(d / c)) ^ 2 * w1.eval (-(d / c)) ^ 3 +
      238878720 * a2.eval (-(d / c)) * u2.eval (-(d / c)) * w1.eval (-(d /
      c)) ^ 3 + 2160 * s2.eval (-(d / c)) * w1.eval (-(d / c)) + 1215 *
      s4.eval (-(d / c)) - 1474560 * u2.eval (-(d / c)) ^ 2 * w1.eval (-(d
      / c)) ^ 3 = 0 := by
    linear_combination hevR3
  have hs4a : s4.eval (-(d / c)) = 0 :=
    alignedEleventhSquareTieResolve_610 h1 hv0 htie hhead11
  obtain ⟨s5, hs5⟩ := linearPolynomial_dvd_of_eval_eq_zero_810 h0
    s4 (-(d / c)) hdeg1 hroot hs4a
  have hmu8 : Polynomial.C μ * w1 ^ 8 = h0 ^ 2 * s5 := by
    rw [hs4, hs5]
    ring
  refine ⟨s4, s5, hs4, ?_, hs5, hmu8⟩
  simp only [alignedEleventhSquarePeeledRow610]
  linear_combination hR3q

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the odd exponent forces both the constant
and the eleventh defect to vanish: `κ₁₀ = 0` and `Λ ≡ 0`, exactly as
for `D`, `F`, `I`, and `L`. -/
theorem alignedNonsquareEleventh_defect_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    {H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₁₀ : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (hL2 :
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
          κ ^ 2 =
        Polynomial.C κ₁₀ * H ^ 55) :
    κ₁₀ = 0 ∧
      alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7
        κ = 0 := by
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set L : K[X] :=
    alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 κ
  have hdvd : (H ^ 27) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₁₀ * H, ?_⟩
    rw [hL2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₁₀ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 54 hH)
    have h54 := hL2
    rw [hG] at h54
    linear_combination h54
  have hGroot : ∀ a : K, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : K[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₁₀ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk10 : κ₁₀ = 0 := by
    have hev := congrArg (fun f : K[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hLzero : L = 0 := by
    have hsq : L ^ 2 = 0 := by
      rw [hL2, hk10]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk10, hLzero⟩

/-- Residue of the vanished nonsquare eleventh defect after the
carried divisor cascade (`t₁, t₂`, then the `p₂` divisor `u` squared,
then the `t₃` divisor cubed, then the `v` divisor squared) peels
`H²⁸`: an inhomogeneous relation on the carried witnesses only — no
new witness and no `q`-coefficient.  On the face it vanishes, and its
root evaluation is the first `p₀`-loaded root relation of the aligned
nonsquare tower. -/
def alignedEleventhNonsquareResidue610 {K : Type*} [CommRing K]
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₅ κ₇ : K) : K[X] :=
  ((80640 : K[X]) * t1 ^ 4 * t3 - (46080 : K[X]) * t1 ^ 3 * v - (46080 :
    K[X]) * t1 ^ 2 * u * t3 + (23040 : K[X]) * t1 ^ 2 * t3 ^ 2 * g1 +
    (23040 : K[X]) * t1 * u * v - (23040 : K[X]) * t1 * t3 * v * g1 +
    (16796160 : K[X]) * t1 * t3 * a0 + (3840 : K[X]) * u ^ 2 * t3 - (3840
    : K[X]) * u * t3 ^ 2 * g1 + (1280 : K[X]) * t3 ^ 3 * g1 ^ 2 + (11520 :
    K[X]) * v ^ 2 * g1 - (16796160 : K[X]) * v * a0 + Polynomial.C κ₇ *
    ((3 : K[X]) * t3) - Polynomial.C κ₅ * ((96 : K[X]) * t1 * t3) +
    Polynomial.C κ₅ * ((96 : K[X]) * v) - Polynomial.C κ * ((46080 : K[X])
    * t1 ^ 3 * t3) + Polynomial.C κ * ((27648 : K[X]) * t1 ^ 2 * v) +
    Polynomial.C κ * ((18432 : K[X]) * t1 * u * t3) - Polynomial.C κ *
    ((9216 : K[X]) * t1 * t3 ^ 2 * g1) - Polynomial.C κ * ((9216 : K[X]) *
    u * v) + Polynomial.C κ * ((9216 : K[X]) * t3 * v * g1) - Polynomial.C
    κ * ((6718464 : K[X]) * t3 * a0)) + H * (-((5120 : K[X]) * t1 * t3 ^
    3) + (3840 : K[X]) * t3 ^ 2 * v + Polynomial.C κ * ((1024 : K[X]) * t3
    ^ 3))

set_option maxHeartbeats 6400000000 in
/-- Descent of the consumed degree-`4` row in the nonsquare chamber:
the eleventh defect vanishes identically, the `H²²`-peeled core
absorbs the undecic head through the seventh-face divisibilities,
peeling `H²` onto the squared carried `p₂` divisor, one `H` onto the
cubed carried `t₃` divisor, one `H` onto the squared carried `v`
divisor, and `H²` beyond — bottoming out on the residue relation
WITHOUT any new witness: every divisor of the cascade is carried. -/
theorem alignedNonsquareEleventh_descent_610 {K : Type*}
    [Field K] [CharZero K]
    {H g1 f t1 t2 u t3 v a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6 b7 :
      K[X]}
    {κ κ₅ κ₇ : K}
    (hH : H ≠ 0)
    (hg1 : a5 = H ^ 2 * g1) (hf : a4 = H * f)
    (hD0 : alignedThirdDefect610 H a3 a4 a5 b7 κ = 0)
    (hF0 : alignedFifthDefect610 H a1 a2 a3 a4 a5 b5 b6 b7 κ = 0)
    (hG : alignedSixthDefect610 H a0 a1 a2 a3 a4 a5 b4 b5 b6 b7 κ =
      Polynomial.C κ₅ * H ^ 15)
    (hI0 :
      alignedSeventhDefect610 H a0 a1 a2 a3 a4 a5 b3 b4 b5 b6 b7 κ = 0)
    (hJ : alignedEighthDefect610 H a0 a1 a2 a3 a4 a5 b2 b3 b4 b5 b6 b7
        κ = Polynomial.C κ₇ * H ^ 20)
    (hL0 : alignedNinthDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 b6
        b7 κ = 0)
    (hLam0 : alignedEleventhDefect610 H a0 a1 a2 a3 a4 a5 b1 b2 b3 b4
        b5 b6 b7 κ = 0)
    (ht1 : (3 : K[X]) * f - g1 ^ 2 = H * t1)
    (ht2 : (27 : K[X]) * a3 - g1 ^ 3 = H * t2)
    (hu : (81 : K[X]) * a2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
      H * u)
    (ht3 : t2 - (6 : K[X]) * g1 * t1 = H * t3)
    (hv : (243 : K[X]) * a1 - g1 * u = H * v) :
    alignedEleventhNonsquareResidue610 H g1 t1 u t3 v a0 κ κ₅ κ₇ =
      0 := by
  have hL' := hLam0
  simp only [alignedEleventhDefect610] at hL'
  rw [hD0, hF0, hG, hI0, hJ, hL0, hg1, hf] at hL'
  have hcore :
      ((15049359360 : K[X]) * f ^ 5 * g1 - (22574039040 : K[X]) * f ^ 4 *
      a3 - (54344908800 : K[X]) * f ^ 4 * g1 ^ 3 + (150493593600 : K[X]) *
      f ^ 3 * a3 * g1 ^ 2 + (57967902720 : K[X]) * f ^ 3 * g1 ^ 5 -
      (135444234240 : K[X]) * f ^ 2 * a3 ^ 2 * g1 - (163034726400 : K[X])
      * f ^ 2 * a3 * g1 ^ 4 - (26223575040 : K[X]) * f ^ 2 * g1 ^ 7 +
      (38698352640 : K[X]) * f * a3 ^ 3 + (150493593600 : K[X]) * f * a3 ^
      2 * g1 ^ 3 + (57967902720 : K[X]) * f * a3 * g1 ^ 6 + (5341839360 :
      K[X]) * f * g1 ^ 9 - (45148078080 : K[X]) * a3 ^ 3 * g1 ^ 2 -
      (32606945280 : K[X]) * a3 ^ 2 * g1 ^ 5 - (6555893760 : K[X]) * a3 *
      g1 ^ 8 - (404684800 : K[X]) * g1 ^ 11) + H * (-((90296156160 : K[X])
      * f ^ 3 * g1 * a2) + (116095057920 : K[X]) * f ^ 2 * a3 * a2 +
      (150493593600 : K[X]) * f ^ 2 * g1 ^ 3 * a2 - (270888468480 : K[X])
      * f * a3 * g1 ^ 2 * a2 - (65213890560 : K[X]) * f * g1 ^ 5 * a2 +
      (116095057920 : K[X]) * a3 ^ 2 * g1 * a2 + (75246796800 : K[X]) * a3
      * g1 ^ 4 * a2 + (8281128960 : K[X]) * g1 ^ 7 * a2 - Polynomial.C κ *
      ((2866544640 : K[X]) * f ^ 4 * g1) + Polynomial.C κ * ((4299816960 :
      K[X]) * f ^ 3 * a3) + Polynomial.C κ * ((7007109120 : K[X]) * f ^ 3
      * g1 ^ 3) - Polynomial.C κ * ((17199267840 : K[X]) * f ^ 2 * a3 * g1
      ^ 2) - Polynomial.C κ * ((4904976384 : K[X]) * f ^ 2 * g1 ^ 5) +
      Polynomial.C κ * ((12899450880 : K[X]) * f * a3 ^ 2 * g1) +
      Polynomial.C κ * ((10510663680 : K[X]) * f * a3 * g1 ^ 4) +
      Polynomial.C κ * ((1323565056 : K[X]) * f * g1 ^ 7) - Polynomial.C κ
      * ((2579890176 : K[X]) * a3 ^ 3) - Polynomial.C κ * ((5733089280 :
      K[X]) * a3 ^ 2 * g1 ^ 3) - Polynomial.C κ * ((1634992128 : K[X]) *
      a3 * g1 ^ 6) - Polynomial.C κ * ((122552320 : K[X]) * g1 ^ 9)) + H ^
      2 * ((38698352640 : K[X]) * f ^ 3 * a1 - (135444234240 : K[X]) * f ^
      2 * g1 ^ 2 * a1 + (232190115840 : K[X]) * f * a3 * g1 * a1 +
      (75246796800 : K[X]) * f * g1 ^ 4 * a1 + (116095057920 : K[X]) * f *
      g1 * a2 ^ 2 - (87071293440 : K[X]) * a3 ^ 2 * a1 - (90296156160 :
      K[X]) * a3 * g1 ^ 3 * a1 - (87071293440 : K[X]) * a3 * a2 ^ 2 -
      (10868981760 : K[X]) * g1 ^ 6 * a1 - (45148078080 : K[X]) * g1 ^ 3 *
      a2 ^ 2 + Polynomial.C κ * ((12899450880 : K[X]) * f ^ 2 * g1 * a2) -
      Polynomial.C κ * ((15479341056 : K[X]) * f * a3 * a2) - Polynomial.C
      κ * ((11466178560 : K[X]) * f * g1 ^ 3 * a2) + Polynomial.C κ *
      ((12899450880 : K[X]) * a3 * g1 ^ 2 * a2) + Polynomial.C κ *
      ((2102132736 : K[X]) * g1 ^ 5 * a2)) + H ^ 3 * ((116095057920 :
      K[X]) * f ^ 2 * g1 * a0 - (174142586880 : K[X]) * f * a3 * a0 -
      (90296156160 : K[X]) * f * g1 ^ 3 * a0 - (174142586880 : K[X]) * f *
      a1 * a2 + (116095057920 : K[X]) * a3 * g1 ^ 2 * a0 + (15049359360 :
      K[X]) * g1 ^ 5 * a0 + (116095057920 : K[X]) * g1 ^ 2 * a1 * a2 -
      Polynomial.C κ₅ * ((663552 : K[X]) * f ^ 2 * g1) + Polynomial.C κ₅ *
      ((995328 : K[X]) * f * a3) + Polynomial.C κ₅ * ((516096 : K[X]) * f
      * g1 ^ 3) - Polynomial.C κ₅ * ((663552 : K[X]) * a3 * g1 ^ 2) -
      Polynomial.C κ₅ * ((86016 : K[X]) * g1 ^ 5) - Polynomial.C κ *
      ((7739670528 : K[X]) * f ^ 2 * a1) + Polynomial.C κ * ((12899450880
      : K[X]) * f * g1 ^ 2 * a1) - Polynomial.C κ * ((15479341056 : K[X])
      * a3 * g1 * a1) - Polynomial.C κ * ((2866544640 : K[X]) * g1 ^ 4 *
      a1) - Polynomial.C κ * ((7739670528 : K[X]) * g1 * a2 ^ 2)) + H ^ 4
      * (-((174142586880 : K[X]) * g1 * a0 * a2) - (87071293440 : K[X]) *
      g1 * a1 ^ 2 + Polynomial.C κ₇ * ((6912 : K[X]) * f * g1) -
      Polynomial.C κ₇ * ((10368 : K[X]) * a3) - Polynomial.C κ₇ * ((1920 :
      K[X]) * g1 ^ 3) + Polynomial.C κ₅ * ((995328 : K[X]) * g1 * a2) -
      Polynomial.C κ * ((15479341056 : K[X]) * f * g1 * a0) + Polynomial.C
      κ * ((23219011584 : K[X]) * a3 * a0) + Polynomial.C κ * ((4299816960
      : K[X]) * g1 ^ 3 * a0) + Polynomial.C κ * ((23219011584 : K[X]) * a1
      * a2)) + H ^ 5 * ((522427760640 : K[X]) * a0 * a1 - Polynomial.C κ₅
      * ((2985984 : K[X]) * a1)) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 22 hH)
    linear_combination hL'
  have hR2n :
      (-((13271040 : K[X]) * t1 ^ 2 * g1 ^ 7) + (8847360 : K[X]) * t1 * t2
      * g1 ^ 6 - (716636160 : K[X]) * t1 * g1 ^ 5 * a2 - (1474560 : K[X])
      * t2 ^ 2 * g1 ^ 5 + (238878720 : K[X]) * t2 * g1 ^ 4 * a2 -
      (9674588160 : K[X]) * g1 ^ 3 * a2 ^ 2) + H * ((247726080 : K[X]) *
      t1 ^ 3 * g1 ^ 5 - (154828800 : K[X]) * t1 ^ 2 * t2 * g1 ^ 4 +
      (7166361600 : K[X]) * t1 ^ 2 * g1 ^ 3 * a2 + (29491200 : K[X]) * t1
      * t2 ^ 2 * g1 ^ 3 - (2388787200 : K[X]) * t1 * t2 * g1 ^ 2 * a2 +
      (2149908480 : K[X]) * t1 * g1 ^ 4 * a1 + (38698352640 : K[X]) * t1 *
      g1 * a2 ^ 2 - (1638400 : K[X]) * t2 ^ 3 * g1 ^ 2 + (159252480 :
      K[X]) * t2 ^ 2 * g1 * a2 - (716636160 : K[X]) * t2 * g1 ^ 3 * a1 -
      (3224862720 : K[X]) * t2 * a2 ^ 2 + (58047528960 : K[X]) * g1 ^ 2 *
      a1 * a2 - Polynomial.C κ * ((31850496 : K[X]) * t1 ^ 2 * g1 ^ 5) +
      Polynomial.C κ * ((17694720 : K[X]) * t1 * t2 * g1 ^ 4) -
      Polynomial.C κ * ((1146617856 : K[X]) * t1 * g1 ^ 3 * a2) -
      Polynomial.C κ * ((2359296 : K[X]) * t2 ^ 2 * g1 ^ 3) + Polynomial.C
      κ * ((286654464 : K[X]) * t2 * g1 ^ 2 * a2) - Polynomial.C κ *
      ((7739670528 : K[X]) * g1 * a2 ^ 2)) + H ^ 2 * (-((371589120 : K[X])
      * t1 ^ 4 * g1 ^ 3) + (165150720 : K[X]) * t1 ^ 3 * t2 * g1 ^ 2 -
      (3344302080 : K[X]) * t1 ^ 3 * g1 * a2 - (20643840 : K[X]) * t1 ^ 2
      * t2 ^ 2 * g1 + (477757440 : K[X]) * t1 ^ 2 * t2 * a2 - (10749542400
      : K[X]) * t1 ^ 2 * g1 ^ 2 * a1 + (655360 : K[X]) * t1 * t2 ^ 3 +
      (2866544640 : K[X]) * t1 * t2 * g1 * a1 - (6449725440 : K[X]) * t1 *
      g1 ^ 3 * a0 - (58047528960 : K[X]) * t1 * a1 * a2 - (119439360 :
      K[X]) * t2 ^ 2 * a1 + (2149908480 : K[X]) * t2 * g1 ^ 2 * a0 -
      (174142586880 : K[X]) * g1 * a0 * a2 - (87071293440 : K[X]) * g1 *
      a1 ^ 2 + Polynomial.C κ₅ * ((36864 : K[X]) * t1 * g1 ^ 3) -
      Polynomial.C κ₅ * ((12288 : K[X]) * t2 * g1 ^ 2) + Polynomial.C κ₅ *
      ((995328 : K[X]) * g1 * a2) + Polynomial.C κ * ((123863040 : K[X]) *
      t1 ^ 3 * g1 ^ 3) - Polynomial.C κ * ((53084160 : K[X]) * t1 ^ 2 * t2
      * g1 ^ 2) + Polynomial.C κ * ((1433272320 : K[X]) * t1 ^ 2 * g1 *
      a2) + Polynomial.C κ * ((5898240 : K[X]) * t1 * t2 ^ 2 * g1) -
      Polynomial.C κ * ((191102976 : K[X]) * t1 * t2 * a2) + Polynomial.C
      κ * ((2579890176 : K[X]) * t1 * g1 ^ 2 * a1) - Polynomial.C κ *
      ((131072 : K[X]) * t2 ^ 3) - Polynomial.C κ * ((573308928 : K[X]) *
      t2 * g1 * a1) + Polynomial.C κ * ((23219011584 : K[X]) * a1 * a2)) +
      H ^ 3 * ((61931520 : K[X]) * t1 ^ 5 * g1 - (10321920 : K[X]) * t1 ^
      4 * t2 + (1433272320 : K[X]) * t1 ^ 3 * a1 + (12899450880 : K[X]) *
      t1 ^ 2 * g1 * a0 - (2149908480 : K[X]) * t1 * t2 * a0 +
      (522427760640 : K[X]) * a0 * a1 + Polynomial.C κ₇ * ((2304 : K[X]) *
      t1 * g1) - Polynomial.C κ₇ * ((384 : K[X]) * t2) - Polynomial.C κ₅ *
      ((73728 : K[X]) * t1 ^ 2 * g1) + Polynomial.C κ₅ * ((12288 : K[X]) *
      t1 * t2) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) - Polynomial.C
      κ * ((35389440 : K[X]) * t1 ^ 4 * g1) + Polynomial.C κ * ((5898240 :
      K[X]) * t1 ^ 3 * t2) - Polynomial.C κ * ((859963392 : K[X]) * t1 ^ 2
      * a1) - Polynomial.C κ * ((5159780352 : K[X]) * t1 * g1 * a0) +
      Polynomial.C κ * ((859963392 : K[X]) * t2 * a0)) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hH)
    linear_combination hcore + (-((61931520 : K[X]) * t1 ^ 4 * g1 * H ^ 4 - (423198720 : K[X]) * t1 ^
      3 * g1 ^ 3 * H ^ 3 + (185794560 : K[X]) * t1 ^ 3 * g1 * f * H ^ 3 -
      (278691840 : K[X]) * t1 ^ 3 * a3 * H ^ 3 + (505774080 : K[X]) * t1 ^
      2 * g1 ^ 5 * H ^ 2 - (1455390720 : K[X]) * t1 ^ 2 * g1 ^ 3 * f * H ^
      2 + (4737761280 : K[X]) * t1 ^ 2 * g1 ^ 2 * a3 * H ^ 2 + (557383680
      : K[X]) * t1 ^ 2 * g1 * f ^ 2 * H ^ 2 - (3344302080 : K[X]) * t1 ^ 2
      * g1 * a2 * H ^ 3 - (836075520 : K[X]) * t1 ^ 2 * f * a3 * H ^ 2 +
      (1433272320 : K[X]) * t1 ^ 2 * a1 * H ^ 4 - (384860160 : K[X]) * t1
      * g1 ^ 7 * H + (2972712960 : K[X]) * t1 * g1 ^ 5 * f * H -
      (7803371520 : K[X]) * t1 * g1 ^ 4 * a3 * H - (4923555840 : K[X]) *
      t1 * g1 ^ 3 * f ^ 2 * H + (10032906240 : K[X]) * t1 * g1 ^ 3 * a2 *
      H ^ 2 + (15049359360 : K[X]) * t1 * g1 ^ 2 * f * a3 * H -
      (12182814720 : K[X]) * t1 * g1 ^ 2 * a1 * H ^ 3 + (1672151040 :
      K[X]) * t1 * g1 * f ^ 3 * H - (10032906240 : K[X]) * t1 * g1 * f *
      a2 * H ^ 2 - (15049359360 : K[X]) * t1 * g1 * a3 ^ 2 * H +
      (12899450880 : K[X]) * t1 * g1 * a0 * H ^ 4 - (2508226560 : K[X]) *
      t1 * f ^ 2 * a3 * H + (4299816960 : K[X]) * t1 * f * a1 * H ^ 3 +
      (12899450880 : K[X]) * t1 * a3 * a2 * H ^ 2 + (404848640 : K[X]) *
      g1 ^ 9 - (4127293440 : K[X]) * g1 ^ 7 * f + (6502809600 : K[X]) * g1
      ^ 6 * a3 + (13841694720 : K[X]) * g1 ^ 5 * f ^ 2 - (8360755200 :
      K[X]) * g1 ^ 5 * a2 * H - (38459473920 : K[X]) * g1 ^ 4 * f * a3 +
      (11466178560 : K[X]) * g1 ^ 4 * a1 * H ^ 2 - (16442818560 : K[X]) *
      g1 ^ 3 * f ^ 3 + (40131624960 : K[X]) * g1 ^ 3 * f * a2 * H +
      (35115171840 : K[X]) * g1 ^ 3 * a3 ^ 2 - (17199267840 : K[X]) * g1 ^
      3 * a0 * H ^ 3 + (47656304640 : K[X]) * g1 ^ 2 * f ^ 2 * a3 -
      (40848261120 : K[X]) * g1 ^ 2 * f * a1 * H ^ 2 - (77396705280 :
      K[X]) * g1 ^ 2 * a3 * a2 * H + (5016453120 : K[X]) * g1 * f ^ 4 -
      (30098718720 : K[X]) * g1 * f ^ 2 * a2 * H - (45148078080 : K[X]) *
      g1 * f * a3 ^ 2 + (38698352640 : K[X]) * g1 * f * a0 * H ^ 3 +
      (77396705280 : K[X]) * g1 * a3 * a1 * H ^ 2 + (38698352640 : K[X]) *
      g1 * a2 ^ 2 * H ^ 2 - (7524679680 : K[X]) * f ^ 3 * a3 +
      (12899450880 : K[X]) * f ^ 2 * a1 * H ^ 2 + (38698352640 : K[X]) * f
      * a3 * a2 * H + (12899450880 : K[X]) * a3 ^ 3 - (58047528960 : K[X])
      * a3 * a0 * H ^ 3 - (58047528960 : K[X]) * a1 * a2 * H ^ 3 +
      Polynomial.C κ₇ * ((2304 : K[X]) * g1 * H ^ 4) - Polynomial.C κ₅ *
      ((73728 : K[X]) * t1 * g1 * H ^ 4) + Polynomial.C κ₅ * ((98304 :
      K[X]) * g1 ^ 3 * H ^ 3) - Polynomial.C κ₅ * ((221184 : K[X]) * g1 *
      f * H ^ 3) + Polynomial.C κ₅ * ((331776 : K[X]) * a3 * H ^ 3) -
      Polynomial.C κ * ((35389440 : K[X]) * t1 ^ 3 * g1 * H ^ 4) +
      Polynomial.C κ * ((153354240 : K[X]) * t1 ^ 2 * g1 ^ 3 * H ^ 3) -
      Polynomial.C κ * ((106168320 : K[X]) * t1 ^ 2 * g1 * f * H ^ 3) +
      Polynomial.C κ * ((159252480 : K[X]) * t1 ^ 2 * a3 * H ^ 3) -
      Polynomial.C κ * ((132120576 : K[X]) * t1 * g1 ^ 5 * H ^ 2) +
      Polynomial.C κ * ((566231040 : K[X]) * t1 * g1 ^ 3 * f * H ^ 2) -
      Polynomial.C κ * ((1592524800 : K[X]) * t1 * g1 ^ 2 * a3 * H ^ 2) -
      Polynomial.C κ * ((318504960 : K[X]) * t1 * g1 * f ^ 2 * H ^ 2) +
      Polynomial.C κ * ((1433272320 : K[X]) * t1 * g1 * a2 * H ^ 3) +
      Polynomial.C κ * ((477757440 : K[X]) * t1 * f * a3 * H ^ 2) -
      Polynomial.C κ * ((859963392 : K[X]) * t1 * a1 * H ^ 4) +
      Polynomial.C κ * ((120324096 : K[X]) * g1 ^ 7 * H) - Polynomial.C κ
      * ((962592768 : K[X]) * g1 ^ 5 * f * H) + Polynomial.C κ *
      ((1751777280 : K[X]) * g1 ^ 4 * a3 * H) + Polynomial.C κ *
      ((2017198080 : K[X]) * g1 ^ 3 * f ^ 2 * H) - Polynomial.C κ *
      ((2388787200 : K[X]) * g1 ^ 3 * a2 * H ^ 2) - Polynomial.C κ *
      ((5255331840 : K[X]) * g1 ^ 2 * f * a3 * H) + Polynomial.C κ *
      ((3439853568 : K[X]) * g1 ^ 2 * a1 * H ^ 3) - Polynomial.C κ *
      ((955514880 : K[X]) * g1 * f ^ 3 * H) + Polynomial.C κ *
      ((4299816960 : K[X]) * g1 * f * a2 * H ^ 2) + Polynomial.C κ *
      ((4299816960 : K[X]) * g1 * a3 ^ 2 * H) - Polynomial.C κ *
      ((5159780352 : K[X]) * g1 * a0 * H ^ 4) + Polynomial.C κ *
      ((1433272320 : K[X]) * f ^ 2 * a3 * H) - Polynomial.C κ *
      ((2579890176 : K[X]) * f * a1 * H ^ 3) - Polynomial.C κ *
      ((5159780352 : K[X]) * a3 * a2 * H ^ 2))) * ht1 + (-(-((10321920 :
      K[X]) * t1 ^ 4 * H ^ 4) + (165150720 : K[X]) * t1 ^ 3 * g1 ^ 2 * H ^
      3 - (20643840 : K[X]) * t1 ^ 2 * t2 * g1 * H ^ 3 - (134184960 :
      K[X]) * t1 ^ 2 * g1 ^ 4 * H ^ 2 - (557383680 : K[X]) * t1 ^ 2 * g1 *
      a3 * H ^ 2 + (477757440 : K[X]) * t1 ^ 2 * a2 * H ^ 3 + (655360 :
      K[X]) * t1 * t2 ^ 2 * H ^ 3 + (28835840 : K[X]) * t1 * t2 * g1 ^ 3 *
      H ^ 2 + (17694720 : K[X]) * t1 * t2 * a3 * H ^ 2 - (19988480 : K[X])
      * t1 * g1 ^ 6 * H + (760872960 : K[X]) * t1 * g1 ^ 3 * a3 * H -
      (2388787200 : K[X]) * t1 * g1 ^ 2 * a2 * H ^ 2 + (2866544640 : K[X])
      * t1 * g1 * a1 * H ^ 3 + (477757440 : K[X]) * t1 * a3 ^ 2 * H -
      (2149908480 : K[X]) * t1 * a0 * H ^ 4 - (1638400 : K[X]) * t2 ^ 2 *
      g1 ^ 2 * H ^ 2 + (163840 : K[X]) * t2 * g1 ^ 5 * H - (44236800 :
      K[X]) * t2 * g1 ^ 2 * a3 * H + (159252480 : K[X]) * t2 * g1 * a2 * H
      ^ 2 - (119439360 : K[X]) * t2 * a1 * H ^ 3 - (163840 : K[X]) * g1 ^
      8 + (48660480 : K[X]) * g1 ^ 5 * a3 + (79626240 : K[X]) * g1 ^ 4 *
      a2 * H - (597196800 : K[X]) * g1 ^ 3 * a1 * H ^ 2 - (1194393600 :
      K[X]) * g1 ^ 2 * a3 ^ 2 + (2149908480 : K[X]) * g1 ^ 2 * a0 * H ^ 3
      + (4299816960 : K[X]) * g1 * a3 * a2 * H - (3224862720 : K[X]) * a3
      * a1 * H ^ 2 - (3224862720 : K[X]) * a2 ^ 2 * H ^ 2 - Polynomial.C
      κ₇ * ((384 : K[X]) * H ^ 4) + Polynomial.C κ₅ * ((12288 : K[X]) * t1
      * H ^ 4) - Polynomial.C κ₅ * ((12288 : K[X]) * g1 ^ 2 * H ^ 3) +
      Polynomial.C κ * ((5898240 : K[X]) * t1 ^ 3 * H ^ 4) - Polynomial.C
      κ * ((53084160 : K[X]) * t1 ^ 2 * g1 ^ 2 * H ^ 3) + Polynomial.C κ *
      ((5898240 : K[X]) * t1 * t2 * g1 * H ^ 3) + Polynomial.C κ *
      ((11796480 : K[X]) * t1 * g1 ^ 4 * H ^ 2) + Polynomial.C κ *
      ((159252480 : K[X]) * t1 * g1 * a3 * H ^ 2) - Polynomial.C κ *
      ((191102976 : K[X]) * t1 * a2 * H ^ 3) - Polynomial.C κ * ((131072 :
      K[X]) * t2 ^ 2 * H ^ 3) - Polynomial.C κ * ((2228224 : K[X]) * t2 *
      g1 ^ 3 * H ^ 2) - Polynomial.C κ * ((3538944 : K[X]) * t2 * a3 * H ^
      2) + Polynomial.C κ * ((2228224 : K[X]) * g1 ^ 6 * H) - Polynomial.C
      κ * ((56623104 : K[X]) * g1 ^ 3 * a3 * H) + Polynomial.C κ *
      ((286654464 : K[X]) * g1 ^ 2 * a2 * H ^ 2) - Polynomial.C κ *
      ((573308928 : K[X]) * g1 * a1 * H ^ 3) - Polynomial.C κ * ((95551488
      : K[X]) * a3 ^ 2 * H) + Polynomial.C κ * ((859963392 : K[X]) * a0 *
      H ^ 4))) * ht2
  have hR3n :
      ((35389440 : K[X]) * t1 ^ 3 * g1 ^ 5 - (17694720 : K[X]) * t1 ^ 2 *
      t2 * g1 ^ 4 + (2949120 : K[X]) * t1 * t2 ^ 2 * g1 ^ 3 - (163840 :
      K[X]) * t2 ^ 3 * g1 ^ 2) + H * (-((247726080 : K[X]) * t1 ^ 4 * g1 ^
      3) + (106168320 : K[X]) * t1 ^ 3 * t2 * g1 ^ 2 - (14745600 : K[X]) *
      t1 ^ 2 * t2 ^ 2 * g1 + (53084160 : K[X]) * t1 ^ 2 * u * g1 ^ 3 -
      (8599633920 : K[X]) * t1 ^ 2 * g1 ^ 2 * a1 + (655360 : K[X]) * t1 *
      t2 ^ 3 - (14745600 : K[X]) * t1 * t2 * u * g1 ^ 2 + (2149908480 :
      K[X]) * t1 * t2 * g1 * a1 + (983040 : K[X]) * t2 ^ 2 * u * g1 -
      (119439360 : K[X]) * t2 ^ 2 * a1 - (1474560 : K[X]) * u ^ 2 * g1 ^ 3
      + (716636160 : K[X]) * u * g1 ^ 2 * a1 - (87071293440 : K[X]) * g1 *
      a1 ^ 2 + Polynomial.C κ * ((70778880 : K[X]) * t1 ^ 3 * g1 ^ 3) -
      Polynomial.C κ * ((28311552 : K[X]) * t1 ^ 2 * t2 * g1 ^ 2) +
      Polynomial.C κ * ((3538944 : K[X]) * t1 * t2 ^ 2 * g1) -
      Polynomial.C κ * ((7077888 : K[X]) * t1 * u * g1 ^ 3) + Polynomial.C
      κ * ((1719926784 : K[X]) * t1 * g1 ^ 2 * a1) - Polynomial.C κ *
      ((131072 : K[X]) * t2 ^ 3) + Polynomial.C κ * ((1179648 : K[X]) * t2
      * u * g1 ^ 2) - Polynomial.C κ * ((286654464 : K[X]) * t2 * g1 *
      a1)) + H ^ 2 * ((61931520 : K[X]) * t1 ^ 5 * g1 - (10321920 : K[X])
      * t1 ^ 4 * t2 - (41287680 : K[X]) * t1 ^ 3 * u * g1 + (1433272320 :
      K[X]) * t1 ^ 3 * a1 + (5898240 : K[X]) * t1 ^ 2 * t2 * u +
      (12899450880 : K[X]) * t1 ^ 2 * g1 * a0 - (2149908480 : K[X]) * t1 *
      t2 * a0 + (5898240 : K[X]) * t1 * u ^ 2 * g1 - (716636160 : K[X]) *
      t1 * u * a1 - (491520 : K[X]) * t2 * u ^ 2 - (2149908480 : K[X]) * u
      * g1 * a0 + (522427760640 : K[X]) * a0 * a1 + Polynomial.C κ₇ *
      ((2304 : K[X]) * t1 * g1) - Polynomial.C κ₇ * ((384 : K[X]) * t2) -
      Polynomial.C κ₅ * ((73728 : K[X]) * t1 ^ 2 * g1) + Polynomial.C κ₅ *
      ((12288 : K[X]) * t1 * t2) + Polynomial.C κ₅ * ((12288 : K[X]) * u *
      g1) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) - Polynomial.C κ *
      ((35389440 : K[X]) * t1 ^ 4 * g1) + Polynomial.C κ * ((5898240 :
      K[X]) * t1 ^ 3 * t2) + Polynomial.C κ * ((17694720 : K[X]) * t1 ^ 2
      * u * g1) - Polynomial.C κ * ((859963392 : K[X]) * t1 ^ 2 * a1) -
      Polynomial.C κ * ((2359296 : K[X]) * t1 * t2 * u) - Polynomial.C κ *
      ((5159780352 : K[X]) * t1 * g1 * a0) + Polynomial.C κ * ((859963392
      : K[X]) * t2 * a0) - Polynomial.C κ * ((1179648 : K[X]) * u ^ 2 *
      g1) + Polynomial.C κ * ((286654464 : K[X]) * u * a1)) = 0 := by
    apply mul_left_cancel₀ hH
    linear_combination hR2n + (-(-((41287680 : K[X]) * t1 ^ 3 * g1 * H ^ 2) + (5898240 : K[X]) * t1 ^
      2 * t2 * H ^ 2 + (70778880 : K[X]) * t1 ^ 2 * g1 ^ 3 * H - (22118400
      : K[X]) * t1 * t2 * g1 ^ 2 * H + (5898240 : K[X]) * t1 * u * g1 * H
      ^ 2 - (4423680 : K[X]) * t1 * g1 ^ 5 + (477757440 : K[X]) * t1 * g1
      * a2 * H - (716636160 : K[X]) * t1 * a1 * H ^ 2 + (1474560 : K[X]) *
      t2 ^ 2 * g1 * H - (491520 : K[X]) * t2 * u * H ^ 2 + (1474560 :
      K[X]) * t2 * g1 ^ 4 - (39813120 : K[X]) * t2 * a2 * H - (1474560 :
      K[X]) * u * g1 ^ 3 * H - (119439360 : K[X]) * g1 ^ 3 * a2 +
      (716636160 : K[X]) * g1 ^ 2 * a1 * H - (2149908480 : K[X]) * g1 * a0
      * H ^ 2 + Polynomial.C κ₅ * ((12288 : K[X]) * g1 * H ^ 2) +
      Polynomial.C κ * ((17694720 : K[X]) * t1 ^ 2 * g1 * H ^ 2) -
      Polynomial.C κ * ((2359296 : K[X]) * t1 * t2 * H ^ 2) - Polynomial.C
      κ * ((10616832 : K[X]) * t1 * g1 ^ 3 * H) + Polynomial.C κ *
      ((2359296 : K[X]) * t2 * g1 ^ 2 * H) - Polynomial.C κ * ((1179648 :
      K[X]) * u * g1 * H ^ 2) - Polynomial.C κ * ((95551488 : K[X]) * g1 *
      a2 * H) + Polynomial.C κ * ((286654464 : K[X]) * a1 * H ^ 2))) * hu
  have hR4n :
      (-((1474560 : K[X]) * u ^ 2 * g1 ^ 3) + (716636160 : K[X]) * u * g1
      ^ 2 * a1 - (87071293440 : K[X]) * g1 * a1 ^ 2) + H * (-((5898240 :
      K[X]) * t1 ^ 3 * u * g1) + (1433272320 : K[X]) * t1 ^ 3 * a1 +
      (2949120 : K[X]) * t1 * u ^ 2 * g1 - (2949120 : K[X]) * t1 * u * t3
      * g1 ^ 2 - (716636160 : K[X]) * t1 * u * a1 + (716636160 : K[X]) *
      t1 * t3 * g1 * a1 - (2149908480 : K[X]) * u * g1 * a0 +
      (522427760640 : K[X]) * a0 * a1 + Polynomial.C κ₅ * ((12288 : K[X])
      * u * g1) - Polynomial.C κ₅ * ((2985984 : K[X]) * a1) + Polynomial.C
      κ * ((3538944 : K[X]) * t1 ^ 2 * u * g1) - Polynomial.C κ *
      ((859963392 : K[X]) * t1 ^ 2 * a1) - Polynomial.C κ * ((1179648 :
      K[X]) * u ^ 2 * g1) + Polynomial.C κ * ((1179648 : K[X]) * u * t3 *
      g1 ^ 2) + Polynomial.C κ * ((286654464 : K[X]) * u * a1) -
      Polynomial.C κ * ((286654464 : K[X]) * t3 * g1 * a1)) + H ^ 2 *
      (-((10321920 : K[X]) * t1 ^ 4 * t3) + (5898240 : K[X]) * t1 ^ 2 * u
      * t3 - (2949120 : K[X]) * t1 ^ 2 * t3 ^ 2 * g1 - (2149908480 : K[X])
      * t1 * t3 * a0 - (491520 : K[X]) * u ^ 2 * t3 + (983040 : K[X]) * u
      * t3 ^ 2 * g1 - (163840 : K[X]) * t3 ^ 3 * g1 ^ 2 - (119439360 :
      K[X]) * t3 ^ 2 * a1 - Polynomial.C κ₇ * ((384 : K[X]) * t3) +
      Polynomial.C κ₅ * ((12288 : K[X]) * t1 * t3) + Polynomial.C κ *
      ((5898240 : K[X]) * t1 ^ 3 * t3) - Polynomial.C κ * ((2359296 :
      K[X]) * t1 * u * t3) + Polynomial.C κ * ((1179648 : K[X]) * t1 * t3
      ^ 2 * g1) + Polynomial.C κ * ((859963392 : K[X]) * t3 * a0)) + H ^ 3
      * ((655360 : K[X]) * t1 * t3 ^ 3 - Polynomial.C κ * ((131072 : K[X])
      * t3 ^ 3)) = 0 := by
    apply mul_left_cancel₀ hH
    linear_combination hR3n + (-(-((10321920 : K[X]) * t1 ^ 4 * H ^ 2) + (41287680 : K[X]) * t1 ^ 3 *
      g1 ^ 2 * H - (10813440 : K[X]) * t1 ^ 2 * t2 * g1 * H + (5898240 :
      K[X]) * t1 ^ 2 * u * H ^ 2 - (6881280 : K[X]) * t1 ^ 2 * t3 * g1 * H
      ^ 2 - (5898240 : K[X]) * t1 ^ 2 * g1 ^ 4 + (655360 : K[X]) * t1 * t2
      ^ 2 * H + (655360 : K[X]) * t1 * t2 * t3 * H ^ 2 + (1966080 : K[X])
      * t1 * t2 * g1 ^ 3 - (8847360 : K[X]) * t1 * u * g1 ^ 2 * H +
      (655360 : K[X]) * t1 * t3 ^ 2 * H ^ 3 + (983040 : K[X]) * t1 * t3 *
      g1 ^ 3 * H + (1433272320 : K[X]) * t1 * g1 * a1 * H - (2149908480 :
      K[X]) * t1 * a0 * H ^ 2 - (163840 : K[X]) * t2 ^ 2 * g1 ^ 2 +
      (983040 : K[X]) * t2 * u * g1 * H - (163840 : K[X]) * t2 * t3 * g1 ^
      2 * H - (119439360 : K[X]) * t2 * a1 * H - (491520 : K[X]) * u ^ 2 *
      H ^ 2 + (983040 : K[X]) * u * t3 * g1 * H ^ 2 - (163840 : K[X]) * t3
      ^ 2 * g1 ^ 2 * H ^ 2 - (119439360 : K[X]) * t3 * a1 * H ^ 2 -
      Polynomial.C κ₇ * ((384 : K[X]) * H ^ 2) + Polynomial.C κ₅ * ((12288
      : K[X]) * t1 * H ^ 2) + Polynomial.C κ * ((5898240 : K[X]) * t1 ^ 3
      * H ^ 2) - Polynomial.C κ * ((11796480 : K[X]) * t1 ^ 2 * g1 ^ 2 *
      H) + Polynomial.C κ * ((2752512 : K[X]) * t1 * t2 * g1 * H) -
      Polynomial.C κ * ((2359296 : K[X]) * t1 * u * H ^ 2) + Polynomial.C
      κ * ((1966080 : K[X]) * t1 * t3 * g1 * H ^ 2) - Polynomial.C κ *
      ((131072 : K[X]) * t2 ^ 2 * H) - Polynomial.C κ * ((131072 : K[X]) *
      t2 * t3 * H ^ 2) + Polynomial.C κ * ((1179648 : K[X]) * u * g1 ^ 2 *
      H) - Polynomial.C κ * ((131072 : K[X]) * t3 ^ 2 * H ^ 3) -
      Polynomial.C κ * ((286654464 : K[X]) * g1 * a1 * H) + Polynomial.C κ
      * ((859963392 : K[X]) * a0 * H ^ 2))) * ht3
  simp only [alignedEleventhNonsquareResidue610]
  apply mul_left_cancel₀ (mul_ne_zero
    (show (-128 : K[X]) ≠ 0 by norm_num) (pow_ne_zero 2 hH))
  linear_combination hR4n + (-((5898240 : K[X]) * t1 ^ 3 * H - (2949120 : K[X]) * t1 * u * H +
    (2949120 : K[X]) * t1 * t3 * g1 * H + (1474560 : K[X]) * u * g1 ^ 2 -
    (491520 : K[X]) * t3 ^ 2 * H ^ 2 - (1474560 : K[X]) * v * g1 * H -
    (358318080 : K[X]) * g1 * a1 + (2149908480 : K[X]) * a0 * H -
    Polynomial.C κ₅ * ((12288 : K[X]) * H) - Polynomial.C κ * ((3538944 :
    K[X]) * t1 ^ 2 * H) + Polynomial.C κ * ((1179648 : K[X]) * u * H) -
    Polynomial.C κ * ((1179648 : K[X]) * t3 * g1 * H))) * hv

/-! ## Source-facing eleventh-row packets -/

/-- Source-facing squared weight-`55/2` integral of a normalized
aligned scale-two `(6,10)` source: the degree-`4` row is consumed into
`Λ² = κ₁₀ H⁵⁵` on top of the previous aligned packet.  The odd
exponent is chambered. -/
theorem normalized610ScaleTwo_alignedEleventhFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₂ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ κ₉ κ₁₀ : K), q.coeff 9 = Polynomial.C (5 /
      3 : K) * p.coeff 5 * H ^ 2 ∧ alignedSecondDefect610 H (p.coeff 4)
      (p.coeff 5) (q.coeff 8) = Polynomial.C κ * H ^ 5 ∧
      alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      7) κ ^ 2 = Polynomial.C κ₂ * H ^ 15 ∧ alignedFourthDefect610 H
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 6) (q.coeff
      7) κ = Polynomial.C κ₃ * H ^ 10 ∧ alignedFifthDefect610 H (p.coeff
      1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ ^ 2 = Polynomial.C κ₄ * H ^ 25 ∧
      alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff
      3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5) (q.coeff 6)
      (q.coeff 7) κ = Polynomial.C κ₅ * H ^ 15 ∧ alignedSeventhDefect610 H
      (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff
      5) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2
      = Polynomial.C κ₆ * H ^ 35 ∧ alignedEighthDefect610 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
      Polynomial.C κ₇ * H ^ 20 ∧ alignedNinthDefect610 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
      (q.coeff 7) κ ^ 2 = Polynomial.C κ₈ * H ^ 45 ∧ alignedTenthDefect610
      H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
      (p.coeff 5) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff
      4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₉ * H ^ 25
      ∧ alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
      Polynomial.C κ₁₀ * H ^ 55 := by
  dsimp only at haligned ⊢
  have hsrc := hsource
  rcases hsrc with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_610 hp hq hjac hH hp6' hq10' haligned
  obtain ⟨κ₂, hD2⟩ :=
    alignedThirdDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₃, hE⟩ :=
    alignedFourthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₅, hG⟩ :=
    alignedSixthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₇, hJ⟩ :=
    alignedEighthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₈, hL2⟩ :=
    alignedNinthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₉, hO⟩ :=
    alignedTenthDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨κ₁₀, hΛ2⟩ :=
    alignedEleventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  exact ⟨κ, κ₂, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, κ₉, κ₁₀,
    aligned_q9_solved_610 haligned, hM, hD2, hE, hF2, hG, hI2, hJ, hL2,
    hO, hΛ2⟩

/-- Exact square-chamber eleventh packet of a normalized aligned
scale-two `(6,10)` source: everything from the tenth packet, plus the
square root `Λ = μ₄ h₀⁵⁵` with `μ₄² = κ₁₀`, the NEW divisibility
`μ w₁⁸ = h₀ s₄`, the peeled eleventh row `= μ₄ h₀⁷` (the first aligned
square row with no `q`-coefficient), and the root-deepened divisor
`μ w₁⁸ = h₀² s₅`. -/
theorem normalized610ScaleTwo_alignedEleventhFace_squareChamber_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ μ κ₃ ν κ₅ ν₂ κ₇ κ₈ μ₃ κ₉ κ₁₀ μ₄ : K) (w1 f2 e1 e2 u2 e3 s2 s4
      s5 : K[X]), μ₃ ^ 2 = κ₈ ∧ μ₄ ^ 2 = κ₁₀ ∧ alignedSecondDefect610 H
      (p.coeff 4) (p.coeff 5) (q.coeff 8) = Polynomial.C κ * H ^ 5 ∧
      p.coeff 5 = h0 ^ 4 * w1 ∧ p.coeff 4 = h0 ^ 2 * f2 ∧ (3 : K[X]) * f2
      - w1 ^ 2 = h0 * e1 ∧ (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧ w1
      * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
      alignedEighthSquarePeeledRow610 h0 w1 e1 e2 (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (q.coeff 2) κ μ κ₃ ν κ₅ ν₂ = Polynomial.C κ₇ * h0 ^ 6 ∧
      e2 = h0 * e3 ∧ (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 ^ 2 * e3 ∧
      alignedNinthSquarePeeledRow610 h0 w1 e1 e2 u2 (p.coeff 0) (p.coeff
      1) (p.coeff 2) (q.coeff 1) κ μ κ₃ ν κ₅ ν₂ κ₇ = Polynomial.C μ₃ * h0
      ^ 6 ∧ (2048 : K[X]) * e1 ^ 3 * w1 ^ 4 - Polynomial.C μ * w1 ^ 7 = h0
      * s2 ∧ alignedTenthSquarePeeledRow610 h0 w1 e1 e2 u2 s2 (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (q.coeff 0) κ μ κ₃ ν κ₅ ν₂ κ₇ μ₃ =
      Polynomial.C κ₉ * h0 ^ 6 ∧ Polynomial.C μ * w1 ^ 8 = h0 * s4 ∧
      alignedEleventhSquarePeeledRow610 h0 w1 e1 e2 u2 s2 s4 (p.coeff 0)
      (p.coeff 1) (p.coeff 2) κ μ ν κ₅ ν₂ κ₇ μ₃ = Polynomial.C μ₄ * h0 ^ 7
      ∧ s4 = h0 * s5 ∧ Polynomial.C μ * w1 ^ 8 = h0 ^ 2 * s5 ∧
      alignedEighthSquareCombinedRow610 h0 w1 e1 e2 (p.coeff 0) (p.coeff
      1) (p.coeff 2) (q.coeff 2) (q.coeff 3) κ μ κ₃ ν κ₅ ν₂ = Polynomial.C
      κ₇ * h0 ^ 5 + Polynomial.C ν₂ * ((2 : K[X]) * w1 * h0 ^ 4) ∧
      alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      7) κ = Polynomial.C μ * h0 ^ 15 ∧ alignedFourthDefect610 H (p.coeff
      2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 6) (q.coeff 7) κ =
      Polynomial.C κ₃ * H ^ 10 ∧ alignedFifthDefect610 H (p.coeff 1)
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 5) (q.coeff
      6) (q.coeff 7) κ = Polynomial.C ν * h0 ^ 25 ∧ alignedSixthDefect610
      H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
      (p.coeff 5) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
      Polynomial.C κ₅ * H ^ 15 ∧ alignedSeventhDefect610 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = Polynomial.C
      ν₂ * h0 ^ 35 ∧ alignedEighthDefect610 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = Polynomial.C
      κ₇ * H ^ 20 ∧ alignedNinthDefect610 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff
      2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
      Polynomial.C μ₃ * h0 ^ 45 ∧ alignedTenthDefect610 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₉ * H ^ 25 ∧
      alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = Polynomial.C
      μ₄ * h0 ^ 55 ∧ alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff
      2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2
      = Polynomial.C κ₁₀ * H ^ 55 := by
  dsimp only at haligned ⊢
  have hsrc := hsource
  rcases hsrc with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hpacket10 :=
    normalized610ScaleTwo_alignedTenthFace_squareChamber_packet
      hsource hh0 hHsq haligned
  dsimp only at hpacket10
  obtain ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, κ₈, μ₃, κ₉, w1, f2, e1, e2, u2, e3,
    s2, hμ₃, hM, hp5w1, hp4f2, he1, he2, hu2, hR8, he3, h27, hR9, hs2,
    hR10x, hQ9, hD, hE, hF, hG, hI, hJ, hL, hO⟩ := hpacket10
  obtain ⟨κ₁₀, hΛ2⟩ :=
    alignedEleventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨μ₄, hμ₄, hΛ⟩ := alignedSquareEleventh_sqrt_610 hh0 hHsq hΛ2
  have hdeg1 : h0.natDegree = 1 := by
    have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨s4, s5, hs4, hR11x, hs5, hmu8⟩ :=
    alignedSquareEleventh_descent_610 hh0 hdeg1 hHsq hp5w1 hp4f2 hD hF
      hG hI hJ hL hΛ he1 he2 hu2 hs2 he3 hR10x
  exact ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, κ₈, μ₃, κ₉, κ₁₀, μ₄, w1, f2, e1, e2,
    u2, e3, s2, s4, s5, hμ₃, hμ₄, hM, hp5w1, hp4f2, he1, he2, hu2, hR8,
    he3, h27, hR9, hs2, hR10x, hs4, hR11x, hs5, hmu8, hQ9, hD, hE, hF,
    hG, hI, hJ, hL, hO, hΛ, hΛ2⟩

/-- Exact nonsquare-chamber eleventh packet of a normalized aligned
scale-two `(6,10)` source: the odd exponent forces `κ₁₀ = 0` and
`Λ ≡ 0`, and the carried divisor cascade bottoms out on the residue
relation — the first `p₀`-loaded relation of the aligned nonsquare
tower, with no new witness and no `q`-coefficient left to solve. -/
theorem normalized610ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g1 f t1 t2 u t3 v : K[X]),
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
      Polynomial.C κ * H ^ 5 ∧ p.coeff 5 = H ^ 2 * g1 ∧ p.coeff 4 = H * f
      ∧ (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧ (27 : K[X]) * p.coeff 3 - g1 ^
      3 = H * t2 ∧ (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 - g1
      * t2 = H * u ∧ t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧ (243 : K[X]) *
      p.coeff 1 - g1 * u = H * v ∧ (9795520512 : K[X]) * q.coeff 0 =
      alignedTenthNonsquareSolved610 H g1 t1 u t3 v (p.coeff 0) κ κ₃ κ₅ κ₇
      - Polynomial.C κ₉ ∧ (1632586752 : K[X]) * q.coeff 1 =
      alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 (p.coeff 0) (p.coeff
      1) κ κ₃ κ₅ κ₇ ∧ (15116544 : K[X]) * q.coeff 2 =
      alignedEighthNonsquareSolved610 H g1 t1 t2 u (p.coeff 0) (p.coeff 1)
      κ κ₃ κ₅ - Polynomial.C κ₇ * H ∧ alignedThirdDefect610 H (p.coeff 3)
      (p.coeff 4) (p.coeff 5) (q.coeff 7) κ = 0 ∧ alignedFourthDefect610 H
      (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 6) (q.coeff
      7) κ = Polynomial.C κ₃ * H ^ 10 ∧ alignedFifthDefect610 H (p.coeff
      1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ = 0 ∧ alignedSixthDefect610 H (p.coeff 0)
      (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff
      4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₅ * H ^ 15
      ∧ alignedSeventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 3) (q.coeff 4) (q.coeff
      5) (q.coeff 6) (q.coeff 7) κ = 0 ∧ alignedEighthDefect610 H (p.coeff
      0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5)
      (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff
      7) κ = Polynomial.C κ₇ * H ^ 20 ∧ alignedNinthDefect610 H (p.coeff
      0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff
      6) (q.coeff 7) κ = 0 ∧ alignedTenthDefect610 H (p.coeff 0) (p.coeff
      1) (p.coeff 2) (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 0)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff
      6) (q.coeff 7) κ = Polynomial.C κ₉ * H ^ 25 ∧
      alignedEleventhDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 1) (q.coeff 2) (q.coeff
      3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ = 0 ∧
      alignedEleventhNonsquareResidue610 H g1 t1 u t3 v (p.coeff 0) κ κ₅
      κ₇ = 0 := by
  dsimp only at haligned ⊢
  have hsrc := hsource
  rcases hsrc with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hpacket10 :=
    normalized610ScaleTwo_alignedTenthFace_nonsquareChamber_packet
      hsource hnsq haligned
  dsimp only at hpacket10
  obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, hM, hp5, hf, ht1,
    ht2, hu, ht3, hv, hq0, hq1, hq2, hD0, hE, hF0, hG, hI0, hJ, hL0,
    hO⟩ := hpacket10
  obtain ⟨κ₁₀, hΛ2⟩ :=
    alignedEleventhDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned hM
  obtain ⟨_hκ₁₀, hΛ0⟩ :=
    alignedNonsquareEleventh_defect_eq_zero_610 hH hHdegree hnsq hΛ2
  have hres :=
    alignedNonsquareEleventh_descent_610 hH hp5 hf hD0 hF0 hG hI0 hJ
      hL0 hΛ0 ht1 ht2 hu ht3 hv
  exact ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, hM, hp5, hf, ht1,
    ht2, hu, ht3, hv, hq0, hq1, hq2, hD0, hE, hF0, hG, hI0, hJ, hL0,
    hO, hΛ0, hres⟩

/-- Honest square/nonsquare chamber split of the consumed degree-`4`
aligned row (peeled rows, the forced `κ₁₀ = 0`, and factored defect
relations are in the two chamber packets above).  Neither chamber is
excluded and no closure is claimed. -/
theorem normalized610ScaleTwo_alignedEleventhFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (μ : K) (w1 f2 e1 e2 u2 e3 s2 s4 s5 : K[X]),
        p.coeff 5 = h0 ^ 4 * w1 ∧
          p.coeff 4 = h0 ^ 2 * f2 ∧
          (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
          w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 ^ 2 * e3 ∧
          (2048 : K[X]) * e1 ^ 3 * w1 ^ 4 - Polynomial.C μ * w1 ^ 7 =
            h0 * s2 ∧
          Polynomial.C μ * w1 ^ 8 = h0 * s4 ∧
          s4 = h0 * s5 ∧
          Polynomial.C μ * w1 ^ 8 = h0 ^ 2 * s5) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (g1 f t1 t2 u t3 v : K[X]),
        p.coeff 5 = H ^ 2 * g1 ∧
          p.coeff 4 = H * f ∧
          (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
          (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
          (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 -
            g1 * t2 = H * u ∧
          t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
          (243 : K[X]) * p.coeff 1 - g1 * u = H * v) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized610ScaleTwo_alignedEleventhFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₃, ν, κ₅, ν₂, κ₇, κ₈, μ₃, κ₉, κ₁₀, μ₄, w1, f2, e1,
      e2, u2, e3, s2, s4, s5, _hμ₃, _hμ₄, _hM, hp5, hp4, he1, he2, hu2,
      _hR8, _he3, h27, _hR9, hs2, _hR10x, hs4, _hR11x, hs5, hmu8, _hQ9,
      _hD, _hE, _hF, _hG, _hI, _hJ, _hL, _hO, _hΛ, _hΛ2⟩ := hpacket
    exact Or.inl ⟨h0, hh0, hHsq, μ, w1, f2, e1, e2, u2, e3, s2, s4, s5,
      hp5, hp4, he1, he2, hu2, h27, hs2, hs4, hs5, hmu8⟩
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized610ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, _hM, hp5, hf,
      ht1, ht2, hu, ht3, hv, _hq0, _hq1, _hq2, _hD0, _hE, _hF0, _hG,
      _hI0, _hJ, _hL0, _hO, _hΛ0, _hres⟩ := hpacket
    exact Or.inr ⟨hnsq, g1, f, t1, t2, u, t3, v, hp5, hf, ht1, ht2,
      hu, ht3, hv⟩

/-- Root data of the consumed degree-`4` row: at scale two the common
core has a root where the jet `p₅, q₉, q₈, q₇, p₄, q₆` vanishes and
the seventh-face pins hold; in the square chamber the carried
resolution `e₂(a) = 0`, the branch `w₁(a) = 0 ∨ (μ = 0 ∧ e₁(a) = 0)`,
the tenth-face tie, the NEW row pin `μ w₁(a)⁸ = 0`, and the NEW exact
vanishing `s₄(a) = 0` of the eleventh witness hold; in the nonsquare
chamber the residue evaluates to the FIRST `p₀`-loaded root relation
of the aligned tower on top of the carried pins. -/
theorem normalized610ScaleTwo_alignedEleventhFace_rootData
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ a : K, H.eval a = 0 ∧ (p.coeff 5).eval a = 0 ∧
      (q.coeff 9).eval a = 0 ∧ (q.coeff 8).eval a = 0 ∧
      (q.coeff 7).eval a = 0 ∧ (p.coeff 4).eval a = 0 ∧
      (q.coeff 6).eval a = 0 ∧
      ((∃ h0 w1 f2 e1 e2 e3 u2 s2 s4 s5 : K[X], ∃ κ μ : K,
          h0 ≠ 0 ∧ H = h0 ^ 2 ∧
          h0.eval a = 0 ∧
          p.coeff 5 = h0 ^ 4 * w1 ∧ p.coeff 4 = h0 ^ 2 * f2 ∧
          (3 : K[X]) * f2 - w1 ^ 2 = h0 * e1 ∧
          (27 : K[X]) * p.coeff 3 - w1 ^ 3 = h0 * e2 ∧
          e2 = h0 * e3 ∧
          w1 * (e2 - (3 : K[X]) * e1 * w1) = h0 * u2 ∧
          (2048 : K[X]) * e1 ^ 3 * w1 ^ 4 - Polynomial.C μ * w1 ^ 7 =
            h0 * s2 ∧
          Polynomial.C μ * w1 ^ 8 = h0 * s4 ∧
          s4 = h0 * s5 ∧
          Polynomial.C μ * w1 ^ 8 = h0 ^ 2 * s5 ∧
          alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
            Polynomial.C κ * H ^ 5 ∧
          alignedThirdDefect610 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (q.coeff 7) κ = Polynomial.C μ * h0 ^ 15 ∧
          3 * f2.eval a = w1.eval a ^ 2 ∧
          27 * (p.coeff 3).eval a = w1.eval a ^ 3 ∧
          e2.eval a = 0 ∧
          (w1.eval a = 0 ∨ (μ = 0 ∧ e1.eval a = 0)) ∧
          135 * s2.eval a =
            92160 * w1.eval a ^ 2 *
              (81 * (p.coeff 2).eval a - u2.eval a) ^ 2 ∧
          μ * w1.eval a ^ 8 = 0 ∧
          s4.eval a = 0) ∨
        (∃ g1 f t1 t2 u t3 v : K[X], ∃ κ κ₅ κ₇ : K,
          p.coeff 5 = H ^ 2 * g1 ∧
          p.coeff 4 = H * f ∧
          (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
          (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
          (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 -
            g1 * t2 = H * u ∧
          t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
          (243 : K[X]) * p.coeff 1 - g1 * u = H * v ∧
          alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
            Polynomial.C κ * H ^ 5 ∧
          alignedSixthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ = Polynomial.C κ₅ * H ^ 15 ∧
          alignedEighthDefect610 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (q.coeff 2) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ =
            Polynomial.C κ₇ * H ^ 20 ∧
          3 * f.eval a = g1.eval a ^ 2 ∧
          27 * (p.coeff 3).eval a = g1.eval a ^ 3 ∧
          81 * (p.coeff 2).eval a =
            g1.eval a * t2.eval a - 3 * g1.eval a ^ 2 * t1.eval a ∧
          t2.eval a = 6 * g1.eval a * t1.eval a ∧
          27 * (p.coeff 2).eval a = g1.eval a ^ 2 * t1.eval a ∧
          243 * (p.coeff 1).eval a = g1.eval a * u.eval a ∧
          1280 * g1.eval a ^ 2 * t3.eval a ^ 3 - 9216 * κ * g1.eval a *
          t1.eval a * t3.eval a ^ 2 + 9216 * κ * g1.eval a * t3.eval a *
          v.eval a + 23040 * g1.eval a * t1.eval a ^ 2 * t3.eval a ^ 2 -
          23040 * g1.eval a * t1.eval a * t3.eval a * v.eval a - 3840 *
          g1.eval a * t3.eval a ^ 2 * u.eval a + 11520 * g1.eval a *
          v.eval a ^ 2 - 96 * κ₅ * t1.eval a * t3.eval a + 96 * κ₅ *
          v.eval a + 3 * κ₇ * t3.eval a - 6718464 * κ * (p.coeff 0).eval a
          * t3.eval a - 46080 * κ * t1.eval a ^ 3 * t3.eval a + 27648 * κ
          * t1.eval a ^ 2 * v.eval a + 18432 * κ * t1.eval a * t3.eval a *
          u.eval a - 9216 * κ * u.eval a * v.eval a + 16796160 * (p.coeff
          0).eval a * t1.eval a * t3.eval a - 16796160 * (p.coeff 0).eval
          a * v.eval a + 80640 * t1.eval a ^ 4 * t3.eval a - 46080 *
          t1.eval a ^ 3 * v.eval a - 46080 * t1.eval a ^ 2 * t3.eval a *
          u.eval a + 23040 * t1.eval a * u.eval a * v.eval a + 3840 *
          t3.eval a * u.eval a ^ 2 = 0)) := by
  dsimp only at haligned ⊢
  have hH : H ≠ 0 := hsource.1
  have hHdegree : H.natDegree = 2 := hsource.2.1
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hH
      simp [hHsq, hzero]
    have hpacket5 :=
      normalized610ScaleTwo_alignedFifthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket5
    obtain ⟨κA, μA, κ₃A, νA, w, r, w1', f1', hp5w, hq9, hq8, hq7,
      htie4, hq6, hw1', hf1', _hq5', _hF5⟩ := hpacket5
    have hpacket11 :=
      normalized610ScaleTwo_alignedEleventhFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket11
    obtain ⟨κB, μB, κ₃B, νB, κ₅B, ν₂B, κ₇B, κ₈B, μ₃B, κ₉B, κ₁₀B, μ₄B,
      w1, f2, e1, e2, u2, e3, s2, s4, s5, _hμ₃, _hμ₄, hM9, hp5w1,
      hp4f2, he1, he2, hu2, _hR8, he3, _h27, hR9, hs2, hR10x, hs4,
      hR11x, hs5, hmu8, hQ9, hD9, _hE, _hF, _hG, _hI, _hJ, _hL, _hO,
      _hΛ, _hΛ2⟩ := hpacket11
    have hdeg1 : h0.natDegree = 1 := by
      have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
      rw [Polynomial.natDegree_pow] at h2
      omega
    have hdegne : h0.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hh0, hdeg1]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root h0 hdegne
    have hroot : h0.eval a = 0 := ha
    have hr : r = h0 ^ 2 *
        ((270 : K[X]) * f2 ^ 2 - (90 : K[X]) * f2 * w1' ^ 2 +
          (10 : K[X]) * w1' ^ 4) := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
      rw [hp4f2, hw1'] at htie4
      linear_combination -htie4
    have hra : r.eval a = 0 := by
      rw [hr, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    have hpin1 : 3 * f2.eval a = w1.eval a ^ 2 := by
      have hev := congrArg (fun t : K[X] => t.eval a) he1
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hpin2 : 27 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 3).eval a) = w1.eval a ^ 3 := by
      have hev := congrArg (fun t : K[X] => t.eval a) he2
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hev1 := congrArg (fun t : K[X] => t.eval a) hu2
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_ofNat] at hev1
    rw [hroot, zero_mul] at hev1
    have h1 : w1.eval a *
        (e2.eval a - 3 * e1.eval a * w1.eval a) = 0 := by
      linear_combination hev1
    have hevQ9 := congrArg (fun t : K[X] => t.eval a) hQ9
    simp only [alignedEighthSquareCombinedRow610, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_neg,
      Polynomial.eval_ofNat] at hevQ9
    rw [hroot] at hevQ9
    have h2 : 1280 * e1.eval a *
        (3 * e1.eval a * w1.eval a - e2.eval a) *
        (6 * e1.eval a * w1.eval a - e2.eval a) +
        189 * μB * w1.eval a ^ 5 = 0 := by
      linear_combination -hevQ9
    have hevR9 := congrArg (fun t : K[X] => t.eval a) hR9
    simp only [alignedNinthSquarePeeledRow610, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_neg,
      Polynomial.eval_ofNat] at hevR9
    rw [hroot] at hevR9
    have h9 : 276480 * e1.eval a ^ 3 * w1.eval a ^ 3 -
        5120 * e2.eval a ^ 3 - 189 * μB * w1.eval a ^ 6 = 0 := by
      linear_combination hevR9
    obtain ⟨hv0, hbranch⟩ := alignedNinthSquareResolve_610 h1 h2 h9
    have hevR11 := congrArg (fun t : K[X] => t.eval a) hR10x
    simp only [alignedTenthSquarePeeledRow610, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_neg,
      Polynomial.eval_ofNat] at hevR11
    rw [hroot] at hevR11
    have hhead : 184320 * e1.eval a ^ 2 * e2.eval a ^ 2 -
        44789760 * e1.eval a ^ 2 *
          ((((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
            2).eval a) * w1.eval a ^ 2 +
        737280 * e1.eval a ^ 2 * u2.eval a * w1.eval a ^ 2 +
        2268 * e1.eval a * μB * w1.eval a ^ 5 -
        2488320 * e2.eval a ^ 2 *
          ((((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
            2).eval a) +
        40960 * e2.eval a ^ 2 * u2.eval a +
        604661760 *
          ((((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
            2).eval a) ^ 2 * w1.eval a ^ 2 -
        14929920 *
          ((((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
            2).eval a) * u2.eval a * w1.eval a ^ 2 -
        135 * s2.eval a + 92160 * u2.eval a ^ 2 * w1.eval a ^ 2 =
          0 := by
      linear_combination hevR11
    have htie := alignedTenthSquareTieResolve_610 h1 hv0 hhead
    have hμw8a : μB * w1.eval a ^ 8 = 0 := by
      have hev4 := congrArg (fun t : K[X] => t.eval a) hs4
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_C] at hev4
      rw [hroot, zero_mul] at hev4
      exact hev4
    have hs4a : s4.eval a = 0 := by
      have hev5 := congrArg (fun t : K[X] => t.eval a) hs5
      simp only [Polynomial.eval_mul] at hev5
      rw [hroot, zero_mul] at hev5
      exact hev5
    refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inl ⟨h0, w1, f2, e1, e2, e3, u2, s2, s4, s5, κB, μB, hh0,
        hHsq, hroot, hp5w1, hp4f2, he1, he2, he3, hu2, hs2, hs4, hs5,
        hmu8, hM9, hD9, hpin1, hpin2, hv0, hbranch, htie, hμw8a,
        hs4a⟩⟩
    · rw [hHsq, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · rw [hp5w1, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (7 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (9 : K) ≠ 0)
    · have hev := congrArg (fun t : K[X] => t.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (81 : K) ≠ 0)
    · rw [hp4f2, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq6
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_ofNat] at hev
      rw [hroot] at hev
      have h486 : (486 : K) * (((Polynomial.Bivariate.equivMvPolynomial
          K).symm Q).coeff 6).eval a = 0 := by
        linear_combination hev + hra
      exact (mul_eq_zero.mp h486).resolve_left
        (by norm_num : (486 : K) ≠ 0)
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket5 :=
      normalized610ScaleTwo_alignedFifthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket5
    obtain ⟨κA, κ₃A, g1', f', _hp5', hq9, hq8, hq7, _hf', hq6, _hq5',
      _hD0', _hE', _hF0'⟩ := hpacket5
    have hpacket11 :=
      normalized610ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket11
    obtain ⟨κB, κ₃B, κ₅B, κ₇B, κ₉B, g1, f, t1, t2, u, t3, v, hM9, hp5,
      hf, ht1, ht2, hu, ht3, hv, _hq0, _hq1, _hq2, _hD0, _hE, _hF0,
      hG6, _hI0, hJ8, _hL0, _hO, _hΛ0, hres⟩ := hpacket11
    have hdegne : H.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hH, hHdegree]
      decide
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
    have hroot : H.eval a = 0 := ha
    have hpin1 : 3 * f.eval a = g1.eval a ^ 2 := by
      have hev := congrArg (fun t : K[X] => t.eval a) ht1
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hpin2 : 27 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 3).eval a) = g1.eval a ^ 3 := by
      have hev := congrArg (fun t : K[X] => t.eval a) ht2
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hp2pin : 81 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 2).eval a) =
        g1.eval a * t2.eval a - 3 * g1.eval a ^ 2 * t1.eval a := by
      have hev := congrArg (fun t : K[X] => t.eval a) hu
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have ht2pin : t2.eval a = 6 * g1.eval a * t1.eval a := by
      have hev := congrArg (fun t : K[X] => t.eval a) ht3
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hp2ref : 27 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 2).eval a) =
        g1.eval a ^ 2 * t1.eval a := by
      linear_combination (3⁻¹ : K) * hp2pin +
        (3⁻¹ : K) * g1.eval a * ht2pin
    have hp1pin : 243 * ((((Polynomial.Bivariate.equivMvPolynomial
        K).symm P).coeff 1).eval a) = g1.eval a * u.eval a := by
      have hev := congrArg (fun t : K[X] => t.eval a) hv
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      linear_combination hev
    have hevRes := congrArg (fun t : K[X] => t.eval a) hres
    simp only [alignedEleventhNonsquareResidue610, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_neg, Polynomial.eval_ofNat,
      Polynomial.eval_zero] at hevRes
    rw [hroot] at hevRes
    have hbr :
        1280 * g1.eval a ^ 2 * t3.eval a ^ 3 - 9216 * κB * g1.eval a *
        t1.eval a * t3.eval a ^ 2 + 9216 * κB * g1.eval a * t3.eval a *
        v.eval a + 23040 * g1.eval a * t1.eval a ^ 2 * t3.eval a ^ 2 -
        23040 * g1.eval a * t1.eval a * t3.eval a * v.eval a - 3840 *
        g1.eval a * t3.eval a ^ 2 * u.eval a + 11520 * g1.eval a * v.eval
        a ^ 2 - 96 * κ₅B * t1.eval a * t3.eval a + 96 * κ₅B * v.eval a + 3
        * κ₇B * t3.eval a - 6718464 * κB *
        ((((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
        0).eval a) * t3.eval a - 46080 * κB * t1.eval a ^ 3 * t3.eval a +
        27648 * κB * t1.eval a ^ 2 * v.eval a + 18432 * κB * t1.eval a *
        t3.eval a * u.eval a - 9216 * κB * u.eval a * v.eval a + 16796160
        * ((((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
        0).eval a) * t1.eval a * t3.eval a - 16796160 *
        ((((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
        0).eval a) * v.eval a + 80640 * t1.eval a ^ 4 * t3.eval a - 46080
        * t1.eval a ^ 3 * v.eval a - 46080 * t1.eval a ^ 2 * t3.eval a *
        u.eval a + 23040 * t1.eval a * u.eval a * v.eval a + 3840 *
        t3.eval a * u.eval a ^ 2 = 0 := by
      linear_combination hevRes
    refine ⟨a, hroot, ?_, ?_, ?_, ?_, ?_, ?_,
      Or.inr ⟨g1, f, t1, t2, u, t3, v, κB, κ₅B, κ₇B, hp5, hf, ht1,
        ht2, hu, ht3, hv, hM9, hG6, hJ8, hpin1, hpin2, hp2pin, ht2pin,
        hp2ref, hp1pin, hbr⟩⟩
    · rw [hp5, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · rw [hq9, Polynomial.eval_mul, Polynomial.eval_pow, hroot,
        zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq8
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_ofNat] at hev
      rw [hroot, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (9 : K) ≠ 0)
    · have hev := congrArg (fun t : K[X] => t.eval a) hq7
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (81 : K) ≠ 0)
    · rw [hf, Polynomial.eval_mul, hroot, zero_mul]
    · have hev := congrArg (fun t : K[X] => t.eval a) hq6
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
      rw [hroot, zero_mul] at hev
      exact (mul_eq_zero.mp hev).resolve_left
        (by norm_num : (486 : K) ≠ 0)

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
