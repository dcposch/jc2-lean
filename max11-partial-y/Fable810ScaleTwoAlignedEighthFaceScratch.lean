import Fable810ScaleTwoAlignedSeventhFaceScratch

/-! # Eighth aligned face row for the normalized `(8,10)` scale-two leaf

Untracked working note.  No tracked file was edited.

`Fable810ScaleTwoAlignedSeventhFaceScratch` consumed the degree-`9`
aligned Keller row (the chamber-free `J = κ₇ H²⁸`).  This file consumes
the next unused aligned row, the degree-`8` Jacobian coefficient — the
first row that sees `q₁` (internal names `alignedNinth*`).

At the common source level, modulo the face `N = 5 p₇ H - 4 q₉ = 0`,
the consumed degree-`15` relation `C = 0`, and the consumed
degree-`14`/`13`/`12`/`11`/`10`/`9` rows `2 H D' - 21 D H' = 0`,
`H E' - 14 E H' = 0`, `2 H F' - 35 F H' = 0`, `H G' - 21 G H' = 0`,
`2 H I' - 49 I H' = 0`, `H J' - 28 J H' = 0`, the degree-`8` row is the
weighted derivative of the weight-sixty-three defect

`L = -536870912 q₁ H³¹ - 83886080 p₁ p₆ H²⁸ - 754974720 p₂ p₅ H²⁸
  - 754974720 p₃ p₄ H²⁸ + 469762048 p₂ q₇ H²⁷ + 402653184 p₃ q₆ H²⁷
  + 335544320 p₄ q₅ H²⁷ + 268435456 p₅ q₄ H²⁷ + 201326592 p₆ q₃ H²⁷
  + 134217728 p₇ q₂ H²⁷ + … - 9392075 p₇⁹
  + κ (16777216 p₁ H³¹ - 18874368 p₂ p₇ H²⁷ - … + 3220140 p₇⁷ H⁷)`

(the full seventy-one-term expression is the literal body of
`alignedNinthDefect810`; the only new coefficient is `q₁`, and no `p₀`
monomial occurs), via the exact multiplier identity

`134217728 H²⁸ · row₈[p₈ = H⁴] = (2 H L' - 63 L H')
  - 301989888 H²⁸ p₀' N
  + (33554432 H²⁵ p₁' + 12582912 p₁ H²⁴ H') C - 4194304 H²⁵ p₁ C'
  + (4718592 p₂ H²⁰ + 4128768 p₃ p₇ H¹⁶ + 4128768 p₄ p₆ H¹⁶
     + 2064384 p₅² H¹⁶ - 258048 p₄ p₇² H¹² - 516096 p₅ p₆ p₇ H¹²
     - 86016 p₆³ H¹² + 96768 p₅ p₇³ H⁸ + 145152 p₆² p₇² H⁸
     - 51408 p₆ p₇⁴ H⁴ + 5355 p₇⁶) (2 H D' - 21 D H')
  + (589824 p₃ H¹⁶ + 442368 p₄ p₇ H¹² + 442368 p₅ p₆ H¹²
     - 55296 p₅ p₇² H⁸ - 55296 p₆² p₇ H⁸ + 23040 p₆ p₇³ H⁴
     - 2592 p₇⁵) (H E' - 14 E H')
  + (36864 p₄ H¹² + 23040 p₅ p₇ H⁸ + 11520 p₆² H⁸ - 4320 p₆ p₇² H⁴
     + 495 p₇⁴) (2 H F' - 35 F H')
  + (18432 p₅ H⁸ + 9216 p₆ p₇ H⁴ - 768 p₇³) (H G' - 21 G H')
  + (144 p₆ H⁴ + 27 p₇²) (2 H I' - 49 I H')
  + 36 p₇ (H J' - 28 J H')`.

The defect no longer sees a new `p`-coefficient (all of `p₀, …, p₇`
were consumed by the previous rows): `q₁` is the only new coefficient,
entering at `H³¹`, and `p₀` couples only through the `p₀' N` and
`36 p₇ (H J' - 28 J H')` corrections.  On the aligned face every
right-hand correction vanishes, so `2 H L' = 63 L H'` and the squared
weight-sixty-three first integral

`L² = κ₈ H⁶³`

holds for a preserved constant `κ₈`.  The exponent is odd, so — exactly
as for the degree-`14`, degree-`12`, and degree-`10` rows — the
integral is **chambered**:

* square chamber `H = h₀²`, `p₇ = h₀⁴ g₁`: `L = ν₃ h₀⁶³` with
  `ν₃² = κ₈`; peeling `h₀³⁶` and consuming the previous factored
  quotient (`128 q₇ h₀²` solved, transported by the mate
  `3670016 p₂ h₀¹⁶ - 4128768 p₃ g₁ h₀¹² - 4128768 p₄ p₆ h₀⁸
   + 4386816 p₄ g₁² h₀⁸ - 2064384 p₅² h₀⁸ + 8773632 p₅ p₆ g₁ h₀⁴
   - 4569600 p₅ g₁³ h₀⁴ + 1462272 p₆³ - 6854400 p₆² g₁²
   + 4712400 p₆ g₁⁴ - 805035 g₁⁶`) leaves the cleared ninth row
  `alignedNinthSquareRow810` (with the new `q₁` at `h₀²⁶`) against
  `ν₃ h₀²⁷`, and the factored transport
  `340 g₁ (15785 g₁⁸ - 174240 p₆ g₁⁶ + 659520 p₆² g₁⁴ - 976896 p₆³ g₁²
   + 442368 p₆⁴) = h₀⁴ · (alignedNinthSquareCof810 - ν₃ h₀²³)`.
* nonsquare chamber (`H` a degree-two nonsquare, simple roots): the odd
  exponent forces `κ₈ = 0` and `L ≡ 0`.  With `p₇ = H² g₂`, peeling
  `H¹⁸` and consuming the previous factored quotient (same mate) leaves
  the cleared ninth row `alignedNinthNonsquareRow810` (with `q₁` at
  `H¹³`) equal to zero and the transport
  `340 g₂ (15785 g₂⁸ - 174240 p₆ g₂⁶ + 659520 p₆² g₂⁴ - 976896 p₆³ g₂²
   + 442368 p₆⁴) = H² · alignedNinthNonsquareCof810`.

At a root of the transport co-factor the honest root branch is the
root nonic `g = 0 ∨ 15785 g⁸ - 174240 p₆ g⁶ + 659520 p₆² g⁴
- 976896 p₆³ g² + 442368 p₆⁴ = 0`.  Like the quintic, sextic, septic,
and octic of the previous rows it adds *no new* root information: the
consumed degree-`13` row already collapsed `g(a) = 0 ∧ p₆(a) = 0` at
every core root, and that collapse absorbs the nonic identically
(`alignedNinth_rootNonic_absorbed_810`).  The chamber-independent root
jet therefore stays `p₇, q₉, q₈, p₆` — the row ties the new coefficient
`q₁` into the cleared ninth row (at `h₀²⁶`, resp. `H¹³`) instead of
killing anything new at the root.

No closure is claimed.  Both chambers remain open where not forced
(`κ₈ = 0` and `L ≡ 0` are forced in the nonsquare chamber only), the
constants `κ`, `μ`, `κ₃`, `κ₄`, `κ₅`, `κ₆`, `κ₇`, `κ₈ = ν₃²` are
preserved where not forced, the zero branches (`g₁ = 0`, `g₂ = 0`,
`κ = 0`, `μ = 0`, `κ₃ = 0`, `κ₄ = 0`, `κ₅ = 0`, `κ₆ = 0`, `κ₇ = 0`,
`κ₈ = 0` in the square chamber, `ν₃ = 0`) are not excluded as
polynomial identities, the deepened quotients `g₁/h₀`, `p₆/h₀`,
`g₂/H`, `p₆/H` from the degree-`13` face are still not re-cleared
through the tower here, the root nonic is recorded but not excluded as
an identity, and no individual vanishing of `p₀`, `p₁`, `p₂`, `p₃`,
`p₄`, `p₅`, `q₁`, `q₂`, `q₃`, `q₄`, `q₅`, `q₆`, `q₇` is claimed.  The
next unused Keller row on the aligned face is the degree-`7` Jacobian
coefficient, the first row that sees `q₀` (weight-seventy defect, even
exponent, hence chamber-free).  No total-degree or twice-prime theorem
is used, and no finite-root shortcut is taken.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-! ## Literal degree-`8` Keller coefficient on the aligned face -/

/-- The ninth row below the leading weighted-Wronskian row for outer
degrees `(8,10)`: the degree-`8` Jacobian coefficient, the first
aligned row that sees `q₁`. -/
theorem alignedNinthCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 8).derivative * q.coeff 1 +
        (p.coeff 7).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 6).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 5).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 4).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 3).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 2).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 1).derivative * (q.coeff 8 * Polynomial.C (8 : K)) +
        (p.coeff 0).derivative * (q.coeff 9 * Polynomial.C (9 : K)) -
      ((p.coeff 8 * Polynomial.C (8 : K)) * (q.coeff 1).derivative +
        (p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 2).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 3).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 4).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 5).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 6).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 7).derivative +
        p.coeff 1 * (q.coeff 8).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 8) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (8 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 8 :
      Finset (ℕ × ℕ)) =
      ({(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2),
        (7, 1), (8, 0)} : Finset (ℕ × ℕ)) := by decide
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
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  rw [hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9]
  linear_combination hcoeff

/-! ## Aligned ninth defect -/

set_option maxHeartbeats 1600000000 in
/-- Weight-sixty-three defect of the degree-`8` aligned `(8,10)` row.
On the aligned face its square is a polynomial first integral of odd
weight sixty-three, hence chambered.  The only new coefficient is
`q₁`; no `p₀` monomial occurs. -/
def alignedNinthDefect810 {K : Type*} [CommRing K]
    (H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]) (κ : K) :
    K[X] :=
    -(536870912 : K[X]) * b1 * H ^ 31 -
    (83886080 : K[X]) * a1 * a6 * H ^ 28 -
    (754974720 : K[X]) * a2 * a5 * H ^ 28 -
    (754974720 : K[X]) * a3 * a4 * H ^ 28 +
    (469762048 : K[X]) * a2 * b7 * H ^ 27 +
    (402653184 : K[X]) * a3 * b6 * H ^ 27 +
    (335544320 : K[X]) * a4 * b5 * H ^ 27 +
    (268435456 : K[X]) * a5 * b4 * H ^ 27 +
    (201326592 : K[X]) * a6 * b3 * H ^ 27 +
    (134217728 : K[X]) * a7 * b2 * H ^ 27 +
    (36700160 : K[X]) * a1 * a7 ^ 2 * H ^ 24 +
    (754974720 : K[X]) * a3 * a5 * a7 * H ^ 24 +
    (47185920 : K[X]) * a3 * a6 ^ 2 * H ^ 24 +
    (377487360 : K[X]) * a4 ^ 2 * a7 * H ^ 24 +
    (849346560 : K[X]) * a4 * a5 * a6 * H ^ 24 +
    (267386880 : K[X]) * a5 ^ 3 * H ^ 24 -
    (528482304 : K[X]) * a3 * a7 * b7 * H ^ 23 -
    (528482304 : K[X]) * a4 * a6 * b7 * H ^ 23 -
    (452984832 : K[X]) * a4 * a7 * b6 * H ^ 23 -
    (264241152 : K[X]) * a5 ^ 2 * b7 * H ^ 23 -
    (452984832 : K[X]) * a5 * a6 * b6 * H ^ 23 -
    (377487360 : K[X]) * a5 * a7 * b5 * H ^ 23 -
    (188743680 : K[X]) * a6 ^ 2 * b5 * H ^ 23 -
    (301989888 : K[X]) * a6 * a7 * b4 * H ^ 23 -
    (113246208 : K[X]) * a7 ^ 2 * b3 * H ^ 23 -
    (27525120 : K[X]) * a2 * a7 ^ 3 * H ^ 20 +
    (5898240 : K[X]) * a3 * a6 * a7 ^ 2 * H ^ 20 -
    (796262400 : K[X]) * a4 * a5 * a7 ^ 2 * H ^ 20 -
    (802160640 : K[X]) * a5 ^ 2 * a6 * a7 * H ^ 20 -
    (33423360 : K[X]) * a5 * a6 ^ 3 * H ^ 20 +
    (561512448 : K[X]) * a4 * a7 ^ 2 * b7 * H ^ 19 +
    (1123024896 : K[X]) * a5 * a6 * a7 * b7 * H ^ 19 +
    (481296384 : K[X]) * a5 * a7 ^ 2 * b6 * H ^ 19 +
    (187170816 : K[X]) * a6 ^ 3 * b7 * H ^ 19 +
    (481296384 : K[X]) * a6 ^ 2 * a7 * b6 * H ^ 19 +
    (401080320 : K[X]) * a6 * a7 ^ 2 * b5 * H ^ 19 +
    (106954752 : K[X]) * a7 ^ 3 * b4 * H ^ 19 +
    (21934080 : K[X]) * a3 * a7 ^ 4 * H ^ 16 -
    (8355840 : K[X]) * a4 * a6 * a7 ^ 3 * H ^ 16 +
    (413614080 : K[X]) * a5 ^ 2 * a7 ^ 3 * H ^ 16 -
    (56401920 : K[X]) * a5 * a6 ^ 2 * a7 ^ 2 * H ^ 16 -
    (208896000 : K[X]) * a6 ^ 4 * a7 * H ^ 16 -
    (584908800 : K[X]) * a5 * a7 ^ 3 * b7 * H ^ 15 -
    (877363200 : K[X]) * a6 ^ 2 * a7 ^ 2 * b7 * H ^ 15 -
    (501350400 : K[X]) * a6 * a7 ^ 3 * b6 * H ^ 15 -
    (104448000 : K[X]) * a7 ^ 4 * b5 * H ^ 15 -
    (18278400 : K[X]) * a4 * a7 ^ 5 * H ^ 12 +
    (9792000 : K[X]) * a5 * a6 * a7 ^ 4 * H ^ 12 +
    (613632000 : K[X]) * a6 ^ 3 * a7 ^ 3 * H ^ 12 +
    (603187200 : K[X]) * a6 * a7 ^ 4 * b7 * H ^ 11 +
    (103403520 : K[X]) * a7 ^ 5 * b6 * H ^ 11 +
    (15708000 : K[X]) * a5 * a7 ^ 6 * H ^ 8 -
    (447004800 : K[X]) * a6 ^ 2 * a7 ^ 5 * H ^ 8 -
    (103044480 : K[X]) * a7 ^ 6 * b7 * H ^ 7 +
    (115005000 : K[X]) * a6 * a7 ^ 7 * H ^ 4 -
    (9392075 : K[X]) * a7 ^ 9 +
    Polynomial.C κ *
      ((16777216 : K[X]) * a1 * H ^ 31 -
        (18874368 : K[X]) * a2 * a7 * H ^ 27 -
        (18874368 : K[X]) * a3 * a6 * H ^ 27 -
        (18874368 : K[X]) * a4 * a5 * H ^ 27 +
        (20054016 : K[X]) * a3 * a7 ^ 2 * H ^ 23 +
        (40108032 : K[X]) * a4 * a6 * a7 * H ^ 23 +
        (20054016 : K[X]) * a5 ^ 2 * a7 * H ^ 23 +
        (20054016 : K[X]) * a5 * a6 ^ 2 * H ^ 23 -
        (20889600 : K[X]) * a4 * a7 ^ 3 * H ^ 19 -
        (62668800 : K[X]) * a5 * a6 * a7 ^ 2 * H ^ 19 -
        (20889600 : K[X]) * a6 ^ 3 * a7 * H ^ 19 +
        (21542400 : K[X]) * a5 * a7 ^ 4 * H ^ 15 +
        (43084800 : K[X]) * a6 ^ 2 * a7 ^ 3 * H ^ 15 -
        (22080960 : K[X]) * a6 * a7 ^ 5 * H ^ 11 +
        (3220140 : K[X]) * a7 ^ 7 * H ^ 7)

set_option maxHeartbeats 1600000000 in
/-- Exact combination of the degree-`8` Jacobian expression with the
weighted derivative of `L`.  Every correction on the right-hand side
vanishes on the aligned face with the consumed degree-`15`,
degree-`14`, degree-`13`, degree-`12`, degree-`11`, degree-`10`, and
degree-`9` rows. -/
theorem alignedNinthDefect_weightedDerivative_identity_810 {K : Type*}
    [Field K] [CharZero K]
    (H a0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 b8 b9 : K[X])
    (κ : K) :
    (134217728 : K[X]) * H ^ 28 *
        ((H ^ 4).derivative * b1 +
          a7.derivative * (b2 * (2 : K[X])) +
          a6.derivative * (b3 * (3 : K[X])) +
          a5.derivative * (b4 * (4 : K[X])) +
          a4.derivative * (b5 * (5 : K[X])) +
          a3.derivative * (b6 * (6 : K[X])) +
          a2.derivative * (b7 * (7 : K[X])) +
          a1.derivative * (b8 * (8 : K[X])) +
          a0.derivative * (b9 * (9 : K[X])) -
        ((H ^ 4 * (8 : K[X])) * b1.derivative +
          (a7 * (7 : K[X])) * b2.derivative +
          (a6 * (6 : K[X])) * b3.derivative +
          (a5 * (5 : K[X])) * b4.derivative +
          (a4 * (4 : K[X])) * b5.derivative +
          (a3 * (3 : K[X])) * b6.derivative +
          (a2 * (2 : K[X])) * b7.derivative +
          a1 * b8.derivative)) =
      ((2 : K[X]) * H *
          (alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
            b6 b7 κ).derivative -
        (63 : K[X]) *
          alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
            b6 b7 κ * H.derivative) -
        (301989888 : K[X]) * H ^ 28 * a0.derivative *
          ((5 : K[X]) * a7 * H - (4 : K[X]) * b9) +
        ((33554432 : K[X]) * H ^ 25 * a1.derivative +
            (12582912 : K[X]) * a1 * H ^ 24 * H.derivative) *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 - Polynomial.C κ * H ^ 7) -
        (4194304 : K[X]) * H ^ 25 * a1 *
          ((32 : K[X]) * b8 * H ^ 3 - (40 : K[X]) * a6 * H ^ 4 -
            (5 : K[X]) * a7 ^ 2 -
            Polynomial.C κ * H ^ 7).derivative +
        ((4718592 : K[X]) * a2 * H ^ 20 +
            (4128768 : K[X]) * a3 * a7 * H ^ 16 +
            (4128768 : K[X]) * a4 * a6 * H ^ 16 +
            (2064384 : K[X]) * a5 ^ 2 * H ^ 16 -
            (258048 : K[X]) * a4 * a7 ^ 2 * H ^ 12 -
            (516096 : K[X]) * a5 * a6 * a7 * H ^ 12 -
            (86016 : K[X]) * a6 ^ 3 * H ^ 12 +
            (96768 : K[X]) * a5 * a7 ^ 3 * H ^ 8 +
            (145152 : K[X]) * a6 ^ 2 * a7 ^ 2 * H ^ 8 -
            (51408 : K[X]) * a6 * a7 ^ 4 * H ^ 4 +
            (5355 : K[X]) * a7 ^ 6) *
          ((2 : K[X]) * H *
              (alignedThirdDefect810 H a5 a6 a7 b7 κ).derivative -
            (21 : K[X]) * alignedThirdDefect810 H a5 a6 a7 b7 κ *
              H.derivative) +
        ((589824 : K[X]) * a3 * H ^ 16 +
            (442368 : K[X]) * a4 * a7 * H ^ 12 +
            (442368 : K[X]) * a5 * a6 * H ^ 12 -
            (55296 : K[X]) * a5 * a7 ^ 2 * H ^ 8 -
            (55296 : K[X]) * a6 ^ 2 * a7 * H ^ 8 +
            (23040 : K[X]) * a6 * a7 ^ 3 * H ^ 4 -
            (2592 : K[X]) * a7 ^ 5) *
          (H * (alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ).derivative -
            (14 : K[X]) * alignedFourthDefect810 H a4 a5 a6 a7 b6 b7 κ *
              H.derivative) +
        ((36864 : K[X]) * a4 * H ^ 12 +
            (23040 : K[X]) * a5 * a7 * H ^ 8 +
            (11520 : K[X]) * a6 ^ 2 * H ^ 8 -
            (4320 : K[X]) * a6 * a7 ^ 2 * H ^ 4 +
            (495 : K[X]) * a7 ^ 4) *
          ((2 : K[X]) * H *
              (alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
                κ).derivative -
            (35 : K[X]) * alignedFifthDefect810 H a3 a4 a5 a6 a7 b5 b6 b7
              κ * H.derivative) +
        ((18432 : K[X]) * a5 * H ^ 8 + (9216 : K[X]) * a6 * a7 * H ^ 4 -
            (768 : K[X]) * a7 ^ 3) *
          (H * (alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5 b6 b7
                κ).derivative -
            (21 : K[X]) * alignedSixthDefect810 H a2 a3 a4 a5 a6 a7 b4 b5
              b6 b7 κ * H.derivative) +
        ((144 : K[X]) * a6 * H ^ 4 + (27 : K[X]) * a7 ^ 2) *
          ((2 : K[X]) * H *
              (alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ).derivative -
            (49 : K[X]) *
              alignedSeventhDefect810 H a1 a2 a3 a4 a5 a6 a7 b3 b4 b5
                b6 b7 κ * H.derivative) +
        (36 : K[X]) * a7 *
          (H * (alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3
                b4 b5 b6 b7 κ).derivative -
            (28 : K[X]) *
              alignedEighthDefect810 H a0 a1 a2 a3 a4 a5 a6 a7 b2 b3 b4
                b5 b6 b7 κ * H.derivative) := by
  simp only [alignedNinthDefect810, alignedEighthDefect810,
    alignedSeventhDefect810, alignedSixthDefect810, alignedFifthDefect810,
    alignedFourthDefect810, alignedThirdDefect810,
    Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_neg, Polynomial.derivative_ofNat,
    Polynomial.derivative_C, nsmul_eq_mul,
    zero_mul, mul_zero, zero_add, add_zero]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_zero, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_C,
    Polynomial.eval_natCast,
    Polynomial.eval_ofNat]
  ring

set_option maxHeartbeats 1600000000 in
/-- On the aligned face, with the consumed degree-`15` through
degree-`9` rows, the degree-`8` row is the weighted derivative
`2 H L' - 63 L H' = 0`. -/
theorem alignedNinthDefectRow_eq_zero_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    (2 : K[X]) * H *
        (alignedNinthDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 1)
          (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ).derivative -
      (63 : K[X]) *
        alignedNinthDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 1)
          (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ * H.derivative = 0 := by
  have hrow := alignedNinthCoefficientJacobianRow_810 hp hq hjac
  rw [hp8] at hrow
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) := C_ofNat_poly
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) := C_ofNat_poly
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) := C_ofNat_poly
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) := C_ofNat_poly
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) := C_ofNat_poly
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) := C_ofNat_poly
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) := C_ofNat_poly
  rw [hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9] at hrow
  have hC0 :
      (32 : K[X]) * q.coeff 8 * H ^ 3 - (40 : K[X]) * p.coeff 6 * H ^ 4 -
          (5 : K[X]) * p.coeff 7 ^ 2 - Polynomial.C κ * H ^ 7 = 0 := by
    have hM' :
        (32 : K[X]) * q.coeff 8 * H ^ 3 -
            (40 : K[X]) * p.coeff 6 * H ^ 4 -
            (5 : K[X]) * p.coeff 7 ^ 2 = Polynomial.C κ * H ^ 7 := by
      simpa only [alignedSecondDefect810] using hM
    linear_combination hM'
  have hrowD :
      (2 : K[X]) * H *
          (alignedThirdDefect810 H (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 7) κ).derivative -
        (21 : K[X]) *
          alignedThirdDefect810 H (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 7) κ * H.derivative = 0 :=
    alignedThirdDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowE :
      H * (alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ).derivative -
        (14 : K[X]) *
          alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 :=
    alignedFourthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowF :
      (2 : K[X]) * H *
          (alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ).derivative -
        (35 : K[X]) *
          alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ * H.derivative = 0 :=
    alignedFifthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowG :
      H * (alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ).derivative -
        (21 : K[X]) *
          alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ * H.derivative = 0 :=
    alignedSixthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowI :
      (2 : K[X]) * H *
          (alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ).derivative -
        (49 : K[X]) *
          alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ *
          H.derivative = 0 :=
    alignedSeventhDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hrowJ :
      H * (alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ).derivative -
        (28 : K[X]) *
          alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ * H.derivative = 0 :=
    alignedEighthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hid := alignedNinthDefect_weightedDerivative_identity_810
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) (p.coeff 4)
    (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 1) (q.coeff 2)
    (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
    (q.coeff 8) (q.coeff 9) κ
  rw [hrow, haligned, hC0, hrowD, hrowE, hrowF, hrowG, hrowI, hrowJ]
    at hid
  simp only [Polynomial.derivative_zero, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add] at hid
  linear_combination -hid

/-- Squared weight-sixty-three polynomial first integral of the aligned
`(8,10)` ninth defect: `L² = κ₈ H⁶³`.  The exponent is odd, so the
integral is chambered. -/
theorem alignedNinthDefectPowerRelation_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]} {κ : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0)
    (hM : alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
      Polynomial.C κ * H ^ 7) :
    ∃ κ₈ : K,
      alignedNinthDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
          (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 1)
          (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
          (q.coeff 7) κ ^ 2 =
        Polynomial.C κ₈ * H ^ 63 := by
  let L : K[X] :=
    alignedNinthDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 1)
      (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
      (q.coeff 7) κ
  have hrow :
      (2 : K[X]) * H * L.derivative -
        (63 : K[X]) * L * H.derivative = 0 := by
    simpa only [L] using
      alignedNinthDefectRow_eq_zero_810 hp hq hjac hp8 hq10 haligned hM
  have hC63 : Polynomial.C (63 : K) = (63 : K[X]) := C_ofNat_poly
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) := C_ofNat_poly
  have hW : Polynomial.wronskian (L ^ 2) (H ^ 63) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      L ^ 2 * (Polynomial.C (63 : K) * H ^ (63 - 1) * H.derivative) -
          Polynomial.C (2 : K) * L ^ (2 - 1) * L.derivative * H ^ 63 =
          L * H ^ 62 *
            (Polynomial.C (63 : K) * L * H.derivative -
              Polynomial.C (2 : K) * H * L.derivative) := by
        ring
      _ = 0 := by
        rw [hC63, hC2]
        have hfac :
            (63 : K[X]) * L * H.derivative -
              (2 : K[X]) * H * L.derivative = 0 := by
          linear_combination -hrow
        rw [hfac, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 63 hH) hW

/-! ## Root branch of the factored transport and its absorption -/

/-- Evaluating a factored-transport ninth row at a root of its
co-factor: either the descent quotient vanishes there, or the even
nonic core `15785 g⁸ - 174240 p₆ g⁶ + 659520 p₆² g⁴ - 976896 p₆³ g²
+ 442368 p₆⁴` does.  Neither branch is excluded. -/
theorem alignedNinth_factored_rootBranch_810 {K : Type*}
    [Field K] [CharZero K] {g a6 W : K[X]}
    (hfac : (340 : K[X]) * g *
        ((15785 : K[X]) * g ^ 8 - (174240 : K[X]) * a6 * g ^ 6 +
          (659520 : K[X]) * a6 ^ 2 * g ^ 4 -
          (976896 : K[X]) * a6 ^ 3 * g ^ 2 +
          (442368 : K[X]) * a6 ^ 4) = W)
    {a : K} (hW : W.eval a = 0) :
    g.eval a = 0 ∨
      15785 * (g.eval a) ^ 8 - 174240 * a6.eval a * (g.eval a) ^ 6 +
        659520 * (a6.eval a) ^ 2 * (g.eval a) ^ 4 -
        976896 * (a6.eval a) ^ 3 * (g.eval a) ^ 2 +
        442368 * (a6.eval a) ^ 4 = 0 := by
  have hev := congrArg (fun f : K[X] => f.eval a) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hW] at hev
  rcases mul_eq_zero.mp hev with h340g | hnonic
  · exact Or.inl
      ((mul_eq_zero.mp h340g).resolve_left (by norm_num : (340 : K) ≠ 0))
  · exact Or.inr (by linear_combination hnonic)

/-- The root nonic of the consumed degree-`8` row is absorbed by the
collapse of the degree-`13` face: at a root where `g` and `p₆` already
vanish it holds identically, so the ninth row adds no new root
constraint. -/
theorem alignedNinth_rootNonic_absorbed_810 {K : Type*} [Field K]
    {P6 G : K} (hG : G = 0) (hP6 : P6 = 0) :
    340 * G * (15785 * G ^ 8 - 174240 * P6 * G ^ 6 +
      659520 * P6 ^ 2 * G ^ 4 - 976896 * P6 ^ 3 * G ^ 2 +
      442368 * P6 ^ 4) = 0 := by
  rw [hG, hP6]
  ring

/-! ## Cleared ninth rows and transport co-factors -/

/-- Transport co-factor of the square-chamber ninth row (`H = h₀²`,
`p₇ = h₀⁴ g₁`, `h₀³⁶` peeled, `128 q₇ h₀²` consumed): the new `q₁`
sits at `h₀²²` here, i.e. at `h₀²⁶` in the cleared row. -/
def alignedNinthSquareCof810 {K : Type*} [CommRing K]
    (h0 g1 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ μ : K) :
    K[X] :=
    -(536870912 : K[X]) * b1 * h0 ^ 22 +
    (134217728 : K[X]) * b2 * g1 * h0 ^ 18 -
    (83886080 : K[X]) * a1 * a6 * h0 ^ 16 +
    (36700160 : K[X]) * a1 * g1 ^ 2 * h0 ^ 16 -
    (167772160 : K[X]) * a2 * a5 * h0 ^ 16 -
    (754974720 : K[X]) * a3 * a4 * h0 ^ 16 +
    (402653184 : K[X]) * a3 * b6 * h0 ^ 14 +
    (335544320 : K[X]) * a4 * b5 * h0 ^ 14 +
    (268435456 : K[X]) * a5 * b4 * h0 ^ 14 +
    (201326592 : K[X]) * a6 * b3 * h0 ^ 14 -
    (113246208 : K[X]) * b3 * g1 ^ 2 * h0 ^ 14 +
    (146800640 : K[X]) * a2 * a6 * g1 * h0 ^ 12 -
    (45875200 : K[X]) * a2 * g1 ^ 3 * h0 ^ 12 +
    (94371840 : K[X]) * a3 * a5 * g1 * h0 ^ 12 +
    (377487360 : K[X]) * a4 ^ 2 * g1 * h0 ^ 12 -
    (452984832 : K[X]) * a4 * b6 * g1 * h0 ^ 10 -
    (377487360 : K[X]) * a5 * b5 * g1 * h0 ^ 10 -
    (301989888 : K[X]) * a6 * b4 * g1 * h0 ^ 10 +
    (106954752 : K[X]) * b4 * g1 ^ 3 * h0 ^ 10 +
    (47185920 : K[X]) * a3 * a6 ^ 2 * h0 ^ 8 -
    (159252480 : K[X]) * a3 * a6 * g1 ^ 2 * h0 ^ 8 +
    (42577920 : K[X]) * a3 * g1 ^ 4 * h0 ^ 8 +
    (188743680 : K[X]) * a4 * a5 * a6 * h0 ^ 8 -
    (94371840 : K[X]) * a4 * a5 * g1 ^ 2 * h0 ^ 8 -
    (62914560 : K[X]) * a5 ^ 3 * h0 ^ 8 -
    (452984832 : K[X]) * a5 * a6 * b6 * h0 ^ 6 +
    (481296384 : K[X]) * a5 * b6 * g1 ^ 2 * h0 ^ 6 -
    (188743680 : K[X]) * a6 ^ 2 * b5 * h0 ^ 6 +
    (401080320 : K[X]) * a6 * b5 * g1 ^ 2 * h0 ^ 6 -
    (104448000 : K[X]) * b5 * g1 ^ 4 * h0 ^ 6 -
    (165150720 : K[X]) * a4 * a6 ^ 2 * g1 * h0 ^ 4 +
    (187760640 : K[X]) * a4 * a6 * g1 ^ 3 * h0 ^ 4 -
    (40212480 : K[X]) * a4 * g1 ^ 5 * h0 ^ 4 +
    (519045120 : K[X]) * a5 ^ 2 * a6 * g1 * h0 ^ 4 -
    (307200000 : K[X]) * a5 ^ 2 * g1 ^ 3 * h0 ^ 4 +
    (481296384 : K[X]) * a6 ^ 2 * b6 * g1 * h0 ^ 2 -
    (501350400 : K[X]) * a6 * b6 * g1 ^ 3 * h0 ^ 2 +
    (103403520 : K[X]) * b6 * g1 ^ 5 * h0 ^ 2 +
    (200540160 : K[X]) * a5 * a6 ^ 3 -
    (802160640 : K[X]) * a5 * a6 ^ 2 * g1 ^ 2 +
    (537123840 : K[X]) * a5 * a6 * g1 ^ 4 -
    (90249600 : K[X]) * a5 * g1 ^ 6 +
    Polynomial.C κ *
      ((16777216 : K[X]) * a1 * h0 ^ 22 -
        (4194304 : K[X]) * a2 * g1 * h0 ^ 18 -
        (18874368 : K[X]) * a3 * a6 * h0 ^ 14 +
        (3538944 : K[X]) * a3 * g1 ^ 2 * h0 ^ 14 -
        (18874368 : K[X]) * a4 * a5 * h0 ^ 14 +
        (23592960 : K[X]) * a4 * a6 * g1 * h0 ^ 10 -
        (3342336 : K[X]) * a4 * g1 ^ 3 * h0 ^ 10 +
        (11796480 : K[X]) * a5 ^ 2 * g1 * h0 ^ 10 +
        (20054016 : K[X]) * a5 * a6 ^ 2 * h0 ^ 6 -
        (27574272 : K[X]) * a5 * a6 * g1 ^ 2 * h0 ^ 6 +
        (3264000 : K[X]) * a5 * g1 ^ 4 * h0 ^ 6 -
        (15040512 : K[X]) * a6 ^ 3 * g1 * h0 ^ 2 +
        (15667200 : K[X]) * a6 ^ 2 * g1 ^ 3 * h0 ^ 2 -
        (3231360 : K[X]) * a6 * g1 ^ 5 * h0 ^ 2) -
    Polynomial.C μ *
      ((3670016 : K[X]) * a2 * h0 ^ 21 -
        (4128768 : K[X]) * a3 * g1 * h0 ^ 17 -
        (4128768 : K[X]) * a4 * a6 * h0 ^ 13 +
        (4386816 : K[X]) * a4 * g1 ^ 2 * h0 ^ 13 -
        (2064384 : K[X]) * a5 ^ 2 * h0 ^ 13 +
        (8773632 : K[X]) * a5 * a6 * g1 * h0 ^ 9 -
        (4569600 : K[X]) * a5 * g1 ^ 3 * h0 ^ 9 +
        (1462272 : K[X]) * a6 ^ 3 * h0 ^ 5 -
        (6854400 : K[X]) * a6 ^ 2 * g1 ^ 2 * h0 ^ 5 +
        (4712400 : K[X]) * a6 * g1 ^ 4 * h0 ^ 5 -
        (805035 : K[X]) * g1 ^ 6 * h0 ^ 5)

/-- Cleared ninth row of the square chamber, in factored form: the
pure `g₁, p₆` nonic block plus `h₀⁴` times the transport co-factor. -/
def alignedNinthSquareRow810 {K : Type*} [CommRing K]
    (h0 g1 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ μ : K) :
    K[X] :=
  h0 ^ 4 *
      alignedNinthSquareCof810 h0 g1 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5
        b6 κ μ -
    (340 : K[X]) * g1 *
      ((15785 : K[X]) * g1 ^ 8 - (174240 : K[X]) * a6 * g1 ^ 6 +
        (659520 : K[X]) * a6 ^ 2 * g1 ^ 4 -
        (976896 : K[X]) * a6 ^ 3 * g1 ^ 2 +
        (442368 : K[X]) * a6 ^ 4)

/-- Transport co-factor of the nonsquare-chamber ninth row
(`p₇ = H² g₂`, `H¹⁸` peeled, `128 q₇ H` consumed): the new `q₁` sits
at `H¹¹` here, i.e. at `H¹³` in the cleared row. -/
def alignedNinthNonsquareCof810 {K : Type*} [CommRing K]
    (H g2 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
    -(536870912 : K[X]) * b1 * H ^ 11 +
    (134217728 : K[X]) * b2 * g2 * H ^ 9 -
    (83886080 : K[X]) * a1 * a6 * H ^ 8 +
    (36700160 : K[X]) * a1 * g2 ^ 2 * H ^ 8 -
    (167772160 : K[X]) * a2 * a5 * H ^ 8 -
    (754974720 : K[X]) * a3 * a4 * H ^ 8 +
    (402653184 : K[X]) * a3 * b6 * H ^ 7 +
    (335544320 : K[X]) * a4 * b5 * H ^ 7 +
    (268435456 : K[X]) * a5 * b4 * H ^ 7 +
    (201326592 : K[X]) * a6 * b3 * H ^ 7 -
    (113246208 : K[X]) * b3 * g2 ^ 2 * H ^ 7 +
    (146800640 : K[X]) * a2 * a6 * g2 * H ^ 6 -
    (45875200 : K[X]) * a2 * g2 ^ 3 * H ^ 6 +
    (94371840 : K[X]) * a3 * a5 * g2 * H ^ 6 +
    (377487360 : K[X]) * a4 ^ 2 * g2 * H ^ 6 -
    (452984832 : K[X]) * a4 * b6 * g2 * H ^ 5 -
    (377487360 : K[X]) * a5 * b5 * g2 * H ^ 5 -
    (301989888 : K[X]) * a6 * b4 * g2 * H ^ 5 +
    (106954752 : K[X]) * b4 * g2 ^ 3 * H ^ 5 +
    (47185920 : K[X]) * a3 * a6 ^ 2 * H ^ 4 -
    (159252480 : K[X]) * a3 * a6 * g2 ^ 2 * H ^ 4 +
    (42577920 : K[X]) * a3 * g2 ^ 4 * H ^ 4 +
    (188743680 : K[X]) * a4 * a5 * a6 * H ^ 4 -
    (94371840 : K[X]) * a4 * a5 * g2 ^ 2 * H ^ 4 -
    (62914560 : K[X]) * a5 ^ 3 * H ^ 4 -
    (452984832 : K[X]) * a5 * a6 * b6 * H ^ 3 +
    (481296384 : K[X]) * a5 * b6 * g2 ^ 2 * H ^ 3 -
    (188743680 : K[X]) * a6 ^ 2 * b5 * H ^ 3 +
    (401080320 : K[X]) * a6 * b5 * g2 ^ 2 * H ^ 3 -
    (104448000 : K[X]) * b5 * g2 ^ 4 * H ^ 3 -
    (165150720 : K[X]) * a4 * a6 ^ 2 * g2 * H ^ 2 +
    (187760640 : K[X]) * a4 * a6 * g2 ^ 3 * H ^ 2 -
    (40212480 : K[X]) * a4 * g2 ^ 5 * H ^ 2 +
    (519045120 : K[X]) * a5 ^ 2 * a6 * g2 * H ^ 2 -
    (307200000 : K[X]) * a5 ^ 2 * g2 ^ 3 * H ^ 2 +
    (481296384 : K[X]) * a6 ^ 2 * b6 * g2 * H -
    (501350400 : K[X]) * a6 * b6 * g2 ^ 3 * H +
    (103403520 : K[X]) * b6 * g2 ^ 5 * H +
    (200540160 : K[X]) * a5 * a6 ^ 3 -
    (802160640 : K[X]) * a5 * a6 ^ 2 * g2 ^ 2 +
    (537123840 : K[X]) * a5 * a6 * g2 ^ 4 -
    (90249600 : K[X]) * a5 * g2 ^ 6 +
    Polynomial.C κ *
      ((16777216 : K[X]) * a1 * H ^ 11 -
        (4194304 : K[X]) * a2 * g2 * H ^ 9 -
        (18874368 : K[X]) * a3 * a6 * H ^ 7 +
        (3538944 : K[X]) * a3 * g2 ^ 2 * H ^ 7 -
        (18874368 : K[X]) * a4 * a5 * H ^ 7 +
        (23592960 : K[X]) * a4 * a6 * g2 * H ^ 5 -
        (3342336 : K[X]) * a4 * g2 ^ 3 * H ^ 5 +
        (11796480 : K[X]) * a5 ^ 2 * g2 * H ^ 5 +
        (20054016 : K[X]) * a5 * a6 ^ 2 * H ^ 3 -
        (27574272 : K[X]) * a5 * a6 * g2 ^ 2 * H ^ 3 +
        (3264000 : K[X]) * a5 * g2 ^ 4 * H ^ 3 -
        (15040512 : K[X]) * a6 ^ 3 * g2 * H +
        (15667200 : K[X]) * a6 ^ 2 * g2 ^ 3 * H -
        (3231360 : K[X]) * a6 * g2 ^ 5 * H)

/-- Cleared ninth row of the nonsquare chamber, in factored form: the
pure `g₂, p₆` nonic block plus `H²` times the transport co-factor. -/
def alignedNinthNonsquareRow810 {K : Type*} [CommRing K]
    (H g2 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : K[X]) (κ : K) :
    K[X] :=
  H ^ 2 *
      alignedNinthNonsquareCof810 H g2 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5
        b6 κ -
    (340 : K[X]) * g2 *
      ((15785 : K[X]) * g2 ^ 8 - (174240 : K[X]) * a6 * g2 ^ 6 +
        (659520 : K[X]) * a6 ^ 2 * g2 ^ 4 -
        (976896 : K[X]) * a6 ^ 3 * g2 ^ 2 +
        (442368 : K[X]) * a6 ^ 4)

/-! ## Square chamber -/

/-- In the square chamber the squared weight-sixty-three integral has a
polynomial square root with square core: `L = ν₃ h₀⁶³` with `ν₃² = κ₈`.
The constant `ν₃` is preserved, not cleared. -/
theorem alignedSquareNinth_sqrt_810 {K : Type*} [Field K] [CharZero K]
    {H h0 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ κ₈ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hL2 : alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
        b6 b7 κ ^ 2 =
      Polynomial.C κ₈ * H ^ 63) :
    ∃ ν₃ : K, ν₃ ^ 2 = κ₈ ∧
      alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7
          κ =
        Polynomial.C ν₃ * h0 ^ 63 := by
  set L : K[X] :=
    alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 κ
    with hLdef
  have hdvd : (h0 ^ 63) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₈, ?_⟩
    rw [hL2, hHsq]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₈ := by
    have h126 := hL2
    rw [hG, hHsq] at h126
    apply mul_left_cancel₀ (pow_ne_zero 126 hh0)
    linear_combination h126
  have hGdeg : G.natDegree = 0 := by
    have h2 : (G ^ 2).natDegree = 0 := by
      rw [hG2]
      exact Polynomial.natDegree_C κ₈
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨ν₃, hν⟩ := Polynomial.natDegree_eq_zero.mp hGdeg
  refine ⟨ν₃, ?_, ?_⟩
  · have hCν : Polynomial.C (ν₃ ^ 2) = Polynomial.C κ₈ := by
      rw [Polynomial.C_pow, hν, hG2]
    exact Polynomial.C_injective hCν
  · rw [hG, ← hν]
    ring

set_option maxHeartbeats 1600000000 in
/-- Peeling `h₀³⁶` from `L = ν₃ h₀⁶³` on `H = h₀²`, `p₇ = h₀⁴ g₁` and
consuming the previous factored quotient (`128 q₇ h₀²` solved),
transported by the mate `3670016 p₂ h₀¹⁶ - 4128768 p₃ g₁ h₀¹²
- 4128768 p₄ p₆ h₀⁸ + 4386816 p₄ g₁² h₀⁸ - 2064384 p₅² h₀⁸
+ 8773632 p₅ p₆ g₁ h₀⁴ - 4569600 p₅ g₁³ h₀⁴ + 1462272 p₆³
- 6854400 p₆² g₁² + 4712400 p₆ g₁⁴ - 805035 g₁⁶`, leaves the cleared
ninth row of the square chamber together with its factored transport
form. -/
theorem alignedSquareNinth_solved_810 {K : Type*} [Field K] [CharZero K]
    {H h0 g1 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]}
    {κ μ ν₃ : K}
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) (hg : a7 = h0 ^ 4 * g1)
    (hL : alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
        b6 b7 κ =
      Polynomial.C ν₃ * h0 ^ 63)
    (hq7 :
      (128 : K[X]) * b7 * h0 ^ 2 =
        (160 : K[X]) * a5 * h0 ^ 4 + (40 : K[X]) * a6 * g1 -
          (5 : K[X]) * g1 ^ 3 +
          Polynomial.C κ * ((4 : K[X]) * g1 * h0 ^ 6) -
          Polynomial.C μ * h0 ^ 9) :
    alignedNinthSquareRow810 h0 g1 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
        κ μ =
      Polynomial.C ν₃ * h0 ^ 27 ∧
    (340 : K[X]) * g1 *
        ((15785 : K[X]) * g1 ^ 8 - (174240 : K[X]) * a6 * g1 ^ 6 +
          (659520 : K[X]) * a6 ^ 2 * g1 ^ 4 -
          (976896 : K[X]) * a6 ^ 3 * g1 ^ 2 +
          (442368 : K[X]) * a6 ^ 4) =
      h0 ^ 4 *
        (alignedNinthSquareCof810 h0 g1 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4
            b5 b6 κ μ -
          Polynomial.C ν₃ * h0 ^ 23) := by
  have hL' := hL
  simp only [alignedNinthDefect810, hHsq, hg] at hL'
  have hclear :
      alignedNinthSquareRow810 h0 g1 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5
          b6 κ μ =
        Polynomial.C ν₃ * h0 ^ 27 := by
    simp only [alignedNinthSquareRow810, alignedNinthSquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 36 hh0)
    linear_combination hL' -
      h0 ^ 36 *
        (         (3670016 : K[X]) * a2 * h0 ^ 16 -
            (4128768 : K[X]) * a3 * g1 * h0 ^ 12 -
            (4128768 : K[X]) * a4 * a6 * h0 ^ 8 +
            (4386816 : K[X]) * a4 * g1 ^ 2 * h0 ^ 8 -
            (2064384 : K[X]) * a5 ^ 2 * h0 ^ 8 +
            (8773632 : K[X]) * a5 * a6 * g1 * h0 ^ 4 -
            (4569600 : K[X]) * a5 * g1 ^ 3 * h0 ^ 4 +
            (1462272 : K[X]) * a6 ^ 3 -
            (6854400 : K[X]) * a6 ^ 2 * g1 ^ 2 +
            (4712400 : K[X]) * a6 * g1 ^ 4 -
            (805035 : K[X]) * g1 ^ 6) * hq7
  refine ⟨hclear, ?_⟩
  simp only [alignedNinthSquareRow810] at hclear
  linear_combination -hclear

/-! ## Nonsquare chamber -/

/-- In the nonsquare chamber the odd exponent of the squared
weight-sixty-three integral forces its constant to vanish, and with it
the whole ninth defect. -/
theorem alignedNonsquareNinth_defect_eq_zero_810 {k : Type*}
    [Field k] [CharZero k] [IsAlgClosed k]
    {H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : k[X]} {κ κ₈ : k}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hL2 : alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
        b6 b7 κ ^ 2 =
      Polynomial.C κ₈ * H ^ 63) :
    κ₈ = 0 ∧
      alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7
          κ =
        0 := by
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  set L : k[X] :=
    alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 κ
    with hLdef
  have hdvd : (H ^ 31) ^ 2 ∣ L ^ 2 := by
    refine ⟨Polynomial.C κ₈ * H, ?_⟩
    rw [hL2]
    ring
  obtain ⟨G, hG⟩ := dvd_of_sq_dvd_sq_poly hdvd
  have hG2 : G ^ 2 = Polynomial.C κ₈ * H := by
    apply mul_left_cancel₀ (pow_ne_zero 62 hH)
    have h62 := hL2
    rw [hG] at h62
    linear_combination h62
  have hGroot : ∀ a : k, H.eval a = 0 → G.eval a = 0 := by
    intro a ha
    have hev := congrArg (fun f : k[X] => f.eval a) hG2
    simp only [Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_C] at hev
    rw [ha, mul_zero] at hev
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hev
  obtain ⟨G1, hG1⟩ :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple hGroot
  have hG12 : H * G1 ^ 2 = Polynomial.C κ₈ := by
    apply mul_left_cancel₀ hH
    have h2 := hG2
    rw [hG1] at h2
    linear_combination h2
  have hdegne : H.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hH, hdeg]
    decide
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H hdegne
  have hroot : H.eval a = 0 := ha
  have hk8 : κ₈ = 0 := by
    have hev := congrArg (fun f : k[X] => f.eval a) hG12
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C] at hev
    rw [hroot, zero_mul] at hev
    exact hev.symm
  have hLzero : L = 0 := by
    have hsq : L ^ 2 = 0 := by
      rw [hL2, hk8]
      simp
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  exact ⟨hk8, hLzero⟩

set_option maxHeartbeats 1600000000 in
/-- Peeling `H¹⁸` from the vanished ninth defect on `p₇ = H² g₂`, then
consuming the previous factored quotient with the mate
`3670016 p₂ H⁸ - 4128768 p₃ g₂ H⁶ - 4128768 p₄ p₆ H⁴ + 4386816 p₄ g₂² H⁴
- 2064384 p₅² H⁴ + 8773632 p₅ p₆ g₂ H² - 4569600 p₅ g₂³ H² + 1462272 p₆³
- 6854400 p₆² g₂² + 4712400 p₆ g₂⁴ - 805035 g₂⁶`, leaves the cleared
ninth row of the nonsquare chamber together with its factored transport
form. -/
theorem alignedNonsquareNinth_solved_810 {K : Type*}
    [Field K] [CharZero K]
    {H g2 a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : K[X]} {κ : K}
    (hH : H ≠ 0) (hg2 : a7 = H ^ 2 * g2)
    (hL0 : alignedNinthDefect810 H a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5
        b6 b7 κ = 0)
    (hfac :
      (5 : K[X]) * g2 * (g2 ^ 2 - (8 : K[X]) * a6) =
        H * ((160 : K[X]) * a5 * H - (128 : K[X]) * b7 +
          Polynomial.C κ * ((4 : K[X]) * g2 * H ^ 2))) :
    alignedNinthNonsquareRow810 H g2 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5
        b6 κ = 0 ∧
    (340 : K[X]) * g2 *
        ((15785 : K[X]) * g2 ^ 8 - (174240 : K[X]) * a6 * g2 ^ 6 +
          (659520 : K[X]) * a6 ^ 2 * g2 ^ 4 -
          (976896 : K[X]) * a6 ^ 3 * g2 ^ 2 +
          (442368 : K[X]) * a6 ^ 4) =
      H ^ 2 *
        alignedNinthNonsquareCof810 H g2 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4
          b5 b6 κ := by
  have hL' := hL0
  simp only [alignedNinthDefect810, hg2] at hL'
  have hclear :
      alignedNinthNonsquareRow810 H g2 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5
          b6 κ = 0 := by
    simp only [alignedNinthNonsquareRow810, alignedNinthNonsquareCof810]
    apply mul_left_cancel₀ (pow_ne_zero 18 hH)
    rw [mul_zero]
    linear_combination hL' -
      H ^ 18 *
        (         (3670016 : K[X]) * a2 * H ^ 8 -
            (4128768 : K[X]) * a3 * g2 * H ^ 6 -
            (4128768 : K[X]) * a4 * a6 * H ^ 4 +
            (4386816 : K[X]) * a4 * g2 ^ 2 * H ^ 4 -
            (2064384 : K[X]) * a5 ^ 2 * H ^ 4 +
            (8773632 : K[X]) * a5 * a6 * g2 * H ^ 2 -
            (4569600 : K[X]) * a5 * g2 ^ 3 * H ^ 2 +
            (1462272 : K[X]) * a6 ^ 3 -
            (6854400 : K[X]) * a6 ^ 2 * g2 ^ 2 +
            (4712400 : K[X]) * a6 * g2 ^ 4 -
            (805035 : K[X]) * g2 ^ 6) * hfac
  refine ⟨hclear, ?_⟩
  simp only [alignedNinthNonsquareRow810] at hclear
  linear_combination -hclear

/-! ## Source-facing ninth-row packets -/

/-- Source-facing squared weight-sixty-three integral of a normalized
aligned scale-two `(8,10)` source: the degree-`8` row is consumed into
`L² = κ₈ H⁶³` on top of the previous aligned packet. -/
theorem normalized810ScaleTwo_alignedNinthFace_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₄ κ₅ κ₆ κ₇ κ₈ : K),
      q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H ∧
        alignedSecondDefect810 H (p.coeff 6) (p.coeff 7) (q.coeff 8) =
          Polynomial.C κ * H ^ 7 ∧
        alignedFourthDefect810 H (p.coeff 4) (p.coeff 5) (p.coeff 6)
            (p.coeff 7) (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₃ * H ^ 14 ∧
        alignedFifthDefect810 H (p.coeff 3) (p.coeff 4) (p.coeff 5)
            (p.coeff 6) (p.coeff 7) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₄ * H ^ 35 ∧
        alignedSixthDefect810 H (p.coeff 2) (p.coeff 3) (p.coeff 4)
            (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 4) (q.coeff 5)
            (q.coeff 6) (q.coeff 7) κ =
          Polynomial.C κ₅ * H ^ 21 ∧
        alignedSeventhDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 3)
            (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₆ * H ^ 49 ∧
        alignedEighthDefect810 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ =
          Polynomial.C κ₇ * H ^ 28 ∧
        alignedNinthDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 1)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ ^ 2 =
          Polynomial.C κ₈ * H ^ 63 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_810 hp hq hjac hH hp8' hq10' haligned
  obtain ⟨κ₃, hE4⟩ :=
    alignedFourthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₄, hF2⟩ :=
    alignedFifthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₅, hG⟩ :=
    alignedSixthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₆, hI2⟩ :=
    alignedSeventhDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₇, hJ⟩ :=
    alignedEighthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨κ₈, hL2⟩ :=
    alignedNinthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  exact ⟨κ, κ₃, κ₄, κ₅, κ₆, κ₇, κ₈, aligned_q9_solved_810 haligned, hM,
    hE4, hF2, hG, hI2, hJ, hL2⟩

/-- Exact square-chamber ninth packet of a normalized aligned scale-two
`(8,10)` source: on top of `p₇ = h₀⁴ g₁`, `q₉ = (5/4) g₁ h₀⁶`, and the
previous packet, the consumed degree-`8` row gives `L = ν₃ h₀⁶³` with
`ν₃² = κ₈`, the cleared ninth row (with the new `q₁` at `h₀²⁶`) against
`ν₃ h₀²⁷`, the carried root collapse `g₁ = p₆ = 0`, and the carried
descents `h₀ ∣ g₁`, `h₀ ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedNinthFace_squareChamber_packet
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ μ κ₈ ν₃ : K) (g1 : K[X]),
      p.coeff 7 = h0 ^ 4 * g1 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
        ν₃ ^ 2 = κ₈ ∧
        alignedNinthSquareRow810 h0 g1 (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (q.coeff 1)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            κ μ =
          Polynomial.C ν₃ * h0 ^ 27 ∧
        (∀ a : K, h0.eval a = 0 →
          g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        h0 ∣ g1 ∧ h0 ∣ p.coeff 6 ∧
        alignedNinthDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 1)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ =
          Polynomial.C ν₃ * h0 ^ 63 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_810 hp hq hjac hH hp8' hq10' haligned
  obtain ⟨g, hg⟩ := alignedSquare_dvd_p7_810 hHsq hM
  have hq9 : q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H :=
    aligned_q9_solved_810 haligned
  obtain ⟨κ₂, hD2⟩ :=
    alignedThirdDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨μ, _hμ2, hD⟩ := alignedSquareThird_sqrt_810 hh0 hHsq hD2
  have hEcore := alignedSquareThird_core_810 hh0 hHsq hg hD
  have hdeg1 : h0.natDegree = 1 := by
    have h2 : (h0 ^ 2).natDegree = 2 := by rw [← hHsq]; exact hHdegree
    rw [Polynomial.natDegree_pow] at h2
    omega
  obtain ⟨g1, hg1, hcore, hfac⟩ :=
    alignedSquareThird_descent_810 hh0 hdeg1 hEcore
  have hp7 : p.coeff 7 = h0 ^ 4 * g1 := by rw [hg, hg1]; ring
  have hbranch : ∀ a : K, h0.eval a = 0 →
      g1.eval a = 0 ∨ g1.eval a ^ 2 = 8 * (p.coeff 6).eval a := by
    intro a ha
    refine alignedThird_factored_rootBranch_810 hfac ?_
    rw [Polynomial.eval_mul, Polynomial.eval_pow, ha,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
  obtain ⟨κ₃, hE4⟩ :=
    alignedFourthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  have hcore4 := alignedSquareFourth_core_810 hh0 hHsq hp7 hE4
  have hsolved4 := alignedSquareFourth_solved_810 hcore4 hcore
  have hcollapse : ∀ a : K, h0.eval a = 0 →
      g1.eval a = 0 ∧ (p.coeff 6).eval a = 0 := fun a ha =>
    alignedFourth_rootCollapse_810
      (alignedSquareFourth_rootQuartic_810 hsolved4 ha) (hbranch a ha)
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  have hroot : h0.eval (-(d / c)) = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    have hcd : d / c * c = d := div_mul_cancel₀ d hc
    linear_combination -hcd
  have hdvdg1 : h0 ∣ g1 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 g1 (-(d / c)) hdeg1
      hroot (hcollapse _ hroot).1
  have hdvdp6 : h0 ∣ p.coeff 6 :=
    linearPolynomial_dvd_of_eval_eq_zero_810 h0 (p.coeff 6) (-(d / c))
      hdeg1 hroot (hcollapse _ hroot).2
  obtain ⟨κ₈, hL2⟩ :=
    alignedNinthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨ν₃, hν3, hL⟩ := alignedSquareNinth_sqrt_810 hh0 hHsq hL2
  obtain ⟨hsolved9, _hfact9⟩ :=
    alignedSquareNinth_solved_810 hh0 hHsq hp7 hL hcore
  exact ⟨κ, μ, κ₈, ν₃, g1, hp7, by rw [hq9, hp7, hHsq]; ring, hν3,
    hsolved9, hcollapse, hdvdg1, hdvdp6, hL⟩

/-- Exact nonsquare-chamber ninth packet of a normalized aligned
scale-two `(8,10)` source: the squared weight-sixty-three constant
vanishes, the ninth defect is identically zero, and on top of
`p₇ = H² g₂` and the previous packet the consumed degree-`8` row gives
the cleared ninth row (with the new `q₁` at `H¹³`) equal to zero, the
carried root collapse `g₂ = p₆ = 0` at every (simple) root of the core,
and the carried descents `H ∣ g₂`, `H ∣ p₆`. -/
theorem normalized810ScaleTwo_alignedNinthFace_nonsquareChamber_packet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ : K) (g2 : K[X]),
      p.coeff 7 = H ^ 2 * g2 ∧
        q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
        alignedNinthNonsquareRow810 H g2 (p.coeff 1) (p.coeff 2)
            (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6) (q.coeff 1)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            κ = 0 ∧
        (∀ a : K, H.eval a = 0 →
          g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
        H ∣ g2 ∧ H ∣ p.coeff 6 ∧
        alignedNinthDefect810 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
            (p.coeff 4) (p.coeff 5) (p.coeff 6) (p.coeff 7) (q.coeff 1)
            (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
            (q.coeff 7) κ = 0 := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_810 hp hq hjac hH hp8' hq10' haligned
  obtain ⟨g, hg⟩ := alignedNonsquare_dvd_p7_810 hHdegree hnsq hM
  obtain ⟨g2, hg2'⟩ := alignedNonsquare_dvd_g_810 hHdegree hnsq hH hg hM
  have hg2 : p.coeff 7 = H ^ 2 * g2 := by
    rw [hg, hg2']
    ring
  have hq9 : q.coeff 9 = Polynomial.C (5 / 4 : K) * p.coeff 7 * H :=
    aligned_q9_solved_810 haligned
  obtain ⟨κ₂, hD2⟩ :=
    alignedThirdDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨_hk2, hD0⟩ :=
    alignedNonsquareThird_defect_eq_zero_810 hH hHdegree hnsq hD2
  obtain ⟨_hpeel, hfac⟩ := alignedNonsquareThird_solved_810 hH hg2 hD0
  have hbranch : ∀ a : K, H.eval a = 0 →
      g2.eval a = 0 ∨ g2.eval a ^ 2 = 8 * (p.coeff 6).eval a := by
    intro a ha
    refine alignedThird_factored_rootBranch_810 hfac ?_
    rw [Polynomial.eval_mul, ha, zero_mul]
  obtain ⟨κ₃, hE4⟩ :=
    alignedFourthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  have hcore4 := alignedNonsquareFourth_core_810 hH hg2 hE4
  have hsolved4 := alignedNonsquareFourth_solved_810 hcore4 hfac
  have hcollapse : ∀ a : K, H.eval a = 0 →
      g2.eval a = 0 ∧ (p.coeff 6).eval a = 0 := fun a ha =>
    alignedFourth_rootCollapse_810
      (alignedNonsquareFourth_rootQuartic_810 hsolved4 ha) (hbranch a ha)
  have hsimple : ∀ a : K, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero
      hHdegree hnsq ha
  have hdvdg2 : H ∣ g2 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple
      (fun a ha => (hcollapse a ha).1)
  have hdvdp6 : H ∣ p.coeff 6 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hHdegree hsimple
      (fun a ha => (hcollapse a ha).2)
  obtain ⟨κ₈, hL2⟩ :=
    alignedNinthDefectPowerRelation_810 hp hq hjac hH hp8' hq10'
      haligned hM
  obtain ⟨_hk8, hL0⟩ :=
    alignedNonsquareNinth_defect_eq_zero_810 hH hHdegree hnsq hL2
  obtain ⟨hclear9, _hfact9⟩ :=
    alignedNonsquareNinth_solved_810 hH hg2 hL0 hfac
  exact ⟨κ, g2, hg2, by rw [hq9, hg2]; ring, hclear9,
    hcollapse, hdvdg2, hdvdp6, hL0⟩

set_option maxHeartbeats 1600000000 in
/-- Honest square/nonsquare chamber split of the consumed degree-`8`
aligned row, carrying the factored transport of the nonic block.
Neither chamber is excluded; in the square chamber `ν₃` is preserved,
in the nonsquare chamber the odd exponent forces the cleared row to
vanish.  No closure is claimed. -/
theorem normalized810ScaleTwo_alignedNinthFace_chamberDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧
      ∃ (κ μ ν₃ : K) (g1 : K[X]),
        p.coeff 7 = h0 ^ 4 * g1 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g1 * h0 ^ 6 ∧
          (340 : K[X]) * g1 *
              ((15785 : K[X]) * g1 ^ 8 -
                (174240 : K[X]) * p.coeff 6 * g1 ^ 6 +
                (659520 : K[X]) * p.coeff 6 ^ 2 * g1 ^ 4 -
                (976896 : K[X]) * p.coeff 6 ^ 3 * g1 ^ 2 +
                (442368 : K[X]) * p.coeff 6 ^ 4) =
            h0 ^ 4 *
              (alignedNinthSquareCof810 h0 g1 (p.coeff 1) (p.coeff 2)
                  (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
                  (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
                  (q.coeff 5) (q.coeff 6) κ μ -
                Polynomial.C ν₃ * h0 ^ 23) ∧
          (∀ a : K, h0.eval a = 0 →
            g1.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          h0 ∣ g1 ∧ h0 ∣ p.coeff 6) ∨
    ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧
      ∃ (κ : K) (g2 : K[X]),
        p.coeff 7 = H ^ 2 * g2 ∧
          q.coeff 9 = Polynomial.C (5 / 4 : K) * g2 * H ^ 3 ∧
          (340 : K[X]) * g2 *
              ((15785 : K[X]) * g2 ^ 8 -
                (174240 : K[X]) * p.coeff 6 * g2 ^ 6 +
                (659520 : K[X]) * p.coeff 6 ^ 2 * g2 ^ 4 -
                (976896 : K[X]) * p.coeff 6 ^ 3 * g2 ^ 2 +
                (442368 : K[X]) * p.coeff 6 ^ 4) =
            H ^ 2 *
              alignedNinthNonsquareCof810 H g2 (p.coeff 1) (p.coeff 2)
                (p.coeff 3) (p.coeff 4) (p.coeff 5) (p.coeff 6)
                (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
                (q.coeff 5) (q.coeff 6) κ ∧
          (∀ a : K, H.eval a = 0 →
            g2.eval a = 0 ∧ (p.coeff 6).eval a = 0) ∧
          H ∣ g2 ∧ H ∣ p.coeff 6) := by
  dsimp only at haligned ⊢
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hHsq⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hHsq, hzero]
    have hpacket :=
      normalized810ScaleTwo_alignedNinthFace_squareChamber_packet
        hsource hh0 hHsq haligned
    dsimp only at hpacket
    obtain ⟨κ, μ, κ₈, ν₃, g1, hp7, hq9, _hν3, hsolved9,
      hcollapse, hdvdg1, hdvdp6, _hL⟩ := hpacket
    refine Or.inl ⟨h0, hh0, hHsq, κ, μ, ν₃, g1, hp7, hq9, ?_,
      hcollapse, hdvdg1, hdvdp6⟩
    simp only [alignedNinthSquareRow810] at hsolved9
    linear_combination -hsolved9
  · have hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hHsq
      exact hsq ⟨h0, hHsq⟩
    have hpacket :=
      normalized810ScaleTwo_alignedNinthFace_nonsquareChamber_packet
        hsource hnsq haligned
    dsimp only at hpacket
    obtain ⟨κ, g2, hp7, hq9, hclear9, hcollapse,
      hdvdg2, hdvdp6, _hL0⟩ := hpacket
    refine Or.inr ⟨hnsq, κ, g2, hp7, hq9, ?_,
      hcollapse, hdvdg2, hdvdp6⟩
    simp only [alignedNinthNonsquareRow810] at hclear9
    linear_combination -hclear9

/-- Chamber-independent root jet after the consumed degree-`8` row:
unchanged from the previous face.  At scale two the common core has a
root, and the jet `p₇, q₉, q₈, p₆` vanishes there.  The consumed row
adds no new root constraint — its nonic content is absorbed by the
degree-`13` collapse (`alignedNinth_rootNonic_absorbed_810`) — and the
new coefficient `q₁` is tied into the cleared ninth row instead of
being killed. -/
theorem normalized810ScaleTwo_alignedNinthFace_rootJet
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ a : K, H.eval a = 0 ∧ (p.coeff 7).eval a = 0 ∧
      (q.coeff 9).eval a = 0 ∧ (q.coeff 8).eval a = 0 ∧
      (p.coeff 6).eval a = 0 :=
  normalized810ScaleTwo_alignedEighthFace_rootJet hsource haligned

#print axioms alignedNinthCoefficientJacobianRow_810
#print axioms alignedNinthDefect_weightedDerivative_identity_810
#print axioms alignedNinthDefectRow_eq_zero_810
#print axioms alignedNinthDefectPowerRelation_810
#print axioms alignedNinth_factored_rootBranch_810
#print axioms alignedNinth_rootNonic_absorbed_810
#print axioms alignedSquareNinth_sqrt_810
#print axioms alignedSquareNinth_solved_810
#print axioms alignedNonsquareNinth_defect_eq_zero_810
#print axioms alignedNonsquareNinth_solved_810
#print axioms normalized810ScaleTwo_alignedNinthFace_packet
#print axioms normalized810ScaleTwo_alignedNinthFace_squareChamber_packet
#print axioms normalized810ScaleTwo_alignedNinthFace_nonsquareChamber_packet
#print axioms normalized810ScaleTwo_alignedNinthFace_chamberDichotomy
#print axioms normalized810ScaleTwo_alignedNinthFace_rootJet

end Max11DegreeRoutes
