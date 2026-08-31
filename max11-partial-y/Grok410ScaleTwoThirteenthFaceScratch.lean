import Grok410ScaleTwoTwelfthFaceScratch

/-! # Scale-two thirteenth face for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the twelfth-face packet supplies the degree-`1`
Jacobian row, the residual `ι` (not cleared), and the upgraded jet
`h³ ∣ p₃`, `h² ∣ p₂`, `h⁸ ∣ q₈`, `h⁶ ∣ q₇`, `h⁵ ∣ q₆`, `h⁴ ∣ q₅`,
`h² ∣ q₄`, `h ∣ q₃`, `h⁸ ∣ q₉` together with `2 (q₇/h⁶)(a) = 5 p₁(a)`,
`(q₅/h³)(a) = 0`, `q₃(a) = 0`,
`8 (q₆/h⁵)(a) = p₁(a) (30 t₂(a) - 9 λ)`,
`8 (q₄/h²)(a) = 15 p₁(a)²`,
`32 (q₅/h⁴)(a) = p₁(a) (64 s₂₂(a) - 40 a₂₂(a) + 27 λ t₂(a) - 90 t₂(a)²)`,
`64 (q₃/h)(a) = 15 p₁(a)² (4 t₂(a) - 3 λ)`, and
`256 q₂(a) = p₁(a)² (256 s₂₂(a) - 400 a₂₂(a) + 243 λ t₂(a) - 540 t₂(a)²)`.

The last unused Keller coefficient is the degree-`0` Jacobian row.  After
the same quartic depression that kills `z³`, that row is the terminal
scalar identity `W C' - B Z' = j`.  The remaining coordinate `Z` appears
only as a Jacobian term.  This identity is not an exact first integral,
and none is cleared against `Z`.  The tenth-face residual `ι` is not
claimed to vanish.

The sixth, seventh, and eighth defects have a spare factor of `h` past
the twelfth-face leadings.  Those leadings vanish at the root of the
degree-one scale, so they are polynomial multiples of `h`.  Evaluating
the leftover cofactors then forces
`ρ(a) + 48 p₁(a) (64 t₂ s₂₂ + 40 t₂ a₂₂ - 24 λ a₂₂ + 27 λ t₂² - 90 t₂³)(a) = 0`,
`ν(a) + 256 p₁(a) (-320 a₂₂² + 512 a₂₂ s₂₂ - 1560 a₂₂ t₂² + 720 λ a₂₂ t₂ - 1344 s₂₂ t₂² - 567 λ t₂³ + 1890 t₂⁴)(a) = 0`,
and
`ξ(a) + 96 p₁(a) (288 λ a₂₂² - 160 t₂ a₂₂² - 1280 t₂ a₂₂ s₂₂ - 900 λ t₂² a₂₂ + 2400 t₂³ a₂₂ + 960 t₂³ s₂₂ + 405 λ t₂⁴ - 1350 t₂⁵)(a) = 0`
on the respective cofactors of the unreduced sixth, seventh, and eighth
leadings.  No further individual vanishing of `p₁, p₀, t₂, a₂₂, s₂₂, q₂`,
of `(p₃/h³)(a)`, or of `ρ, ν, ξ` is claimed.  Next leftovers of the
second through fifth defects still carry the ground constants
`α, β, γ, δ` and are not cleared.

The coefficient-row tower is exhausted: there is no unused Jacobian
coefficient below degree `0`.  No total-degree or twice-prime theorem is
used.  The aligned face `N = 0` is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal last Keller coefficient -/

/-- The thirteenth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`.  Unused Jacobian coefficients of the twelfth face start
at degree `0`, and this is the constant term of the Keller identity. -/
theorem thirteenthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative =
      Polynomial.C j := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 0) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 0 :
      Finset (ℕ × ℕ)) =
      ({(0, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  linear_combination hcoeff

/-! ## Degree-`0` depressed Jacobian coefficient -/

section DepressedRow410Thirteenth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option linter.unusedVariables false

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`0` Jacobian coefficient is
exactly `W C' - B Z'`.  The coordinate `Z = g.coeff 0` is recorded only
as a Jacobian term; it is not a first integral and is not cleared. -/
theorem differentialJacobian_coeff_0_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 0 =
      g.coeff 1 * d (f.coeff 0) -
        f.coeff 1 * d (g.coeff 0) := by
  have hanti0 : (Finset.HasAntidiagonal.antidiagonal (0 : ℕ) :
      Finset (ℕ × ℕ)) =
      ({(0, 0)} : Finset (ℕ × ℕ)) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 0 =
        d (f.coeff 0) * g.coeff 1 := by
    rw [Polynomial.coeff_mul, hanti0, Finset.sum_singleton]
    have hder0 : g.derivative.coeff 0 = g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    rw [coeff_coefficientDeriv, hder0]
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 0 =
        f.coeff 1 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti0, Finset.sum_singleton]
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    rw [hder0, coeff_coefficientDeriv]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

end DepressedRow410Thirteenth

/-! ## Order-one scalar algebra on the twelfth-face leftovers -/

section ThirteenthFaceScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- After the twelfth-face sixth-face leading vanishes at the root, its
degree-one cofactor together with the fifth leftover forces
`ρ + 48 p₁ (64 t₂ s₂₂ + 40 t₂ a₂₂ - 24 λ a₂₂ + 27 λ t₂² - 90 t₂³) = 0`. -/
theorem thirteenthFace_W_nextOrder410 (rho q54 a1 a22 s22 vis w73 t2
    lam : F)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (8 : F) * w73 =
      a1 * ((30 : F) * t2 - (9 : F) * lam))
    (hV : (32 : F) * q54 + (40 : F) * a1 * a22 - (64 : F) * a1 * s22 -
        (27 : F) * a1 * lam * t2 + (90 : F) * a1 * t2 ^ 2 =
      0)
    (hW1 : rho + (-(2560 : F) * t2 * q54 -
          (4608 : F) * a1 * a22 * lam -
          (7680 : F) * a1 * a22 * t2 +
          (6912 : F) * a1 * lam * t2 ^ 2 +
          (8192 : F) * a1 * s22 * t2 - (14080 : F) * a1 * t2 ^ 3 +
          (7168 : F) * a22 * t2 * vis - (3072 : F) * a22 * w73 -
          (3584 : F) * t2 ^ 3 * vis + (3072 : F) * t2 ^ 2 * w73) =
      0) :
    rho + (48 : F) * a1 *
        ((64 : F) * t2 * s22 + (40 : F) * t2 * a22 -
          (24 : F) * lam * a22 + (27 : F) * lam * t2 ^ 2 -
          (90 : F) * t2 ^ 3) =
      0 := by
  have hU0 : (8 : F) * w73 -
      a1 * ((30 : F) * t2 - (9 : F) * lam) = 0 := by
    linear_combination hU
  have hid :
      rho + (48 : F) * a1 *
            ((64 : F) * t2 * s22 + (40 : F) * t2 * a22 -
              (24 : F) * lam * a22 + (27 : F) * lam * t2 ^ 2 -
              (90 : F) * t2 ^ 3) =
        rho + (-(2560 : F) * t2 * q54 -
            (4608 : F) * a1 * a22 * lam -
            (7680 : F) * a1 * a22 * t2 +
            (6912 : F) * a1 * lam * t2 ^ 2 +
            (8192 : F) * a1 * s22 * t2 - (14080 : F) * a1 * t2 ^ 3 +
            (7168 : F) * a22 * t2 * vis - (3072 : F) * a22 * w73 -
            (3584 : F) * t2 ^ 3 * vis + (3072 : F) * t2 ^ 2 * w73) +
          ((-(112 : F) * a22 * t2 + (56 : F) * t2 ^ 3) *
            ((64 : F) * vis - (160 : F) * a1) +
            ((384 : F) * a22 - (384 : F) * t2 ^ 2) *
              ((8 : F) * w73 -
                a1 * ((30 : F) * t2 - (9 : F) * lam)) +
            (80 : F) * t2 *
              ((32 : F) * q54 + (40 : F) * a1 * a22 -
                (64 : F) * a1 * s22 - (27 : F) * a1 * lam * t2 +
                (90 : F) * a1 * t2 ^ 2)) := by
    ring
  rw [hid]
  linear_combination hW1 +
    ((-(112 : F) * a22 * t2 + (56 : F) * t2 ^ 3) * hT +
      ((384 : F) * a22 - (384 : F) * t2 ^ 2) * hU0 +
        (80 : F) * t2 * hV)

/-- After the twelfth-face seventh-face leading vanishes at the root, its
degree-one cofactor together with the fifth leftover forces
`ν + 256 p₁ (-320 a₂₂² + 512 a₂₂ s₂₂ - 1560 a₂₂ t₂² + 720 λ a₂₂ t₂ - 1344 s₂₂ t₂² - 567 λ t₂³ + 1890 t₂⁴) = 0`. -/
theorem thirteenthFace_X_nextOrder410 (nu q54 a1 a0 a22 s22 vis w73 t2
    lam : F)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (8 : F) * w73 =
      a1 * ((30 : F) * t2 - (9 : F) * lam))
    (hV : (32 : F) * q54 + (40 : F) * a1 * a22 - (64 : F) * a1 * s22 -
        (27 : F) * a1 * lam * t2 + (90 : F) * a1 * t2 ^ 2 =
      0)
    (hX1 : nu + (-(163840 : F) * a22 * q54 + (143360 : F) * q54 * t2 ^ 2 +
          (573440 : F) * a0 * a1 - (229376 : F) * a0 * vis -
          (788480 : F) * a1 * a22 ^ 2 +
          (709632 : F) * a1 * a22 * lam * t2 +
          (458752 : F) * a1 * a22 * s22 -
          (591360 : F) * a1 * a22 * t2 ^ 2 -
          (443520 : F) * a1 * lam * t2 ^ 3 -
          (630784 : F) * a1 * s22 * t2 ^ 2 +
          (1047200 : F) * a1 * t2 ^ 4 +
          (200704 : F) * a22 ^ 2 * vis -
          (551936 : F) * a22 * t2 ^ 2 * vis +
          (344064 : F) * a22 * t2 * w73 +
          (172480 : F) * t2 ^ 4 * vis -
          (157696 : F) * t2 ^ 3 * w73) =
      0) :
    nu + (256 : F) * a1 *
        (-(320 : F) * a22 ^ 2 + (512 : F) * a22 * s22 -
          (1560 : F) * a22 * t2 ^ 2 + (720 : F) * lam * a22 * t2 -
          (1344 : F) * s22 * t2 ^ 2 - (567 : F) * lam * t2 ^ 3 +
          (1890 : F) * t2 ^ 4) =
      0 := by
  have hU0 : (8 : F) * w73 -
      a1 * ((30 : F) * t2 - (9 : F) * lam) = 0 := by
    linear_combination hU
  have hid :
      nu + (256 : F) * a1 *
            (-(320 : F) * a22 ^ 2 + (512 : F) * a22 * s22 -
              (1560 : F) * a22 * t2 ^ 2 +
              (720 : F) * lam * a22 * t2 -
              (1344 : F) * s22 * t2 ^ 2 -
              (567 : F) * lam * t2 ^ 3 + (1890 : F) * t2 ^ 4) =
        nu + (-(163840 : F) * a22 * q54 +
            (143360 : F) * q54 * t2 ^ 2 +
            (573440 : F) * a0 * a1 - (229376 : F) * a0 * vis -
            (788480 : F) * a1 * a22 ^ 2 +
            (709632 : F) * a1 * a22 * lam * t2 +
            (458752 : F) * a1 * a22 * s22 -
            (591360 : F) * a1 * a22 * t2 ^ 2 -
            (443520 : F) * a1 * lam * t2 ^ 3 -
            (630784 : F) * a1 * s22 * t2 ^ 2 +
            (1047200 : F) * a1 * t2 ^ 4 +
            (200704 : F) * a22 ^ 2 * vis -
            (551936 : F) * a22 * t2 ^ 2 * vis +
            (344064 : F) * a22 * t2 * w73 +
            (172480 : F) * t2 ^ 4 * vis -
            (157696 : F) * t2 ^ 3 * w73) +
          (((3584 : F) * a0 - (3136 : F) * a22 ^ 2 +
                (8624 : F) * a22 * t2 ^ 2 - (2695 : F) * t2 ^ 4) *
              ((64 : F) * vis - (160 : F) * a1) +
            ((-(43008 : F) * a22 * t2 + (19712 : F) * t2 ^ 3) *
              ((8 : F) * w73 -
                a1 * ((30 : F) * t2 - (9 : F) * lam)) +
              ((5120 : F) * a22 - (4480 : F) * t2 ^ 2) *
                ((32 : F) * q54 + (40 : F) * a1 * a22 -
                  (64 : F) * a1 * s22 - (27 : F) * a1 * lam * t2 +
                  (90 : F) * a1 * t2 ^ 2))) := by
    ring
  rw [hid]
  linear_combination hX1 +
    (((3584 : F) * a0 - (3136 : F) * a22 ^ 2 +
          (8624 : F) * a22 * t2 ^ 2 - (2695 : F) * t2 ^ 4) * hT +
      ((-(43008 : F) * a22 * t2 + (19712 : F) * t2 ^ 3) * hU0 +
        ((5120 : F) * a22 - (4480 : F) * t2 ^ 2) * hV))

/-- After the twelfth-face eighth-face leading vanishes at the root, its
degree-one cofactor together with the fifth leftover forces
`ξ + 96 p₁ (288 λ a₂₂² - 160 t₂ a₂₂² - 1280 t₂ a₂₂ s₂₂ - 900 λ t₂² a₂₂ + 2400 t₂³ a₂₂ + 960 t₂³ s₂₂ + 405 λ t₂⁴ - 1350 t₂⁵) = 0`. -/
theorem thirteenthFace_Y_nextOrder410 (xi q54 a1 a0 a22 s22 vis w73 t2
    lam : F)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (8 : F) * w73 =
      a1 * ((30 : F) * t2 - (9 : F) * lam))
    (hV : (32 : F) * q54 + (40 : F) * a1 * a22 - (64 : F) * a1 * s22 -
        (27 : F) * a1 * lam * t2 + (90 : F) * a1 * t2 ^ 2 =
      0)
    (hY1 : xi + (-(49152 : F) * a0 * w73 -
          (55296 : F) * a1 * a0 * lam +
          (36864 : F) * a22 ^ 2 * w73 +
          (86016 : F) * t2 * a0 * vis -
          (30720 : F) * t2 * a1 * a0 +
          (61440 : F) * t2 * a22 * q54 +
          (69120 : F) * a22 ^ 2 * a1 * lam -
          (245760 : F) * t2 * a22 * a1 * s22 -
          (107520 : F) * t2 * a22 ^ 2 * vis +
          (192000 : F) * t2 * a22 ^ 2 * a1 -
          (92160 : F) * t2 ^ 2 * a22 * w73 -
          (25600 : F) * t2 ^ 3 * q54 -
          (241920 : F) * t2 ^ 2 * a22 * a1 * lam +
          (143360 : F) * t2 ^ 3 * a1 * s22 +
          (125440 : F) * t2 ^ 3 * a22 * vis +
          (403200 : F) * t2 ^ 3 * a22 * a1 +
          (26880 : F) * t2 ^ 4 * w73 +
          (90720 : F) * t2 ^ 4 * a1 * lam -
          (28224 : F) * t2 ^ 5 * vis -
          (231840 : F) * t2 ^ 5 * a1) =
      0) :
    xi + (96 : F) * a1 *
        ((288 : F) * lam * a22 ^ 2 - (160 : F) * t2 * a22 ^ 2 -
          (1280 : F) * t2 * a22 * s22 -
          (900 : F) * lam * t2 ^ 2 * a22 +
          (2400 : F) * t2 ^ 3 * a22 + (960 : F) * t2 ^ 3 * s22 +
          (405 : F) * lam * t2 ^ 4 - (1350 : F) * t2 ^ 5) =
      0 := by
  have hU0 : (8 : F) * w73 -
      a1 * ((30 : F) * t2 - (9 : F) * lam) = 0 := by
    linear_combination hU
  have hid :
      xi + (96 : F) * a1 *
            ((288 : F) * lam * a22 ^ 2 - (160 : F) * t2 * a22 ^ 2 -
              (1280 : F) * t2 * a22 * s22 -
              (900 : F) * lam * t2 ^ 2 * a22 +
              (2400 : F) * t2 ^ 3 * a22 +
              (960 : F) * t2 ^ 3 * s22 +
              (405 : F) * lam * t2 ^ 4 - (1350 : F) * t2 ^ 5) =
        xi + (-(49152 : F) * a0 * w73 -
            (55296 : F) * a1 * a0 * lam +
            (36864 : F) * a22 ^ 2 * w73 +
            (86016 : F) * t2 * a0 * vis -
            (30720 : F) * t2 * a1 * a0 +
            (61440 : F) * t2 * a22 * q54 +
            (69120 : F) * a22 ^ 2 * a1 * lam -
            (245760 : F) * t2 * a22 * a1 * s22 -
            (107520 : F) * t2 * a22 ^ 2 * vis +
            (192000 : F) * t2 * a22 ^ 2 * a1 -
            (92160 : F) * t2 ^ 2 * a22 * w73 -
            (25600 : F) * t2 ^ 3 * q54 -
            (241920 : F) * t2 ^ 2 * a22 * a1 * lam +
            (143360 : F) * t2 ^ 3 * a1 * s22 +
            (125440 : F) * t2 ^ 3 * a22 * vis +
            (403200 : F) * t2 ^ 3 * a22 * a1 +
            (26880 : F) * t2 ^ 4 * w73 +
            (90720 : F) * t2 ^ 4 * a1 * lam -
            (28224 : F) * t2 ^ 5 * vis -
            (231840 : F) * t2 ^ 5 * a1) +
          (((-(1344 : F) * t2 * a0 + (1680 : F) * a22 ^ 2 * t2 -
                  (1960 : F) * a22 * t2 ^ 3 + (441 : F) * t2 ^ 5) *
              ((64 : F) * vis - (160 : F) * a1) +
            ((6144 : F) * a0 - (4608 : F) * a22 ^ 2 +
                  (11520 : F) * a22 * t2 ^ 2 - (3360 : F) * t2 ^ 4) *
              ((8 : F) * w73 -
                a1 * ((30 : F) * t2 - (9 : F) * lam)) +
            ((-(1920 : F) * a22 * t2 + (800 : F) * t2 ^ 3) *
              ((32 : F) * q54 + (40 : F) * a1 * a22 -
                (64 : F) * a1 * s22 - (27 : F) * a1 * lam * t2 +
                (90 : F) * a1 * t2 ^ 2)))) := by
    ring
  rw [hid]
  linear_combination hY1 +
    (((-(1344 : F) * t2 * a0 + (1680 : F) * a22 ^ 2 * t2 -
            (1960 : F) * a22 * t2 ^ 3 + (441 : F) * t2 ^ 5) * hT +
      ((6144 : F) * a0 - (4608 : F) * a22 ^ 2 +
            (11520 : F) * a22 * t2 ^ 2 - (3360 : F) * t2 ^ 4) * hU0 +
        ((-(1920 : F) * a22 * t2 + (800 : F) * t2 ^ 3) * hV)))

/-- Combined next-order identities of the cofactored twelfth-face
leadings. -/
theorem thirteenthFace_upgradedNextOrder410 (rho nu xi vis a1 t2 w73 q54
    a22 s22 a0 lam : F)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (8 : F) * w73 =
      a1 * ((30 : F) * t2 - (9 : F) * lam))
    (hV : (32 : F) * q54 + (40 : F) * a1 * a22 - (64 : F) * a1 * s22 -
        (27 : F) * a1 * lam * t2 + (90 : F) * a1 * t2 ^ 2 =
      0)
    (hW1 : rho + (-(2560 : F) * t2 * q54 -
          (4608 : F) * a1 * a22 * lam -
          (7680 : F) * a1 * a22 * t2 +
          (6912 : F) * a1 * lam * t2 ^ 2 +
          (8192 : F) * a1 * s22 * t2 - (14080 : F) * a1 * t2 ^ 3 +
          (7168 : F) * a22 * t2 * vis - (3072 : F) * a22 * w73 -
          (3584 : F) * t2 ^ 3 * vis + (3072 : F) * t2 ^ 2 * w73) =
      0)
    (hX1 : nu + (-(163840 : F) * a22 * q54 + (143360 : F) * q54 * t2 ^ 2 +
          (573440 : F) * a0 * a1 - (229376 : F) * a0 * vis -
          (788480 : F) * a1 * a22 ^ 2 +
          (709632 : F) * a1 * a22 * lam * t2 +
          (458752 : F) * a1 * a22 * s22 -
          (591360 : F) * a1 * a22 * t2 ^ 2 -
          (443520 : F) * a1 * lam * t2 ^ 3 -
          (630784 : F) * a1 * s22 * t2 ^ 2 +
          (1047200 : F) * a1 * t2 ^ 4 +
          (200704 : F) * a22 ^ 2 * vis -
          (551936 : F) * a22 * t2 ^ 2 * vis +
          (344064 : F) * a22 * t2 * w73 +
          (172480 : F) * t2 ^ 4 * vis -
          (157696 : F) * t2 ^ 3 * w73) =
      0)
    (hY1 : xi + (-(49152 : F) * a0 * w73 -
          (55296 : F) * a1 * a0 * lam +
          (36864 : F) * a22 ^ 2 * w73 +
          (86016 : F) * t2 * a0 * vis -
          (30720 : F) * t2 * a1 * a0 +
          (61440 : F) * t2 * a22 * q54 +
          (69120 : F) * a22 ^ 2 * a1 * lam -
          (245760 : F) * t2 * a22 * a1 * s22 -
          (107520 : F) * t2 * a22 ^ 2 * vis +
          (192000 : F) * t2 * a22 ^ 2 * a1 -
          (92160 : F) * t2 ^ 2 * a22 * w73 -
          (25600 : F) * t2 ^ 3 * q54 -
          (241920 : F) * t2 ^ 2 * a22 * a1 * lam +
          (143360 : F) * t2 ^ 3 * a1 * s22 +
          (125440 : F) * t2 ^ 3 * a22 * vis +
          (403200 : F) * t2 ^ 3 * a22 * a1 +
          (26880 : F) * t2 ^ 4 * w73 +
          (90720 : F) * t2 ^ 4 * a1 * lam -
          (28224 : F) * t2 ^ 5 * vis -
          (231840 : F) * t2 ^ 5 * a1) =
      0) :
    rho + (48 : F) * a1 *
          ((64 : F) * t2 * s22 + (40 : F) * t2 * a22 -
            (24 : F) * lam * a22 + (27 : F) * lam * t2 ^ 2 -
            (90 : F) * t2 ^ 3) =
        0 ∧
      nu + (256 : F) * a1 *
          (-(320 : F) * a22 ^ 2 + (512 : F) * a22 * s22 -
            (1560 : F) * a22 * t2 ^ 2 + (720 : F) * lam * a22 * t2 -
            (1344 : F) * s22 * t2 ^ 2 - (567 : F) * lam * t2 ^ 3 +
            (1890 : F) * t2 ^ 4) =
        0 ∧
      xi + (96 : F) * a1 *
          ((288 : F) * lam * a22 ^ 2 - (160 : F) * t2 * a22 ^ 2 -
            (1280 : F) * t2 * a22 * s22 -
            (900 : F) * lam * t2 ^ 2 * a22 +
            (2400 : F) * t2 ^ 3 * a22 + (960 : F) * t2 ^ 3 * s22 +
            (405 : F) * lam * t2 ^ 4 - (1350 : F) * t2 ^ 5) =
        0 :=
  ⟨thirteenthFace_W_nextOrder410 rho q54 a1 a22 s22 vis w73 t2 lam hT hU
      hV hW1,
    thirteenthFace_X_nextOrder410 nu q54 a1 a0 a22 s22 vis w73 t2 lam hT
      hU hV hX1,
    thirteenthFace_Y_nextOrder410 xi q54 a1 a0 a22 s22 vis w73 t2 lam hT
      hU hV hY1⟩

end ThirteenthFaceScalars410

/-! ## Source-facing thirteenth-face packet -/

section NonzeroThirteenthFace410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-- The unreduced sixth-face leading vanishes at the root of a degree-one
scale, so it is a polynomial multiple of `h`. -/
theorem thirteenthFace_exists_W_cofactor410 (h vis a1 b42 : k[X]) (a : k)
    (hdegree : h.natDegree = 1) (hroot : h.eval a = 0)
    (hW : (5120 : k) * (a1.eval a) ^ 2 -
        (3584 : k) * vis.eval a * a1.eval a +
      (2048 : k) * b42.eval a =
      0) :
    ∃ rho : k[X],
      (5120 : k[X]) * a1 ^ 2 - (3584 : k[X]) * vis * a1 +
          (2048 : k[X]) * b42 =
        h * rho := by
  have heval :
      ((5120 : k[X]) * a1 ^ 2 - (3584 : k[X]) * vis * a1 +
          (2048 : k[X]) * b42).eval a =
        0 := by
    simpa [eval_add, eval_sub, eval_mul, eval_pow] using hW
  exact linearPolynomial_dvd_of_eval_eq_zero_410 h
    ((5120 : k[X]) * a1 ^ 2 - (3584 : k[X]) * vis * a1 +
      (2048 : k[X]) * b42)
    a hdegree hroot heval

/-- The unreduced seventh-face leading vanishes at the root of a degree-one
scale, so it is a polynomial multiple of `h`. -/
theorem thirteenthFace_exists_X_cofactor410 (h b31 a1 w73 t2 b42 vis :
    k[X]) (lambda a : k) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hX : (131072 : k) * b31.eval a -
        (196608 : k) * a1.eval a * w73.eval a -
        (131072 : k) * t2.eval a * b42.eval a -
        (129024 : k) * (a1.eval a) ^ 2 * lambda +
        (401408 : k) * t2.eval a * a1.eval a * vis.eval a -
        (143360 : k) * t2.eval a * (a1.eval a) ^ 2 =
      0) :
    ∃ nu : k[X],
      (131072 : k[X]) * b31 - (196608 : k[X]) * a1 * w73 -
          (131072 : k[X]) * t2 * b42 -
          (129024 : k[X]) * a1 ^ 2 * Polynomial.C lambda +
          (401408 : k[X]) * t2 * a1 * vis -
          (143360 : k[X]) * t2 * a1 ^ 2 =
        h * nu := by
  have heval :
      ((131072 : k[X]) * b31 - (196608 : k[X]) * a1 * w73 -
          (131072 : k[X]) * t2 * b42 -
          (129024 : k[X]) * a1 ^ 2 * Polynomial.C lambda +
          (401408 : k[X]) * t2 * a1 * vis -
          (143360 : k[X]) * t2 * a1 ^ 2).eval a =
        0 := by
    simpa [hroot, eval_add, eval_sub, eval_mul, eval_pow, mul_comm,
      mul_left_comm, mul_assoc] using hX
  exact linearPolynomial_dvd_of_eval_eq_zero_410 h
    ((131072 : k[X]) * b31 - (196608 : k[X]) * a1 * w73 -
      (131072 : k[X]) * t2 * b42 -
      (129024 : k[X]) * a1 ^ 2 * Polynomial.C lambda +
      (401408 : k[X]) * t2 * a1 * vis -
      (143360 : k[X]) * t2 * a1 ^ 2)
    a hdegree hroot heval

/-- The unreduced eighth-face leading vanishes at the root of a degree-one
scale, so it is a polynomial multiple of `h`. -/
theorem thirteenthFace_exists_Y_cofactor410 (h b2 q54 a1 a22 b42 t2 b31
    s22 vis w73 : k[X]) (lambda a : k) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hY : (32768 : k) * b2.eval a - (40960 : k) * a1.eval a * q54.eval a -
        (32768 : k) * a22.eval a * b42.eval a -
        (24576 : k) * t2.eval a * b31.eval a +
        (49152 : k) * (a1.eval a) ^ 2 * s22.eval a +
        (86016 : k) * a22.eval a * a1.eval a * vis.eval a -
        (153600 : k) * a22.eval a * (a1.eval a) ^ 2 +
        (73728 : k) * t2.eval a * a1.eval a * w73.eval a +
        (24576 : k) * (t2.eval a) ^ 2 * b42.eval a +
        (69120 : k) * t2.eval a * (a1.eval a) ^ 2 * lambda -
        (107520 : k) * (t2.eval a) ^ 2 * a1.eval a * vis.eval a -
        (76800 : k) * (t2.eval a) ^ 2 * (a1.eval a) ^ 2 =
      0) :
    ∃ xi : k[X],
      (32768 : k[X]) * b2 - (40960 : k[X]) * a1 * q54 -
          (32768 : k[X]) * a22 * b42 - (24576 : k[X]) * t2 * b31 +
          (49152 : k[X]) * a1 ^ 2 * s22 +
          (86016 : k[X]) * a22 * a1 * vis -
          (153600 : k[X]) * a22 * a1 ^ 2 +
          (73728 : k[X]) * t2 * a1 * w73 +
          (24576 : k[X]) * t2 ^ 2 * b42 +
          (69120 : k[X]) * t2 * a1 ^ 2 * Polynomial.C lambda -
          (107520 : k[X]) * t2 ^ 2 * a1 * vis -
          (76800 : k[X]) * t2 ^ 2 * a1 ^ 2 =
        h * xi := by
  have heval :
      ((32768 : k[X]) * b2 - (40960 : k[X]) * a1 * q54 -
          (32768 : k[X]) * a22 * b42 - (24576 : k[X]) * t2 * b31 +
          (49152 : k[X]) * a1 ^ 2 * s22 +
          (86016 : k[X]) * a22 * a1 * vis -
          (153600 : k[X]) * a22 * a1 ^ 2 +
          (73728 : k[X]) * t2 * a1 * w73 +
          (24576 : k[X]) * t2 ^ 2 * b42 +
          (69120 : k[X]) * t2 * a1 ^ 2 * Polynomial.C lambda -
          (107520 : k[X]) * t2 ^ 2 * a1 * vis -
          (76800 : k[X]) * t2 ^ 2 * a1 ^ 2).eval a =
        0 := by
    simpa [hroot, eval_add, eval_sub, eval_mul, eval_pow, mul_comm,
      mul_left_comm, mul_assoc] using hY
  exact linearPolynomial_dvd_of_eval_eq_zero_410 h
    ((32768 : k[X]) * b2 - (40960 : k[X]) * a1 * q54 -
      (32768 : k[X]) * a22 * b42 - (24576 : k[X]) * t2 * b31 +
      (49152 : k[X]) * a1 ^ 2 * s22 +
      (86016 : k[X]) * a22 * a1 * vis -
      (153600 : k[X]) * a22 * a1 ^ 2 +
      (73728 : k[X]) * t2 * a1 * w73 +
      (24576 : k[X]) * t2 ^ 2 * b42 +
      (69120 : k[X]) * t2 * a1 ^ 2 * Polynomial.C lambda -
      (107520 : k[X]) * t2 ^ 2 * a1 * vis -
      (76800 : k[X]) * t2 ^ 2 * a1 ^ 2)
    a hdegree hroot heval

theorem thirteenthFace_evalW410 (h t2 a22 s22 vis w73 q54 a1 a0 b42 rho :
    k[X]) (lambda a eps : k) (hh : h ≠ 0) (hroot : h.eval a = 0)
    (hpow : localClearedSixthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
        (h ^ 2 * b42) lambda =
      Polynomial.C eps * h ^ 20)
    (hcof : (5120 : k[X]) * a1 ^ 2 - (3584 : k[X]) * vis * a1 +
        (2048 : k[X]) * b42 =
      h * rho)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hV : (32 : k) * q54.eval a + (40 : k) * a1.eval a * a22.eval a -
        (64 : k) * a1.eval a * s22.eval a -
        (27 : k) * a1.eval a * lambda * t2.eval a +
        (90 : k) * a1.eval a * (t2.eval a) ^ 2 =
      0) :
    rho.eval a + (48 : k) * a1.eval a *
        ((64 : k) * t2.eval a * s22.eval a +
          (40 : k) * t2.eval a * a22.eval a -
          (24 : k) * lambda * a22.eval a +
          (27 : k) * lambda * (t2.eval a) ^ 2 -
          (90 : k) * (t2.eval a) ^ 3) =
      0 := by
  have hclr :=
    twelfthFace_clearedW_upgraded410 h t2 a22 s22 vis w73 q54 a1 a0 b42
      lambda
  have hpoly :
      (5120 : k[X]) * a1 ^ 2 - (3584 : k[X]) * vis * a1 +
          (2048 : k[X]) * b42 +
        h * ((-2560 : k[X]) * t2 * q54 -
          (4608 : k[X]) * a1 * a22 * Polynomial.C lambda -
          (7680 : k[X]) * a1 * a22 * t2 +
          (6912 : k[X]) * a1 * Polynomial.C lambda * t2 ^ 2 +
          (8192 : k[X]) * a1 * s22 * t2 -
          (14080 : k[X]) * a1 * t2 ^ 3 +
          (7168 : k[X]) * a22 * t2 * vis - (3072 : k[X]) * a22 * w73 -
          (3584 : k[X]) * t2 ^ 3 * vis +
          (3072 : k[X]) * t2 ^ 2 * w73 +
          h * ((10240 : k[X]) * a0 * a22 -
            (4608 : k[X]) * a0 * Polynomial.C lambda * t2 -
            (4096 : k[X]) * a0 * s22 + (7680 : k[X]) * a0 * t2 ^ 2 -
            (5120 : k[X]) * a22 ^ 3 +
            (6912 : k[X]) * a22 ^ 2 * Polynomial.C lambda * t2 +
            (4096 : k[X]) * a22 ^ 2 * s22 -
            (3840 : k[X]) * a22 ^ 2 * t2 ^ 2 -
            (9216 : k[X]) * a22 * Polynomial.C lambda * t2 ^ 3 -
            (12288 : k[X]) * a22 * s22 * t2 ^ 2 +
            (20480 : k[X]) * a22 * t2 ^ 4 +
            (2304 : k[X]) * Polynomial.C lambda * t2 ^ 5 +
            (4096 : k[X]) * s22 * t2 ^ 4 - (6400 : k[X]) * t2 ^ 6)) =
        Polynomial.C eps * h ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 18 hh)
    rw [← hclr, hpow]
    ring
  have hnext :
      rho + ((-2560 : k[X]) * t2 * q54 -
            (4608 : k[X]) * a1 * a22 * Polynomial.C lambda -
            (7680 : k[X]) * a1 * a22 * t2 +
            (6912 : k[X]) * a1 * Polynomial.C lambda * t2 ^ 2 +
            (8192 : k[X]) * a1 * s22 * t2 -
            (14080 : k[X]) * a1 * t2 ^ 3 +
            (7168 : k[X]) * a22 * t2 * vis - (3072 : k[X]) * a22 * w73 -
            (3584 : k[X]) * t2 ^ 3 * vis +
            (3072 : k[X]) * t2 ^ 2 * w73 +
            h * ((10240 : k[X]) * a0 * a22 -
              (4608 : k[X]) * a0 * Polynomial.C lambda * t2 -
              (4096 : k[X]) * a0 * s22 + (7680 : k[X]) * a0 * t2 ^ 2 -
              (5120 : k[X]) * a22 ^ 3 +
              (6912 : k[X]) * a22 ^ 2 * Polynomial.C lambda * t2 +
              (4096 : k[X]) * a22 ^ 2 * s22 -
              (3840 : k[X]) * a22 ^ 2 * t2 ^ 2 -
              (9216 : k[X]) * a22 * Polynomial.C lambda * t2 ^ 3 -
              (12288 : k[X]) * a22 * s22 * t2 ^ 2 +
              (20480 : k[X]) * a22 * t2 ^ 4 +
              (2304 : k[X]) * Polynomial.C lambda * t2 ^ 5 +
              (4096 : k[X]) * s22 * t2 ^ 4 - (6400 : k[X]) * t2 ^ 6)) =
        Polynomial.C eps * h := by
    apply mul_left_cancel₀ hh
    calc
      h *
            (rho + ((-2560 : k[X]) * t2 * q54 -
                (4608 : k[X]) * a1 * a22 * Polynomial.C lambda -
                (7680 : k[X]) * a1 * a22 * t2 +
                (6912 : k[X]) * a1 * Polynomial.C lambda * t2 ^ 2 +
                (8192 : k[X]) * a1 * s22 * t2 -
                (14080 : k[X]) * a1 * t2 ^ 3 +
                (7168 : k[X]) * a22 * t2 * vis -
                (3072 : k[X]) * a22 * w73 -
                (3584 : k[X]) * t2 ^ 3 * vis +
                (3072 : k[X]) * t2 ^ 2 * w73 +
                h * ((10240 : k[X]) * a0 * a22 -
                  (4608 : k[X]) * a0 * Polynomial.C lambda * t2 -
                  (4096 : k[X]) * a0 * s22 +
                  (7680 : k[X]) * a0 * t2 ^ 2 -
                  (5120 : k[X]) * a22 ^ 3 +
                  (6912 : k[X]) * a22 ^ 2 * Polynomial.C lambda * t2 +
                  (4096 : k[X]) * a22 ^ 2 * s22 -
                  (3840 : k[X]) * a22 ^ 2 * t2 ^ 2 -
                  (9216 : k[X]) * a22 * Polynomial.C lambda * t2 ^ 3 -
                  (12288 : k[X]) * a22 * s22 * t2 ^ 2 +
                  (20480 : k[X]) * a22 * t2 ^ 4 +
                  (2304 : k[X]) * Polynomial.C lambda * t2 ^ 5 +
                  (4096 : k[X]) * s22 * t2 ^ 4 -
                  (6400 : k[X]) * t2 ^ 6))) =
          h * rho +
            h * ((-2560 : k[X]) * t2 * q54 -
              (4608 : k[X]) * a1 * a22 * Polynomial.C lambda -
              (7680 : k[X]) * a1 * a22 * t2 +
              (6912 : k[X]) * a1 * Polynomial.C lambda * t2 ^ 2 +
              (8192 : k[X]) * a1 * s22 * t2 -
              (14080 : k[X]) * a1 * t2 ^ 3 +
              (7168 : k[X]) * a22 * t2 * vis -
              (3072 : k[X]) * a22 * w73 -
              (3584 : k[X]) * t2 ^ 3 * vis +
              (3072 : k[X]) * t2 ^ 2 * w73 +
              h * ((10240 : k[X]) * a0 * a22 -
                (4608 : k[X]) * a0 * Polynomial.C lambda * t2 -
                (4096 : k[X]) * a0 * s22 +
                (7680 : k[X]) * a0 * t2 ^ 2 -
                (5120 : k[X]) * a22 ^ 3 +
                (6912 : k[X]) * a22 ^ 2 * Polynomial.C lambda * t2 +
                (4096 : k[X]) * a22 ^ 2 * s22 -
                (3840 : k[X]) * a22 ^ 2 * t2 ^ 2 -
                (9216 : k[X]) * a22 * Polynomial.C lambda * t2 ^ 3 -
                (12288 : k[X]) * a22 * s22 * t2 ^ 2 +
                (20480 : k[X]) * a22 * t2 ^ 4 +
                (2304 : k[X]) * Polynomial.C lambda * t2 ^ 5 +
                (4096 : k[X]) * s22 * t2 ^ 4 -
                (6400 : k[X]) * t2 ^ 6)) := by
        ring
      _ = (5120 : k[X]) * a1 ^ 2 - (3584 : k[X]) * vis * a1 +
            (2048 : k[X]) * b42 +
          h * ((-2560 : k[X]) * t2 * q54 -
            (4608 : k[X]) * a1 * a22 * Polynomial.C lambda -
            (7680 : k[X]) * a1 * a22 * t2 +
            (6912 : k[X]) * a1 * Polynomial.C lambda * t2 ^ 2 +
            (8192 : k[X]) * a1 * s22 * t2 -
            (14080 : k[X]) * a1 * t2 ^ 3 +
            (7168 : k[X]) * a22 * t2 * vis - (3072 : k[X]) * a22 * w73 -
            (3584 : k[X]) * t2 ^ 3 * vis +
            (3072 : k[X]) * t2 ^ 2 * w73 +
            h * ((10240 : k[X]) * a0 * a22 -
              (4608 : k[X]) * a0 * Polynomial.C lambda * t2 -
              (4096 : k[X]) * a0 * s22 + (7680 : k[X]) * a0 * t2 ^ 2 -
              (5120 : k[X]) * a22 ^ 3 +
              (6912 : k[X]) * a22 ^ 2 * Polynomial.C lambda * t2 +
              (4096 : k[X]) * a22 ^ 2 * s22 -
              (3840 : k[X]) * a22 ^ 2 * t2 ^ 2 -
              (9216 : k[X]) * a22 * Polynomial.C lambda * t2 ^ 3 -
              (12288 : k[X]) * a22 * s22 * t2 ^ 2 +
              (20480 : k[X]) * a22 * t2 ^ 4 +
              (2304 : k[X]) * Polynomial.C lambda * t2 ^ 5 +
              (4096 : k[X]) * s22 * t2 ^ 4 - (6400 : k[X]) * t2 ^ 6)) :=
        by
        rw [hcof] <;> try ring
      _ = Polynomial.C eps * h ^ 2 := hpoly
      _ = h * (Polynomial.C eps * h) := by ring
  have heval := congrArg (fun r : k[X] => r.eval a) hnext
  have hraw :
      rho.eval a + (-(2560 : k) * t2.eval a * q54.eval a -
          (4608 : k) * a1.eval a * a22.eval a * lambda -
          (7680 : k) * a1.eval a * a22.eval a * t2.eval a +
          (6912 : k) * a1.eval a * lambda * (t2.eval a) ^ 2 +
          (8192 : k) * a1.eval a * s22.eval a * t2.eval a -
          (14080 : k) * a1.eval a * (t2.eval a) ^ 3 +
          (7168 : k) * a22.eval a * t2.eval a * vis.eval a -
          (3072 : k) * a22.eval a * w73.eval a -
          (3584 : k) * (t2.eval a) ^ 3 * vis.eval a +
          (3072 : k) * (t2.eval a) ^ 2 * w73.eval a) =
        0 := by
    simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub, mul_comm,
      mul_left_comm, mul_assoc] using heval
  exact thirteenthFace_W_nextOrder410 (rho.eval a) (q54.eval a)
    (a1.eval a) (a22.eval a) (s22.eval a) (vis.eval a) (w73.eval a)
    (t2.eval a) lambda hT hU hV hraw

set_option maxHeartbeats 8000000 in
theorem thirteenthFace_evalX410 (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31
    nu : k[X]) (lambda a xi : k) (hh : h ≠ 0) (hroot : h.eval a = 0)
    (hpow : localClearedSeventhDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1
        a0 (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
        (h ^ 2 * b42) (h * b31) lambda =
      Polynomial.C xi * h ^ 23)
    (hcof : (131072 : k[X]) * b31 - (196608 : k[X]) * a1 * w73 -
        (131072 : k[X]) * t2 * b42 -
        (129024 : k[X]) * a1 ^ 2 * Polynomial.C lambda +
        (401408 : k[X]) * t2 * a1 * vis -
        (143360 : k[X]) * t2 * a1 ^ 2 =
      h * nu)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hV : (32 : k) * q54.eval a + (40 : k) * a1.eval a * a22.eval a -
        (64 : k) * a1.eval a * s22.eval a -
        (27 : k) * a1.eval a * lambda * t2.eval a +
        (90 : k) * a1.eval a * (t2.eval a) ^ 2 =
      0) :
    nu.eval a + (256 : k) * a1.eval a *
        (-(320 : k) * (a22.eval a) ^ 2 +
          (512 : k) * a22.eval a * s22.eval a -
          (1560 : k) * a22.eval a * (t2.eval a) ^ 2 +
          (720 : k) * lambda * a22.eval a * t2.eval a -
          (1344 : k) * s22.eval a * (t2.eval a) ^ 2 -
          (567 : k) * lambda * (t2.eval a) ^ 3 +
          (1890 : k) * (t2.eval a) ^ 4) =
      0 := by
  have hclr :=
    twelfthFace_clearedX_upgraded410 h t2 a22 s22 vis w73 q54 a1 a0 b42
      b31 lambda
  have hpoly :
      (131072 : k[X]) * b31 - (196608 : k[X]) * a1 * w73 -
          (131072 : k[X]) * t2 * b42 -
          (129024 : k[X]) * a1 ^ 2 * Polynomial.C lambda +
          (401408 : k[X]) * t2 * a1 * vis -
          (143360 : k[X]) * t2 * a1 ^ 2 +
        h * ((-163840 : k[X]) * a22 * q54 +
          (143360 : k[X]) * q54 * t2 ^ 2 +
          (573440 : k[X]) * a0 * a1 - (229376 : k[X]) * a0 * vis -
          (788480 : k[X]) * a1 * a22 ^ 2 +
          (709632 : k[X]) * a1 * a22 * Polynomial.C lambda * t2 +
          (458752 : k[X]) * a1 * a22 * s22 -
          (591360 : k[X]) * a1 * a22 * t2 ^ 2 -
          (443520 : k[X]) * a1 * Polynomial.C lambda * t2 ^ 3 -
          (630784 : k[X]) * a1 * s22 * t2 ^ 2 +
          (1047200 : k[X]) * a1 * t2 ^ 4 +
          (200704 : k[X]) * a22 ^ 2 * vis -
          (551936 : k[X]) * a22 * t2 ^ 2 * vis +
          (344064 : k[X]) * a22 * t2 * w73 +
          (172480 : k[X]) * t2 ^ 4 * vis -
          (157696 : k[X]) * t2 ^ 3 * w73 +
          h * ((-258048 : k[X]) * a0 * a22 * Polynomial.C lambda -
            (286720 : k[X]) * a0 * a22 * t2 +
            (354816 : k[X]) * a0 * Polynomial.C lambda * t2 ^ 2 +
            (458752 : k[X]) * a0 * s22 * t2 -
            (788480 : k[X]) * a0 * t2 ^ 3 +
            (118272 : k[X]) * a22 ^ 3 * Polynomial.C lambda +
            (394240 : k[X]) * a22 ^ 3 * t2 -
            (665280 : k[X]) * a22 ^ 2 * Polynomial.C lambda *
              t2 ^ 2 -
            (630784 : k[X]) * a22 ^ 2 * s22 * t2 +
            (985600 : k[X]) * a22 ^ 2 * t2 ^ 3 +
            (526680 : k[X]) * a22 * Polynomial.C lambda * t2 ^ 4 +
            (788480 : k[X]) * a22 * s22 * t2 ^ 3 -
            (1287440 : k[X]) * a22 * t2 ^ 5 -
            (100947 : k[X]) * Polynomial.C lambda * t2 ^ 6 -
            (187264 : k[X]) * s22 * t2 ^ 5 +
            (288420 : k[X]) * t2 ^ 7)) =
        Polynomial.C xi * h ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 21 hh)
    rw [← hclr, hpow]
    ring
  have hnext :
      nu + ((-163840 : k[X]) * a22 * q54 +
            (143360 : k[X]) * q54 * t2 ^ 2 +
            (573440 : k[X]) * a0 * a1 - (229376 : k[X]) * a0 * vis -
            (788480 : k[X]) * a1 * a22 ^ 2 +
            (709632 : k[X]) * a1 * a22 * Polynomial.C lambda * t2 +
            (458752 : k[X]) * a1 * a22 * s22 -
            (591360 : k[X]) * a1 * a22 * t2 ^ 2 -
            (443520 : k[X]) * a1 * Polynomial.C lambda * t2 ^ 3 -
            (630784 : k[X]) * a1 * s22 * t2 ^ 2 +
            (1047200 : k[X]) * a1 * t2 ^ 4 +
            (200704 : k[X]) * a22 ^ 2 * vis -
            (551936 : k[X]) * a22 * t2 ^ 2 * vis +
            (344064 : k[X]) * a22 * t2 * w73 +
            (172480 : k[X]) * t2 ^ 4 * vis -
            (157696 : k[X]) * t2 ^ 3 * w73 +
            h * ((-258048 : k[X]) * a0 * a22 * Polynomial.C lambda -
              (286720 : k[X]) * a0 * a22 * t2 +
              (354816 : k[X]) * a0 * Polynomial.C lambda * t2 ^ 2 +
              (458752 : k[X]) * a0 * s22 * t2 -
              (788480 : k[X]) * a0 * t2 ^ 3 +
              (118272 : k[X]) * a22 ^ 3 * Polynomial.C lambda +
              (394240 : k[X]) * a22 ^ 3 * t2 -
              (665280 : k[X]) * a22 ^ 2 * Polynomial.C lambda *
                t2 ^ 2 -
              (630784 : k[X]) * a22 ^ 2 * s22 * t2 +
              (985600 : k[X]) * a22 ^ 2 * t2 ^ 3 +
              (526680 : k[X]) * a22 * Polynomial.C lambda * t2 ^ 4 +
              (788480 : k[X]) * a22 * s22 * t2 ^ 3 -
              (1287440 : k[X]) * a22 * t2 ^ 5 -
              (100947 : k[X]) * Polynomial.C lambda * t2 ^ 6 -
              (187264 : k[X]) * s22 * t2 ^ 5 +
              (288420 : k[X]) * t2 ^ 7)) =
        Polynomial.C xi * h := by
    apply mul_left_cancel₀ hh
    have hmul :
        h *
            (nu + ((-163840 : k[X]) * a22 * q54 +
                (143360 : k[X]) * q54 * t2 ^ 2 +
                (573440 : k[X]) * a0 * a1 - (229376 : k[X]) * a0 * vis -
                (788480 : k[X]) * a1 * a22 ^ 2 +
                (709632 : k[X]) * a1 * a22 * Polynomial.C lambda * t2 +
                (458752 : k[X]) * a1 * a22 * s22 -
                (591360 : k[X]) * a1 * a22 * t2 ^ 2 -
                (443520 : k[X]) * a1 * Polynomial.C lambda * t2 ^ 3 -
                (630784 : k[X]) * a1 * s22 * t2 ^ 2 +
                (1047200 : k[X]) * a1 * t2 ^ 4 +
                (200704 : k[X]) * a22 ^ 2 * vis -
                (551936 : k[X]) * a22 * t2 ^ 2 * vis +
                (344064 : k[X]) * a22 * t2 * w73 +
                (172480 : k[X]) * t2 ^ 4 * vis -
                (157696 : k[X]) * t2 ^ 3 * w73 +
                h * ((-258048 : k[X]) * a0 * a22 *
                    Polynomial.C lambda -
                  (286720 : k[X]) * a0 * a22 * t2 +
                  (354816 : k[X]) * a0 * Polynomial.C lambda *
                    t2 ^ 2 +
                  (458752 : k[X]) * a0 * s22 * t2 -
                  (788480 : k[X]) * a0 * t2 ^ 3 +
                  (118272 : k[X]) * a22 ^ 3 * Polynomial.C lambda +
                  (394240 : k[X]) * a22 ^ 3 * t2 -
                  (665280 : k[X]) * a22 ^ 2 * Polynomial.C lambda *
                    t2 ^ 2 -
                  (630784 : k[X]) * a22 ^ 2 * s22 * t2 +
                  (985600 : k[X]) * a22 ^ 2 * t2 ^ 3 +
                  (526680 : k[X]) * a22 * Polynomial.C lambda *
                    t2 ^ 4 +
                  (788480 : k[X]) * a22 * s22 * t2 ^ 3 -
                  (1287440 : k[X]) * a22 * t2 ^ 5 -
                  (100947 : k[X]) * Polynomial.C lambda * t2 ^ 6 -
                  (187264 : k[X]) * s22 * t2 ^ 5 +
                  (288420 : k[X]) * t2 ^ 7))) =
          (131072 : k[X]) * b31 - (196608 : k[X]) * a1 * w73 -
              (131072 : k[X]) * t2 * b42 -
              (129024 : k[X]) * a1 ^ 2 * Polynomial.C lambda +
              (401408 : k[X]) * t2 * a1 * vis -
              (143360 : k[X]) * t2 * a1 ^ 2 +
            h * ((-163840 : k[X]) * a22 * q54 +
              (143360 : k[X]) * q54 * t2 ^ 2 +
              (573440 : k[X]) * a0 * a1 - (229376 : k[X]) * a0 * vis -
              (788480 : k[X]) * a1 * a22 ^ 2 +
              (709632 : k[X]) * a1 * a22 * Polynomial.C lambda * t2 +
              (458752 : k[X]) * a1 * a22 * s22 -
              (591360 : k[X]) * a1 * a22 * t2 ^ 2 -
              (443520 : k[X]) * a1 * Polynomial.C lambda * t2 ^ 3 -
              (630784 : k[X]) * a1 * s22 * t2 ^ 2 +
              (1047200 : k[X]) * a1 * t2 ^ 4 +
              (200704 : k[X]) * a22 ^ 2 * vis -
              (551936 : k[X]) * a22 * t2 ^ 2 * vis +
              (344064 : k[X]) * a22 * t2 * w73 +
              (172480 : k[X]) * t2 ^ 4 * vis -
              (157696 : k[X]) * t2 ^ 3 * w73 +
              h * ((-258048 : k[X]) * a0 * a22 * Polynomial.C lambda -
                (286720 : k[X]) * a0 * a22 * t2 +
                (354816 : k[X]) * a0 * Polynomial.C lambda * t2 ^ 2 +
                (458752 : k[X]) * a0 * s22 * t2 -
                (788480 : k[X]) * a0 * t2 ^ 3 +
                (118272 : k[X]) * a22 ^ 3 * Polynomial.C lambda +
                (394240 : k[X]) * a22 ^ 3 * t2 -
                (665280 : k[X]) * a22 ^ 2 * Polynomial.C lambda *
                  t2 ^ 2 -
                (630784 : k[X]) * a22 ^ 2 * s22 * t2 +
                (985600 : k[X]) * a22 ^ 2 * t2 ^ 3 +
                (526680 : k[X]) * a22 * Polynomial.C lambda * t2 ^ 4 +
                (788480 : k[X]) * a22 * s22 * t2 ^ 3 -
                (1287440 : k[X]) * a22 * t2 ^ 5 -
                (100947 : k[X]) * Polynomial.C lambda * t2 ^ 6 -
                (187264 : k[X]) * s22 * t2 ^ 5 +
                (288420 : k[X]) * t2 ^ 7)) := by
      rw [hcof] <;> try ring
    rw [hmul, hpoly]
    ring
  have heval := congrArg (fun r : k[X] => r.eval a) hnext
  have hraw :
      nu.eval a + (-(163840 : k) * a22.eval a * q54.eval a +
          (143360 : k) * q54.eval a * (t2.eval a) ^ 2 +
          (573440 : k) * a0.eval a * a1.eval a -
          (229376 : k) * a0.eval a * vis.eval a -
          (788480 : k) * a1.eval a * (a22.eval a) ^ 2 +
          (709632 : k) * a1.eval a * a22.eval a * lambda * t2.eval a +
          (458752 : k) * a1.eval a * a22.eval a * s22.eval a -
          (591360 : k) * a1.eval a * a22.eval a * (t2.eval a) ^ 2 -
          (443520 : k) * a1.eval a * lambda * (t2.eval a) ^ 3 -
          (630784 : k) * a1.eval a * s22.eval a * (t2.eval a) ^ 2 +
          (1047200 : k) * a1.eval a * (t2.eval a) ^ 4 +
          (200704 : k) * (a22.eval a) ^ 2 * vis.eval a -
          (551936 : k) * a22.eval a * (t2.eval a) ^ 2 * vis.eval a +
          (344064 : k) * a22.eval a * t2.eval a * w73.eval a +
          (172480 : k) * (t2.eval a) ^ 4 * vis.eval a -
          (157696 : k) * (t2.eval a) ^ 3 * w73.eval a) =
        0 := by
    simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub, mul_comm,
      mul_left_comm, mul_assoc] using heval
  exact thirteenthFace_X_nextOrder410 (nu.eval a) (q54.eval a)
    (a1.eval a) (a0.eval a) (a22.eval a) (s22.eval a) (vis.eval a)
    (w73.eval a) (t2.eval a) lambda hT hU hV hraw

set_option maxHeartbeats 16000000 in
theorem thirteenthFace_evalY410 (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31
    b2 xi : k[X]) (lambda a eta : k) (hh : h ≠ 0) (hroot : h.eval a = 0)
    (hpow : localClearedEighthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1
        a0 (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
        (h ^ 2 * b42) (h * b31) b2 lambda =
      Polynomial.C eta * h ^ 26)
    (hcof : (32768 : k[X]) * b2 - (40960 : k[X]) * a1 * q54 -
        (32768 : k[X]) * a22 * b42 - (24576 : k[X]) * t2 * b31 +
        (49152 : k[X]) * a1 ^ 2 * s22 +
        (86016 : k[X]) * a22 * a1 * vis -
        (153600 : k[X]) * a22 * a1 ^ 2 +
        (73728 : k[X]) * t2 * a1 * w73 +
        (24576 : k[X]) * t2 ^ 2 * b42 +
        (69120 : k[X]) * t2 * a1 ^ 2 * Polynomial.C lambda -
        (107520 : k[X]) * t2 ^ 2 * a1 * vis -
        (76800 : k[X]) * t2 ^ 2 * a1 ^ 2 =
      h * xi)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hV : (32 : k) * q54.eval a + (40 : k) * a1.eval a * a22.eval a -
        (64 : k) * a1.eval a * s22.eval a -
        (27 : k) * a1.eval a * lambda * t2.eval a +
        (90 : k) * a1.eval a * (t2.eval a) ^ 2 =
      0) :
    xi.eval a + (96 : k) * a1.eval a *
        ((288 : k) * lambda * (a22.eval a) ^ 2 -
          (160 : k) * t2.eval a * (a22.eval a) ^ 2 -
          (1280 : k) * t2.eval a * a22.eval a * s22.eval a -
          (900 : k) * lambda * (t2.eval a) ^ 2 * a22.eval a +
          (2400 : k) * (t2.eval a) ^ 3 * a22.eval a +
          (960 : k) * (t2.eval a) ^ 3 * s22.eval a +
          (405 : k) * lambda * (t2.eval a) ^ 4 -
          (1350 : k) * (t2.eval a) ^ 5) =
      0 := by
  have hclr :=
    twelfthFace_clearedY_upgraded410 h t2 a22 s22 vis w73 q54 a1 a0 b42
      b31 b2 lambda
  have hpoly :
      (32768 : k[X]) * b2 - (40960 : k[X]) * a1 * q54 -
          (32768 : k[X]) * a22 * b42 - (24576 : k[X]) * t2 * b31 +
          (49152 : k[X]) * a1 ^ 2 * s22 +
          (86016 : k[X]) * a22 * a1 * vis -
          (153600 : k[X]) * a22 * a1 ^ 2 +
          (73728 : k[X]) * t2 * a1 * w73 +
          (24576 : k[X]) * t2 ^ 2 * b42 +
          (69120 : k[X]) * t2 * a1 ^ 2 * Polynomial.C lambda -
          (107520 : k[X]) * t2 ^ 2 * a1 * vis -
          (76800 : k[X]) * t2 ^ 2 * a1 ^ 2 +
        h * ((-49152 : k[X]) * a0 * w73 -
          (55296 : k[X]) * a1 * a0 * Polynomial.C lambda +
          (36864 : k[X]) * a22 ^ 2 * w73 +
          (86016 : k[X]) * t2 * a0 * vis -
          (30720 : k[X]) * t2 * a1 * a0 +
          (61440 : k[X]) * t2 * a22 * q54 +
          (69120 : k[X]) * a22 ^ 2 * a1 * Polynomial.C lambda -
          (245760 : k[X]) * t2 * a22 * a1 * s22 -
          (107520 : k[X]) * t2 * a22 ^ 2 * vis +
          (192000 : k[X]) * t2 * a22 ^ 2 * a1 -
          (92160 : k[X]) * t2 ^ 2 * a22 * w73 -
          (25600 : k[X]) * t2 ^ 3 * q54 -
          (241920 : k[X]) * t2 ^ 2 * a22 * a1 * Polynomial.C lambda +
          (143360 : k[X]) * t2 ^ 3 * a1 * s22 +
          (125440 : k[X]) * t2 ^ 3 * a22 * vis +
          (403200 : k[X]) * t2 ^ 3 * a22 * a1 +
          (26880 : k[X]) * t2 ^ 4 * w73 +
          (90720 : k[X]) * t2 ^ 4 * a1 * Polynomial.C lambda -
          (28224 : k[X]) * t2 ^ 5 * vis -
          (231840 : k[X]) * t2 ^ 5 * a1 +
          h * ((61440 : k[X]) * a0 ^ 2 +
            (98304 : k[X]) * a22 * a0 * s22 -
            (153600 : k[X]) * a22 ^ 2 * a0 -
            (40960 : k[X]) * a22 ^ 3 * s22 +
            (44800 : k[X]) * a22 ^ 4 +
            (138240 : k[X]) * t2 * a22 * a0 * Polynomial.C lambda -
            (122880 : k[X]) * t2 ^ 2 * a0 * s22 -
            (153600 : k[X]) * t2 ^ 2 * a22 * a0 -
            (80640 : k[X]) * t2 * a22 ^ 3 * Polynomial.C lambda +
            (215040 : k[X]) * t2 ^ 2 * a22 ^ 2 * s22 -
            (80640 : k[X]) * t2 ^ 3 * a0 * Polynomial.C lambda +
            (201600 : k[X]) * t2 ^ 4 * a0 +
            (181440 : k[X]) * t2 ^ 3 * a22 ^ 2 * Polynomial.C lambda -
            (161280 : k[X]) * t2 ^ 4 * a22 * s22 -
            (352800 : k[X]) * t2 ^ 4 * a22 ^ 2 -
            (99792 : k[X]) * t2 ^ 5 * a22 * Polynomial.C lambda +
            (29568 : k[X]) * t2 ^ 6 * s22 +
            (258720 : k[X]) * t2 ^ 6 * a22 +
            (15444 : k[X]) * t2 ^ 7 * Polynomial.C lambda -
            (45045 : k[X]) * t2 ^ 8)) =
        Polynomial.C eta * h ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 24 hh)
    rw [← hclr, hpow]
    ring
  have hnext :
      xi + ((-49152 : k[X]) * a0 * w73 -
            (55296 : k[X]) * a1 * a0 * Polynomial.C lambda +
            (36864 : k[X]) * a22 ^ 2 * w73 +
            (86016 : k[X]) * t2 * a0 * vis -
            (30720 : k[X]) * t2 * a1 * a0 +
            (61440 : k[X]) * t2 * a22 * q54 +
            (69120 : k[X]) * a22 ^ 2 * a1 * Polynomial.C lambda -
            (245760 : k[X]) * t2 * a22 * a1 * s22 -
            (107520 : k[X]) * t2 * a22 ^ 2 * vis +
            (192000 : k[X]) * t2 * a22 ^ 2 * a1 -
            (92160 : k[X]) * t2 ^ 2 * a22 * w73 -
            (25600 : k[X]) * t2 ^ 3 * q54 -
            (241920 : k[X]) * t2 ^ 2 * a22 * a1 * Polynomial.C lambda +
            (143360 : k[X]) * t2 ^ 3 * a1 * s22 +
            (125440 : k[X]) * t2 ^ 3 * a22 * vis +
            (403200 : k[X]) * t2 ^ 3 * a22 * a1 +
            (26880 : k[X]) * t2 ^ 4 * w73 +
            (90720 : k[X]) * t2 ^ 4 * a1 * Polynomial.C lambda -
            (28224 : k[X]) * t2 ^ 5 * vis -
            (231840 : k[X]) * t2 ^ 5 * a1 +
            h * ((61440 : k[X]) * a0 ^ 2 +
              (98304 : k[X]) * a22 * a0 * s22 -
              (153600 : k[X]) * a22 ^ 2 * a0 -
              (40960 : k[X]) * a22 ^ 3 * s22 +
              (44800 : k[X]) * a22 ^ 4 +
              (138240 : k[X]) * t2 * a22 * a0 * Polynomial.C lambda -
              (122880 : k[X]) * t2 ^ 2 * a0 * s22 -
              (153600 : k[X]) * t2 ^ 2 * a22 * a0 -
              (80640 : k[X]) * t2 * a22 ^ 3 * Polynomial.C lambda +
              (215040 : k[X]) * t2 ^ 2 * a22 ^ 2 * s22 -
              (80640 : k[X]) * t2 ^ 3 * a0 * Polynomial.C lambda +
              (201600 : k[X]) * t2 ^ 4 * a0 +
              (181440 : k[X]) * t2 ^ 3 * a22 ^ 2 * Polynomial.C lambda -
              (161280 : k[X]) * t2 ^ 4 * a22 * s22 -
              (352800 : k[X]) * t2 ^ 4 * a22 ^ 2 -
              (99792 : k[X]) * t2 ^ 5 * a22 * Polynomial.C lambda +
              (29568 : k[X]) * t2 ^ 6 * s22 +
              (258720 : k[X]) * t2 ^ 6 * a22 +
              (15444 : k[X]) * t2 ^ 7 * Polynomial.C lambda -
              (45045 : k[X]) * t2 ^ 8)) =
        Polynomial.C eta * h := by
    apply mul_left_cancel₀ hh
    have hmul :
        h *
            (xi + ((-49152 : k[X]) * a0 * w73 -
                (55296 : k[X]) * a1 * a0 * Polynomial.C lambda +
                (36864 : k[X]) * a22 ^ 2 * w73 +
                (86016 : k[X]) * t2 * a0 * vis -
                (30720 : k[X]) * t2 * a1 * a0 +
                (61440 : k[X]) * t2 * a22 * q54 +
                (69120 : k[X]) * a22 ^ 2 * a1 * Polynomial.C lambda -
                (245760 : k[X]) * t2 * a22 * a1 * s22 -
                (107520 : k[X]) * t2 * a22 ^ 2 * vis +
                (192000 : k[X]) * t2 * a22 ^ 2 * a1 -
                (92160 : k[X]) * t2 ^ 2 * a22 * w73 -
                (25600 : k[X]) * t2 ^ 3 * q54 -
                (241920 : k[X]) * t2 ^ 2 * a22 * a1 *
                  Polynomial.C lambda +
                (143360 : k[X]) * t2 ^ 3 * a1 * s22 +
                (125440 : k[X]) * t2 ^ 3 * a22 * vis +
                (403200 : k[X]) * t2 ^ 3 * a22 * a1 +
                (26880 : k[X]) * t2 ^ 4 * w73 +
                (90720 : k[X]) * t2 ^ 4 * a1 * Polynomial.C lambda -
                (28224 : k[X]) * t2 ^ 5 * vis -
                (231840 : k[X]) * t2 ^ 5 * a1 +
                h * ((61440 : k[X]) * a0 ^ 2 +
                  (98304 : k[X]) * a22 * a0 * s22 -
                  (153600 : k[X]) * a22 ^ 2 * a0 -
                  (40960 : k[X]) * a22 ^ 3 * s22 +
                  (44800 : k[X]) * a22 ^ 4 +
                  (138240 : k[X]) * t2 * a22 * a0 *
                    Polynomial.C lambda -
                  (122880 : k[X]) * t2 ^ 2 * a0 * s22 -
                  (153600 : k[X]) * t2 ^ 2 * a22 * a0 -
                  (80640 : k[X]) * t2 * a22 ^ 3 * Polynomial.C lambda +
                  (215040 : k[X]) * t2 ^ 2 * a22 ^ 2 * s22 -
                  (80640 : k[X]) * t2 ^ 3 * a0 * Polynomial.C lambda +
                  (201600 : k[X]) * t2 ^ 4 * a0 +
                  (181440 : k[X]) * t2 ^ 3 * a22 ^ 2 *
                    Polynomial.C lambda -
                  (161280 : k[X]) * t2 ^ 4 * a22 * s22 -
                  (352800 : k[X]) * t2 ^ 4 * a22 ^ 2 -
                  (99792 : k[X]) * t2 ^ 5 * a22 * Polynomial.C lambda +
                  (29568 : k[X]) * t2 ^ 6 * s22 +
                  (258720 : k[X]) * t2 ^ 6 * a22 +
                  (15444 : k[X]) * t2 ^ 7 * Polynomial.C lambda -
                  (45045 : k[X]) * t2 ^ 8))) =
          (32768 : k[X]) * b2 - (40960 : k[X]) * a1 * q54 -
              (32768 : k[X]) * a22 * b42 - (24576 : k[X]) * t2 * b31 +
              (49152 : k[X]) * a1 ^ 2 * s22 +
              (86016 : k[X]) * a22 * a1 * vis -
              (153600 : k[X]) * a22 * a1 ^ 2 +
              (73728 : k[X]) * t2 * a1 * w73 +
              (24576 : k[X]) * t2 ^ 2 * b42 +
              (69120 : k[X]) * t2 * a1 ^ 2 * Polynomial.C lambda -
              (107520 : k[X]) * t2 ^ 2 * a1 * vis -
              (76800 : k[X]) * t2 ^ 2 * a1 ^ 2 +
            h * ((-49152 : k[X]) * a0 * w73 -
              (55296 : k[X]) * a1 * a0 * Polynomial.C lambda +
              (36864 : k[X]) * a22 ^ 2 * w73 +
              (86016 : k[X]) * t2 * a0 * vis -
              (30720 : k[X]) * t2 * a1 * a0 +
              (61440 : k[X]) * t2 * a22 * q54 +
              (69120 : k[X]) * a22 ^ 2 * a1 * Polynomial.C lambda -
              (245760 : k[X]) * t2 * a22 * a1 * s22 -
              (107520 : k[X]) * t2 * a22 ^ 2 * vis +
              (192000 : k[X]) * t2 * a22 ^ 2 * a1 -
              (92160 : k[X]) * t2 ^ 2 * a22 * w73 -
              (25600 : k[X]) * t2 ^ 3 * q54 -
              (241920 : k[X]) * t2 ^ 2 * a22 * a1 *
                Polynomial.C lambda +
              (143360 : k[X]) * t2 ^ 3 * a1 * s22 +
              (125440 : k[X]) * t2 ^ 3 * a22 * vis +
              (403200 : k[X]) * t2 ^ 3 * a22 * a1 +
              (26880 : k[X]) * t2 ^ 4 * w73 +
              (90720 : k[X]) * t2 ^ 4 * a1 * Polynomial.C lambda -
              (28224 : k[X]) * t2 ^ 5 * vis -
              (231840 : k[X]) * t2 ^ 5 * a1 +
              h * ((61440 : k[X]) * a0 ^ 2 +
                (98304 : k[X]) * a22 * a0 * s22 -
                (153600 : k[X]) * a22 ^ 2 * a0 -
                (40960 : k[X]) * a22 ^ 3 * s22 +
                (44800 : k[X]) * a22 ^ 4 +
                (138240 : k[X]) * t2 * a22 * a0 * Polynomial.C lambda -
                (122880 : k[X]) * t2 ^ 2 * a0 * s22 -
                (153600 : k[X]) * t2 ^ 2 * a22 * a0 -
                (80640 : k[X]) * t2 * a22 ^ 3 * Polynomial.C lambda +
                (215040 : k[X]) * t2 ^ 2 * a22 ^ 2 * s22 -
                (80640 : k[X]) * t2 ^ 3 * a0 * Polynomial.C lambda +
                (201600 : k[X]) * t2 ^ 4 * a0 +
                (181440 : k[X]) * t2 ^ 3 * a22 ^ 2 *
                  Polynomial.C lambda -
                (161280 : k[X]) * t2 ^ 4 * a22 * s22 -
                (352800 : k[X]) * t2 ^ 4 * a22 ^ 2 -
                (99792 : k[X]) * t2 ^ 5 * a22 * Polynomial.C lambda +
                (29568 : k[X]) * t2 ^ 6 * s22 +
                (258720 : k[X]) * t2 ^ 6 * a22 +
                (15444 : k[X]) * t2 ^ 7 * Polynomial.C lambda -
                (45045 : k[X]) * t2 ^ 8)) := by
      rw [hcof] <;> try ring
    rw [hmul, hpoly]
    ring
  have heval := congrArg (fun r : k[X] => r.eval a) hnext
  have hraw :
      xi.eval a + (-(49152 : k) * a0.eval a * w73.eval a -
          (55296 : k) * a1.eval a * a0.eval a * lambda +
          (36864 : k) * (a22.eval a) ^ 2 * w73.eval a +
          (86016 : k) * t2.eval a * a0.eval a * vis.eval a -
          (30720 : k) * t2.eval a * a1.eval a * a0.eval a +
          (61440 : k) * t2.eval a * a22.eval a * q54.eval a +
          (69120 : k) * (a22.eval a) ^ 2 * a1.eval a * lambda -
          (245760 : k) * t2.eval a * a22.eval a * a1.eval a *
            s22.eval a -
          (107520 : k) * t2.eval a * (a22.eval a) ^ 2 * vis.eval a +
          (192000 : k) * t2.eval a * (a22.eval a) ^ 2 * a1.eval a -
          (92160 : k) * (t2.eval a) ^ 2 * a22.eval a * w73.eval a -
          (25600 : k) * (t2.eval a) ^ 3 * q54.eval a -
          (241920 : k) * (t2.eval a) ^ 2 * a22.eval a * a1.eval a *
            lambda +
          (143360 : k) * (t2.eval a) ^ 3 * a1.eval a * s22.eval a +
          (125440 : k) * (t2.eval a) ^ 3 * a22.eval a * vis.eval a +
          (403200 : k) * (t2.eval a) ^ 3 * a22.eval a * a1.eval a +
          (26880 : k) * (t2.eval a) ^ 4 * w73.eval a +
          (90720 : k) * (t2.eval a) ^ 4 * a1.eval a * lambda -
          (28224 : k) * (t2.eval a) ^ 5 * vis.eval a -
          (231840 : k) * (t2.eval a) ^ 5 * a1.eval a) =
        0 := by
    simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub, mul_comm,
      mul_left_comm, mul_assoc] using heval
  exact thirteenthFace_Y_nextOrder410 (xi.eval a) (q54.eval a)
    (a1.eval a) (a0.eval a) (a22.eval a) (s22.eval a) (vis.eval a)
    (w73.eval a) (t2.eval a) lambda hT hU hV hraw

end NonzeroThirteenthFace410

#print axioms thirteenthCoefficientJacobianRow_410
#print axioms differentialJacobian_coeff_0_monicQuarticDecic
#print axioms thirteenthFace_W_nextOrder410
#print axioms thirteenthFace_X_nextOrder410
#print axioms thirteenthFace_Y_nextOrder410
#print axioms thirteenthFace_upgradedNextOrder410
#print axioms thirteenthFace_exists_W_cofactor410
#print axioms thirteenthFace_exists_X_cofactor410
#print axioms thirteenthFace_exists_Y_cofactor410
#print axioms thirteenthFace_evalW410
#print axioms thirteenthFace_evalX410
#print axioms thirteenthFace_evalY410

end Max11DegreeRoutes
