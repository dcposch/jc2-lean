import Grok410ScaleTwoEleventhFaceScratch

/-! # Scale-two twelfth face for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the eleventh-face packet supplies the degree-`2`
Jacobian row, the residual `ι` (not cleared), and the upgraded jet
`h³ ∣ p₃`, `h² ∣ p₂`, `h⁸ ∣ q₈`, `h⁶ ∣ q₇`, `h⁵ ∣ q₆`, `h³ ∣ q₅`,
`h² ∣ q₄`, `h⁸ ∣ q₉` together with `2 (q₇/h⁶)(a) = 5 p₁(a)`,
`(q₅/h³)(a) = 0`, `q₃(a) = 0`,
`8 (q₆/h⁵)(a) = p₁(a) (30 t₂(a) - 9 λ)`, and
`8 (q₄/h²)(a) = 15 p₁(a)²`.

The next unused Keller coefficient is the degree-`1` Jacobian row.  After
the same quartic depression that kills `z³`, that row is
`2 V C' + W B' - B W' - 2 A Z' = 0`.  The new decic coordinate in this
identity is `Z` itself.  Clearing a first integral against that `z⁰`
coordinate produces a defect larger than the remaining exact jet, so this
file isolates the Jacobian identity and does not introduce or clear any
residual below `z⁰`.  The tenth-face residual `ι` is not claimed to
vanish.

On the upgraded jet the already-vanishing evaluations `(q₅/h³)(a) = 0`
and `q₃(a) = 0` supply the extra factors `h⁴ ∣ q₅` and `h ∣ q₃`.
Evaluating the fifth, seventh, and eighth defects at the next leftover
order then forces
`32 (q₅/h⁴)(a) = p₁(a) (64 s₂₂(a) - 40 a₂₂(a) + 27 λ t₂(a) - 90 t₂(a)²)`,
`64 (q₃/h)(a) = 15 p₁(a)² (4 t₂(a) - 3 λ)`, and
`256 q₂(a) = p₁(a)² (256 s₂₂(a) - 400 a₂₂(a) + 243 λ t₂(a) - 540 t₂(a)²)`.
No further individual vanishing of `p₁, p₀, t₂, a₂₂, s₂₂, q₂` or of
`(p₃/h³)(a)` is claimed.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The twelfth row below the leading weighted-Wronskian row for outer
degrees `(4,10)`.  Unused Jacobian coefficients of the eleventh face start
at degree `1`. -/
theorem twelfthCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 1).derivative * q.coeff 1 +
        (p.coeff 0).derivative * (q.coeff 2 * Polynomial.C (2 : K)) -
      ((p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 0).derivative +
        p.coeff 1 * (q.coeff 1).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 1) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (1 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 1 :
      Finset (ℕ × ℕ)) =
      ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC2]
  linear_combination hcoeff

/-! ## Degree-`1` depressed Jacobian coefficient -/

section DepressedRow410Twelfth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option linter.unusedVariables false

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`1` Jacobian coefficient is
exactly `2 V C' + W B' - B W' - 2 A Z'`.  The coordinate `Z = g.coeff 0`
is recorded only as a Jacobian term; it is not cleared. -/
theorem differentialJacobian_coeff_1_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 1 =
      (2 : F) * g.coeff 2 * d (f.coeff 0) +
        g.coeff 1 * d (f.coeff 1) -
          f.coeff 1 * d (g.coeff 1) -
          (2 : F) * f.coeff 2 * d (g.coeff 0) := by
  have hanti1 : (Finset.HasAntidiagonal.antidiagonal (1 : ℕ) :
      Finset (ℕ × ℕ)) =
      ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne01 : ((0, 1) : ℕ × ℕ) ≠ (1, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 1 =
        (2 : F) * g.coeff 2 * d (f.coeff 0) +
          g.coeff 1 * d (f.coeff 1) := by
    rw [Polynomial.coeff_mul, hanti1,
      Finset.sum_insert (by simp [hne01]), Finset.sum_singleton]
    have hder1 : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0 : g.derivative.coeff 0 = g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    rw [coeff_coefficientDeriv, coeff_coefficientDeriv, hder1, hder0]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 1 =
        f.coeff 1 * d (g.coeff 1) +
          (2 : F) * f.coeff 2 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti1,
      Finset.sum_insert (by simp [hne01]), Finset.sum_singleton]
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hder0, hder1, coeff_coefficientDeriv, coeff_coefficientDeriv]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

end DepressedRow410Twelfth

/-! ## Order-one scalar algebra on the further upgraded jet -/

section TwelfthFaceScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- After `(q₅/h³)(a) = 0`, the fifth defect at the next leftover order
forces
`32 (q₅/h⁴)(a) = p₁(a) (64 s₂₂(a) - 40 a₂₂(a) + 27 λ t₂(a) - 90 t₂(a)²)`. -/
theorem twelfthFace_V_nextOrder410 (q54 a1 a22 s22 vis w73 t2 lam : F)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (8 : F) * w73 =
      a1 * ((30 : F) * t2 - (9 : F) * lam))
    (hV : (4096 : F) * q54 - (8192 : F) * a1 * s22 -
        (7168 : F) * a22 * vis + (23040 : F) * a22 * a1 -
        (6144 : F) * t2 * w73 - (10368 : F) * t2 * a1 * lam +
        (8064 : F) * t2 ^ 2 * vis + (14400 : F) * t2 ^ 2 * a1 =
      0) :
    (32 : F) * q54 + (40 : F) * a1 * a22 - (64 : F) * a1 * s22 -
        (27 : F) * a1 * lam * t2 + (90 : F) * a1 * t2 ^ 2 =
      0 := by
  have hU0 : (8 : F) * w73 -
      a1 * ((30 : F) * t2 - (9 : F) * lam) = 0 := by
    linear_combination hU
  have h128 : (128 : F) ≠ 0 := by norm_num
  have hid :
      (128 : F) *
          ((32 : F) * q54 + (40 : F) * a1 * a22 -
            (64 : F) * a1 * s22 - (27 : F) * a1 * lam * t2 +
            (90 : F) * a1 * t2 ^ 2) =
        (4096 : F) * q54 - (8192 : F) * a1 * s22 -
            (7168 : F) * a22 * vis + (23040 : F) * a22 * a1 -
            (6144 : F) * t2 * w73 - (10368 : F) * t2 * a1 * lam +
            (8064 : F) * t2 ^ 2 * vis + (14400 : F) * t2 ^ 2 * a1 +
          ((112 : F) * a22 - (126 : F) * t2 ^ 2) *
            ((64 : F) * vis - (160 : F) * a1) +
          (768 : F) * t2 *
            ((8 : F) * w73 -
              a1 * ((30 : F) * t2 - (9 : F) * lam)) := by
    ring
  have hcomb :
      (128 : F) *
          ((32 : F) * q54 + (40 : F) * a1 * a22 -
            (64 : F) * a1 * s22 - (27 : F) * a1 * lam * t2 +
            (90 : F) * a1 * t2 ^ 2) =
        0 := by
    rw [hid]
    linear_combination hV +
      ((112 : F) * a22 - (126 : F) * t2 ^ 2) * hT +
        (768 : F) * t2 * hU0
  exact (mul_eq_zero.mp hcomb).resolve_left h128

/-- After `q₃(a) = 0`, the seventh defect at the next leftover order
forces `64 (q₃/h)(a) = 15 p₁(a)² (4 t₂(a) - 3 λ)`. -/
theorem twelfthFace_X_nextOrder410 (b31 a1 t2 vis w73 b42 lam : F)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (8 : F) * w73 =
      a1 * ((30 : F) * t2 - (9 : F) * lam))
    (hW : (8 : F) * b42 = (15 : F) * a1 ^ 2)
    (hX : (131072 : F) * b31 - (196608 : F) * a1 * w73 -
        (131072 : F) * t2 * b42 - (129024 : F) * a1 ^ 2 * lam +
        (401408 : F) * t2 * a1 * vis - (143360 : F) * t2 * a1 ^ 2 =
      0) :
    (64 : F) * b31 - (15 : F) * a1 ^ 2 *
        ((4 : F) * t2 - (3 : F) * lam) =
      0 := by
  have hU0 : (8 : F) * w73 -
      a1 * ((30 : F) * t2 - (9 : F) * lam) = 0 := by
    linear_combination hU
  have hW0 : (8 : F) * b42 - (15 : F) * a1 ^ 2 = 0 := by
    linear_combination hW
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have hid :
      (2048 : F) *
          ((64 : F) * b31 - (15 : F) * a1 ^ 2 *
            ((4 : F) * t2 - (3 : F) * lam)) =
        (131072 : F) * b31 - (196608 : F) * a1 * w73 -
            (131072 : F) * t2 * b42 - (129024 : F) * a1 ^ 2 * lam +
            (401408 : F) * t2 * a1 * vis -
            (143360 : F) * t2 * a1 ^ 2 +
          (-(6272 : F) * a1 * t2) *
            ((64 : F) * vis - (160 : F) * a1) +
          (24576 : F) * a1 *
            ((8 : F) * w73 -
              a1 * ((30 : F) * t2 - (9 : F) * lam)) +
          (16384 : F) * t2 *
            ((8 : F) * b42 - (15 : F) * a1 ^ 2) := by
    ring
  have hcomb :
      (2048 : F) *
          ((64 : F) * b31 - (15 : F) * a1 ^ 2 *
            ((4 : F) * t2 - (3 : F) * lam)) =
        0 := by
    rw [hid]
    linear_combination hX + (-(6272 : F) * a1 * t2) * hT +
      (24576 : F) * a1 * hU0 + (16384 : F) * t2 * hW0
  exact (mul_eq_zero.mp hcomb).resolve_left h2048

/-- After the fifth- and seventh-face identities, the eighth defect at
the next leftover order forces
`256 q₂(a) = p₁(a)² (256 s₂₂(a) - 400 a₂₂(a) + 243 λ t₂(a) - 540 t₂(a)²)`. -/
theorem twelfthFace_Y_nextOrder410 (b2 q54 b31 a1 a22 s22 vis w73 b42
    t2 lam : F)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (8 : F) * w73 =
      a1 * ((30 : F) * t2 - (9 : F) * lam))
    (hW : (8 : F) * b42 = (15 : F) * a1 ^ 2)
    (hV : (4096 : F) * q54 - (8192 : F) * a1 * s22 -
        (7168 : F) * a22 * vis + (23040 : F) * a22 * a1 -
        (6144 : F) * t2 * w73 - (10368 : F) * t2 * a1 * lam +
        (8064 : F) * t2 ^ 2 * vis + (14400 : F) * t2 ^ 2 * a1 =
      0)
    (hX : (131072 : F) * b31 - (196608 : F) * a1 * w73 -
        (131072 : F) * t2 * b42 - (129024 : F) * a1 ^ 2 * lam +
        (401408 : F) * t2 * a1 * vis - (143360 : F) * t2 * a1 ^ 2 =
      0)
    (hY : (32768 : F) * b2 - (40960 : F) * a1 * q54 -
        (32768 : F) * a22 * b42 - (24576 : F) * t2 * b31 +
        (49152 : F) * a1 ^ 2 * s22 + (86016 : F) * a22 * a1 * vis -
        (153600 : F) * a22 * a1 ^ 2 + (73728 : F) * t2 * a1 * w73 +
        (24576 : F) * t2 ^ 2 * b42 + (69120 : F) * t2 * a1 ^ 2 * lam -
        (107520 : F) * t2 ^ 2 * a1 * vis -
        (76800 : F) * t2 ^ 2 * a1 ^ 2 =
      0) :
    (256 : F) * b2 - (256 : F) * a1 ^ 2 * s22 +
        (400 : F) * a1 ^ 2 * a22 - (243 : F) * a1 ^ 2 * t2 * lam +
        (540 : F) * a1 ^ 2 * t2 ^ 2 =
      0 := by
  have hVred :=
    twelfthFace_V_nextOrder410 q54 a1 a22 s22 vis w73 t2 lam hT hU hV
  have hXred :=
    twelfthFace_X_nextOrder410 b31 a1 t2 vis w73 b42 lam hT hU hW hX
  have hU0 : (8 : F) * w73 -
      a1 * ((30 : F) * t2 - (9 : F) * lam) = 0 := by
    linear_combination hU
  have hW0 : (8 : F) * b42 - (15 : F) * a1 ^ 2 = 0 := by
    linear_combination hW
  have h128 : (128 : F) ≠ 0 := by norm_num
  have hid :
      (128 : F) *
          ((256 : F) * b2 - (256 : F) * a1 ^ 2 * s22 +
            (400 : F) * a1 ^ 2 * a22 -
            (243 : F) * a1 ^ 2 * t2 * lam +
            (540 : F) * a1 ^ 2 * t2 ^ 2) =
        (32768 : F) * b2 - (40960 : F) * a1 * q54 -
            (32768 : F) * a22 * b42 - (24576 : F) * t2 * b31 +
            (49152 : F) * a1 ^ 2 * s22 +
            (86016 : F) * a22 * a1 * vis -
            (153600 : F) * a22 * a1 ^ 2 +
            (73728 : F) * t2 * a1 * w73 +
            (24576 : F) * t2 ^ 2 * b42 +
            (69120 : F) * t2 * a1 ^ 2 * lam -
            (107520 : F) * t2 ^ 2 * a1 * vis -
            (76800 : F) * t2 ^ 2 * a1 ^ 2 +
          (1280 : F) * a1 *
            ((32 : F) * q54 + (40 : F) * a1 * a22 -
              (64 : F) * a1 * s22 - (27 : F) * a1 * lam * t2 +
              (90 : F) * a1 * t2 ^ 2) +
          (384 : F) * t2 *
            ((64 : F) * b31 - (15 : F) * a1 ^ 2 *
              ((4 : F) * t2 - (3 : F) * lam)) +
          ((-1344 : F) * a1 * a22 + (1680 : F) * a1 * t2 ^ 2) *
            ((64 : F) * vis - (160 : F) * a1) +
          ((4096 : F) * a22 - (3072 : F) * t2 ^ 2) *
            ((8 : F) * b42 - (15 : F) * a1 ^ 2) +
          ((-9216 : F) * a1 * t2) *
            ((8 : F) * w73 -
              a1 * ((30 : F) * t2 - (9 : F) * lam)) := by
    ring
  have hcomb :
      (128 : F) *
          ((256 : F) * b2 - (256 : F) * a1 ^ 2 * s22 +
            (400 : F) * a1 ^ 2 * a22 -
            (243 : F) * a1 ^ 2 * t2 * lam +
            (540 : F) * a1 ^ 2 * t2 ^ 2) =
        0 := by
    rw [hid]
    linear_combination hY + (1280 : F) * a1 * hVred +
      (384 : F) * t2 * hXred +
      ((-1344 : F) * a1 * a22 + (1680 : F) * a1 * t2 ^ 2) * hT +
      ((4096 : F) * a22 - (3072 : F) * t2 ^ 2) * hW0 +
      ((-9216 : F) * a1 * t2) * hU0
  exact (mul_eq_zero.mp hcomb).resolve_left h128

/-- Combined next-order identities of the upgraded eleventh-face jet. -/
theorem twelfthFace_upgradedNextOrder410 (vis a1 t2 w73 b42 q54 b31 b2
    a22 s22 lam : F)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (144 : F) * a1 * lam + (80 : F) * t2 * a1 -
      (224 : F) * t2 * vis + (128 : F) * w73 = 0)
    (hW : (5120 : F) * a1 ^ 2 - (3584 : F) * vis * a1 +
      (2048 : F) * b42 = 0)
    (hV : (4096 : F) * q54 - (8192 : F) * a1 * s22 -
        (7168 : F) * a22 * vis + (23040 : F) * a22 * a1 -
        (6144 : F) * t2 * w73 - (10368 : F) * t2 * a1 * lam +
        (8064 : F) * t2 ^ 2 * vis + (14400 : F) * t2 ^ 2 * a1 =
      0)
    (hX : (131072 : F) * b31 - (196608 : F) * a1 * w73 -
        (131072 : F) * t2 * b42 - (129024 : F) * a1 ^ 2 * lam +
        (401408 : F) * t2 * a1 * vis - (143360 : F) * t2 * a1 ^ 2 =
      0)
    (hY : (32768 : F) * b2 - (40960 : F) * a1 * q54 -
        (32768 : F) * a22 * b42 - (24576 : F) * t2 * b31 +
        (49152 : F) * a1 ^ 2 * s22 + (86016 : F) * a22 * a1 * vis -
        (153600 : F) * a22 * a1 ^ 2 + (73728 : F) * t2 * a1 * w73 +
        (24576 : F) * t2 ^ 2 * b42 + (69120 : F) * t2 * a1 ^ 2 * lam -
        (107520 : F) * t2 ^ 2 * a1 * vis -
        (76800 : F) * t2 ^ 2 * a1 ^ 2 =
      0) :
    (2 : F) * vis = (5 : F) * a1 ∧
      (8 : F) * w73 = a1 * ((30 : F) * t2 - (9 : F) * lam) ∧
      (8 : F) * b42 = (15 : F) * a1 ^ 2 ∧
      (32 : F) * q54 + (40 : F) * a1 * a22 - (64 : F) * a1 * s22 -
          (27 : F) * a1 * lam * t2 + (90 : F) * a1 * t2 ^ 2 =
        0 ∧
      (64 : F) * b31 =
        (15 : F) * a1 ^ 2 * ((4 : F) * t2 - (3 : F) * lam) ∧
      (256 : F) * b2 =
        a1 ^ 2 *
          ((256 : F) * s22 - (400 : F) * a22 +
            (243 : F) * lam * t2 - (540 : F) * t2 ^ 2) := by
  have hTred := tenthFace_T_collapsed410 vis a1 hT
  have hUred := tenthFace_U_collapsed410 t2 vis w73 a1 lam hT hU
  have hWred := tenthFace_W_collapsed410 vis a1 b42 hT hW
  have hVred :=
    twelfthFace_V_nextOrder410 q54 a1 a22 s22 vis w73 t2 lam hT hUred hV
  have hXred :=
    twelfthFace_X_nextOrder410 b31 a1 t2 vis w73 b42 lam hT hUred hWred
      hX
  have hYred :=
    twelfthFace_Y_nextOrder410 b2 q54 b31 a1 a22 s22 vis w73 b42 t2 lam
      hT hUred hWred hV hX hY
  refine ⟨hTred, hUred, hWred, hVred, ?_, ?_⟩
  · linear_combination hXred
  · linear_combination hYred

/-! ## Further-upgraded substitutions of the cleared defects -/

theorem twelfthFace_clearedM_upgraded410 (h t2 a22 s22 : F[X])
    (lambda : F) :
    localClearedSecondDefect410 h (h ^ 3 * t2) (h ^ 2 * a22)
        (h ^ 8 * s22) lambda =
      h ^ 8 * ((8 : F[X]) * s22 - (20 : F[X]) * a22 +
        (9 : F[X]) * Polynomial.C lambda * t2 -
        (15 : F[X]) * t2 ^ 2) := by
  have h2 : h ^ 2 * a22 = h * (h * a22) := by ring
  have h8 : h ^ 8 * s22 = h ^ 7 * (h * s22) := by ring
  rw [h2, h8, tenthFace_clearedM_collapsed410]
  ring

theorem twelfthFace_clearedV_upgraded410 (h t2 a22 s22 vis w73 q54 a1 a0 :
    F[X]) (lambda : F) :
    localClearedFifthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
        lambda =
      h ^ 16 * ((4096 : F[X]) * q54 +
        (23040 : F[X]) * a1 * a22 -
          (10368 : F[X]) * a1 * Polynomial.C lambda * t2 -
          (8192 : F[X]) * a1 * s22 + (14400 : F[X]) * a1 * t2 ^ 2 -
          (7168 : F[X]) * a22 * vis + (8064 : F[X]) * t2 ^ 2 * vis -
          (6144 : F[X]) * t2 * w73 +
        h * ((4608 : F[X]) * a0 * Polynomial.C lambda -
          (5184 : F[X]) * a22 ^ 2 * Polynomial.C lambda -
          (11520 : F[X]) * a22 ^ 2 * t2 +
          (16848 : F[X]) * a22 * Polynomial.C lambda * t2 ^ 2 +
          (18432 : F[X]) * a22 * s22 * t2 -
          (31200 : F[X]) * a22 * t2 ^ 3 -
          (5967 : F[X]) * Polynomial.C lambda * t2 ^ 4 -
          (9984 : F[X]) * s22 * t2 ^ 3 +
          (15912 : F[X]) * t2 ^ 5)) := by
  have h4 : h ^ 4 * q54 = h ^ 3 * (h * q54) := by ring
  rw [h4, eleventhFace_clearedV_collapsed410]
  ring

set_option maxHeartbeats 8000000 in
theorem twelfthFace_clearedW_upgraded410 (h t2 a22 s22 vis w73 q54 a1 a0
    b42 : F[X]) (lambda : F) :
    localClearedSixthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
        (h ^ 2 * b42) lambda =
      h ^ 18 * ((5120 : F[X]) * a1 ^ 2 - (3584 : F[X]) * vis * a1 +
        (2048 : F[X]) * b42 +
        h * ((-2560 : F[X]) * t2 * q54 -
          (4608 : F[X]) * a1 * a22 * Polynomial.C lambda -
          (7680 : F[X]) * a1 * a22 * t2 +
          (6912 : F[X]) * a1 * Polynomial.C lambda * t2 ^ 2 +
          (8192 : F[X]) * a1 * s22 * t2 - (14080 : F[X]) * a1 * t2 ^ 3 +
          (7168 : F[X]) * a22 * t2 * vis - (3072 : F[X]) * a22 * w73 -
          (3584 : F[X]) * t2 ^ 3 * vis + (3072 : F[X]) * t2 ^ 2 * w73 +
          h * ((10240 : F[X]) * a0 * a22 -
            (4608 : F[X]) * a0 * Polynomial.C lambda * t2 -
            (4096 : F[X]) * a0 * s22 + (7680 : F[X]) * a0 * t2 ^ 2 -
            (5120 : F[X]) * a22 ^ 3 +
            (6912 : F[X]) * a22 ^ 2 * Polynomial.C lambda * t2 +
            (4096 : F[X]) * a22 ^ 2 * s22 -
            (3840 : F[X]) * a22 ^ 2 * t2 ^ 2 -
            (9216 : F[X]) * a22 * Polynomial.C lambda * t2 ^ 3 -
            (12288 : F[X]) * a22 * s22 * t2 ^ 2 +
            (20480 : F[X]) * a22 * t2 ^ 4 +
            (2304 : F[X]) * Polynomial.C lambda * t2 ^ 5 +
            (4096 : F[X]) * s22 * t2 ^ 4 - (6400 : F[X]) * t2 ^ 6))) :=
    by
  have h4 : h ^ 4 * q54 = h ^ 3 * (h * q54) := by ring
  rw [h4, eleventhFace_clearedW_collapsed410]
  ring

set_option maxHeartbeats 16000000 in
theorem twelfthFace_clearedX_upgraded410 (h t2 a22 s22 vis w73 q54 a1 a0
    b42 b31 : F[X]) (lambda : F) :
    localClearedSeventhDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
        (h ^ 2 * b42) (h * b31) lambda =
      h ^ 21 * ((131072 : F[X]) * b31 - (196608 : F[X]) * a1 * w73 -
        (131072 : F[X]) * t2 * b42 -
        (129024 : F[X]) * a1 ^ 2 * Polynomial.C lambda +
        (401408 : F[X]) * t2 * a1 * vis - (143360 : F[X]) * t2 * a1 ^ 2 +
        h * ((-163840 : F[X]) * a22 * q54 +
          (143360 : F[X]) * q54 * t2 ^ 2 +
          (573440 : F[X]) * a0 * a1 - (229376 : F[X]) * a0 * vis -
          (788480 : F[X]) * a1 * a22 ^ 2 +
          (709632 : F[X]) * a1 * a22 * Polynomial.C lambda * t2 +
          (458752 : F[X]) * a1 * a22 * s22 -
          (591360 : F[X]) * a1 * a22 * t2 ^ 2 -
          (443520 : F[X]) * a1 * Polynomial.C lambda * t2 ^ 3 -
          (630784 : F[X]) * a1 * s22 * t2 ^ 2 +
          (1047200 : F[X]) * a1 * t2 ^ 4 +
          (200704 : F[X]) * a22 ^ 2 * vis -
          (551936 : F[X]) * a22 * t2 ^ 2 * vis +
          (344064 : F[X]) * a22 * t2 * w73 +
          (172480 : F[X]) * t2 ^ 4 * vis -
          (157696 : F[X]) * t2 ^ 3 * w73 +
          h * ((-258048 : F[X]) * a0 * a22 * Polynomial.C lambda -
            (286720 : F[X]) * a0 * a22 * t2 +
            (354816 : F[X]) * a0 * Polynomial.C lambda * t2 ^ 2 +
            (458752 : F[X]) * a0 * s22 * t2 -
            (788480 : F[X]) * a0 * t2 ^ 3 +
            (118272 : F[X]) * a22 ^ 3 * Polynomial.C lambda +
            (394240 : F[X]) * a22 ^ 3 * t2 -
            (665280 : F[X]) * a22 ^ 2 * Polynomial.C lambda * t2 ^ 2 -
            (630784 : F[X]) * a22 ^ 2 * s22 * t2 +
            (985600 : F[X]) * a22 ^ 2 * t2 ^ 3 +
            (526680 : F[X]) * a22 * Polynomial.C lambda * t2 ^ 4 +
            (788480 : F[X]) * a22 * s22 * t2 ^ 3 -
            (1287440 : F[X]) * a22 * t2 ^ 5 -
            (100947 : F[X]) * Polynomial.C lambda * t2 ^ 6 -
            (187264 : F[X]) * s22 * t2 ^ 5 +
            (288420 : F[X]) * t2 ^ 7))) := by
  have h4 : h ^ 4 * q54 = h ^ 3 * (h * q54) := by ring
  rw [h4, eleventhFace_clearedX_collapsed410]
  ring

set_option maxHeartbeats 32000000 in
theorem twelfthFace_clearedY_upgraded410 (h t2 a22 s22 vis w73 q54 a1 a0
    b42 b31 b2 : F[X]) (lambda : F) :
    localClearedEighthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
        (h ^ 2 * b42) (h * b31) b2 lambda =
      h ^ 24 * ((32768 : F[X]) * b2 - (40960 : F[X]) * a1 * q54 -
        (32768 : F[X]) * a22 * b42 - (24576 : F[X]) * t2 * b31 +
        (49152 : F[X]) * a1 ^ 2 * s22 +
        (86016 : F[X]) * a22 * a1 * vis -
        (153600 : F[X]) * a22 * a1 ^ 2 +
        (73728 : F[X]) * t2 * a1 * w73 +
        (24576 : F[X]) * t2 ^ 2 * b42 +
        (69120 : F[X]) * t2 * a1 ^ 2 * Polynomial.C lambda -
        (107520 : F[X]) * t2 ^ 2 * a1 * vis -
        (76800 : F[X]) * t2 ^ 2 * a1 ^ 2 +
        h * ((-49152 : F[X]) * a0 * w73 -
          (55296 : F[X]) * a1 * a0 * Polynomial.C lambda +
          (36864 : F[X]) * a22 ^ 2 * w73 +
          (86016 : F[X]) * t2 * a0 * vis -
          (30720 : F[X]) * t2 * a1 * a0 +
          (61440 : F[X]) * t2 * a22 * q54 +
          (69120 : F[X]) * a22 ^ 2 * a1 * Polynomial.C lambda -
          (245760 : F[X]) * t2 * a22 * a1 * s22 -
          (107520 : F[X]) * t2 * a22 ^ 2 * vis +
          (192000 : F[X]) * t2 * a22 ^ 2 * a1 -
          (92160 : F[X]) * t2 ^ 2 * a22 * w73 -
          (25600 : F[X]) * t2 ^ 3 * q54 -
          (241920 : F[X]) * t2 ^ 2 * a22 * a1 * Polynomial.C lambda +
          (143360 : F[X]) * t2 ^ 3 * a1 * s22 +
          (125440 : F[X]) * t2 ^ 3 * a22 * vis +
          (403200 : F[X]) * t2 ^ 3 * a22 * a1 +
          (26880 : F[X]) * t2 ^ 4 * w73 +
          (90720 : F[X]) * t2 ^ 4 * a1 * Polynomial.C lambda -
          (28224 : F[X]) * t2 ^ 5 * vis -
          (231840 : F[X]) * t2 ^ 5 * a1 +
          h * ((61440 : F[X]) * a0 ^ 2 +
            (98304 : F[X]) * a22 * a0 * s22 -
            (153600 : F[X]) * a22 ^ 2 * a0 -
            (40960 : F[X]) * a22 ^ 3 * s22 +
            (44800 : F[X]) * a22 ^ 4 +
            (138240 : F[X]) * t2 * a22 * a0 * Polynomial.C lambda -
            (122880 : F[X]) * t2 ^ 2 * a0 * s22 -
            (153600 : F[X]) * t2 ^ 2 * a22 * a0 -
            (80640 : F[X]) * t2 * a22 ^ 3 * Polynomial.C lambda +
            (215040 : F[X]) * t2 ^ 2 * a22 ^ 2 * s22 -
            (80640 : F[X]) * t2 ^ 3 * a0 * Polynomial.C lambda +
            (201600 : F[X]) * t2 ^ 4 * a0 +
            (181440 : F[X]) * t2 ^ 3 * a22 ^ 2 * Polynomial.C lambda -
            (161280 : F[X]) * t2 ^ 4 * a22 * s22 -
            (352800 : F[X]) * t2 ^ 4 * a22 ^ 2 -
            (99792 : F[X]) * t2 ^ 5 * a22 * Polynomial.C lambda +
            (29568 : F[X]) * t2 ^ 6 * s22 +
            (258720 : F[X]) * t2 ^ 6 * a22 +
            (15444 : F[X]) * t2 ^ 7 * Polynomial.C lambda -
            (45045 : F[X]) * t2 ^ 8))) := by
  have h2 : h ^ 2 * a22 = h * (h * a22) := by ring
  have h8 : h ^ 8 * s22 = h ^ 7 * (h * s22) := by ring
  have h5 : h ^ 5 * w73 = h ^ 4 * (h * w73) := by ring
  have h4 : h ^ 4 * q54 = h ^ 2 * (h ^ 2 * q54) := by ring
  have hb : h ^ 2 * b42 = h * (h * b42) := by ring
  rw [h2, h8, h5, h4, hb, tenthFace_clearedY_collapsed410]
  ring

end TwelfthFaceScalars410

/-! ## Source-facing twelfth-face packet -/

section NonzeroTwelfthFace410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

theorem twelfthFace_evalV410 (h t2 a22 s22 vis w73 q54 a1 a0 : k[X])
    (lambda a eps : k) (hh : h ≠ 0) (hroot : h.eval a = 0)
    (hpow : localClearedFifthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) lambda =
      Polynomial.C eps * h ^ 17)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda)) :
    (32 : k) * q54.eval a + (40 : k) * a1.eval a * a22.eval a -
        (64 : k) * a1.eval a * s22.eval a -
        (27 : k) * a1.eval a * lambda * t2.eval a +
        (90 : k) * a1.eval a * (t2.eval a) ^ 2 =
      0 := by
  have hclr :=
    twelfthFace_clearedV_upgraded410 h t2 a22 s22 vis w73 q54 a1 a0
      lambda
  have hcof :
      (4096 : k[X]) * q54 + (23040 : k[X]) * a1 * a22 -
          (10368 : k[X]) * a1 * Polynomial.C lambda * t2 -
          (8192 : k[X]) * a1 * s22 + (14400 : k[X]) * a1 * t2 ^ 2 -
          (7168 : k[X]) * a22 * vis + (8064 : k[X]) * t2 ^ 2 * vis -
          (6144 : k[X]) * t2 * w73 +
        h * ((4608 : k[X]) * a0 * Polynomial.C lambda -
          (5184 : k[X]) * a22 ^ 2 * Polynomial.C lambda -
          (11520 : k[X]) * a22 ^ 2 * t2 +
          (16848 : k[X]) * a22 * Polynomial.C lambda * t2 ^ 2 +
          (18432 : k[X]) * a22 * s22 * t2 -
          (31200 : k[X]) * a22 * t2 ^ 3 -
          (5967 : k[X]) * Polynomial.C lambda * t2 ^ 4 -
          (9984 : k[X]) * s22 * t2 ^ 3 +
          (15912 : k[X]) * t2 ^ 5) =
        Polynomial.C eps * h := by
    apply mul_left_cancel₀ (pow_ne_zero 16 hh)
    rw [← hclr, hpow]
    ring
  have heval := congrArg (fun r : k[X] => r.eval a) hcof
  have hraw :
      (4096 : k) * q54.eval a - (8192 : k) * a1.eval a * s22.eval a -
          (7168 : k) * a22.eval a * vis.eval a +
          (23040 : k) * a22.eval a * a1.eval a -
          (6144 : k) * t2.eval a * w73.eval a -
          (10368 : k) * t2.eval a * a1.eval a * lambda +
          (8064 : k) * (t2.eval a) ^ 2 * vis.eval a +
          (14400 : k) * (t2.eval a) ^ 2 * a1.eval a =
        0 := by
    simp [hroot, eval_add, eval_mul, eval_pow, eval_sub] at heval
    linear_combination heval
  exact twelfthFace_V_nextOrder410 (q54.eval a) (a1.eval a)
    (a22.eval a) (s22.eval a) (vis.eval a) (w73.eval a) (t2.eval a)
    lambda hT hU hraw

theorem twelfthFace_evalX410 (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31 :
    k[X]) (lambda a xi : k) (hh : h ≠ 0) (hroot : h.eval a = 0)
    (hpow : localClearedSeventhDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1
        a0 (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
        (h ^ 2 * b42) (h * b31) lambda =
      Polynomial.C xi * h ^ 23)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * (a1.eval a) ^ 2) :
    (64 : k) * b31.eval a =
      (15 : k) * (a1.eval a) ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda) := by
  have hclr :=
    twelfthFace_clearedX_upgraded410 h t2 a22 s22 vis w73 q54 a1 a0 b42
      b31 lambda
  have hcof :
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
  have heval := congrArg (fun r : k[X] => r.eval a) hcof
  have hraw :
      (131072 : k) * b31.eval a - (196608 : k) * a1.eval a * w73.eval a -
          (131072 : k) * t2.eval a * b42.eval a -
          (129024 : k) * (a1.eval a) ^ 2 * lambda +
          (401408 : k) * t2.eval a * a1.eval a * vis.eval a -
          (143360 : k) * t2.eval a * (a1.eval a) ^ 2 =
        0 := by
    simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub, mul_comm,
      mul_left_comm, mul_assoc] using heval
  have hXred :=
    twelfthFace_X_nextOrder410 (b31.eval a) (a1.eval a) (t2.eval a)
      (vis.eval a) (w73.eval a) (b42.eval a) lambda hT hU hW hraw
  linear_combination hXred

set_option maxHeartbeats 8000000 in
theorem twelfthFace_evalY410 (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 :
    k[X]) (lambda a eta : k) (hh : h ≠ 0) (hroot : h.eval a = 0)
    (hpow : localClearedEighthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1
        a0 (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
        (h ^ 2 * b42) (h * b31) b2 lambda =
      Polynomial.C eta * h ^ 26)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * (a1.eval a) ^ 2)
    (hV : (4096 : k) * q54.eval a - (8192 : k) * a1.eval a * s22.eval a -
        (7168 : k) * a22.eval a * vis.eval a +
        (23040 : k) * a22.eval a * a1.eval a -
        (6144 : k) * t2.eval a * w73.eval a -
        (10368 : k) * t2.eval a * a1.eval a * lambda +
        (8064 : k) * (t2.eval a) ^ 2 * vis.eval a +
        (14400 : k) * (t2.eval a) ^ 2 * a1.eval a =
      0)
    (hX : (131072 : k) * b31.eval a -
        (196608 : k) * a1.eval a * w73.eval a -
        (131072 : k) * t2.eval a * b42.eval a -
        (129024 : k) * (a1.eval a) ^ 2 * lambda +
        (401408 : k) * t2.eval a * a1.eval a * vis.eval a -
        (143360 : k) * t2.eval a * (a1.eval a) ^ 2 =
      0) :
    (256 : k) * b2.eval a =
      (a1.eval a) ^ 2 *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * (t2.eval a) ^ 2) := by
  have hclr :=
    twelfthFace_clearedY_upgraded410 h t2 a22 s22 vis w73 q54 a1 a0 b42
      b31 b2 lambda
  have hcof :
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
  have heval := congrArg (fun r : k[X] => r.eval a) hcof
  have hraw :
      (32768 : k) * b2.eval a - (40960 : k) * a1.eval a * q54.eval a -
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
        0 := by
    simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub, mul_comm,
      mul_left_comm, mul_assoc] using heval
  have hYred :=
    twelfthFace_Y_nextOrder410 (b2.eval a) (q54.eval a) (b31.eval a)
      (a1.eval a) (a22.eval a) (s22.eval a) (vis.eval a) (w73.eval a)
      (b42.eval a) (t2.eval a) lambda hT hU hW hV hX hraw
  linear_combination hYred

end NonzeroTwelfthFace410

#print axioms twelfthCoefficientJacobianRow_410
#print axioms differentialJacobian_coeff_1_monicQuarticDecic
#print axioms twelfthFace_V_nextOrder410
#print axioms twelfthFace_X_nextOrder410
#print axioms twelfthFace_Y_nextOrder410
#print axioms twelfthFace_upgradedNextOrder410
#print axioms twelfthFace_clearedM_upgraded410
#print axioms twelfthFace_clearedV_upgraded410
#print axioms twelfthFace_clearedW_upgraded410
#print axioms twelfthFace_clearedX_upgraded410
#print axioms twelfthFace_clearedY_upgraded410
#print axioms twelfthFace_evalV410
#print axioms twelfthFace_evalX410
#print axioms twelfthFace_evalY410

end Max11DegreeRoutes
