import Grok410ScaleTwoTenthFaceScratch

/-! # Scale-two eleventh face for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the tenth-face packet supplies the degree-`3`
Jacobian row, the residual `ι` (not cleared), and the collapsed jet
`h³ ∣ p₃`, `h² ∣ p₂`, `h⁸ ∣ q₈`, `h⁶ ∣ q₇`, `h⁵ ∣ q₆`, `h³ ∣ q₅`,
`h² ∣ q₄`, `h⁸ ∣ q₉` together with `2 (q₇/h⁶)(a) = 5 p₁(a)`.

The next unused Keller coefficient is the degree-`2` Jacobian row.  After
the same quartic depression that kills `z³`, that row is
`3 U C' + 2 V B' + W A' - B V' - 2 A W' = 0`.  Unlike the degree-`3`
row, this identity does not introduce a new decic coordinate below `z⁰`,
so there is no analogue of `ι` to clear.  The residual `ι` is not claimed
to vanish.

On the upgraded collapsed jet the third through seventh cleared defects
evaluate to the identities `eleventhFace_evalV410`–`eleventhFace_evalX410`:
`(q₅/h³)(a) = 0`, `q₃(a) = 0`,
`8 (q₆/h⁵)(a) = p₁(a) (30 t₂(a) - 9 λ)`, and
`8 (q₄/h²)(a) = 15 p₁(a)²`.  No further individual vanishing of
`p₁, p₀, t₂, q₂` or of `(p₃/h³)(a)` is claimed.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The eleventh row below the leading weighted-Wronskian row for outer
degrees `(4,10)`.  Unused Jacobian coefficients of the tenth face start
at degree `2`. -/
theorem eleventhCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : K)) -
      ((p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 2) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (2 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 2 :
      Finset (ℕ × ℕ)) =
      ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  rw [hC2, hC3]
  linear_combination hcoeff

/-! ## Degree-`2` depressed Jacobian coefficient -/

section DepressedRow410Eleventh

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic quartic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`2` Jacobian coefficient is
exactly `3 U C' + 2 V B' + W A' - B V' - 2 A W'`. -/
theorem differentialJacobian_coeff_2_monicQuarticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 4 < n → f.coeff n = 0) (hf4 : f.coeff 4 = 1)
    (hf3 : f.coeff 3 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 2 =
      (3 : F) * g.coeff 3 * d (f.coeff 0) +
        (2 : F) * g.coeff 2 * d (f.coeff 1) +
        g.coeff 1 * d (f.coeff 2) -
          f.coeff 1 * d (g.coeff 2) -
          (2 : F) * f.coeff 2 * d (g.coeff 1) := by
  have hanti2 : (Finset.HasAntidiagonal.antidiagonal (2 : ℕ) :
      Finset (ℕ × ℕ)) =
      ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne01 : ((0, 2) : ℕ × ℕ) ≠ (1, 1) := by decide
  have hne02 : ((0, 2) : ℕ × ℕ) ≠ (2, 0) := by decide
  have hne12 : ((1, 1) : ℕ × ℕ) ≠ (2, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 2 =
        (3 : F) * g.coeff 3 * d (f.coeff 0) +
          (2 : F) * g.coeff 2 * d (f.coeff 1) +
          g.coeff 1 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul, hanti2,
      Finset.sum_insert (by simp [hne01, hne02]),
      Finset.sum_insert (by simp [hne12]), Finset.sum_singleton]
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0 : g.derivative.coeff 0 = g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    rw [coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder2, hder1, hder0]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 2 =
        f.coeff 1 * d (g.coeff 2) +
          (2 : F) * f.coeff 2 * d (g.coeff 1) := by
    rw [Polynomial.coeff_mul, hanti2,
      Finset.sum_insert (by simp [hne01, hne02]),
      Finset.sum_insert (by simp [hne12]), Finset.sum_singleton]
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = 0 := by
      rw [Polynomial.coeff_derivative, hf3]; simp
    rw [hder0, hder1, hder2, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv]
    ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

end DepressedRow410Eleventh

/-! ## Order-one scalar algebra on the upgraded collapsed jet -/

section EleventhFaceScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- The fifth defect at the next order on the upgraded jet forces
`(q₅/h³)(a) = 0`. -/
theorem eleventhFace_V_nextOrder410 (q53 : F)
    (hV : (4096 : F) * q53 = 0) :
    q53 = 0 := by
  have h4096 : (4096 : F) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hV).resolve_left h4096

/-- The seventh defect at the next order on the upgraded jet forces
`q₃(a) = 0`. -/
theorem eleventhFace_X_nextOrder410 (b3 : F)
    (hX : (131072 : F) * b3 = 0) :
    b3 = 0 := by
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hX).resolve_left h131072

/-- Combined next-order identities of the upgraded tenth-face jet. -/
theorem eleventhFace_collapsedNextOrder410 (v32 a1 t2 w73 b42 q53 b3
    lam : F)
    (hT : (64 : F) * v32 - (160 : F) * a1 = 0)
    (hU : (144 : F) * a1 * lam + (80 : F) * t2 * a1 -
      (224 : F) * t2 * v32 + (128 : F) * w73 = 0)
    (hV : (4096 : F) * q53 = 0)
    (hW : (5120 : F) * a1 ^ 2 - (3584 : F) * v32 * a1 +
      (2048 : F) * b42 = 0)
    (hX : (131072 : F) * b3 = 0) :
    (2 : F) * v32 = (5 : F) * a1 ∧ q53 = 0 ∧ b3 = 0 ∧
      (8 : F) * w73 = a1 * ((30 : F) * t2 - (9 : F) * lam) ∧
      (8 : F) * b42 = (15 : F) * a1 ^ 2 :=
  ⟨tenthFace_T_collapsed410 v32 a1 hT,
    eleventhFace_V_nextOrder410 q53 hV,
    eleventhFace_X_nextOrder410 b3 hX,
    tenthFace_U_collapsed410 t2 v32 w73 a1 lam hT hU,
    tenthFace_W_collapsed410 v32 a1 b42 hT hW⟩

/-! ## Upgraded substitutions of the cleared defects -/

theorem eleventhFace_clearedT_collapsed410 (h t2 a22 s22 vis a1 : F[X])
    (lambda : F) :
    localClearedThirdDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1
        (h ^ 8 * s22) (h ^ 6 * vis) lambda =
      h ^ 10 * ((64 : F[X]) * vis - (160 : F[X]) * a1 +
        h * ((72 : F[X]) * Polynomial.C lambda * a22 -
          (128 : F[X]) * t2 * s22 + (80 : F[X]) * t2 * a22 +
          (220 : F[X]) * t2 ^ 3 -
          (99 : F[X]) * Polynomial.C lambda * t2 ^ 2)) := by
  have h2 : h ^ 2 * a22 = h * (h * a22) := by ring
  have h8 : h ^ 8 * s22 = h ^ 7 * (h * s22) := by ring
  rw [h2, h8, tenthFace_clearedT_collapsed410]
  ring

theorem eleventhFace_clearedU_collapsed410 (h t2 a22 s22 vis w73 a1 a0 :
    F[X]) (lambda : F) :
    localClearedFourthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) lambda =
      h ^ 13 * ((144 : F[X]) * Polynomial.C lambda * a1 +
        (80 : F[X]) * t2 * a1 - (224 : F[X]) * t2 * vis +
        (128 : F[X]) * w73 +
        h * ((-320 : F[X]) * a0 + (400 : F[X]) * a22 ^ 2 -
          (360 : F[X]) * a22 * Polynomial.C lambda * t2 -
          (256 : F[X]) * a22 * s22 + (400 : F[X]) * a22 * t2 ^ 2 +
          (210 : F[X]) * Polynomial.C lambda * t2 ^ 3 +
          (320 : F[X]) * s22 * t2 ^ 2 - (525 : F[X]) * t2 ^ 4)) := by
  have h2 : h ^ 2 * a22 = h * (h * a22) := by ring
  have h8 : h ^ 8 * s22 = h ^ 7 * (h * s22) := by ring
  have h5 : h ^ 5 * w73 = h ^ 4 * (h * w73) := by ring
  rw [h2, h8, h5, tenthFace_clearedU_collapsed410]
  ring

set_option maxHeartbeats 4000000 in
theorem eleventhFace_clearedV_collapsed410 (h t2 a22 s22 vis w73 q53 a1
    a0 : F[X]) (lambda : F) :
    localClearedFifthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 3 * q53)
        lambda =
      h ^ 15 * ((4096 : F[X]) * q53 +
        h * ((23040 : F[X]) * a1 * a22 -
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
            (15912 : F[X]) * t2 ^ 5))) := by
  have h2 : h ^ 2 * a22 = h * (h * a22) := by ring
  have h8 : h ^ 8 * s22 = h ^ 7 * (h * s22) := by ring
  have h5 : h ^ 5 * w73 = h ^ 4 * (h * w73) := by ring
  have h3 : h ^ 3 * q53 = h ^ 2 * (h * q53) := by ring
  rw [h2, h8, h5, h3, tenthFace_clearedV_collapsed410]
  ring

set_option maxHeartbeats 8000000 in
theorem eleventhFace_clearedW_collapsed410 (h t2 a22 s22 vis w73 q53 a1
    a0 b42 : F[X]) (lambda : F) :
    localClearedSixthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 3 * q53)
        (h ^ 2 * b42) lambda =
      h ^ 18 * ((5120 : F[X]) * a1 ^ 2 - (3584 : F[X]) * vis * a1 +
        (2048 : F[X]) * b42 - (2560 : F[X]) * t2 * q53 +
        h * ((-4608 : F[X]) * a1 * a22 * Polynomial.C lambda -
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
  have h2 : h ^ 2 * a22 = h * (h * a22) := by ring
  have h8 : h ^ 8 * s22 = h ^ 7 * (h * s22) := by ring
  have h5 : h ^ 5 * w73 = h ^ 4 * (h * w73) := by ring
  have h3 : h ^ 3 * q53 = h ^ 2 * (h * q53) := by ring
  rw [h2, h8, h5, h3, tenthFace_clearedW_collapsed410]
  ring

set_option maxHeartbeats 16000000 in
theorem eleventhFace_clearedX_collapsed410 (h t2 a22 s22 vis w73 q53 a1
    a0 b42 b3 : F[X]) (lambda : F) :
    localClearedSeventhDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 3 * q53)
        (h ^ 2 * b42) b3 lambda =
      h ^ 20 * ((131072 : F[X]) * b3 +
        h * ((-129024 : F[X]) * a1 ^ 2 * Polynomial.C lambda -
          (143360 : F[X]) * a1 ^ 2 * t2 +
          (401408 : F[X]) * a1 * t2 * vis -
          (196608 : F[X]) * a1 * w73 - (163840 : F[X]) * a22 * q53 -
          (131072 : F[X]) * b42 * t2 + (143360 : F[X]) * q53 * t2 ^ 2 +
          h * ((573440 : F[X]) * a0 * a1 - (229376 : F[X]) * a0 * vis -
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
              (665280 : F[X]) * a22 ^ 2 * Polynomial.C lambda *
                t2 ^ 2 -
              (630784 : F[X]) * a22 ^ 2 * s22 * t2 +
              (985600 : F[X]) * a22 ^ 2 * t2 ^ 3 +
              (526680 : F[X]) * a22 * Polynomial.C lambda * t2 ^ 4 +
              (788480 : F[X]) * a22 * s22 * t2 ^ 3 -
              (1287440 : F[X]) * a22 * t2 ^ 5 -
              (100947 : F[X]) * Polynomial.C lambda * t2 ^ 6 -
              (187264 : F[X]) * s22 * t2 ^ 5 +
              (288420 : F[X]) * t2 ^ 7)))) := by
  simp only [localClearedSeventhDefect410]
  ring

end EleventhFaceScalars410

/-! ## Source-facing eleventh-face packet -/

section NonzeroEleventhFace410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

theorem eleventhFace_evalV410 (h t2 a22 s22 vis w73 q53 a1 a0 : k[X])
    (lambda a eps : k) (hh : h ≠ 0) (hroot : h.eval a = 0)
    (hpow : localClearedFifthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 3 * q53) lambda =
      Polynomial.C eps * h ^ 17) :
    q53.eval a = 0 := by
  have hclr :=
    eleventhFace_clearedV_collapsed410 h t2 a22 s22 vis w73 q53 a1 a0
      lambda
  have hcof :
      (4096 : k[X]) * q53 +
          h * ((23040 : k[X]) * a1 * a22 -
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
              (15912 : k[X]) * t2 ^ 5)) =
        Polynomial.C eps * h ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 15 hh)
    rw [← hclr, hpow]
    ring
  have heval := congrArg (fun r : k[X] => r.eval a) hcof
  have h4096 : (4096 : k) ≠ 0 := by norm_num
  have : (4096 : k) * q53.eval a = 0 := by
    simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub] using heval
  exact (mul_eq_zero.mp this).resolve_left h4096

theorem eleventhFace_evalU410 (h t2 a22 s22 vis w73 a1 a0 : k[X])
    (lambda a delta : k) (hh : h ≠ 0) (hroot : h.eval a = 0)
    (hpow : localClearedFourthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) lambda =
      Polynomial.C delta * h ^ 14)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0) :
    (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda) := by
  have hclr :=
    eleventhFace_clearedU_collapsed410 h t2 a22 s22 vis w73 a1 a0 lambda
  have hcof :
      (144 : k[X]) * Polynomial.C lambda * a1 +
          (80 : k[X]) * t2 * a1 - (224 : k[X]) * t2 * vis +
        (128 : k[X]) * w73 +
        h * ((-320 : k[X]) * a0 + (400 : k[X]) * a22 ^ 2 -
          (360 : k[X]) * a22 * Polynomial.C lambda * t2 -
          (256 : k[X]) * a22 * s22 + (400 : k[X]) * a22 * t2 ^ 2 +
          (210 : k[X]) * Polynomial.C lambda * t2 ^ 3 +
          (320 : k[X]) * s22 * t2 ^ 2 - (525 : k[X]) * t2 ^ 4) =
        Polynomial.C delta * h := by
    apply mul_left_cancel₀ (pow_ne_zero 13 hh)
    rw [← hclr, hpow]
    ring
  have heval := congrArg (fun r : k[X] => r.eval a) hcof
  have hUeval :
      (144 : k) * a1.eval a * lambda +
          (80 : k) * t2.eval a * a1.eval a -
        (224 : k) * t2.eval a * vis.eval a +
          (128 : k) * w73.eval a = 0 := by
    simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub, mul_comm,
      mul_left_comm, mul_assoc] using heval
  exact tenthFace_U_collapsed410 (t2.eval a) (vis.eval a) (w73.eval a)
    (a1.eval a) lambda hT hUeval

theorem eleventhFace_evalW410 (h t2 a22 s22 vis w73 q53 a1 a0 b42 :
    k[X]) (lambda a zeta : k) (hh : h ≠ 0) (hroot : h.eval a = 0)
    (hpow : localClearedSixthDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0
        (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 3 * q53)
        (h ^ 2 * b42) lambda =
      Polynomial.C zeta * h ^ 20)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hq53 : q53.eval a = 0) :
    (8 : k) * b42.eval a = (15 : k) * (a1.eval a) ^ 2 := by
  have hclr :=
    eleventhFace_clearedW_collapsed410 h t2 a22 s22 vis w73 q53 a1 a0
      b42 lambda
  have hcof :
      (5120 : k[X]) * a1 ^ 2 - (3584 : k[X]) * vis * a1 +
          (2048 : k[X]) * b42 - (2560 : k[X]) * t2 * q53 +
        h * ((-4608 : k[X]) * a1 * a22 * Polynomial.C lambda -
          (7680 : k[X]) * a1 * a22 * t2 +
          (6912 : k[X]) * a1 * Polynomial.C lambda * t2 ^ 2 +
          (8192 : k[X]) * a1 * s22 * t2 - (14080 : k[X]) * a1 * t2 ^ 3 +
          (7168 : k[X]) * a22 * t2 * vis - (3072 : k[X]) * a22 * w73 -
          (3584 : k[X]) * t2 ^ 3 * vis + (3072 : k[X]) * t2 ^ 2 * w73 +
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
        Polynomial.C zeta * h ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 18 hh)
    rw [← hclr, hpow]
    ring
  have heval := congrArg (fun r : k[X] => r.eval a) hcof
  have hraw :
      (5120 : k) * (a1.eval a) ^ 2 -
          (3584 : k) * vis.eval a * a1.eval a +
        (2048 : k) * b42.eval a -
          (2560 : k) * t2.eval a * q53.eval a = 0 := by
    simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub] using heval
  have hWeval :
      (5120 : k) * (a1.eval a) ^ 2 -
          (3584 : k) * vis.eval a * a1.eval a +
        (2048 : k) * b42.eval a = 0 := by
    simpa [hq53, mul_zero, sub_zero] using hraw
  exact tenthFace_W_collapsed410 (vis.eval a) (a1.eval a) (b42.eval a)
    hT hWeval

theorem eleventhFace_evalX410 (h t2 a22 s22 vis w73 q53 a1 a0 b42 b3 :
    k[X]) (lambda a xi : k) (hh : h ≠ 0) (hroot : h.eval a = 0)
    (hpow : localClearedSeventhDefect410 h (h ^ 3 * t2) (h ^ 2 * a22) a1
        a0 (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 3 * q53)
        (h ^ 2 * b42) b3 lambda =
      Polynomial.C xi * h ^ 23) :
    b3.eval a = 0 := by
  have hclr :=
    eleventhFace_clearedX_collapsed410 h t2 a22 s22 vis w73 q53 a1 a0
      b42 b3 lambda
  have hcof :
      (131072 : k[X]) * b3 +
          h * ((-129024 : k[X]) * a1 ^ 2 * Polynomial.C lambda -
            (143360 : k[X]) * a1 ^ 2 * t2 +
            (401408 : k[X]) * a1 * t2 * vis -
            (196608 : k[X]) * a1 * w73 - (163840 : k[X]) * a22 * q53 -
            (131072 : k[X]) * b42 * t2 +
            (143360 : k[X]) * q53 * t2 ^ 2 +
            h * ((573440 : k[X]) * a0 * a1 - (229376 : k[X]) * a0 * vis -
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
                (288420 : k[X]) * t2 ^ 7))) =
        Polynomial.C xi * h ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 20 hh)
    rw [← hclr, hpow]
    ring
  have heval := congrArg (fun r : k[X] => r.eval a) hcof
  have h131072 : (131072 : k) ≠ 0 := by norm_num
  have : (131072 : k) * b3.eval a = 0 := by
    simpa [hroot, eval_add, eval_mul, eval_pow, eval_sub] using heval
  exact (mul_eq_zero.mp this).resolve_left h131072

end NonzeroEleventhFace410

#print axioms eleventhCoefficientJacobianRow_410
#print axioms differentialJacobian_coeff_2_monicQuarticDecic
#print axioms eleventhFace_V_nextOrder410
#print axioms eleventhFace_X_nextOrder410
#print axioms eleventhFace_collapsedNextOrder410
#print axioms eleventhFace_clearedT_collapsed410
#print axioms eleventhFace_clearedU_collapsed410
#print axioms eleventhFace_clearedV_collapsed410
#print axioms eleventhFace_clearedW_collapsed410
#print axioms eleventhFace_clearedX_collapsed410
#print axioms eleventhFace_evalV410
#print axioms eleventhFace_evalU410
#print axioms eleventhFace_evalW410
#print axioms eleventhFace_evalX410

end Max11DegreeRoutes
