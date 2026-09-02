import Grok810ScaleTwoTenthFaceScratch

/-! # Scale-two eleventh face for the normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the tenth-face packet supplies the degree-`7`
Jacobian row and the two-component jet `v₀ = h v₁`, `s₀ = h s₁`,
`u₀ = h u₁`, `w₀ = h w₁`, `q₆ = h² b₆₂` together with `h⁸ ∣ q₉`.  On
the left the source-facing loads are `Gred, Vred, Wred, Xred`; on the
right, `t₀ = 0`, `4 s₁ = 5 v₁`, `4 w₁ = 5 u₁`,
`40 a₄ - 32 b₆₂ + 5 v₁² = 0`, `16 b₅ = 5 u₁ v₁`,
`16 b₆₂ v₁ + 10 u₁² - 5 v₁³ = 0`, and the alternative
`u₁ (5 v₁² - 8 b₆₂) = 0`.

The next unused Keller coefficient is the degree-`6` Jacobian row.  After
the same octic depression that kills `z⁷`, that row is
`7 Q G' + 6 R F' + 5 S E' + 4 T D' + 3 U C' + 2 V B' + W A'
- F Q' - 2 E R' - 3 D S' - 4 C T' - 5 B U' - 6 A V' - 7 G W' = 0`.
Clearing the corresponding first integral against the remaining decic
coordinate produces a defect larger than the remaining exact jet, so
this file isolates that Jacobian identity and the strongest exact
source-facing refinement of both tenth-face siblings.

The right alternative splits the right component.  On `u₁(a) = 0` the
tenth-face laws upgrade the jet to `h³ ∣ p₅`, `h⁵ ∣ q₇`, `h ∣ q₅`,
and the third and fifth defects at the next order force
`32 w₂ - 40 u₂ = v₁ (10 t₁ - 9 λ)` and
`2560 b₅₁ + 576 λ b₆₂ - 640 t₁ b₆₂ - 45 λ v₁² + 400 t₁ v₁²
- 800 u₂ v₁ = 0` at the root of `h`.  On the complementary factor the
same alternative solves `a₄`, `b₆₂`, and `u₁` exactly by
`8 a₄ = 3 v₁²`, `8 b₆₂ = 5 v₁²`, and `2 u₁² + v₁³ = 0`.  The left
component is retained with its tenth-face loads.  Neither factor is
closed further: no individual vanishing of `v₁, a₄, t₁, p₃, q₄` (nor of
the left loads `t₀, a₄, b₅`) is claimed, and the aligned face `N = 0`
remains open.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Literal next Keller coefficient -/

/-- The eleventh row below the leading weighted-Wronskian row for outer
degrees `(8,10)`.  Unused Jacobian coefficients of the tenth face start
at degree `6`. -/
theorem eleventhCoefficientJacobianRow_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * q.coeff 1 +
        (p.coeff 5).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 4).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 3).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 2).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 1).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 0).derivative * (q.coeff 7 * Polynomial.C (7 : K)) -
      ((p.coeff 7 * Polynomial.C (7 : K)) * (q.coeff 0).derivative +
        (p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 1).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 2).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 3).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 4).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 5).derivative +
        p.coeff 1 * (q.coeff 6).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 6) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (6 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 6 :
      Finset (ℕ × ℕ)) =
      ({(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1),
        (6, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  rw [hC7, hC6, hC5, hC4, hC3, hC2]
  linear_combination hcoeff

/-! ## Scalar algebra of the tenth-face right alternative -/

section EleventhFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

/-- On the complementary factor of the tenth-face alternative, `b₆₂`
is exact. -/
theorem eleventhFace_comp_b62_810 (v1 u1 b62 : F)
    (hu1 : u1 ≠ 0)
    (hX : u1 * ((5 : F) * v1 ^ 2 - (8 : F) * b62) = 0) :
    (5 : F) * v1 ^ 2 - (8 : F) * b62 = 0 :=
  (mul_eq_zero.mp hX).resolve_left hu1

/-- The tenth-face load together with the complementary factor solves
`a₄`. -/
theorem eleventhFace_comp_a4_810 (v1 a4 b62 : F)
    (hG : (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 = 0)
    (hB : (5 : F) * v1 ^ 2 - (8 : F) * b62 = 0) :
    (8 : F) * a4 - (3 : F) * v1 ^ 2 = 0 := by
  have h5 : (5 : F) ≠ 0 := by norm_num
  have hid :
      (5 : F) * ((8 : F) * a4 - (3 : F) * v1 ^ 2) =
        (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 -
          (4 : F) * ((5 : F) * v1 ^ 2 - (8 : F) * b62) := by
    ring
  have hcomb :
      (5 : F) * ((8 : F) * a4 - (3 : F) * v1 ^ 2) = 0 := by
    rw [hid]
    linear_combination hG - (4 : F) * hB
  exact (mul_eq_zero.mp hcomb).resolve_left h5

/-- The tenth-face sixth defect together with the complementary factor
solves `u₁`. -/
theorem eleventhFace_comp_u1_810 (v1 u1 b62 : F)
    (hW : (16 : F) * b62 * v1 + (10 : F) * u1 ^ 2 - (5 : F) * v1 ^ 3 =
      0)
    (hB : (5 : F) * v1 ^ 2 - (8 : F) * b62 = 0) :
    (2 : F) * u1 ^ 2 + v1 ^ 3 = 0 := by
  have h5 : (5 : F) ≠ 0 := by norm_num
  have hid :
      (5 : F) * ((2 : F) * u1 ^ 2 + v1 ^ 3) =
        (16 : F) * b62 * v1 + (10 : F) * u1 ^ 2 - (5 : F) * v1 ^ 3 +
          (2 : F) * v1 * ((5 : F) * v1 ^ 2 - (8 : F) * b62) := by
    ring
  have hcomb : (5 : F) * ((2 : F) * u1 ^ 2 + v1 ^ 3) = 0 := by
    rw [hid]
    linear_combination hW + (2 : F) * v1 * hB
  exact (mul_eq_zero.mp hcomb).resolve_left h5

/-- Combined complementary identities of the tenth-face alternative. -/
theorem eleventhFace_comp_nextOrder810 (v1 u1 a4 b62 : F)
    (hu1 : u1 ≠ 0)
    (hG : (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 = 0)
    (hW : (16 : F) * b62 * v1 + (10 : F) * u1 ^ 2 - (5 : F) * v1 ^ 3 =
      0)
    (hX : u1 * ((5 : F) * v1 ^ 2 - (8 : F) * b62) = 0) :
    (5 : F) * v1 ^ 2 - (8 : F) * b62 = 0 ∧
      (8 : F) * a4 - (3 : F) * v1 ^ 2 = 0 ∧
      (2 : F) * u1 ^ 2 + v1 ^ 3 = 0 := by
  have hB := eleventhFace_comp_b62_810 v1 u1 b62 hu1 hX
  exact ⟨hB, eleventhFace_comp_a4_810 v1 a4 b62 hG hB,
    eleventhFace_comp_u1_810 v1 u1 b62 hW hB⟩

/-- The third defect at the next order on the `u₁ = 0` jet is
`32 w₂ - 40 u₂ = v₁ (10 t₁ - 9 λ)`. -/
theorem eleventhFace_zeroU1_T_nextOrder810 (v1 s1 t1 u2 w2 : F)
    (lambda : F)
    (hM : (32 : F) * s1 - (40 : F) * v1 = 0)
    (hT : (144 : F) * lambda * v1 - (512 : F) * s1 * t1 +
        (480 : F) * t1 * v1 - (640 : F) * u2 + (512 : F) * w2 = 0) :
    (32 : F) * w2 - (40 : F) * u2 - (10 : F) * t1 * v1 +
      (9 : F) * lambda * v1 = 0 := by
  have h16 : (16 : F) ≠ 0 := by norm_num
  have hid :
      (16 : F) * ((32 : F) * w2 - (40 : F) * u2 -
          (10 : F) * t1 * v1 + (9 : F) * lambda * v1) =
        (144 : F) * lambda * v1 - (512 : F) * s1 * t1 +
          (480 : F) * t1 * v1 - (640 : F) * u2 + (512 : F) * w2 +
          (16 : F) * t1 * ((32 : F) * s1 - (40 : F) * v1) := by
    ring
  have hcomb :
      (16 : F) * ((32 : F) * w2 - (40 : F) * u2 -
          (10 : F) * t1 * v1 + (9 : F) * lambda * v1) = 0 := by
    rw [hid]
    linear_combination hT + (16 : F) * t1 * hM
  exact (mul_eq_zero.mp hcomb).resolve_left h16

set_option maxHeartbeats 4000000 in
/-- The fifth defect at the next order on the `u₁ = 0` jet determines
`(q₅ / h)(a)`. -/
theorem eleventhFace_zeroU1_V_nextOrder810 (v1 s1 t1 u2 w2 a4 b62 b51 :
    F) (lambda : F)
    (hM : (32 : F) * s1 - (40 : F) * v1 = 0)
    (hG : (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 = 0)
    (hT : (32 : F) * w2 - (40 : F) * u2 - (10 : F) * t1 * v1 +
      (9 : F) * lambda * v1 = 0)
    (hV : (36864 : F) * a4 * lambda + (81920 : F) * a4 * t1 +
        (131072 : F) * b51 - (98304 : F) * b62 * t1 -
        (29952 : F) * lambda * v1 ^ 2 +
        (212992 : F) * s1 * t1 * v1 - (131072 : F) * s1 * u2 -
        (199680 : F) * t1 * v1 ^ 2 + (266240 : F) * u2 * v1 -
        (114688 : F) * v1 * w2 = 0) :
    (2560 : F) * b51 + (576 : F) * lambda * b62 -
        (640 : F) * t1 * b62 - (45 : F) * lambda * v1 ^ 2 +
      (400 : F) * t1 * v1 ^ 2 - (800 : F) * u2 * v1 = 0 := by
  have h256 : (256 : F) ≠ 0 := by norm_num
  have hid :
      (256 : F) * ((2560 : F) * b51 + (576 : F) * lambda * b62 -
          (640 : F) * t1 * b62 - (45 : F) * lambda * v1 ^ 2 +
          (400 : F) * t1 * v1 ^ 2 - (800 : F) * u2 * v1) =
        (5 : F) * ((36864 : F) * a4 * lambda + (81920 : F) * a4 * t1 +
            (131072 : F) * b51 - (98304 : F) * b62 * t1 -
            (29952 : F) * lambda * v1 ^ 2 +
            (212992 : F) * s1 * t1 * v1 - (131072 : F) * s1 * u2 -
            (199680 : F) * t1 * v1 ^ 2 + (266240 : F) * u2 * v1 -
            (114688 : F) * v1 * w2) -
          (33280 : F) * t1 * v1 *
            ((32 : F) * s1 - (40 : F) * v1) +
          (20480 : F) * u2 * ((32 : F) * s1 - (40 : F) * v1) -
          (4608 : F) * lambda *
            ((40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2) -
          (10240 : F) * t1 *
            ((40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2) +
          (17920 : F) * v1 *
            ((32 : F) * w2 - (40 : F) * u2 - (10 : F) * t1 * v1 +
              (9 : F) * lambda * v1) := by
    ring
  have hcomb :
      (256 : F) * ((2560 : F) * b51 + (576 : F) * lambda * b62 -
          (640 : F) * t1 * b62 - (45 : F) * lambda * v1 ^ 2 +
          (400 : F) * t1 * v1 ^ 2 - (800 : F) * u2 * v1) = 0 := by
    rw [hid]
    linear_combination (5 : F) * hV - (33280 : F) * t1 * v1 * hM +
      (20480 : F) * u2 * hM - (4608 : F) * lambda * hG -
      (10240 : F) * t1 * hG + (17920 : F) * v1 * hT
  exact (mul_eq_zero.mp hcomb).resolve_left h256

/-- Combined next-order identities of the `u₁ = 0` jet. -/
theorem eleventhFace_zeroU1_nextOrder810 (v1 s1 t1 u2 w2 a4 b62 b51 : F)
    (lambda : F)
    (hM : (32 : F) * s1 - (40 : F) * v1 = 0)
    (hG : (40 : F) * a4 - (32 : F) * b62 + (5 : F) * v1 ^ 2 = 0)
    (hT : (144 : F) * lambda * v1 - (512 : F) * s1 * t1 +
        (480 : F) * t1 * v1 - (640 : F) * u2 + (512 : F) * w2 = 0)
    (hV : (36864 : F) * a4 * lambda + (81920 : F) * a4 * t1 +
        (131072 : F) * b51 - (98304 : F) * b62 * t1 -
        (29952 : F) * lambda * v1 ^ 2 +
        (212992 : F) * s1 * t1 * v1 - (131072 : F) * s1 * u2 -
        (199680 : F) * t1 * v1 ^ 2 + (266240 : F) * u2 * v1 -
        (114688 : F) * v1 * w2 = 0) :
    (32 : F) * w2 - (40 : F) * u2 - (10 : F) * t1 * v1 +
        (9 : F) * lambda * v1 = 0 ∧
      (2560 : F) * b51 + (576 : F) * lambda * b62 -
          (640 : F) * t1 * b62 - (45 : F) * lambda * v1 ^ 2 +
        (400 : F) * t1 * v1 ^ 2 - (800 : F) * u2 * v1 = 0 := by
  have hTred :=
    eleventhFace_zeroU1_T_nextOrder810 v1 s1 t1 u2 w2 lambda hM hT
  exact ⟨hTred,
    eleventhFace_zeroU1_V_nextOrder810 v1 s1 t1 u2 w2 a4 b62 b51 lambda
      hM hG hTred hV⟩

/-! ## Extra-`h` substitutions of the sixth-jet parentheticals on
`u₁ = 0` -/

/-- Cofactor of `h²` in the sixth-jet third defect after the extra
right vanishing `t₀ = h t₁`, `u₁ = h u₂`, `w₁ = h w₂`. -/
def eleventhFace_Tcof810 (h t1 v1 s1 w2 u2 : F[X]) (lambda : F) :
    F[X] :=
  (144 : F[X]) * Polynomial.C lambda * v1 - (512 : F[X]) * s1 * t1 +
    (480 : F[X]) * t1 * v1 - (640 : F[X]) * u2 + (512 : F[X]) * w2 +
    ((100 : F[X]) * t1 ^ 3 -
        (135 : F[X]) * Polynomial.C lambda * t1 ^ 2) * h ^ 2

/-- Cofactor of `h³` in the sixth-jet fifth defect after the extra
right vanishing `t₀ = h t₁`, `u₁ = h u₂`, `w₁ = h w₂`, `b₅ = h b₅₁`. -/
def eleventhFace_Vcof810
    (h t1 v1 s1 w2 u2 a4 a3 b62 b51 : F[X]) (lambda : F) : F[X] :=
  (36864 : F[X]) * a4 * Polynomial.C lambda + (81920 : F[X]) * a4 * t1 +
    (131072 : F[X]) * b51 - (98304 : F[X]) * b62 * t1 -
    (29952 : F[X]) * Polynomial.C lambda * v1 ^ 2 +
    (212992 : F[X]) * s1 * t1 * v1 - (131072 : F[X]) * s1 * u2 -
    (199680 : F[X]) * t1 * v1 ^ 2 + (266240 : F[X]) * u2 * v1 -
    (114688 : F[X]) * v1 * w2 +
    (-(163840 : F[X]) * a3) * h +
    ((78624 : F[X]) * Polynomial.C lambda * t1 ^ 2 * v1 -
        (59904 : F[X]) * Polynomial.C lambda * t1 * u2 -
      (93184 : F[X]) * s1 * t1 ^ 3 + (29120 : F[X]) * t1 ^ 3 * v1 -
        (49920 : F[X]) * t1 ^ 2 * u2 +
      (93184 : F[X]) * t1 ^ 2 * w2) * h ^ 2 +
    (-(23751 : F[X]) * Polynomial.C lambda * t1 ^ 4 +
        (21112 : F[X]) * t1 ^ 5) * h ^ 4

theorem eleventhFace_third_zeroU1_mul_h
    (h t1 v1 s1 w2 u2 : F[X]) (lambda : F) :
    thirdJetParen810_sixth h (h * t1) (h * v1) (h * s1) (h ^ 2 * w2)
        (h ^ 2 * u2) lambda =
      h ^ 2 * eleventhFace_Tcof810 h t1 v1 s1 w2 u2 lambda := by
  simp only [thirdJetParen810_sixth, eleventhFace_Tcof810]
  ring

set_option maxHeartbeats 8000000 in
theorem eleventhFace_fifth_zeroU1_mul_h
    (h t1 v1 s1 w2 u2 a4 a3 b62 b51 : F[X]) (lambda : F) :
    fifthJetParen810_sixth h (h * t1) (h * v1) (h * s1) (h ^ 2 * w2)
        (h ^ 2 * u2) a4 a3 (h ^ 2 * b62) (h * b51) lambda =
      h ^ 3 * eleventhFace_Vcof810 h t1 v1 s1 w2 u2 a4 a3 b62 b51
        lambda := by
  simp only [fifthJetParen810_sixth, eleventhFace_Vcof810]
  ring

theorem eval_eleventhFace_Tcof810
    (h t1 v1 s1 w2 u2 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (eleventhFace_Tcof810 h t1 v1 s1 w2 u2 lambda) =
      (144 : F) * lambda * Polynomial.eval root v1 -
        (512 : F) * Polynomial.eval root s1 * Polynomial.eval root t1 +
        (480 : F) * Polynomial.eval root t1 *
          Polynomial.eval root v1 -
        (640 : F) * Polynomial.eval root u2 +
        (512 : F) * Polynomial.eval root w2 := by
  simp [eleventhFace_Tcof810, hroot]

theorem eval_eleventhFace_Vcof810
    (h t1 v1 s1 w2 u2 a4 a3 b62 b51 : F[X]) (lambda : F) (root : F)
    (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (eleventhFace_Vcof810 h t1 v1 s1 w2 u2 a4 a3 b62 b51 lambda) =
      (36864 : F) * Polynomial.eval root a4 * lambda +
        (81920 : F) * Polynomial.eval root a4 *
          Polynomial.eval root t1 +
        (131072 : F) * Polynomial.eval root b51 -
        (98304 : F) * Polynomial.eval root b62 *
          Polynomial.eval root t1 -
        (29952 : F) * lambda * (Polynomial.eval root v1) ^ 2 +
        (212992 : F) * Polynomial.eval root s1 *
          Polynomial.eval root t1 * Polynomial.eval root v1 -
        (131072 : F) * Polynomial.eval root s1 *
          Polynomial.eval root u2 -
        (199680 : F) * Polynomial.eval root t1 *
          (Polynomial.eval root v1) ^ 2 +
        (266240 : F) * Polynomial.eval root u2 *
          Polynomial.eval root v1 -
        (114688 : F) * Polynomial.eval root v1 *
          Polynomial.eval root w2 := by
  simp [eleventhFace_Vcof810, hroot]

end EleventhFaceScalars810

/-! ## Source-facing eleventh-face packet -/

section NonzeroEleventhFace810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local eleventh-face packet: the tenth-face split together
with the refinement of both right-alternative siblings. -/
theorem nonzeroFace810_linearRoot_eleventhInitialPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : k[X],
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧ h0 ^ 2 ∣ q.coeff 6 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : k) * s1.eval a - (40 : k) * v1.eval a =
              (5 : k) * (t0.eval a) ^ 2 ∧
            (128 : k) * w1.eval a - (160 : k) * u1.eval a -
                (40 : k) * t0.eval a * v1.eval a +
              (5 : k) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Wred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Xred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s1.eval a = (5 : k) * v1.eval a ∧
            (4 : k) * w1.eval a = (5 : k) * u1.eval a ∧
            (40 : k) * (p.coeff 4).eval a - (32 : k) * b62.eval a +
              (5 : k) * (v1.eval a) ^ 2 = 0 ∧
            (16 : k) * (q.coeff 5).eval a =
              (5 : k) * u1.eval a * v1.eval a ∧
            (16 : k) * b62.eval a * v1.eval a +
                (10 : k) * (u1.eval a) ^ 2 -
              (5 : k) * (v1.eval a) ^ 3 = 0 ∧
            u1.eval a *
                ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a) =
              0 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 4 ∣ p.coeff 6 ∧
            h0 ^ 6 ∣ q.coeff 8 ∧
            ((u1.eval a = 0 ∧
                ∃ (t1 u2 w2 b51 : k[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧
                    (32 : k) * w2.eval a - (40 : k) * u2.eval a -
                        (10 : k) * t1.eval a * v1.eval a +
                      (9 : k) * lambda * v1.eval a = 0 ∧
                    (2560 : k) * b51.eval a +
                        (576 : k) * lambda * b62.eval a -
                        (640 : k) * t1.eval a * b62.eval a -
                        (45 : k) * lambda * (v1.eval a) ^ 2 +
                        (400 : k) * t1.eval a * (v1.eval a) ^ 2 -
                        (800 : k) * u2.eval a * v1.eval a = 0) ∨
              ((5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a = 0 ∧
                (8 : k) * (p.coeff 4).eval a -
                    (3 : k) * (v1.eval a) ^ 2 = 0 ∧
                (2 : k) * (u1.eval a) ^ 2 + (v1.eval a) ^ 3 = 0)))) :=
    by
  obtain ⟨gamma, hTrel⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨eps, hVrel⟩ :=
    nonzeroFace810_fifthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
    hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2, hsplit⟩ :=
    nonzeroFace810_linearRoot_tenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  rcases hsplit with hleft | hright
  · exact ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2, Or.inl hleft⟩
  · obtain ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hs1rel, hw1rel, ha4,
      hb5, hWspec, hXspec, hp7_7, hp5_2, hq7_4, hp6_4, hq8_6⟩ := hright
    refine ⟨t0, v0, u0, s0, w0, v1, s1, u1, w1, b62, ht0, hv0, hu0, hs0,
      hw0, hv1, hs1, hu1, hw1, hb62, hq9d, hq6_2,
      Or.inr ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hs1rel, hw1rel, ha4,
        hb5, hWspec, hXspec, hp7_7, hp5_2, hq7_4, hp6_4, hq8_6, ?_⟩⟩
    rcases mul_eq_zero.mp hXspec with hu1z | hcomp
    · have hw1z : w1.eval a = 0 := by
        have h4 : (4 : k) ≠ 0 := by norm_num
        have : (4 : k) * w1.eval a = 0 := by
          simpa [hu1z] using hw1rel
        exact (mul_eq_zero.mp this).resolve_left h4
      have hb5z : (q.coeff 5).eval a = 0 := by
        have h16 : (16 : k) ≠ 0 := by norm_num
        have : (16 : k) * (q.coeff 5).eval a = 0 := by
          simpa [hu1z] using hb5
        exact (mul_eq_zero.mp this).resolve_left h16
      obtain ⟨t1, ht1⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0 t0 a hh0degree
          hroot ht0z
      obtain ⟨u2, hu2⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0 u1 a hh0degree
          hroot hu1z
      obtain ⟨w2, hw2⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0 w1 a hh0degree
          hroot hw1z
      obtain ⟨b51, hb51⟩ :=
        linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 5) a
          hh0degree hroot hb5z
      have hu0' : u0 = h0 ^ 2 * u2 := by
        rw [hu1, hu2]
        ring
      have hw0' : w0 = h0 ^ 2 * w2 := by
        rw [hw1, hw2]
        ring
      have hp5_3 : p.coeff 5 = h0 ^ 3 * u2 := by
        rw [hu0, hu0']
        ring
      have hq7_5 : q.coeff 7 = h0 ^ 5 * w2 := by
        rw [hw0, hw0']
        ring
      have hMsubst :
          localClearedThirdDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
              (h0 * u0) (h0 ^ 5 * s0) (h0 ^ 3 * w0) lambda =
            localClearedThirdDefect810 h0 (p.coeff 7) (p.coeff 6)
              (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda := by
        simp only [ht0, hv0, hu0, hs0, hw0]
      have hVsubst :
          localClearedFifthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
              (h0 * u0) (p.coeff 4) (p.coeff 3) (h0 ^ 5 * s0)
              (h0 ^ 3 * w0) (h0 ^ 2 * b62) (q.coeff 5) lambda =
            localClearedFifthDefect810 h0 (p.coeff 7) (p.coeff 6)
              (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8)
              (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda := by
        simp only [ht0, hv0, hu0, hs0, hw0, hb62]
      have hTparen :
          thirdJetParen810_sixth h0 t0 v0 s0 w0 u0 lambda =
            Polynomial.C gamma * h0 ^ 4 :=
        thirdJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0 lambda
          gamma hh0 (hMsubst.trans hTrel)
      have hVparen :
          fifthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
              (p.coeff 3) (h0 ^ 2 * b62) (q.coeff 5) lambda =
            Polynomial.C eps * h0 ^ 7 :=
        fifthJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0
          (p.coeff 4) (p.coeff 3) (h0 ^ 2 * b62) (q.coeff 5) lambda
          eps hh0 (hVsubst.trans hVrel)
      have hTleft :
          thirdJetParen810_sixth h0 t0 v0 s0 w0 u0 lambda =
            h0 ^ 2 * eleventhFace_Tcof810 h0 t1 v1 s1 w2 u2
              lambda := by
        simpa [ht1, hv1, hs1, hw0', hu0'] using
          eleventhFace_third_zeroU1_mul_h h0 t1 v1 s1 w2 u2 lambda
      have hVleft :
          fifthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
              (p.coeff 3) (h0 ^ 2 * b62) (q.coeff 5) lambda =
            h0 ^ 3 * eleventhFace_Vcof810 h0 t1 v1 s1 w2 u2
              (p.coeff 4) (p.coeff 3) b62 b51 lambda := by
        simpa [ht1, hv1, hs1, hw0', hu0', hb51] using
          eleventhFace_fifth_zeroU1_mul_h h0 t1 v1 s1 w2 u2
            (p.coeff 4) (p.coeff 3) b62 b51 lambda
      have hTcof :
          eleventhFace_Tcof810 h0 t1 v1 s1 w2 u2 lambda =
            Polynomial.C gamma * h0 ^ 2 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
        have hscale : Polynomial.C gamma * h0 ^ 4 =
            h0 ^ 2 * (Polynomial.C gamma * h0 ^ 2) := by ring
        rw [← hTleft, hTparen, hscale]
      have hVcof :
          eleventhFace_Vcof810 h0 t1 v1 s1 w2 u2 (p.coeff 4)
              (p.coeff 3) b62 b51 lambda =
            Polynomial.C eps * h0 ^ 4 := by
        apply mul_left_cancel₀ (pow_ne_zero 3 hh0)
        have hscale : Polynomial.C eps * h0 ^ 7 =
            h0 ^ 3 * (Polynomial.C eps * h0 ^ 4) := by ring
        rw [← hVleft, hVparen, hscale]
      have hTeval :
          (144 : k) * lambda * v1.eval a -
              (512 : k) * s1.eval a * t1.eval a +
              (480 : k) * t1.eval a * v1.eval a -
              (640 : k) * u2.eval a + (512 : k) * w2.eval a = 0 := by
        have hleft :=
          eval_eleventhFace_Tcof810 h0 t1 v1 s1 w2 u2 lambda a hroot
        have hzero :
            Polynomial.eval a
                (eleventhFace_Tcof810 h0 t1 v1 s1 w2 u2 lambda) =
              0 := by
          rw [hTcof]
          simp [hroot]
        rw [← hleft]
        exact hzero
      have hVeval :
          (36864 : k) * (p.coeff 4).eval a * lambda +
              (81920 : k) * (p.coeff 4).eval a * t1.eval a +
              (131072 : k) * b51.eval a -
              (98304 : k) * b62.eval a * t1.eval a -
              (29952 : k) * lambda * (v1.eval a) ^ 2 +
              (212992 : k) * s1.eval a * t1.eval a * v1.eval a -
              (131072 : k) * s1.eval a * u2.eval a -
              (199680 : k) * t1.eval a * (v1.eval a) ^ 2 +
              (266240 : k) * u2.eval a * v1.eval a -
              (114688 : k) * v1.eval a * w2.eval a = 0 := by
        have hleft :=
          eval_eleventhFace_Vcof810 h0 t1 v1 s1 w2 u2 (p.coeff 4)
            (p.coeff 3) b62 b51 lambda a hroot
        have hzero :
            Polynomial.eval a
                (eleventhFace_Vcof810 h0 t1 v1 s1 w2 u2 (p.coeff 4)
                  (p.coeff 3) b62 b51 lambda) = 0 := by
          rw [hVcof]
          simp [hroot]
        rw [← hleft]
        exact hzero
      have hM1 :
          (32 : k) * s1.eval a - (40 : k) * v1.eval a = 0 := by
        linear_combination (8 : k) * hs1rel
      obtain ⟨hTform, hVform⟩ :=
        eleventhFace_zeroU1_nextOrder810 (v1.eval a) (s1.eval a)
          (t1.eval a) (u2.eval a) (w2.eval a) ((p.coeff 4).eval a)
          (b62.eval a) (b51.eval a) lambda hM1 ha4 hTeval hVeval
      refine Or.inl ⟨hu1z, t1, u2, w2, b51, ht1, hu2, hw2, hb51,
        ⟨u2, hp5_3⟩, ⟨w2, hq7_5⟩, ⟨b51, hb51⟩, hTform, hVform⟩
    · have hB : (5 : k) * (v1.eval a) ^ 2 - (8 : k) * b62.eval a =
          0 := hcomp
      have ha4c :=
        eleventhFace_comp_a4_810 (v1.eval a) ((p.coeff 4).eval a)
          (b62.eval a) ha4 hB
      have hu1c :=
        eleventhFace_comp_u1_810 (v1.eval a) (u1.eval a)
          (b62.eval a) hWspec hB
      exact Or.inr ⟨hB, ha4c, hu1c⟩

/-- Source-facing eleventh-face packet of a normalized scale-two `(8,10)`
nonzero face: the tenth-face split together with the refinement of both
right-alternative siblings. -/
theorem normalized810ScaleTwo_nonzeroFace_eleventhInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K)
      (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ v0 = h0 * v1 ∧ s0 = h0 * s1 ∧
        u0 = h0 * u1 ∧ w0 = h0 * w1 ∧ q.coeff 6 = h0 ^ 2 * b62 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧ h0 ^ 2 ∣ q.coeff 6 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (32 : K) * s1.eval a - (40 : K) * v1.eval a =
              (5 : K) * (t0.eval a) ^ 2 ∧
            (128 : K) * w1.eval a - (160 : K) * u1.eval a -
                (40 : K) * t0.eval a * v1.eval a +
              (5 : K) * (t0.eval a) ^ 3 = 0 ∧
            tenthFace_Gred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a) ∧
            tenthFace_Vred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Wred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            tenthFace_Xred810 (t0.eval a) (v1.eval a) (u1.eval a)
                ((p.coeff 4).eval a) (b62.eval a)
                ((q.coeff 5).eval a) ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ^ 2 ∣ p.coeff 5 ∧ h0 ^ 4 ∣ q.coeff 7) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : K) * s1.eval a = (5 : K) * v1.eval a ∧
            (4 : K) * w1.eval a = (5 : K) * u1.eval a ∧
            (40 : K) * (p.coeff 4).eval a - (32 : K) * b62.eval a +
              (5 : K) * (v1.eval a) ^ 2 = 0 ∧
            (16 : K) * (q.coeff 5).eval a =
              (5 : K) * u1.eval a * v1.eval a ∧
            (16 : K) * b62.eval a * v1.eval a +
                (10 : K) * (u1.eval a) ^ 2 -
              (5 : K) * (v1.eval a) ^ 3 = 0 ∧
            u1.eval a *
                ((5 : K) * (v1.eval a) ^ 2 - (8 : K) * b62.eval a) =
              0 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 4 ∣ p.coeff 6 ∧
            h0 ^ 6 ∣ q.coeff 8 ∧
            ((u1.eval a = 0 ∧
                ∃ (t1 u2 w2 b51 : K[X]),
                  t0 = h0 * t1 ∧ u1 = h0 * u2 ∧ w1 = h0 * w2 ∧
                    q.coeff 5 = h0 * b51 ∧
                    h0 ^ 3 ∣ p.coeff 5 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
                    h0 ∣ q.coeff 5 ∧
                    (32 : K) * w2.eval a - (40 : K) * u2.eval a -
                        (10 : K) * t1.eval a * v1.eval a +
                      (9 : K) * lambda * v1.eval a = 0 ∧
                    (2560 : K) * b51.eval a +
                        (576 : K) * lambda * b62.eval a -
                        (640 : K) * t1.eval a * b62.eval a -
                        (45 : K) * lambda * (v1.eval a) ^ 2 +
                        (400 : K) * t1.eval a * (v1.eval a) ^ 2 -
                        (800 : K) * u2.eval a * v1.eval a = 0) ∨
              ((5 : K) * (v1.eval a) ^ 2 - (8 : K) * b62.eval a = 0 ∧
                (8 : K) * (p.coeff 4).eval a -
                    (3 : K) * (v1.eval a) ^ 2 = 0 ∧
                (2 : K) * (u1.eval a) ^ 2 +
                  (v1.eval a) ^ 3 = 0)))) := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized810ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨t0', v0', u0', s0', w0', v1', s1', u1', w1', b62', ht0', hv0',
    hu0', hs0', hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6',
    hsplit'⟩ :=
    nonzeroFace810_linearRoot_eleventhInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, t0', v0', u0', s0', w0', v1', s1', u1', w1',
    b62', hh0, hlambda, hh0degree, hH, hroot, ht0', hv0', hu0', hs0',
    hw0', hv1', hs1', hu1', hw1', hb62', hq9', hq6', hN', hsplit'⟩

end NonzeroEleventhFace810

#print axioms eleventhCoefficientJacobianRow_810
#print axioms eleventhFace_comp_b62_810
#print axioms eleventhFace_comp_a4_810
#print axioms eleventhFace_comp_u1_810
#print axioms eleventhFace_comp_nextOrder810
#print axioms eleventhFace_zeroU1_T_nextOrder810
#print axioms eleventhFace_zeroU1_V_nextOrder810
#print axioms eleventhFace_zeroU1_nextOrder810
#print axioms eleventhFace_third_zeroU1_mul_h
#print axioms eleventhFace_fifth_zeroU1_mul_h
#print axioms nonzeroFace810_linearRoot_eleventhInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_eleventhInitialPacket

end Max11DegreeRoutes
