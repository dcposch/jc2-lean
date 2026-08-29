import LowScale68ScaleTwoAlignedNonsquareMonicEliminant
import LowScale68ScaleTwoAlignedSecondDefect

/-! # Partial even-cleared divisibility and mixed last-row cores for
aligned nonsquare `(6,8)`

The even-cleared ratios `N/H^n` and the monic linear eliminants after
`H^n ∣ N` are already canonical.  This file does not restate those
divisibilities.  It uses the aligned source second defect, deck-even
`I₄`, and the two-term last-row `W`-form.

Degree-specific `(4,6)` residuals are not used: not the aligned shift
`V=0`, not the boundary quartic, not `K=B²` reconstruction from that
quartic, and not the last-row restriction to `(-3/4) B² dB`.  No
twice-prime or total-degree argument is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section EvenClearedSecondDefect68

variable {k : Type*} [Field k] [CharZero k]

/-- The first-integral remainder after removing both `D²` and the mixed
even product `A·BD`. -/
def alignedI3remWithoutABD68 {F : Type*} [Field F] [CharZero F]
    (A Bsq C0 E gamma epsilon : F) : F :=
  (-16 / 243 : F) * A ^ 5 + 2 * C0 * epsilon + 4 * E * gamma -
    (8 / 9 : F) * A * C0 ^ 2 - (8 / 9 : F) * Bsq * C0 -
    (8 / 9 : F) * A ^ 2 * E - (2 / 3 : F) * A ^ 2 * epsilon -
    (2 / 3 : F) * Bsq * gamma + (8 / 3 : F) * C0 * E +
    (8 / 27 : F) * A ^ 3 * gamma + (20 / 27 : F) * A ^ 2 * Bsq +
    (40 / 81 : F) * A ^ 3 * C0 - (4 / 3 : F) * A * C0 * gamma

theorem alignedFirstIntegralThreeWithoutDsq68_splitABD
    {F : Type*} [Field F] [CharZero F]
    (A B C0 D E gamma epsilon : F) :
    alignedFirstIntegralThreeWithoutDsq68 A B C0 D E gamma epsilon =
      alignedI3remWithoutABD68 A (B ^ 2) C0 E gamma epsilon -
        (16 / 9 : F) * A * (B * D) := by
  simp only [alignedFirstIntegralThreeWithoutDsq68,
    alignedI3remWithoutABD68]
  ring

/-- On `L = beta = delta = zeta = 0` the octic constant is even in
`A,C₀,E,B²,BD`. -/
theorem integratedV68_even_BD
    {F : Type*} [Field F] [CharZero F]
    (A B C0 D E alpha gamma epsilon eta : F) :
    integratedV68 0 A B C0 D E alpha 0 gamma 0 epsilon eta =
      (2 / 9 : F) * C0 ^ 2 + (4 / 9 : F) * (B * D) +
        (4 / 9 : F) * A * E - (4 / 27 : F) * A * (B ^ 2) -
        (4 / 27 : F) * A ^ 2 * C0 + (5 / 243 : F) * A ^ 4 +
        alpha * E +
        gamma * ((2 / 3 : F) * C0 - (1 / 9 : F) * A ^ 2) +
        (1 / 3 : F) * epsilon * A + eta := by
  simp only [integratedV68]
  ring

theorem C_mul_twelve_five_twelfths :
    C (12 : k) * C (5 / 12 : k) = C (5 : k) := by
  rw [← map_mul]
  congr 1
  norm_num

theorem C_mul_twelve_inv_twelve :
    C (12 : k) * C (1 / 12 : k) = (1 : k[X]) := by
  rw [← map_mul]
  have h : (12 : k) * (1 / 12 : k) = 1 := by norm_num
  rw [h, map_one]

/-- Exact linear combination of the second defect and the even-cleared
numerator of `A`. -/
theorem evenClearedA68_secondDefect_identity
    (H a4 a5 b6 : k[X]) :
    alignedSecondDefect68 H a4 a5 b6 +
        C (12 : k) * evenClearedA68 H a5 a4 =
      (9 : k[X]) * b6 * H ^ 2 - (7 : k[X]) * a5 ^ 2 := by
  have hC12 : (12 : k[X]) = C (12 : k) := (C_eq_natCast 12).symm
  have hC9 : (9 : k[X]) = C (9 : k) := (C_eq_natCast 9).symm
  have hC7 : (7 : k[X]) = C (7 : k) := (C_eq_natCast 7).symm
  have hC2 : (2 : k[X]) = C (2 : k) := (C_eq_natCast 2).symm
  simp only [alignedSecondDefect68, evenClearedA68]
  rw [hC12, hC9, hC7, hC2, mul_sub]
  have h512 :
      C (12 : k) * (C (5 / 12 : k) * a5 ^ 2) = C (5 : k) * a5 ^ 2 := by
    rw [← mul_assoc, C_mul_twelve_five_twelfths]
  rw [h512]
  have hC5 : C (5 : k) = (5 : k[X]) := C_eq_natCast 5
  rw [hC5, ← hC12, ← hC9, ← hC7, ← hC2]
  ring

/-- After the second defect and `p₅ = g H`, the even-cleared numerator
of `A` is visibly divisible by `H²`. -/
theorem evenClearedA68_of_secondDefect_p5
    (H a4 a5 b6 g : k[X]) (κ : k)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C κ * H ^ 5)
    (hg : a5 = H * g) :
    evenClearedA68 H a5 a4 =
      H ^ 2 *
        (C (1 / 12 : k) *
          ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3)) := by
  have hid := evenClearedA68_secondDefect_identity H a4 a5 b6
  have hC12ne : C (12 : k) ≠ (0 : k[X]) :=
    C_ne_zero.mpr (by norm_num)
  apply mul_left_cancel₀ hC12ne
  have hleft :
      C (12 : k) * evenClearedA68 H a5 a4 =
        (9 : k[X]) * b6 * H ^ 2 - (7 : k[X]) * a5 ^ 2 -
          alignedSecondDefect68 H a4 a5 b6 := by
    linear_combination hid
  rw [hleft, hM, hg]
  have hmid :
      (9 : k[X]) * b6 * H ^ 2 - (7 : k[X]) * (H * g) ^ 2 - C κ * H ^ 5 =
        H ^ 2 *
          ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3) := by
    ring
  rw [hmid]
  have hfac :
      H ^ 2 *
          ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3) =
        (C (12 : k) * C (1 / 12 : k)) *
          (H ^ 2 *
            ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3)) := by
    rw [C_mul_twelve_inv_twelve, one_mul]
  rw [hfac]
  ring

theorem evenClearedA68_pow2_dvd
    (H a4 a5 b6 g : k[X]) (κ : k)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C κ * H ^ 5)
    (hg : a5 = H * g) :
    H ^ 2 ∣ evenClearedA68 H a5 a4 :=
  ⟨_, evenClearedA68_of_secondDefect_p5 H a4 a5 b6 g κ hM hg⟩

/-- The remaining A-divisibility is exactly `H³ ∣ 9 q₆ - 7 g²`. -/
theorem evenClearedA68_pow5_iff_source
    (H a4 a5 b6 g : k[X]) (κ : k) (hH : H ≠ 0)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C κ * H ^ 5)
    (hg : a5 = H * g) :
    H ^ 5 ∣ evenClearedA68 H a5 a4 ↔
      H ^ 3 ∣ (9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 := by
  have hshape :=
    evenClearedA68_of_secondDefect_p5 H a4 a5 b6 g κ hM hg
  have h12unit : IsUnit (C (1 / 12 : k) : k[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
  have hH2 : H ^ 2 ≠ 0 := pow_ne_zero 2 hH
  have hpow : H ^ 5 = H ^ 2 * H ^ 3 := by ring
  constructor
  · intro hpow5
    have hrewritten :
        H ^ 2 * H ^ 3 ∣
          H ^ 2 *
            (C (1 / 12 : k) *
              ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 -
                C κ * H ^ 3)) := by
      rw [← hpow, ← hshape]
      exact hpow5
    have hmid :
        H ^ 3 ∣
          C (1 / 12 : k) *
            ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3) :=
      (mul_dvd_mul_iff_left hH2).mp hrewritten
    have hlin :
        H ^ 3 ∣
          (9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3 :=
      (h12unit.dvd_mul_left).mp hmid
    have hκ : H ^ 3 ∣ C κ * H ^ 3 := ⟨C κ, by ring⟩
    have hsum :
        H ^ 3 ∣
          ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3) +
            C κ * H ^ 3 :=
      dvd_add hlin hκ
    simpa [sub_add_cancel] using hsum
  · intro hsrc
    have hκ : H ^ 3 ∣ C κ * H ^ 3 := ⟨C κ, by ring⟩
    have hsum :
        H ^ 3 ∣
          ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3) :=
      dvd_sub hsrc hκ
    have hmid :
        H ^ 3 ∣
          C (1 / 12 : k) *
            ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3) :=
      (h12unit.dvd_mul_left).mpr hsum
    have hprod :
        H ^ 2 * H ^ 3 ∣
          H ^ 2 *
            (C (1 / 12 : k) *
              ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3)) :=
      mul_dvd_mul_left _ hmid
    rw [hpow, hshape]
    exact hprod

theorem evenClearedC68_of_dvd_p5
    (H a5 a4 a3 a2 g : k[X]) (hg : a5 = H * g) :
    evenClearedC68 H a5 a4 a3 a2 =
      H ^ 4 *
        (a2 * H ^ 5 - C (1 / 2 : k) * a3 * g * H ^ 3 +
          C (1 / 6 : k) * a4 * g ^ 2 * H -
          C (5 / 144 : k) * g ^ 4) := by
  simp only [evenClearedC68, hg]
  ring

theorem evenClearedC68_pow4_dvd
    (H a5 a4 a3 a2 g : k[X]) (hg : a5 = H * g) :
    H ^ 4 ∣ evenClearedC68 H a5 a4 a3 a2 :=
  ⟨_, evenClearedC68_of_dvd_p5 H a5 a4 a3 a2 g hg⟩

theorem evenClearedE68_of_dvd_p5
    (H a5 a4 a3 a2 a1 a0 g : k[X]) (hg : a5 = H * g) :
    evenClearedE68 H a5 a4 a3 a2 a1 a0 =
      H ^ 6 *
        (a0 * H ^ 9 - C (1 / 6 : k) * a1 * g * H ^ 7 +
          C (1 / 36 : k) * a2 * g ^ 2 * H ^ 5 -
          C (1 / 216 : k) * a3 * g ^ 3 * H ^ 3 +
          C (1 / 1296 : k) * a4 * g ^ 4 * H -
          C (5 / 46656 : k) * g ^ 6) := by
  simp only [evenClearedE68, hg]
  ring

theorem evenClearedE68_pow6_dvd
    (H a5 a4 a3 a2 a1 a0 g : k[X]) (hg : a5 = H * g) :
    H ^ 6 ∣ evenClearedE68 H a5 a4 a3 a2 a1 a0 :=
  ⟨_, evenClearedE68_of_dvd_p5 H a5 a4 a3 a2 a1 a0 g hg⟩

/-- The unused Keller coefficient after the aligned second defect.  It
is the smallest source row that mixes `p₃,q₅` with the jet `p₅ = g H`. -/
theorem thirdCoefficientJacobianRow_68 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 5).derivative * (q.coeff 6 * Polynomial.C (6 : K)) +
        (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 5).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 6).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 8).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 10) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (10 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 10 :
      Finset (ℕ × ℕ)) =
      ({(0, 10), (1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4),
        (7, 3), (8, 2), (9, 1), (10, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
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
  rw [hC8, hC7, hC6, hC5, hC4, hC3]
  linear_combination hcoeff

end EvenClearedSecondDefect68

section QuadraticDivisibility68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticDivisibilityCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- Source-facing partial even-cleared divisibilities from the aligned
second defect. -/
theorem NonsquareAlignedSourceCurveData68.partialEvenClearedDvd
    {p q : k[X][X]} {j : k}
    (_S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (κ : k) (g : k[X]),
      p.coeff 5 = H * g ∧
        alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
          C κ * H ^ 5 ∧
        H ^ 2 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ∧
        H ^ 4 ∣
          evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
            (p.coeff 2) ∧
        H ^ 6 ∣
          evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (p.coeff 1) (p.coeff 0) ∧
        (H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ↔
          H ^ 3 ∣
            (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2) := by
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_68 hp hq hjac hH hp6 hq8 haligned
  obtain ⟨g, hg⟩ :=
    alignedSecondDefect_dvd_p5_68 hp hq hjac hH hp6 hq8 haligned
  exact ⟨κ, g, hg, hM,
    evenClearedA68_pow2_dvd H (p.coeff 4) (p.coeff 5) (q.coeff 6) g κ
      hM hg,
    evenClearedC68_pow4_dvd H (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) g hg,
    evenClearedE68_pow6_dvd H (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) g hg,
    evenClearedA68_pow5_iff_source H (p.coeff 4) (p.coeff 5)
      (q.coeff 6) g κ hH hM hg⟩

/-- On the mixed face, `I₄` linearly relates the two last-row cores
`M_B` and `M_D`. -/
theorem NonsquareAlignedSourceCurveData68.lastRow_I4_cores
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    ∃ mB wR eR mD aR vR φR : RatFunc k,
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B =
        algebraMap (RatFunc k) F68 mB ∧
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) =
        algebraMap (RatFunc k) F68 wR ∧
      S.E = algebraMap (RatFunc k) F68 eR ∧
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D =
        algebraMap (RatFunc k) F68 mD ∧
      S.A = algebraMap (RatFunc k) F68 aR ∧
      integratedV68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
          (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
        algebraMap (RatFunc k) F68 vR ∧
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) =
        algebraMap (RatFunc k) F68 φR ∧
      (6 : RatFunc k) * wR * mD + mB * φR = 0 ∧
      mB * wR * Differential.deriv eR -
          mD *
            (Differential.deriv vR -
              ((4 / 9 : RatFunc k) * aR +
                algebraMap k (RatFunc k) S.alpha) *
                Differential.deriv eR) =
        algebraMap k (RatFunc k) j := by
  obtain ⟨mB, wR, eR, mD, aR, vR, hmB, hwR, heR, hmD, haR, hvR,
      hlast⟩ := S.lastRow_W_ratFunc
  obtain ⟨⟨_wR', _hwR'⟩, ⟨φR, hφR⟩, _hbd⟩ := S.evenAuxiliariesDescend
  have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  refine ⟨mB, wR, eR, mD, aR, vR, φR, hmB, hwR, heR, hmD, haR, hvR, hφR,
      ?_, hlast⟩
  apply hι
  simp only [map_add, map_mul, map_ofNat, map_zero]
  rw [← hwR, ← hmD, ← hmB, ← hφR]
  have hI4 := S.I4_factor
  calc
    (6 : F68) *
          alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) *
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D) +
        (AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B) *
          alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
            (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) =
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
          (S.B *
              alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
                (algebraMap k F68 S.gamma)
                (algebraMap k F68 S.epsilon) +
            (6 : F68) *
              alignedLastRowShiftW68 S.A S.C0
                (algebraMap k F68 S.gamma) * S.D) := by
      ring
    _ = AdjoinRoot.root (alignedQuadraticPolynomial46 H) * 0 := by
      rw [hI4]
    _ = 0 := by simp

/-- On `W = 0` with `B ≠ 0`, last-row nonvanishing forces `D ≠ 0` and
`Φ = 0`, and the descended last row is the single `D`-core product. -/
theorem NonsquareAlignedSourceCurveData68.lastRow_W_zero_mixed
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (hW :
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) = 0)
    (hB : S.B ≠ 0) :
    S.D ≠ 0 ∧
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) = 0 ∧
      ∃ mD aR eR vR : RatFunc k,
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D =
          algebraMap (RatFunc k) F68 mD ∧
        S.A = algebraMap (RatFunc k) F68 aR ∧
        S.E = algebraMap (RatFunc k) F68 eR ∧
        integratedV68 0 S.A S.B S.C0 S.D S.E
            (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
            (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
          algebraMap (RatFunc k) F68 vR ∧
        mD *
            (Differential.deriv vR -
              ((4 / 9 : RatFunc k) * aR +
                algebraMap k (RatFunc k) S.alpha) *
                Differential.deriv eR) =
          - algebraMap k (RatFunc k) j := by
  have hDne : S.D ≠ 0 := by
    intro hD0
    exact (NonsquareAlignedSourceCurveData68.lastRow_D_zero_W
      (H := H) S hj hD0).2.1 hW
  have hΦ :
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) =
        0 := by
    have hI4 := S.I4_factor
    simp only [hW, mul_zero, zero_mul, add_zero] at hI4
    exact (mul_eq_zero.mp hI4).resolve_left hB
  obtain ⟨_mB, wR, eR, mD, aR, vR, _φR, _hmB, hwR, heR, hmD, haR, hvR,
      _hφR, _hcores, hlast⟩ :=
    NonsquareAlignedSourceCurveData68.lastRow_I4_cores (H := H) S
  have hw0 : wR = 0 := by
    have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
      (algebraMap (RatFunc k) F68).injective
    apply hι
    rw [← hwR, hW, map_zero]
  refine ⟨hDne, hΦ, mD, aR, eR, vR, hmD, haR, heR, hvR, ?_⟩
  rw [hw0, mul_zero, zero_mul, zero_sub] at hlast
  linear_combination -hlast

/-- On `W ≠ 0` the two-term last row is a single `B`-core product. -/
theorem NonsquareAlignedSourceCurveData68.lastRow_W_ne_Bcore
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hW :
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) ≠ 0) :
    ∃ mB wR eR φR aR vR : RatFunc k,
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B =
        algebraMap (RatFunc k) F68 mB ∧
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) =
        algebraMap (RatFunc k) F68 wR ∧
      S.E = algebraMap (RatFunc k) F68 eR ∧
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) =
        algebraMap (RatFunc k) F68 φR ∧
      S.A = algebraMap (RatFunc k) F68 aR ∧
      integratedV68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
          (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
        algebraMap (RatFunc k) F68 vR ∧
      wR ≠ 0 ∧
      mB *
          ((6 : RatFunc k) * wR ^ 2 * Differential.deriv eR +
            φR *
              (Differential.deriv vR -
                ((4 / 9 : RatFunc k) * aR +
                  algebraMap k (RatFunc k) S.alpha) *
                  Differential.deriv eR)) =
        (6 : RatFunc k) * wR * algebraMap k (RatFunc k) j := by
  obtain ⟨mB, wR, eR, mD, aR, vR, φR, hmB, hwR, heR, _hmD, haR, hvR,
      hφR, hcores, hlast⟩ :=
    NonsquareAlignedSourceCurveData68.lastRow_I4_cores (H := H) S
  have hwne : wR ≠ 0 := by
    intro hw0
    exact hW (by rw [hwR, hw0, map_zero])
  refine ⟨mB, wR, eR, φR, aR, vR, hmB, hwR, heR, hφR, haR, hvR, hwne, ?_⟩
  have hmd :
      (6 : RatFunc k) * wR * mD = - (mB * φR) := by
    linear_combination hcores
  have hclear :=
    congrArg (fun z : RatFunc k => (6 : RatFunc k) * wR * z) hlast
  have hexpand :
      (6 : RatFunc k) * wR *
          (mB * wR * Differential.deriv eR -
            mD *
              (Differential.deriv vR -
                ((4 / 9 : RatFunc k) * aR +
                  algebraMap k (RatFunc k) S.alpha) *
                  Differential.deriv eR)) =
        mB * ((6 : RatFunc k) * wR ^ 2 * Differential.deriv eR) -
          ((6 : RatFunc k) * wR * mD) *
            (Differential.deriv vR -
              ((4 / 9 : RatFunc k) * aR +
                algebraMap k (RatFunc k) S.alpha) *
                Differential.deriv eR) := by
    ring
  have hsubst :
      mB * ((6 : RatFunc k) * wR ^ 2 * Differential.deriv eR) -
          ((6 : RatFunc k) * wR * mD) *
            (Differential.deriv vR -
              ((4 / 9 : RatFunc k) * aR +
                algebraMap k (RatFunc k) S.alpha) *
                Differential.deriv eR) =
        mB *
          ((6 : RatFunc k) * wR ^ 2 * Differential.deriv eR +
            φR *
              (Differential.deriv vR -
                ((4 / 9 : RatFunc k) * aR +
                  algebraMap k (RatFunc k) S.alpha) *
                  Differential.deriv eR)) := by
    rw [hmd]
    ring
  exact (hexpand.trans hsubst).symm.trans hclear

/-- On `W = 0`, constant `I₃` supplies a monic quadratic for the mixed
even product `BD` once `B²` is known. -/
theorem NonsquareAlignedSourceCurveData68.BD_monic_quadratic_W_zero
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (i3 : k)
    (hi3 :
      firstIntegralThree68 0 S.A S.B S.C0 S.D S.E 0
          (algebraMap k F68 S.gamma) 0 (algebraMap k F68 S.epsilon) 0 =
        algebraMap k F68 i3) :
    let Q :=
      (3 / 4 : F68) *
        (algebraMap k F68 i3 -
          alignedI3remWithoutABD68 S.A (S.B ^ 2) S.C0 S.E
            (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon))
    (S.B * S.D) ^ 2 -
        (4 / 3 : F68) * (S.B ^ 2) * S.A * (S.B * S.D) -
        (S.B ^ 2) * Q = 0 := by
  intro Q
  have hremWithout :=
    alignedFirstIntegralThreeWithoutDsq68_splitABD S.A S.B S.C0 S.D
      S.E (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon)
  have hDsq := Dsq_of_firstIntegralThree68 S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon)
    (algebraMap k F68 i3) hi3
  have hDsq' :
      S.D ^ 2 =
        (3 / 4 : F68) *
            (algebraMap k F68 i3 -
              alignedI3remWithoutABD68 S.A (S.B ^ 2) S.C0 S.E
                (algebraMap k F68 S.gamma)
                (algebraMap k F68 S.epsilon)) +
          (4 / 3 : F68) * S.A * (S.B * S.D) := by
    rw [hDsq, hremWithout]
    ring
  have hBD2 : (S.B * S.D) ^ 2 = S.B ^ 2 * S.D ^ 2 := by ring
  rw [hBD2, hDsq']
  ring

/-- Residual packet after the partial-divisibility layer.  The even
numerators are divisible by `H²,H⁴,H⁶` from the aligned second defect.
The remaining A-divisibility is the source relation
`H³ ∣ 9 q₆ - 7 g²`.  Mixed `W = 0` is a single `D`-core with a monic
quadratic for `BD`; mixed `W ≠ 0` is a single `B`-core. -/
theorem NonsquareAlignedSourceCurveData68.partialDivisibilityPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    (∃ (κ : k) (g : k[X]),
        p.coeff 5 = H * g ∧
          H ^ 2 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ∧
          H ^ 4 ∣
            evenClearedC68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) ∧
          H ^ 6 ∣
            evenClearedE68 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) ∧
          (H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ↔
            H ^ 3 ∣
              (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2)) ∧
      (alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) = 0 →
        S.B ≠ 0 →
          alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
              (algebraMap k F68 S.gamma)
              (algebraMap k F68 S.epsilon) = 0 ∧ S.D ≠ 0) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨κ, g, hg, _hM, hA, hC, hE, hiff⟩ :=
      S.partialEvenClearedDvd (H := H) hp hq hp6 hq8 haligned hjac
    exact ⟨κ, g, hg, hA, hC, hE, hiff⟩
  · intro hW hB
    obtain ⟨hDne, hΦ, _⟩ :=
      NonsquareAlignedSourceCurveData68.lastRow_W_zero_mixed (H := H)
        S hj hW hB
    exact ⟨hΦ, hDne⟩

end QuadraticDivisibility68

#print axioms evenClearedA68_secondDefect_identity
#print axioms evenClearedA68_pow5_iff_source
#print axioms thirdCoefficientJacobianRow_68
#print axioms NonsquareAlignedSourceCurveData68.partialEvenClearedDvd
#print axioms NonsquareAlignedSourceCurveData68.lastRow_I4_cores
#print axioms NonsquareAlignedSourceCurveData68.lastRow_W_zero_mixed
#print axioms NonsquareAlignedSourceCurveData68.lastRow_W_ne_Bcore
#print axioms NonsquareAlignedSourceCurveData68.BD_monic_quadratic_W_zero
#print axioms NonsquareAlignedSourceCurveData68.partialDivisibilityPacket

end Max11DegreeRoutes
