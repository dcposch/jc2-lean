import LowScale68ScaleTwoAlignedNonsquareRepresentatives

/-! # Polynomial even coordinates and last-row products for aligned
nonsquare `(6,8)`

The quadratic polynomial `Z²-H`, deck involution, fixed-field descent,
polynomial derivative, square-root normality, and the nonsquare
unit-product lemma are independent of the outer pair.  They are taken
from `LowScale46QuadraticField` / `LowScale46Integrality`.  The input
packet is `NonsquareAlignedSourceCurveData68.representativesPacket`.

Degree-specific `(4,6)` residuals are not used: not the aligned shift
`V=0`, not the boundary quartic, not `K=B²` reconstruction from that
quartic, and not the last-row restriction to `(-3/4) B² dB`.

The `(6,8)` even-cleared numerators below exhibit `A,C₀,E` as explicit
elements of `k(x)`.  Polynomiality of those images is the remaining
`H`-power divisibility of the numerators (or a future monic
eliminant).  On each coordinate face `D=0` or `B=0`, polynomial even
coordinates reconstruct the corresponding square core and reduce the
last-row `W`-form to a polynomial unit product.

No twice-prime or total-degree argument is used.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section EvenClearedAlgebra68

variable {F : Type*} [Field F] [CharZero F]

/-- Polynomial numerator of the even coordinate `A` after replacing
`h²` by the core `H`. -/
def evenClearedA68 {k : Type*} [Field k]
    (H a5 a4 : k[X]) : k[X] :=
  a4 * H ^ 3 - C (5 / 12 : k) * a5 ^ 2

/-- Polynomial numerator of the even coordinate `C₀`. -/
def evenClearedC68 {k : Type*} [Field k]
    (H a5 a4 a3 a2 : k[X]) : k[X] :=
  a2 * H ^ 9 - C (1 / 2 : k) * a3 * a5 * H ^ 6 +
    C (1 / 6 : k) * a4 * a5 ^ 2 * H ^ 3 -
    C (5 / 144 : k) * a5 ^ 4

/-- Polynomial numerator of the even coordinate `E`. -/
def evenClearedE68 {k : Type*} [Field k]
    (H a5 a4 a3 a2 a1 a0 : k[X]) : k[X] :=
  a0 * H ^ 15 - C (1 / 6 : k) * a1 * a5 * H ^ 12 +
    C (1 / 36 : k) * a2 * a5 ^ 2 * H ^ 9 -
    C (1 / 216 : k) * a3 * a5 ^ 3 * H ^ 6 +
    C (1 / 1296 : k) * a4 * a5 ^ 4 * H ^ 3 -
    C (5 / 46656 : k) * a5 ^ 6

theorem depressedSextic68_coeff_five
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 5 = 0 := by
  simp [depressedSextic68]

theorem depressedSextic68_coeff_four
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 4 = A := by
  simp [depressedSextic68]

theorem depressedSextic68_coeff_two
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 2 = C0 := by
  simp [depressedSextic68]

theorem depressedSextic68_coeff_zero
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 0 = E := by
  simp [depressedSextic68]

theorem C_pow_inv_mul_one
    (h : F) (n : ℕ) (hh : h ≠ 0) :
    C (h ^ n) * C (h⁻¹) ^ n = 1 := by
  rw [← map_pow, ← map_mul, inv_pow, mul_inv_cancel₀ (pow_ne_zero n hh),
    map_one]

/-- The quintic coefficient of the affine depression vanishes if and
only if `r` is the sextic depression parameter. -/
theorem affineDepress_rawSextic68_coeff_five
    (h r a5 a4 a3 a2 a1 a0 : F) (hh : h ≠ 0) :
    (affineDepress68 h r (rawSextic68 h a5 a4 a3 a2 a1 a0)).coeff 5 =
      -6 * r + a5 / h ^ 5 := by
  have hhinv : h⁻¹ ≠ 0 := inv_ne_zero hh
  have hdegLin : ((X - C r) * C h⁻¹).natDegree = 1 := by
    have hX : (X - C r).natDegree = 1 := natDegree_X_sub_C r
    have hC : (C h⁻¹).natDegree = 0 := natDegree_C h⁻¹
    rw [natDegree_mul (X_sub_C_ne_zero r) (C_ne_zero.mpr hhinv), hX, hC]
  have hterm (k : ℕ) (ak : F) (hk : k ≤ 4) :
      (C ak * ((X - C r) * C h⁻¹) ^ k).coeff 5 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have hpow :
        (((X - C r) * C h⁻¹) ^ k).natDegree = k * 1 := by
      rw [natDegree_pow, hdegLin]
    have hbound :
        (C ak * ((X - C r) * C h⁻¹) ^ k).natDegree ≤ k := by
      calc
        (C ak * ((X - C r) * C h⁻¹) ^ k).natDegree ≤
            (C ak).natDegree + (((X - C r) * C h⁻¹) ^ k).natDegree :=
          natDegree_mul_le
        _ = 0 + k * 1 := by rw [natDegree_C, hpow]
        _ = k := by simp
    omega
  have hshift : X - C r = X + C (-r) := by
    simp [sub_eq_add_neg, map_neg]
  have h6 :
      C (h ^ 6) * ((X - C r) * C h⁻¹) ^ 6 = (X - C r) ^ 6 := by
    have hpow :
        ((X - C r) * C h⁻¹) ^ 6 = (X - C r) ^ 6 * C (h⁻¹) ^ 6 :=
      mul_pow _ _ 6
    rw [hpow]
    calc
      C (h ^ 6) * ((X - C r) ^ 6 * C (h⁻¹) ^ 6) =
          (X - C r) ^ 6 * (C (h ^ 6) * C (h⁻¹) ^ 6) := by ring
      _ = (X - C r) ^ 6 * 1 := by rw [C_pow_inv_mul_one h 6 hh]
      _ = (X - C r) ^ 6 := by ring
  have h5 :
      C a5 * ((X - C r) * C h⁻¹) ^ 5 =
        C (a5 / h ^ 5) * (X - C r) ^ 5 := by
    have hpow :
        ((X - C r) * C h⁻¹) ^ 5 = (X - C r) ^ 5 * C (h⁻¹ ^ 5) := by
      rw [mul_pow, map_pow]
    have hdiv : a5 * h⁻¹ ^ 5 = a5 / h ^ 5 := by
      rw [inv_pow, div_eq_mul_inv]
    rw [hpow]
    calc
      C a5 * ((X - C r) ^ 5 * C (h⁻¹ ^ 5)) =
          C a5 * C (h⁻¹ ^ 5) * (X - C r) ^ 5 := by ring
      _ = C (a5 * h⁻¹ ^ 5) * (X - C r) ^ 5 := by simp [map_mul]
      _ = C (a5 / h ^ 5) * (X - C r) ^ 5 := by rw [hdiv]
  have hcomp :
      affineDepress68 h r (rawSextic68 h a5 a4 a3 a2 a1 a0) =
        C (h ^ 6) * ((X - C r) * C h⁻¹) ^ 6 +
          C a5 * ((X - C r) * C h⁻¹) ^ 5 +
          C a4 * ((X - C r) * C h⁻¹) ^ 4 +
          C a3 * ((X - C r) * C h⁻¹) ^ 3 +
          C a2 * ((X - C r) * C h⁻¹) ^ 2 +
          C a1 * ((X - C r) * C h⁻¹) ^ 1 +
          C a0 * ((X - C r) * C h⁻¹) ^ 0 := by
    simp only [affineDepress68, rawSextic68]
    simp [add_comp, mul_comp, C_comp, X_pow_comp, X_comp, pow_one,
      pow_zero, mul_one]
  rw [hcomp, h6, h5]
  have hcoeff6 : ((X - C r) ^ 6).coeff 5 = -6 * r := by
    rw [hshift, coeff_X_add_C_pow]
    norm_num
    ring
  have hcoeff5 : ((X - C r) ^ 5).coeff 5 = 1 := by
    rw [hshift, coeff_X_add_C_pow]
    simp
  have hlow4 := hterm 4 a4 (by norm_num)
  have hlow3 := hterm 3 a3 (by norm_num)
  have hlow2 := hterm 2 a2 (by norm_num)
  have hlow1 := hterm 1 a1 (by norm_num)
  have hlow0 := hterm 0 a0 (by norm_num)
  simp only [coeff_add, coeff_C_mul, hcoeff6, hcoeff5, hlow4, hlow3,
    hlow2, hlow1, hlow0]
  ring

theorem r_eq_sexticDepression_of_coeff_five
    (h r a5 a4 a3 a2 a1 a0 : F) (hh : h ≠ 0)
    (h5 :
      (affineDepress68 h r (rawSextic68 h a5 a4 a3 a2 a1 a0)).coeff 5 =
        0) :
    r = sexticDepressionR68 h a5 := by
  have hcoeff := affineDepress_rawSextic68_coeff_five
    h r a5 a4 a3 a2 a1 a0 hh
  rw [hcoeff] at h5
  simp only [sexticDepressionR68]
  have h6 : (6 : F) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h6
  have hr : 6 * r = a5 / h ^ 5 := by
    linear_combination -h5
  rw [hr]
  field_simp [hh]

/-- Exact even form of the depressed quartic coefficient. -/
theorem depressedA68_evenCleared
    (h r a5 a4 : F) (hh : h ≠ 0)
    (hr : r = sexticDepressionR68 h a5) :
    depressedA68 h r a5 a4 =
      (a4 * (h ^ 2) ^ 3 - (5 / 12 : F) * a5 ^ 2) / (h ^ 2) ^ 5 := by
  subst r
  simp only [depressedA68, sexticDepressionR68]
  field_simp [hh]
  ring

/-- Exact even form of the depressed quadratic coefficient. -/
theorem depressedC68_evenCleared
    (h r a5 a4 a3 a2 : F) (hh : h ≠ 0)
    (hr : r = sexticDepressionR68 h a5) :
    depressedC68 h r a5 a4 a3 a2 =
      (a2 * (h ^ 2) ^ 9 - (1 / 2 : F) * a3 * a5 * (h ^ 2) ^ 6 +
          (1 / 6 : F) * a4 * a5 ^ 2 * (h ^ 2) ^ 3 -
          (5 / 144 : F) * a5 ^ 4) / (h ^ 2) ^ 10 := by
  subst r
  simp only [depressedC68, sexticDepressionR68]
  field_simp [hh]
  ring

/-- Exact even form of the depressed constant coefficient. -/
theorem depressedE68_evenCleared
    (h r a5 a4 a3 a2 a1 a0 : F) (hh : h ≠ 0)
    (hr : r = sexticDepressionR68 h a5) :
    depressedE68 h r a5 a4 a3 a2 a1 a0 =
      (a0 * (h ^ 2) ^ 15 - (1 / 6 : F) * a1 * a5 * (h ^ 2) ^ 12 +
          (1 / 36 : F) * a2 * a5 ^ 2 * (h ^ 2) ^ 9 -
          (1 / 216 : F) * a3 * a5 ^ 3 * (h ^ 2) ^ 6 +
          (1 / 1296 : F) * a4 * a5 ^ 4 * (h ^ 2) ^ 3 -
          (5 / 46656 : F) * a5 ^ 6) / (h ^ 2) ^ 15 := by
  subst r
  simp only [depressedE68, sexticDepressionR68]
  field_simp [hh]
  ring

/-- On `B=0` the constant octic coefficient is even in `A,C₀,E`. -/
theorem integratedV68_B_zero
    (A C0 D E alpha gamma epsilon eta : F) :
    integratedV68 0 A 0 C0 D E alpha 0 gamma 0 epsilon eta =
      (2 / 9 : F) * C0 ^ 2 + (4 / 9 : F) * A * E -
        (4 / 27 : F) * A ^ 2 * C0 + (5 / 243 : F) * A ^ 4 +
        alpha * E +
        gamma * ((2 / 3 : F) * C0 - (1 / 9 : F) * A ^ 2) +
        (1 / 3 : F) * epsilon * A + eta := by
  simp only [integratedV68]
  ring

/-- On `B=0` the first-integral remainder is even in `A,C₀,E`. -/
theorem alignedFirstIntegralThreeWithoutDsq68_B_zero
    (A C0 D E gamma epsilon : F) :
    alignedFirstIntegralThreeWithoutDsq68 A 0 C0 D E gamma epsilon =
      (-16 / 243 : F) * A ^ 5 + 2 * C0 * epsilon + 4 * E * gamma -
        (8 / 9 : F) * A * C0 ^ 2 - (8 / 9 : F) * A ^ 2 * E -
        (2 / 3 : F) * A ^ 2 * epsilon + (8 / 3 : F) * C0 * E +
        (8 / 27 : F) * A ^ 3 * gamma + (40 / 81 : F) * A ^ 3 * C0 -
        (4 / 3 : F) * A * C0 * gamma := by
  simp only [alignedFirstIntegralThreeWithoutDsq68]
  ring

end EvenClearedAlgebra68

section RatFuncPolynomiality68

variable {k : Type*} [Field k] [CharZero k]

/-- A rational function which is integral over `k[x]` is a polynomial.
This is the generic monic-eliminant handoff; no specific `(6,8)`
eliminant is supplied. -/
theorem ratFunc_isPolynomial_of_monic_eval68
    (z : RatFunc k) (P : (k[X])[X]) (hP : P.Monic)
    (heval : eval₂ (algebraMap k[X] (RatFunc k)) z P = 0) :
    ∃ Q : k[X], algebraMap k[X] (RatFunc k) Q = z := by
  apply IsIntegrallyClosed.algebraMap_eq_of_integral
  exact ⟨P, hP, heval⟩

/-- Exact division: a ratio of polynomials is itself a polynomial
precisely when the denominator divides the numerator. -/
theorem ratFunc_div_isPolynomial_iff_dvd68
    (N D : k[X]) (hD : D ≠ 0) :
    (∃ Q : k[X], algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k) N /
          algebraMap k[X] (RatFunc k) D) ↔
      D ∣ N := by
  have hD' : algebraMap k[X] (RatFunc k) D ≠ 0 :=
    RatFunc.algebraMap_ne_zero hD
  constructor
  · intro ⟨Q, hQ⟩
    have hmul :
        algebraMap k[X] (RatFunc k) (D * Q) =
          algebraMap k[X] (RatFunc k) N := by
      rw [map_mul, hQ, mul_div_cancel₀ _ hD']
    exact ⟨Q, (FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
      hmul).symm⟩
  · intro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    rw [hQ, map_mul, mul_div_cancel_left₀ _ hD']

/-- Direct polynomial representative of the last-row shift `W`. -/
theorem ratFunc_W_of_polynomial_AC68
    (aR cR wR : RatFunc k) (A0 C0p : k[X]) (gamma : k)
    (hA : algebraMap k[X] (RatFunc k) A0 = aR)
    (hC : algebraMap k[X] (RatFunc k) C0p = cR)
    (hw :
      wR =
        (4 / 9 : RatFunc k) * cR -
          (4 / 27 : RatFunc k) * aR ^ 2 +
          (2 / 3 : RatFunc k) * algebraMap k (RatFunc k) gamma) :
    ∃ W0 : k[X], algebraMap k[X] (RatFunc k) W0 = wR := by
  refine ⟨C (4 / 9 : k) * C0p - C (4 / 27 : k) * A0 ^ 2 +
      C (2 / 3 : k) * C gamma, ?_⟩
  simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
    hA, hC]
  simp only [← RatFunc.algebraMap_eq_C]
  have h49 : algebraMap k (RatFunc k) (4 / 9 : k) =
      (4 / 9 : RatFunc k) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have h427 : algebraMap k (RatFunc k) (4 / 27 : k) =
      (4 / 27 : RatFunc k) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have h23 : algebraMap k (RatFunc k) (2 / 3 : k) =
      (2 / 3 : RatFunc k) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  rw [h49, h427, h23]
  exact hw.symm

/-- Direct polynomial representative of the `B=0` octic constant. -/
theorem ratFunc_V_of_B_zero_polynomial68
    (aR cR eR vR : RatFunc k) (A0 C0p E0 : k[X])
    (alpha gamma epsilon eta : k)
    (hA : algebraMap k[X] (RatFunc k) A0 = aR)
    (hC : algebraMap k[X] (RatFunc k) C0p = cR)
    (hE : algebraMap k[X] (RatFunc k) E0 = eR)
    (hv :
      vR =
        (2 / 9 : RatFunc k) * cR ^ 2 + (4 / 9 : RatFunc k) * aR * eR -
          (4 / 27 : RatFunc k) * aR ^ 2 * cR +
          (5 / 243 : RatFunc k) * aR ^ 4 +
          algebraMap k (RatFunc k) alpha * eR +
          algebraMap k (RatFunc k) gamma *
            ((2 / 3 : RatFunc k) * cR -
              (1 / 9 : RatFunc k) * aR ^ 2) +
          (1 / 3 : RatFunc k) * algebraMap k (RatFunc k) epsilon * aR +
          algebraMap k (RatFunc k) eta) :
    ∃ V0 : k[X], algebraMap k[X] (RatFunc k) V0 = vR := by
  refine ⟨C (2 / 9 : k) * C0p ^ 2 + C (4 / 9 : k) * A0 * E0 -
      C (4 / 27 : k) * A0 ^ 2 * C0p + C (5 / 243 : k) * A0 ^ 4 +
      C alpha * E0 +
      C gamma * (C (2 / 3 : k) * C0p - C (1 / 9 : k) * A0 ^ 2) +
      C (1 / 3 : k) * C epsilon * A0 + C eta, ?_⟩
  simp only [map_add, map_sub, map_mul, map_pow, RatFunc.algebraMap_C,
    hA, hC, hE]
  simp only [← RatFunc.algebraMap_eq_C]
  have hdiv (a b : ℕ) :
      algebraMap k (RatFunc k) ((a : k) / (b : k)) =
        (a : RatFunc k) / (b : RatFunc k) := by
    rw [map_div₀, map_natCast, map_natCast]
  have h29 : algebraMap k (RatFunc k) (2 / 9 : k) =
      (2 / 9 : RatFunc k) := by
    simpa using hdiv 2 9
  have h49 : algebraMap k (RatFunc k) (4 / 9 : k) =
      (4 / 9 : RatFunc k) := by
    simpa using hdiv 4 9
  have h427 : algebraMap k (RatFunc k) (4 / 27 : k) =
      (4 / 27 : RatFunc k) := by
    simpa using hdiv 4 27
  have h5243 : algebraMap k (RatFunc k) (5 / 243 : k) =
      (5 / 243 : RatFunc k) := by
    simpa using hdiv 5 243
  have h23 : algebraMap k (RatFunc k) (2 / 3 : k) =
      (2 / 3 : RatFunc k) := by
    simpa using hdiv 2 3
  have h19 : algebraMap k (RatFunc k) (1 / 9 : k) =
      (1 / 9 : RatFunc k) := by
    rw [map_div₀, map_one, map_ofNat]
  have h13 : algebraMap k (RatFunc k) (1 / 3 : k) =
      (1 / 3 : RatFunc k) := by
    rw [map_div₀, map_one, map_ofNat]
  rw [h29, h49, h427, h5243, h23, h19, h13]
  exact hv.symm

/-- A polynomial product `M P = j` with `M² = H K` and `H` nonsquare is
impossible over an algebraically closed ground field: `M` would be a
unit, hence so would `H`, hence `H` would be a square. -/
theorem nonsquare_polynomial_product_impossible68
    [IsAlgClosed k]
    (H K M P : k[X]) (j : k) (hj : j ≠ 0)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hMK : M ^ 2 = H * K)
    (hlast : M * P = C j) : False := by
  have hjUnit : IsUnit (C j : k[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hj)
  have hprod : IsUnit (M * P) := by
    rw [hlast]
    exact hjUnit
  have hMUnit : IsUnit M := (IsUnit.mul_iff.mp hprod).1
  have hHKUnit : IsUnit (H * K) := by
    rw [← hMK]
    exact hMUnit.pow 2
  have hHUnit : IsUnit H := (IsUnit.mul_iff.mp hHKUnit).1
  obtain ⟨c, hc, hC⟩ := Polynomial.isUnit_iff.mp hHUnit
  obtain ⟨a, ha⟩ :=
    IsAlgClosed.exists_pow_nat_eq c (by norm_num : 0 < 2)
  apply hnsq (C a)
  calc
    H = C c := hC.symm
    _ = C (a ^ 2) := by rw [ha]
    _ = C a ^ 2 := by rw [← map_pow]

end RatFuncPolynomiality68

section QuadraticPolynomialEndgame68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticPolynomialEndgameCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

theorem H_ne_zero_of_nonsquare68 : H ≠ 0 := by
  intro hzero
  exact NonsquarePolynomial46.not_sq (H := H) (0 : k[X]) (by simp [hzero])

/-- Source-facing identification of the depression centre. -/
theorem NonsquareAlignedSourceCurveData68.r_eq_depression
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3) :
    S.r =
      sexticDepressionR68
        (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
        (quadraticCoefficientMap46 H (p.coeff 5)) := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hroot : h ^ 2 = quadraticCoefficientMap46 H H :=
    alignedQuadraticRoot_sq46 H
  have hh : h ≠ 0 := S.scale_ne_zero
  have htop : quadraticCoefficientMap46 H (p.coeff 6) = h ^ 6 := by
    rw [hp6, map_pow, ← hroot]
    ring
  have hraw :
      sourceToQuadratic46 H p =
        rawSextic68 h
          (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3))
          (quadraticCoefficientMap46 H (p.coeff 2))
          (quadraticCoefficientMap46 H (p.coeff 1))
          (quadraticCoefficientMap46 H (p.coeff 0)) :=
    sourceToQuadratic68_eq_rawSextic (H := H) p h hp htop
  have h5 :
      (affineDepress68 h S.r (sourceToQuadratic46 H p)).coeff 5 = 0 := by
    rw [S.sextic_eq, depressedSextic68_coeff_five]
  rw [hraw] at h5
  exact r_eq_sexticDepression_of_coeff_five h S.r
    (quadraticCoefficientMap46 H (p.coeff 5))
    (quadraticCoefficientMap46 H (p.coeff 4))
    (quadraticCoefficientMap46 H (p.coeff 3))
    (quadraticCoefficientMap46 H (p.coeff 2))
    (quadraticCoefficientMap46 H (p.coeff 1))
    (quadraticCoefficientMap46 H (p.coeff 0)) hh h5

/-- The structure coordinates are the source depression coefficients. -/
theorem NonsquareAlignedSourceCurveData68.eq_depressed
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3) :
    S.A =
        depressedA68 (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          S.r (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4)) ∧
      S.C0 =
        depressedC68 (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          S.r (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3))
          (quadraticCoefficientMap46 H (p.coeff 2)) ∧
      S.E =
        depressedE68 (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          S.r (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3))
          (quadraticCoefficientMap46 H (p.coeff 2))
          (quadraticCoefficientMap46 H (p.coeff 1))
          (quadraticCoefficientMap46 H (p.coeff 0)) := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let a5 := quadraticCoefficientMap46 H (p.coeff 5)
  let a4 := quadraticCoefficientMap46 H (p.coeff 4)
  let a3 := quadraticCoefficientMap46 H (p.coeff 3)
  let a2 := quadraticCoefficientMap46 H (p.coeff 2)
  let a1 := quadraticCoefficientMap46 H (p.coeff 1)
  let a0 := quadraticCoefficientMap46 H (p.coeff 0)
  have hroot : h ^ 2 = quadraticCoefficientMap46 H H :=
    alignedQuadraticRoot_sq46 H
  have hh : h ≠ 0 := S.scale_ne_zero
  have htop : quadraticCoefficientMap46 H (p.coeff 6) = h ^ 6 := by
    rw [hp6, map_pow, ← hroot]
    ring
  have hraw :
      sourceToQuadratic46 H p =
        rawSextic68 h a5 a4 a3 a2 a1 a0 :=
    sourceToQuadratic68_eq_rawSextic (H := H) p h hp htop
  have hr := S.r_eq_depression (H := H) hp hp6
  have hdep :=
    affineDepress_rawSextic68 h S.r a5 a4 a3 a2 a1 a0 hh hr
  have hshape := S.sextic_eq
  rw [hraw] at hshape
  rw [hdep] at hshape
  have hA := congrArg (fun f : F68[X] => f.coeff 4) hshape
  have hC := congrArg (fun f : F68[X] => f.coeff 2) hshape
  have hE := congrArg (fun f : F68[X] => f.coeff 0) hshape
  simp only [depressedSextic68_coeff_four, depressedSextic68_coeff_two,
    depressedSextic68_coeff_zero] at hA hC hE
  exact ⟨hA.symm, hC.symm, hE.symm⟩

/-- On `D=0`, polynomial even coordinates reduce the last row to a
polynomial unit product `M_B W E' = j`. -/
theorem NonsquareAlignedSourceCurveData68.impossible_of_D_zero_polynomial_even
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (hD : S.D = 0)
    (A0 C0p E0 : k[X])
    (hA : algebraMap k[X] F68 A0 = S.A)
    (hC : algebraMap k[X] F68 C0p = S.C0)
    (hE : algebraMap k[X] F68 E0 = S.E) : False := by
  obtain ⟨hBne, hWne, hΦ, mB, wR, eR, hmB, hwR, heR, hlast⟩ :=
    NonsquareAlignedSourceCurveData68.lastRow_D_zero_W (H := H) S hj hD
  obtain ⟨K0, hK⟩ :=
    NonsquareAlignedSourceCurveData68.polynomialKB_of_Phi_zero
      (H := H) S A0 C0p E0 hA hC hE hΦ
  obtain ⟨M0, hM, hMK⟩ :=
    NonsquareAlignedSourceCurveData68.polynomialMB_of_polynomialKB
      (H := H) S K0 hK
  have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  have hmBpoly : mB = algebraMap k[X] (RatFunc k) M0 := by
    apply hι
    have hM' : algebraMap k[X] F68 M0 =
        algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) M0) :=
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 M0).symm
    rw [← hM', hM, hmB]
  have heRpoly : eR = algebraMap k[X] (RatFunc k) E0 := by
    apply hι
    have hE' : algebraMap k[X] F68 E0 =
        algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) E0) :=
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 E0).symm
    rw [← hE', hE, heR]
  have hwform :
      wR =
        (4 / 9 : RatFunc k) * algebraMap k[X] (RatFunc k) C0p -
          (4 / 27 : RatFunc k) *
            (algebraMap k[X] (RatFunc k) A0) ^ 2 +
          (2 / 3 : RatFunc k) * algebraMap k (RatFunc k) S.gamma := by
    apply hι
    simp only [map_add, map_sub, map_mul, map_pow, map_div₀, map_ofNat]
    have hA' : algebraMap k[X] F68 A0 =
        algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) A0) :=
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 A0).symm
    have hC' : algebraMap k[X] F68 C0p =
        algebraMap (RatFunc k) F68 (algebraMap k[X] (RatFunc k) C0p) :=
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 C0p).symm
    have hγ : algebraMap k F68 S.gamma =
        algebraMap (RatFunc k) F68 (algebraMap k (RatFunc k) S.gamma) :=
      (IsScalarTower.algebraMap_apply k (RatFunc k) F68 S.gamma).symm
    rw [← hwR]
    simp only [alignedLastRowShiftW68, ← hA', ← hC', hA, hC, hγ]
  obtain ⟨W0, hW0⟩ :=
    ratFunc_W_of_polynomial_AC68
      (algebraMap k[X] (RatFunc k) A0)
      (algebraMap k[X] (RatFunc k) C0p) wR A0 C0p S.gamma
      rfl rfl hwform
  have hder : Differential.deriv eR =
      algebraMap k[X] (RatFunc k) E0.derivative := by
    rw [heRpoly, GCD369RatFuncDerivative]
  have hprodRat :
      algebraMap k[X] (RatFunc k) (M0 * W0 * E0.derivative) =
        algebraMap k (RatFunc k) j := by
    simp only [map_mul, ← hmBpoly, hW0, ← hder]
    exact hlast
  have hCj : algebraMap k (RatFunc k) j =
      algebraMap k[X] (RatFunc k) (C j) := by
    simp only [RatFunc.algebraMap_C]
    rw [RatFunc.algebraMap_eq_C]
  have hpoly : M0 * W0 * E0.derivative = C j :=
    FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
      (hprodRat.trans hCj.symm)
  exact nonsquare_polynomial_product_impossible68 H K0 M0
    (W0 * E0.derivative) j hj NonsquarePolynomial46.not_sq hMK
    (by simpa [mul_assoc] using hpoly)

/-- Residual packet after the polynomial-endgame layer.  The structure
coordinates are the source depression coefficients, which have exact
even-cleared closed forms over `H`.  The face `D=0` closes once
polynomial representatives of `A,C₀,E` are supplied.  Polynomiality of
those coordinates, the `B=0` face, and the mixed two-term last row
remain. -/
theorem NonsquareAlignedSourceCurveData68.polynomialEndgamePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) (hj : j ≠ 0)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3) :
    S.A =
        depressedA68 (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          S.r (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4)) ∧
      S.C0 =
        depressedC68 (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          S.r (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3))
          (quadraticCoefficientMap46 H (p.coeff 2)) ∧
      S.E =
        depressedE68 (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          S.r (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3))
          (quadraticCoefficientMap46 H (p.coeff 2))
          (quadraticCoefficientMap46 H (p.coeff 1))
          (quadraticCoefficientMap46 H (p.coeff 0)) ∧
      (∀ (A0 C0p E0 : k[X]),
        algebraMap k[X] F68 A0 = S.A →
        algebraMap k[X] F68 C0p = S.C0 →
        algebraMap k[X] F68 E0 = S.E →
          S.D = 0 → False) := by
  obtain ⟨hA, hC, hE⟩ := S.eq_depressed (H := H) hp hp6
  refine ⟨hA, hC, hE, ?_⟩
  intro A0 C0p E0 hA' hC' hE' hD
  exact S.impossible_of_D_zero_polynomial_even (H := H) hj hD
    A0 C0p E0 hA' hC' hE'

end QuadraticPolynomialEndgame68

#print axioms ratFunc_isPolynomial_of_monic_eval68
#print axioms ratFunc_div_isPolynomial_iff_dvd68
#print axioms affineDepress_rawSextic68_coeff_five
#print axioms NonsquareAlignedSourceCurveData68.r_eq_depression
#print axioms NonsquareAlignedSourceCurveData68.eq_depressed
#print axioms depressedA68_evenCleared
#print axioms depressedC68_evenCleared
#print axioms depressedE68_evenCleared
#print axioms nonsquare_polynomial_product_impossible68
#print axioms NonsquareAlignedSourceCurveData68.impossible_of_D_zero_polynomial_even
#print axioms NonsquareAlignedSourceCurveData68.polynomialEndgamePacket

end Max11DegreeRoutes
