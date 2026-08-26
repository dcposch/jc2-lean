import ClassicalRoutes
import Solution

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

abbrev XRest := {i : Fin 2 // i ≠ 1}

def xRestEquivUnit : XRest ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0, by decide⟩
  left_inv i := by
    apply Subtype.ext
    change (0 : Fin 2) = i.val
    apply Fin.ext
    have hi : i.val.val ≠ 1 := by
      intro h
      apply i.property
      apply Fin.ext
      exact h
    omega
  right_inv _ := rfl

def xCoefficientEquiv (K : Type*) [CommSemiring K] :
    MvPolynomial XRest K ≃ₐ[K] K[X] :=
  (renameEquiv K xRestEquivUnit).trans (uniqueAlgEquiv K Unit)

@[simp]
theorem xCoefficientEquiv_X (K : Type*) [CommSemiring K] (i : XRest) :
    xCoefficientEquiv K (MvPolynomial.X i) = Polynomial.X := by
  rw [xCoefficientEquiv]
  simp only [AlgEquiv.trans_apply, renameEquiv_apply, rename_X]
  change MvPolynomial.eval₂ Polynomial.C (fun _ : Unit => Polynomial.X)
      (MvPolynomial.X ()) = Polynomial.X
  simpa using
    (MvPolynomial.eval₂_X (Polynomial.C : K →+* K[X])
      (fun _ : Unit => Polynomial.X) ())

def canonicalYEquiv (K : Type*) [CommSemiring K] :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (MvPolynomial XRest K) :=
  (renameEquiv K (Equiv.optionSubtypeNe (1 : Fin 2)).symm).trans
    (optionEquivLeft K XRest)

def canonicalBivariateEquiv (K : Type*) [CommSemiring K] :
    MvPolynomial (Fin 2) K ≃ₐ[K] K[X][Y] :=
  (canonicalYEquiv K).trans (Polynomial.mapAlgEquiv (xCoefficientEquiv K))

theorem canonicalBivariateEquiv_eq (K : Type*) [CommSemiring K] :
    canonicalBivariateEquiv K = (Polynomial.Bivariate.equivMvPolynomial K).symm := by
  apply AlgEquiv.ext
  have hhom : (canonicalBivariateEquiv K).toAlgHom =
      (Polynomial.Bivariate.equivMvPolynomial K).symm.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [canonicalBivariateEquiv, canonicalYEquiv,
        xRestEquivUnit, xCoefficientEquiv_X]
  exact fun P => DFunLike.congr_fun hhom P

theorem natDegree_bivariate_eq_degreeOf_y {K : Type*} [CommSemiring K]
    (P : MvPolynomial (Fin 2) K) :
    ((Polynomial.Bivariate.equivMvPolynomial K).symm P).natDegree =
      degreeOf 1 P := by
  rw [← canonicalBivariateEquiv_eq]
  simp only [canonicalBivariateEquiv, AlgEquiv.trans_apply,
    Polynomial.coe_mapAlgEquiv]
  rw [Polynomial.natDegree_map_eq_of_injective
    (xCoefficientEquiv K).injective]
  exact (degreeOf_eq_natDegree 1 P).symm

/-- Differentiate a bivariate polynomial coefficientwise in its inner
`x` variable while retaining the outer `y` variable. -/
def xderiv {K : Type*} [CommRing K] (p : K[X][Y]) : K[X][Y] :=
  PolynomialModule.equivPolynomialSelf (Polynomial.derivative'.mapCoeffs p)

@[simp]
theorem coeff_xderiv {K : Type*} [CommRing K] (p : K[X][Y]) (n : ℕ) :
    (xderiv p).coeff n = (p.coeff n).derivative := by
  rfl

theorem natDegree_xderiv_le {K : Type*} [CommRing K] (p : K[X][Y]) :
    (xderiv p).natDegree ≤ p.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_xderiv, Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  exact Polynomial.derivative_zero

/-- Over a characteristic-zero field, two nonzero polynomials with zero
Wronskian differ by a scalar. -/
theorem eq_C_mul_of_wronskian_eq_zero {K : Type*} [Field K] [CharZero K]
    {a b : K[X]} (hb : b ≠ 0) (hW : Polynomial.wronskian a b = 0) :
    ∃ c : K, a = Polynomial.C c * b := by
  classical
  letI := EuclideanDomain.gcdMonoid K[X]
  let d := gcd a b
  let a' := a / d
  let b' := b / d
  have hd : d ≠ 0 := gcd_ne_zero_of_right hb
  have ha : d * a' = a := by
    exact EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left a b)
  have hb' : d * b' = b := by
    exact EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right a b)
  have hb'0 : b' ≠ 0 := by
    exact right_div_gcd_ne_zero hb
  have hcop : IsCoprime a' b' := by
    exact isCoprime_div_gcd_div_gcd hb
  have hW' : Polynomial.wronskian a' b' = 0 := by
    have hscaled : d ^ 2 * Polynomial.wronskian a' b' = 0 := by
      rw [← hW]
      rw [← ha, ← hb']
      simp only [Polynomial.wronskian, Polynomial.derivative_mul]
      ring
    exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 2 hd)
  obtain ⟨hda, hdb⟩ := hcop.wronskian_eq_zero_iff.mp hW'
  let ca := a'.coeff 0
  let cb := b'.coeff 0
  have haC : a' = Polynomial.C ca := Polynomial.eq_C_of_derivative_eq_zero hda
  have hbC : b' = Polynomial.C cb := Polynomial.eq_C_of_derivative_eq_zero hdb
  have hcb : cb ≠ 0 := by
    intro h
    apply hb'0
    rw [hbC, h, Polynomial.C_0]
  refine ⟨ca * cb⁻¹, ?_⟩
  rw [← ha, ← hb', haC, hbC]
  have hc : ca * cb⁻¹ * cb = ca := by
    field_simp
  calc
    d * Polynomial.C ca = d * Polynomial.C (ca * cb⁻¹ * cb) := by rw [hc]
    _ = d * (Polynomial.C (ca * cb⁻¹) * Polynomial.C cb) := by
      rw [Polynomial.C_mul]
    _ = Polynomial.C (ca * cb⁻¹) * (d * Polynomial.C cb) := by ring

/-- The bivariate Jacobian after viewing a polynomial as an outer polynomial
in `y` with coefficients in `K[x]`. -/
def bivariateJacobian {K : Type*} [CommRing K] (p q : K[X][Y]) : K[X][Y] :=
  xderiv p * q.derivative - p.derivative * xderiv q

theorem equivMvPolynomial_bivariateJacobian {K : Type*} [CommRing K]
    (p q : K[X][Y]) :
    Polynomial.Bivariate.equivMvPolynomial K (bivariateJacobian p q) =
      PlaneJacobian (Polynomial.Bivariate.equivMvPolynomial K p)
        (Polynomial.Bivariate.equivMvPolynomial K q) := by
  simp only [bivariateJacobian, PlaneJacobian, map_sub, map_mul,
    Polynomial.Bivariate.pderiv_zero_equivMvPolynomial,
    Polynomial.Bivariate.pderiv_one_equivMvPolynomial, xderiv]

theorem bivariateJacobian_eq_C_of_keller {K : Type*} [Field K]
    {P Q : MvPolynomial (Fin 2) K} (hKeller : IsPlaneKellerPair P Q) :
    ∃ j : K, j ≠ 0 ∧
      bivariateJacobian
          ((Polynomial.Bivariate.equivMvPolynomial K).symm P)
          ((Polynomial.Bivariate.equivMvPolynomial K).symm Q) =
        Polynomial.C (Polynomial.C j) := by
  obtain ⟨j, hj, hjac⟩ := hKeller
  refine ⟨j, hj, ?_⟩
  apply (Polynomial.Bivariate.equivMvPolynomial K).injective
  rw [equivMvPolynomial_bivariateJacobian]
  simpa using hjac

/-- The top `y`-coefficient of a constant-Jacobian equation is the weighted
Wronskian relation between the two leading coefficients in `K[x]`. -/
theorem leadingCoefficient_weightedWronskian {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {m n : ℕ} {j : K}
    (hm : p.natDegree = m) (hn : q.natDegree = n)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    Polynomial.C (n : K) * q.coeff n * (p.coeff m).derivative =
      Polynomial.C (m : K) * p.coeff m * (q.coeff n).derivative := by
  have hxp : (xderiv p).natDegree ≤ m := (natDegree_xderiv_le p).trans_eq hm
  have hxq : (xderiv q).natDegree ≤ n := (natDegree_xderiv_le q).trans_eq hn
  have hdp : p.derivative.natDegree ≤ m - 1 := by
    simpa [hm] using Polynomial.natDegree_derivative_le p
  have hdq : q.derivative.natDegree ≤ n - 1 := by
    simpa [hn] using Polynomial.natDegree_derivative_le q
  have hindex₁ : m + (n - 1) = m + n - 1 := by omega
  have hindex₂ : (m - 1) + n = m + n - 1 := by omega
  have hleft :
      (xderiv p * q.derivative).coeff (m + n - 1) =
        (p.coeff m).derivative * (q.coeff n * Polynomial.C (n : K)) := by
    rw [← hindex₁, Polynomial.coeff_mul_add_eq_of_natDegree_le hxp hdq,
      coeff_xderiv, Polynomial.coeff_derivative]
    have hnsub : n - 1 + 1 = n := by omega
    have hncast : ((n - 1 : ℕ) : K[X]) + 1 = Polynomial.C (n : K) := by
      rw [Polynomial.C_eq_natCast]
      norm_cast
    rw [hnsub, hncast]
  have hright :
      (p.derivative * xderiv q).coeff (m + n - 1) =
        (p.coeff m * Polynomial.C (m : K)) * (q.coeff n).derivative := by
    rw [← hindex₂, Polynomial.coeff_mul_add_eq_of_natDegree_le hdp hxq,
      Polynomial.coeff_derivative, coeff_xderiv]
    have hmsub : m - 1 + 1 = m := by omega
    have hmcast : ((m - 1 : ℕ) : K[X]) + 1 = Polynomial.C (m : K) := by
      rw [Polynomial.C_eq_natCast]
      norm_cast
    rw [hmsub, hmcast]
  have hdegreepos : 0 < m + n - 1 := by omega
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff (m + n - 1)) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, hleft, hright,
    Polynomial.coeff_C, if_neg hdegreepos.ne'] at hcoeff
  have heq := sub_eq_zero.mp hcoeff
  calc
    Polynomial.C (n : K) * q.coeff n * (p.coeff m).derivative =
        (p.coeff m).derivative * (q.coeff n * Polynomial.C (n : K)) := by
      ring
    _ = (p.coeff m * Polynomial.C (m : K)) *
        (q.coeff n).derivative := heq
    _ = Polynomial.C (m : K) * p.coeff m *
        (q.coeff n).derivative := by ring

/-- When the positive outer degree of `q` is a multiple of that of `p`, the
top coefficient of `q` is a scalar multiple of the corresponding power of
the top coefficient of `p`.  This is the cancellation needed for the
classical degree-lowering target shear. -/
theorem leadingCoefficient_power_of_dvd {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {m n k : ℕ} {j : K}
    (hm : p.natDegree = m) (hn : q.natDegree = n)
    (hmpos : 0 < m) (hnpos : 0 < n) (hk : n = k * m)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    ∃ c : K, q.coeff n = Polynomial.C c * (p.coeff m) ^ k := by
  have hkpos : 0 < k := by
    by_contra hkzero
    have : k = 0 := Nat.eq_zero_of_not_pos hkzero
    simp [this] at hk
    omega
  have hp : p ≠ 0 := by
    intro hp
    rw [hp, Polynomial.natDegree_zero] at hm
    omega
  have hpcoeff : p.coeff m ≠ 0 := by
    rw [← hm, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hmC : Polynomial.C (m : K) ≠ 0 := by
    rw [Polynomial.C_ne_zero]
    exact_mod_cast hmpos.ne'
  have hweighted :=
    leadingCoefficient_weightedWronskian hm hn hmpos hnpos hjac
  have hscaled :
      Polynomial.C (k : K) * q.coeff n * (p.coeff m).derivative =
        p.coeff m * (q.coeff n).derivative := by
    apply mul_left_cancel₀ hmC
    calc
      Polynomial.C (m : K) *
          (Polynomial.C (k : K) * q.coeff n * (p.coeff m).derivative) =
          Polynomial.C (n : K) * q.coeff n *
            (p.coeff m).derivative := by
        rw [hk, Nat.cast_mul, Polynomial.C_mul]
        ring
      _ = Polynomial.C (m : K) * p.coeff m *
          (q.coeff n).derivative := hweighted
      _ = Polynomial.C (m : K) *
          (p.coeff m * (q.coeff n).derivative) := by ring
  have hkpow : (p.coeff m) ^ k =
      (p.coeff m) ^ (k - 1) * p.coeff m := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hkpos, pow_succ]
    rw [Nat.pred_eq_sub_one]
  have hW : Polynomial.wronskian (q.coeff n) ((p.coeff m) ^ k) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow, hkpow]
    calc
      q.coeff n *
            (Polynomial.C (k : K) * (p.coeff m) ^ (k - 1) *
              (p.coeff m).derivative) -
          (q.coeff n).derivative *
            ((p.coeff m) ^ (k - 1) * p.coeff m) =
          (p.coeff m) ^ (k - 1) *
            (Polynomial.C (k : K) * q.coeff n *
                (p.coeff m).derivative -
              p.coeff m * (q.coeff n).derivative) := by ring
      _ = 0 := by rw [hscaled, sub_self, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero k hpcoeff) hW

/-- The `(6,9)` weighted leading-coefficient equation has the expected UFD
shape: the two nonzero coefficients are scalar multiples of the square and
cube of one common polynomial core. -/
theorem commonCore_of_weightedWronskian_69 {K : Type*}
    [Field K] [CharZero K] {a b : K[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hweighted :
      Polynomial.C (9 : K) * b * a.derivative =
        Polynomial.C (6 : K) * a * b.derivative) :
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        a = Polynomial.C alpha * h ^ 2 ∧
        b = Polynomial.C beta * h ^ 3 := by
  classical
  have hrel :
      Polynomial.C (3 : K) * b * a.derivative =
        Polynomial.C (2 : K) * a * b.derivative := by
    have hC3 : Polynomial.C (3 : K) ≠ 0 := by norm_num
    have h33 : Polynomial.C (3 : K) * Polynomial.C (3 : K) =
        Polynomial.C (9 : K) := by
      rw [← Polynomial.C_mul]
      norm_num
    have h32 : Polynomial.C (3 : K) * Polynomial.C (2 : K) =
        Polynomial.C (6 : K) := by
      rw [← Polynomial.C_mul]
      norm_num
    apply mul_left_cancel₀ hC3
    calc
      Polynomial.C (3 : K) *
          (Polynomial.C (3 : K) * b * a.derivative) =
          Polynomial.C (9 : K) * b * a.derivative := by
        rw [← h33]
        ring
      _ = Polynomial.C (6 : K) * a * b.derivative := hweighted
      _ = Polynomial.C (3 : K) *
          (Polynomial.C (2 : K) * a * b.derivative) := by
        rw [← h32]
        ring
  have hW : Polynomial.wronskian (a ^ 3) (b ^ 2) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      a ^ 3 * (Polynomial.C (2 : K) * b ^ (2 - 1) * b.derivative) -
          (Polynomial.C (3 : K) * a ^ (3 - 1) * a.derivative) * b ^ 2 =
          a ^ 2 * b *
            (Polynomial.C (2 : K) * a * b.derivative -
              Polynomial.C (3 : K) * b * a.derivative) := by ring
      _ = 0 := by rw [hrel, sub_self, mul_zero]
  obtain ⟨c, hcubes⟩ :=
    eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 2 hb) hW
  have hc : c ≠ 0 := by
    intro hczero
    apply pow_ne_zero 3 ha
    rw [hcubes, hczero, Polynomial.C_0, zero_mul]
  letI := EuclideanDomain.gcdMonoid K[X]
  let d := gcd a b
  let a' := a / d
  let b' := b / d
  have hd : d ≠ 0 := gcd_ne_zero_of_right hb
  have hda : d * a' = a :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left a b)
  have hdb : d * b' = b :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right a b)
  have hb' : b' ≠ 0 := by
    intro hb'zero
    apply hb
    rw [← hdb, hb'zero, mul_zero]
  have hcop : IsCoprime a' b' := isCoprime_div_gcd_div_gcd hb
  have hreduced : d * a' ^ 3 = Polynomial.C c * b' ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hd)
    calc
      d ^ 2 * (d * a' ^ 3) = (d * a') ^ 3 := by ring
      _ = a ^ 3 := by rw [hda]
      _ = Polynomial.C c * b ^ 2 := hcubes
      _ = Polynomial.C c * (d * b') ^ 2 := by rw [hdb]
      _ = d ^ 2 * (Polynomial.C c * b' ^ 2) := by ring
  have hCunit : IsUnit (Polynomial.C c) := by
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have ha'dvd : a' ∣ Polynomial.C c * b' ^ 2 := by
    refine ⟨d * a' ^ 2, ?_⟩
    rw [← hreduced]
    ring
  have ha'unit : IsUnit a' := by
    apply isUnit_of_dvd_unit
      (hcop.pow_right.dvd_of_dvd_mul_right ha'dvd) hCunit
  have hdassoc : Associated d (b' ^ 2) :=
    (associated_mul_unit_left d (a' ^ 3) (ha'unit.pow 3)).symm |>.trans
      (Associated.of_eq hreduced) |>.trans
        (associated_unit_mul_left (b' ^ 2) (Polynomial.C c) hCunit)
  have haassoc : Associated a (b' ^ 2) :=
    (Associated.of_eq hda.symm).trans
      ((associated_mul_unit_left d a' ha'unit).trans hdassoc)
  have hbassoc : Associated b (b' ^ 3) := by
    apply (Associated.of_eq hdb.symm).trans
    have hmul := hdassoc.mul_right b'
    exact hmul.trans (Associated.of_eq (by ring))
  obtain ⟨ua, hua⟩ := haassoc.symm
  obtain ⟨ub, hub⟩ := hbassoc.symm
  obtain ⟨alpha, halphaUnit, halpha⟩ :=
    Polynomial.isUnit_iff.mp ua.isUnit
  obtain ⟨beta, hbetaUnit, hbeta⟩ :=
    Polynomial.isUnit_iff.mp ub.isUnit
  refine ⟨alpha, beta, b', ?_, ?_, hb', ?_, ?_⟩
  · exact (isUnit_iff_ne_zero.mp halphaUnit)
  · exact (isUnit_iff_ne_zero.mp hbetaUnit)
  · calc
      a = b' ^ 2 * (ua : K[X]) := hua.symm
      _ = Polynomial.C alpha * b' ^ 2 := by rw [halpha]; ring
  · calc
      b = b' ^ 3 * (ub : K[X]) := hub.symm
      _ = Polynomial.C beta * b' ^ 3 := by rw [hbeta]; ring

/-- An actual bivariate Keller pair of positive partial `y`-degrees `(6,9)`
produces a nonzero common leading core directly from its Jacobian equation. -/
theorem planeKellerPair_69_commonCore {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hP : degreeOf 1 P = 6) (hQ : degreeOf 1 Q = 9)
    (hKeller : IsPlaneKellerPair P Q) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        p.coeff 6 = Polynomial.C alpha * h ^ 2 ∧
        q.coeff 9 = Polynomial.C beta * h ^ 3 := by
  dsimp only
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hm : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hP
  have hn : q.natDegree = 9 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQ
  have hp : p ≠ 0 := by
    intro hp
    rw [hp, Polynomial.natDegree_zero] at hm
    omega
  have hq : q ≠ 0 := by
    intro hq
    rw [hq, Polynomial.natDegree_zero] at hn
    omega
  have hpcoeff : p.coeff 6 ≠ 0 := by
    rw [← hm, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hqcoeff : q.coeff 9 ≠ 0 := by
    rw [← hn, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨j, -, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hweighted := leadingCoefficient_weightedWronskian
    hm hn (by norm_num) (by norm_num) hjac
  exact commonCore_of_weightedWronskian_69 hpcoeff hqcoeff hweighted

/-- Subtract a scalar multiple of a power of the first target coordinate
from the second target coordinate. -/
def targetShear {K : Type*} [CommRing K] (c : K) (k : ℕ)
    (P Q : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  Q - MvPolynomial.C c * P ^ k

/-- A triangular target shear leaves the generated coordinate subalgebra
unchanged. -/
theorem adjoin_targetShear_eq {K : Type*} [Field K] (c : K) (k : ℕ)
    (P Q : MvPolynomial (Fin 2) K) :
    Algebra.adjoin K ({P, targetShear c k P Q} :
      Set (MvPolynomial (Fin 2) K)) =
      Algebra.adjoin K ({P, Q} : Set (MvPolynomial (Fin 2) K)) := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    intro R hR
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
    rcases hR with hR | hR
    · subst R
      exact Algebra.subset_adjoin (Set.mem_insert P {Q})
    · subst R
      apply Subalgebra.sub_mem
      · exact Algebra.subset_adjoin (Set.mem_insert_of_mem P (Set.mem_singleton Q))
      · apply Subalgebra.mul_mem
        · exact Subalgebra.algebraMap_mem _ c
        · exact Subalgebra.pow_mem _
            (Algebra.subset_adjoin (Set.mem_insert P {Q})) k
  · rw [Algebra.adjoin_le_iff]
    intro R hR
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
    rcases hR with hR | hR
    · subst R
      exact Algebra.subset_adjoin (Set.mem_insert P {targetShear c k P Q})
    · subst R
      have hP : P ∈ Algebra.adjoin K
          ({P, targetShear c k P Q} : Set (MvPolynomial (Fin 2) K)) :=
          Algebra.subset_adjoin (Set.mem_insert P {targetShear c k P Q})
      have hS : targetShear c k P Q ∈ Algebra.adjoin K
          ({P, targetShear c k P Q} : Set (MvPolynomial (Fin 2) K)) :=
          Algebra.subset_adjoin
            (Set.mem_insert_of_mem P (Set.mem_singleton (targetShear c k P Q)))
      have hterm : MvPolynomial.C c * P ^ k ∈ Algebra.adjoin K
          ({P, targetShear c k P Q} : Set (MvPolynomial (Fin 2) K)) := by
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c)
          (Subalgebra.pow_mem _ hP k)
      have hadd := Subalgebra.add_mem _ hS hterm
      change Q ∈ Algebra.adjoin K
        ({P, Max11DegreeRoutes.targetShear c k P Q} :
          Set (MvPolynomial (Fin 2) K))
      simpa only [Max11DegreeRoutes.targetShear, sub_add_cancel] using hadd

theorem planePairGenerates_targetShear_iff {K : Type*} [Field K]
    (c : K) (k : ℕ) (P Q : MvPolynomial (Fin 2) K) :
    PlanePairGenerates P (targetShear c k P Q) ↔ PlanePairGenerates P Q := by
  unfold PlanePairGenerates
  rw [adjoin_targetShear_eq]

/-- A triangular target shear preserves the nonzero constant Jacobian. -/
theorem IsPlaneKellerPair.targetShear {K : Type*} [Field K]
    {P Q : MvPolynomial (Fin 2) K} (h : IsPlaneKellerPair P Q)
    (c : K) (k : ℕ) : IsPlaneKellerPair P (targetShear c k P Q) := by
  rcases h with ⟨j, hj, hjac⟩
  refine ⟨j, hj, ?_⟩
  rw [← hjac]
  unfold Max11DegreeRoutes.targetShear PlaneJacobian
  simp only [map_sub, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow]
  ring

/-- Cancelling equal top coefficients lowers the outer degree. -/
theorem natDegree_targetShear_lt {K : Type*} [Field K]
    {p q : K[X][Y]} {m n k : ℕ} {c : K}
    (hm : p.natDegree = m) (hn : q.natDegree = n) (hnpos : 0 < n)
    (hk : n = k * m)
    (hlead : q.coeff n = Polynomial.C c * (p.coeff m) ^ k) :
    (q - Polynomial.C (Polynomial.C c) * p ^ k).natDegree < n := by
  let r := q - Polynomial.C (Polynomial.C c) * p ^ k
  change r.natDegree < n
  have hterm : (Polynomial.C (Polynomial.C c) * p ^ k).natDegree ≤ n := by
    calc
      (Polynomial.C (Polynomial.C c) * p ^ k).natDegree ≤
          (Polynomial.C (Polynomial.C c)).natDegree + (p ^ k).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + k * p.natDegree := Nat.add_le_add
        (le_of_eq (Polynomial.natDegree_C _)) Polynomial.natDegree_pow_le
      _ = n := by simp [hm, hk]
  have hrle : r.natDegree ≤ n := by
    exact (Polynomial.natDegree_sub_le q
      (Polynomial.C (Polynomial.C c) * p ^ k)).trans
        (max_le (le_of_eq hn) hterm)
  have hrcoeff : r.coeff n = 0 := by
    dsimp only [r]
    have hpcoeff : (p ^ k).coeff n = (p.coeff m) ^ k := by
      rw [hk, Polynomial.coeff_pow_of_natDegree_le (le_of_eq hm)]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hpcoeff, hlead, sub_self]
  exact lt_of_le_of_ne hrle (fun hrn => by
    have hrzero : r ≠ 0 := by
      intro hz
      rw [hz, Polynomial.natDegree_zero] at hrn
      omega
    have hlc := Polynomial.leadingCoeff_ne_zero.mpr hrzero
    rw [← Polynomial.coeff_natDegree, hrn, hrcoeff] at hlc
    exact hlc rfl)

/-- For a positive divisibility relation between the two partial
`y`-degrees, some triangular target shear strictly lowers the second degree. -/
theorem exists_targetShear_degreeOf_lt_of_dvd {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    {m n k : ℕ} (hP : degreeOf 1 P = m) (hQ : degreeOf 1 Q = n)
    (hmpos : 0 < m) (hnpos : 0 < n) (hk : n = k * m)
    (hKeller : IsPlaneKellerPair P Q) :
    ∃ c : K, degreeOf 1 (targetShear c k P Q) < n := by
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hm : p.natDegree = m := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hP
  have hn : q.natDegree = n := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQ
  obtain ⟨j, -, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨c, hlead⟩ :=
    leadingCoefficient_power_of_dvd hm hn hmpos hnpos hk hjac
  refine ⟨c, ?_⟩
  rw [← natDegree_bivariate_eq_degreeOf_y]
  have hdrop := natDegree_targetShear_lt hm hn hnpos hk hlead
  simpa only [targetShear, map_sub, map_mul, map_pow,
    Polynomial.Bivariate.equivMvPolynomial_symm_C, p, q] using hdrop

/-- The classical divisibility route, proved from the explicit triangular
target shear and a strong-induction hypothesis on the second degree. -/
theorem planeKellerAutomorphicAtDegrees_of_dvd {K : Type*}
    [Field K] [CharZero K] (m n : ℕ) (hmn : m < n) (hdvd : m ∣ n)
    (hrec : ∀ r, r < n → PlaneKellerAutomorphicAtDegrees (K := K) m r) :
    PlaneKellerAutomorphicAtDegrees (K := K) m n := by
  obtain ⟨k, hkn⟩ := hdvd
  have hmpos : 0 < m := by
    by_contra hm
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp only [zero_mul] at hkn
    omega
  have hnpos : 0 < n := hmpos.trans hmn
  have hk : n = k * m := by rw [hkn, Nat.mul_comm]
  intro P Q hP hQ hKeller
  obtain ⟨c, hdegree⟩ :=
    exists_targetShear_degreeOf_lt_of_dvd hP hQ hmpos hnpos hk hKeller
  have hgenerated : PlanePairGenerates P (targetShear c k P Q) :=
    hrec (degreeOf 1 (targetShear c k P Q)) hdegree
      P (targetShear c k P Q) hP rfl
        (Max11DegreeRoutes.IsPlaneKellerPair.targetShear hKeller c k)
  exact (planePairGenerates_targetShear_iff c k P Q).mp hgenerated

/-- The equal-degree route: a linear target shear lowers one degree, after
which symmetry puts the result in the recursive hypothesis. -/
theorem planeKellerAutomorphicAtDegrees_equal {K : Type*}
    [Field K] [CharZero K] (n : ℕ)
    (hrec : ∀ r, r < n → PlaneKellerAutomorphicAtDegrees (K := K) r n) :
    PlaneKellerAutomorphicAtDegrees (K := K) n n := by
  by_cases hnzero : n = 0
  · subst n
    exact Max11ClassicalRoutes.planeKellerAutomorphicAtDegrees_zero 0
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
    intro P Q hP hQ hKeller
    obtain ⟨c, hdegree⟩ :=
      exists_targetShear_degreeOf_lt_of_dvd hP hQ hnpos hnpos
        (show n = 1 * n by simp) hKeller
    have hroute := (hrec (degreeOf 1 (targetShear c 1 P Q)) hdegree).swap
    have hgenerated : PlanePairGenerates P (targetShear c 1 P Q) :=
      hroute P (targetShear c 1 P Q) hP rfl
        (Max11DegreeRoutes.IsPlaneKellerPair.targetShear hKeller c 1)
    exact (planePairGenerates_targetShear_iff c 1 P Q).mp hgenerated

/-- Concrete maximum-eleven composition with the zero, equal-degree, and
divisibility routes proved internally.  Only the gcd-at-most-two theorem and
the global `(6,9)` leaf remain as mathematical hypotheses. -/
theorem Max11PlaneKellerGenerationWithElementaryRoutes {K : Type*}
    [Field K] [CharZero K]
    (hgcd : ∀ m n, Nat.gcd m n ≤ 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (h69 : PlaneKellerAutomorphicAtDegrees (K := K) 6 9) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11ClassicalRoutes.Max11PlaneKellerGenerationWithZeroRoute
    hgcd planeKellerAutomorphicAtDegrees_of_dvd
      planeKellerAutomorphicAtDegrees_equal h69

end Max11DegreeRoutes
