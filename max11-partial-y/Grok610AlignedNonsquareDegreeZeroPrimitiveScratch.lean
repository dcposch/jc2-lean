import Grok68AlignedNonsquareDegreeZeroPrimitiveScratch
import Grok610AlignedSquareChamberClosureScratch

/-! # Degree-zero primitive on the `(6,10)` aligned-nonsquare quadratic packet

Untracked working note. No tracked file was edited.

Target Prop: `PlaneKeller610AlignedNonsquareExclusion`
(`Grok610RemainingAlignedFacesScratch.lean`).  Model: the `(6,8)`
nonsquare route in `Grok68AlignedNonsquareDegreeZeroPrimitiveScratch`
(tracked, green).  The Newton-limb route in
`Grok610ScaleTwoAlignedNonsquareLimbsScratch` is not continued.

Parents (tracked, green):
`Sol610ScaleTwoDegreeZeroPrimitiveScratch` (`degreeZeroPrimitive610`,
weight 15) and
`Sol610ScaleTwoDegreeZeroDifferentialBridgeScratch`
(`degreeZeroPrimitive610_deriv_eq_row_of_depressed_rows` and
`degreeZeroPrimitive610_deriv_eq_constant_of_monic_differentialJacobian`
for an arbitrary `Derivation k F F`; the RatFunc specialisation
`degreeZeroPrimitive610_ratFuncDeriv_eq_simplePole` is not needed).
Affine chain rule
`differentialJacobian_affineDepress_sourceToQuadratic68`
(`LowScale68ScaleTwoAlignedNonsquareBridge.lean:117`) is stated for
arbitrary `p q`, so it applies to `(6,10)`.

The ODE polynomial lemma in `Grok68AlignedNonsquareOdeClosureScratch`
is not green (no SHA in `.max11-lanes/gates` receipts), so this file
carries its own copy of the leading-coefficient comparison
`2 H (n' d - n d') + n H' d = 2 j d²` for `natDegree H = 2`.
The odd part `ρ − σρ = Q · √H` realises `d(ρ − σρ) = 2 j / √H`,
hence the rational ODE `2 H Q' + Q H' = 4 j`.  CAS job
`20260902T123231Z-68-aligned-nonsquare-degree-zero-618409`
(`scripts/derive_68_aligned_nonsquare_degree_zero.py`).

On the aligned face the discriminator is
`(5 : K[X]) * p.coeff 5 * H^2 - (3 : K[X]) * q.coeff 9 = 0`.
The depressed `z⁹` coefficient is `L = depressedL610 h r b9` with
`h = √H`, and `alignedSquareL_eq_zero610` forces `L = 0`, so the
bracket is a genuine simple pole `j / √H`.

Landed: `d ρ = j / √H` (unconditional), odd-part descent
`ρ − σρ = Q · √H`, ODE transport, the polynomial obstruction, and
`planeKeller610AlignedNonsquareExclusion_closed`.  With
`planeKeller610AlignedSquareExclusion_closed`, the scale-two closure
`planeKellerNormalized610LowScaleRoute_of_scaleZero`.

FLAG: 610 SCALE-TWO CLOSED

No `sorry`, no new axioms, no finite-root shortcut, no closure
overclaim.  Scale zero remains an explicit premise.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Composition with `-X` and affine high coefficients -/

section AffineHighCoeffs610

variable {R : Type*} [CommRing R]

theorem neg_X_pow610 (k : ℕ) :
    (-X : R[X]) ^ k = C ((-1 : R) ^ k) * X ^ k := by
  rw [neg_eq_neg_one_mul, mul_pow]
  have h1 : (-1 : R[X]) = C (-1) := by simp
  rw [h1, ← C_pow]

theorem C_mul_X_pow_comp_neg_X610 (a : R) (k n : ℕ) :
    ((C a * X ^ k).comp (-X)).coeff n =
      if n = k then a * (-1 : R) ^ k else 0 := by
  have hcomp : (C a * X ^ k).comp (-X) = C a * (-X) ^ k := by
    rw [mul_comp, C_comp, X_pow_comp]
  rw [hcomp, neg_X_pow610]
  have hmul : C a * (C ((-1 : R) ^ k) * X ^ k) =
      C (a * (-1 : R) ^ k) * X ^ k := by
    rw [← mul_assoc, ← C_mul]
  rw [hmul, coeff_C_mul, coeff_X_pow]
  split_ifs with hnk
  · simp [hnk]
  · simp

theorem coeff_comp_neg_X610 (p : R[X]) (n : ℕ) :
    (p.comp (-X)).coeff n = (-1 : R) ^ n * p.coeff n := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a
    simp only [C_comp, coeff_C]
    by_cases hn : n = 0
    · subst n
      simp
    · simp [hn]
  · intro p q hp hq
    simp only [add_comp, coeff_add, hp, hq]
    ring
  · intro m a _ih
    rw [C_mul_X_pow_comp_neg_X610]
    split_ifs with hnk
    · subst n
      simp [coeff_C_mul, coeff_X_pow]
      ring
    · simp [coeff_C_mul, coeff_X_pow, hnk]

end AffineHighCoeffs610

section AffineScaleGeneric610

variable {F : Type*} [Field F]

theorem natDegree_affineScale610 (h r : F) (hh : h ≠ 0) :
    (((X - C r) * C h⁻¹ : F[X]).natDegree) = 1 := by
  have hinv : h⁻¹ ≠ 0 := inv_ne_zero hh
  rw [mul_comm, natDegree_C_mul hinv, natDegree_X_sub_C]

theorem coeff_comp_C_mul_X_pow_affineScale610
    (c h r : F) (n m : ℕ) (hh : h ≠ 0) :
    ((C c * X ^ n).comp ((X - C r) * C h⁻¹)).coeff m =
      if m ≤ n then
        c * h⁻¹ ^ n * (-r) ^ (n - m) * (n.choose m : F)
      else 0 := by
  have hpow :
      ((X - C r) * C h⁻¹ : F[X]) ^ n =
        C (h⁻¹ ^ n) * (X - C r) ^ n := by
    calc
      ((X - C r) * C h⁻¹) ^ n
          = (X - C r) ^ n * (C h⁻¹) ^ n := mul_pow _ _ n
      _ = (X - C r) ^ n * C (h⁻¹ ^ n) := by rw [← C_pow]
      _ = C (h⁻¹ ^ n) * (X - C r) ^ n := mul_comm _ _
  rw [C_mul_comp, X_pow_comp, hpow, ← mul_assoc, ← C_mul]
  by_cases hle : m ≤ n
  · simp only [hle, ite_true]
    have hsub : X - C r = X + C (-r) := by
      simp [sub_eq_add_neg]
    rw [hsub, coeff_C_mul, coeff_X_add_C_pow]
    ring
  · simp only [hle, ite_false]
    have hsub : X - C r = X + C (-r) := by
      simp [sub_eq_add_neg]
    rw [hsub, coeff_C_mul, coeff_X_add_C_pow]
    have hlt : n < m := Nat.not_le.mp hle
    simp [Nat.choose_eq_zero_of_lt hlt]

/-- High coefficients of the affine depression of a degree-ten source,
over an arbitrary coefficient field. -/
theorem affineDepress_degreeTen_highCoeffs610
    (p : F[X]) (h r : F) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 10 = 1 ∧
      (affineDepress68 h r p).coeff 9 = -10 * r + p.coeff 9 / h ^ 9 ∧
      (∀ n, 10 < n → (affineDepress68 h r p).coeff n = 0) := by
  let plow : F[X] :=
    p - C (p.coeff 10) * X ^ 10 - C (p.coeff 9) * X ^ 9
  have hplow : ∀ n, 9 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h9 | hlt9
    · subst n
      simp
    · have : 10 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h10 | hlt10
      · subst n
        simp [hp10]
      · simp [hp_high n (by omega), show n ≠ 10 by omega,
          show n ≠ 9 by omega]
  have hplowDeg : plow.natDegree ≤ 8 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = C (p.coeff 10) * X ^ 10 + C (p.coeff 9) * X ^ 9 + plow := by
    simp only [plow]
    ring
  have hq :
      affineDepress68 h r p =
        (C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹) +
          plow.comp ((X - C r) * C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((X - C r) * C h⁻¹) := rfl
    have hsum (A B D s : F[X]) :
        (A + B + D).comp s = A.comp s + B.comp s + D.comp s := by
      have h1 : (A + B + D).comp s = (A + B).comp s + D.comp s := add_comp
      have h2 : (A + B).comp s = A.comp s + B.comp s := add_comp
      rw [h1, h2]
    exact hdef.trans ((congrArg (fun t => t.comp ((X - C r) * C h⁻¹))
      hp_split).trans (hsum _ _ _ _))
  have hlow (n : ℕ) (hn : 9 ≤ n) :
      (plow.comp ((X - C r) * C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤
          plow.natDegree * ((X - C r) * C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((X - C r) * C h⁻¹).natDegree = 1 :=
      natDegree_affineScale610 h r hh
    have hprod : plow.natDegree * ((X - C r) * C h⁻¹).natDegree ≤ 8 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((X - C r) * C h⁻¹)).natDegree ≤ 8 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 9 ≤ n))
  have h10_10 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 10 = 1 := by
    rw [coeff_comp_C_mul_X_pow_affineScale610 (p.coeff 10) h r 10 10 hh]
    simp [hp10, Nat.choose_self, pow_zero]
    field_simp [hh]
  have h10_9 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 9 =
        -10 * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale610 (p.coeff 10) h r 10 9 hh]
    have hle : (9 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 9 = 10 := by decide
    simp [hp10, hle, hbin, pow_one]
    field_simp [hh]
  have h9_9 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 9 =
        p.coeff 9 / h ^ 9 := by
    rw [coeff_comp_C_mul_X_pow_affineScale610 (p.coeff 9) h r 9 9 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  have h9_10 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 10 = 0 := by
    rw [coeff_comp_C_mul_X_pow_affineScale610 (p.coeff 9) h r 9 10 hh]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hq, coeff_add, coeff_add, h10_10, h9_10, hlow 10 (by omega)]
    simp
  · rw [hq, coeff_add, coeff_add, h10_9, h9_9, hlow 9 (by omega)]
    ring
  · intro n hn
    have hn9 : 9 ≤ n := by omega
    have hn10 : ¬ n ≤ 10 ∨ 10 < n := Or.inr hn
    have h10n :
        ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff n = 0 := by
      rw [coeff_comp_C_mul_X_pow_affineScale610 (p.coeff 10) h r 10 n hh]
      have : ¬ n ≤ 10 := Nat.not_le.mpr hn
      simp [this]
    have h9n :
        ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff n = 0 := by
      rw [coeff_comp_C_mul_X_pow_affineScale610 (p.coeff 9) h r 9 n hh]
      have : ¬ n ≤ 9 := by omega
      simp [this]
    rw [hq, coeff_add, coeff_add, h10n, h9n, hlow n (by omega)]
    simp

end AffineScaleGeneric610

/-! ## Polynomial Wronskian and the quadratic-core ODE obstruction -/

section QuadraticOdePolynomial610

variable {k : Type*} [Field k] [CharZero k]

/-- Polynomial Wronskian `n' d - n d'`. -/
def wronskianPoly610 (n d : k[X]) : k[X] :=
  n.derivative * d - n * d.derivative

theorem wronskianPoly610_zero_of_constants
    (n d : k[X]) (hn : n.natDegree = 0) (hd : d.natDegree = 0) :
    wronskianPoly610 n d = 0 := by
  have hn' : n.derivative = 0 := by
    rw [eq_C_of_natDegree_eq_zero hn, derivative_C]
  have hd' : d.derivative = 0 := by
    rw [eq_C_of_natDegree_eq_zero hd, derivative_C]
  simp [wronskianPoly610, hn', hd']

theorem natDegree_cast_pred_succ610
    {n : ℕ} (hp : 0 < n) :
    ((n - 1 : ℕ) : k) + 1 = (n : k) := by
  have hle : 1 ≤ n := Nat.succ_le_of_lt hp
  rw [Nat.cast_sub hle, Nat.cast_one]
  ring

theorem natDegree_derivative_eq610
    (p : k[X]) (hp : 0 < p.natDegree) :
    p.derivative.natDegree = p.natDegree - 1 := by
  have hpne : p ≠ 0 := fun h => by simp [h] at hp
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hpne
  have hcoeff : p.derivative.coeff (p.natDegree - 1) ≠ 0 := by
    have hn : p.natDegree - 1 + 1 = p.natDegree :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hp)
    rw [coeff_derivative, hn, coeff_natDegree]
    have hn1 : ((p.natDegree - 1 : ℕ) : k) + 1 ≠ 0 := by
      rw [natDegree_cast_pred_succ610 hp]
      exact Nat.cast_ne_zero.mpr (ne_of_gt hp)
    exact mul_ne_zero hlc hn1
  exact le_antisymm (natDegree_derivative_le p)
    (le_natDegree_of_ne_zero hcoeff)

theorem leadingCoeff_derivative_eq610
    (p : k[X]) (hp : 0 < p.natDegree) :
    p.derivative.leadingCoeff =
      (p.natDegree : k) * p.leadingCoeff := by
  have hdeg := natDegree_derivative_eq610 p hp
  have hn : p.natDegree - 1 + 1 = p.natDegree :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hp)
  rw [leadingCoeff, hdeg, coeff_derivative, hn, coeff_natDegree,
    natDegree_cast_pred_succ610 hp]
  ring

theorem wronskianPoly610_coeff_top
    (n d : k[X]) (hn : n ≠ 0) (hd : d ≠ 0) :
    (wronskianPoly610 n d).coeff
        (n.natDegree + d.natDegree - 1) =
      ((n.natDegree : k) - (d.natDegree : k)) *
        n.leadingCoeff * d.leadingCoeff := by
  set a := n.natDegree with ha
  set b := d.natDegree with hb
  by_cases ha0 : a = 0
  · have hnC : n = C n.leadingCoeff := by
      have hC := eq_C_of_natDegree_eq_zero (ha.symm.trans ha0)
      have hlc : n.coeff 0 = n.leadingCoeff := by
        rw [leadingCoeff, show n.natDegree = 0 from ha.symm.trans ha0]
      exact hC.trans (congrArg C hlc)
    have hn' : n.derivative = 0 := by
      rw [hnC, derivative_C]
    have hleft : (n.derivative * d).coeff (a + b - 1) = 0 := by
      simp [hn']
    by_cases hb0 : b = 0
    · have hd' : d.derivative = 0 := by
        rw [eq_C_of_natDegree_eq_zero (hb.symm.trans hb0), derivative_C]
      simp [wronskianPoly610, hn', hd', ha0, hb0]
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      have hN : a + b - 1 = b - 1 := by simp [ha0]
      have hright :
          (n * d.derivative).coeff (b - 1) =
            n.leadingCoeff * ((b : k) * d.leadingCoeff) := by
        have hdb : d.derivative.natDegree = b - 1 :=
          natDegree_derivative_eq610 d hbpos
        rw [hnC, coeff_C_mul, ← hdb, coeff_natDegree,
          leadingCoeff_derivative_eq610 d hbpos]
        simp [show d.natDegree = b from hb.symm]
      have hleft' : (n.derivative * d).coeff (b - 1) = 0 := by
        rw [← hN]
        exact hleft
      rw [wronskianPoly610, coeff_sub, hN, hleft', hright]
      simp [ha0]
      ring
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
    have hn' : n.derivative ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hapos)
    have hna : n.derivative.natDegree = a - 1 :=
      natDegree_derivative_eq610 n hapos
    by_cases hb0 : b = 0
    · have hdC : d = C d.leadingCoeff := by
        have hC := eq_C_of_natDegree_eq_zero (hb.symm.trans hb0)
        have hlc : d.coeff 0 = d.leadingCoeff := by
          rw [leadingCoeff, show d.natDegree = 0 from hb.symm.trans hb0]
        exact hC.trans (congrArg C hlc)
      have hd' : d.derivative = 0 := by
        rw [hdC, derivative_C]
      have hN : a + b - 1 = a - 1 := by simp [hb0]
      have hleft :
          (n.derivative * d).coeff (a - 1) =
            ((a : k) * n.leadingCoeff) * d.leadingCoeff := by
        rw [hdC]
        simp only [leadingCoeff_C]
        rw [mul_comm n.derivative, coeff_C_mul, ← hna, coeff_natDegree,
          leadingCoeff_derivative_eq610 n hapos]
        simp only [show n.natDegree = a from ha.symm]
        ring
      have hright0 : (n * d.derivative).coeff (a - 1) = 0 := by
        simp [hd']
      rw [wronskianPoly610, coeff_sub, hN, hleft, hright0]
      simp only [hb0]
      ring
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      have hd' : d.derivative ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hbpos)
      have hdb : d.derivative.natDegree = b - 1 :=
        natDegree_derivative_eq610 d hbpos
      have hN : a - 1 + b = a + b - 1 := by omega
      have hN' : a + (b - 1) = a + b - 1 := by omega
      have hleft :
          (n.derivative * d).coeff (a + b - 1) =
            ((a : k) * n.leadingCoeff) * d.leadingCoeff := by
        have hmul := natDegree_mul hn' hd
        rw [hna] at hmul
        rw [← hN, ← hmul, coeff_natDegree, leadingCoeff_mul,
          leadingCoeff_derivative_eq610 n hapos]
      have hright :
          (n * d.derivative).coeff (a + b - 1) =
            n.leadingCoeff * ((b : k) * d.leadingCoeff) := by
        have hmul := natDegree_mul hn hd'
        rw [hdb] at hmul
        rw [← hN', ← hmul, coeff_natDegree, leadingCoeff_mul,
          leadingCoeff_derivative_eq610 d hbpos]
      rw [wronskianPoly610, coeff_sub, hleft, hright]
      ring

theorem wronskianPoly610_natDegree_le
    (n d : k[X]) :
    (wronskianPoly610 n d).natDegree ≤
      n.natDegree + d.natDegree - 1 := by
  set a := n.natDegree
  set b := d.natDegree
  have hleft : (n.derivative * d).natDegree ≤ a + b - 1 := by
    by_cases ha0 : a = 0
    · have hn' : n.derivative = 0 := by
        rw [eq_C_of_natDegree_eq_zero (show n.natDegree = 0 from ha0),
          derivative_C]
      simp [hn']
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
      have hn' : n.derivative ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hapos)
      have hmul : (n.derivative * d).natDegree ≤
          n.derivative.natDegree + d.natDegree := natDegree_mul_le
      have hder := natDegree_derivative_eq610 n hapos
      have : a - 1 + b = a + b - 1 := by omega
      exact hmul.trans (le_of_eq (by simp [a, b, hder, this]))
  have hright : (n * d.derivative).natDegree ≤ a + b - 1 := by
    by_cases hb0 : b = 0
    · have hd' : d.derivative = 0 := by
        rw [eq_C_of_natDegree_eq_zero (show d.natDegree = 0 from hb0),
          derivative_C]
      simp [hd']
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      have hd' : d.derivative ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hbpos)
      have hmul : (n * d.derivative).natDegree ≤
          n.natDegree + d.derivative.natDegree := natDegree_mul_le
      have hder := natDegree_derivative_eq610 d hbpos
      have : a + (b - 1) = a + b - 1 := by omega
      exact hmul.trans (le_of_eq (by simp [a, b, hder, this]))
  exact (natDegree_sub_le (n.derivative * d) (n * d.derivative)).trans
    (max_le hleft hright)

theorem wronskianPoly610_natDegree_eq_of_ne
    (n d : k[X]) (hn : n ≠ 0) (hd : d ≠ 0)
    (hneq : n.natDegree ≠ d.natDegree) :
    (wronskianPoly610 n d).natDegree =
      n.natDegree + d.natDegree - 1 := by
  have hcoeff := wronskianPoly610_coeff_top n d hn hd
  have hcast : (n.natDegree : k) ≠ (d.natDegree : k) :=
    (Nat.cast_injective (R := k)).ne hneq
  have ha : n.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hn
  have hb : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd
  have hne :
      (wronskianPoly610 n d).coeff (n.natDegree + d.natDegree - 1) ≠ 0 := by
    intro hz
    have hsub : (n.natDegree : k) - (d.natDegree : k) ≠ 0 :=
      sub_ne_zero.mpr hcast
    apply hsub
    have hprod := hcoeff.symm.trans hz
    rcases mul_eq_zero.mp hprod with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact (ha h').elim
    · exact (hb h).elim
  exact le_antisymm (wronskianPoly610_natDegree_le n d)
    (le_natDegree_of_ne_zero hne)

theorem wronskianPoly610_leadingCoeff_of_ne
    (n d : k[X]) (hn : n ≠ 0) (hd : d ≠ 0)
    (hneq : n.natDegree ≠ d.natDegree) :
    (wronskianPoly610 n d).leadingCoeff =
      ((n.natDegree : k) - (d.natDegree : k)) *
        n.leadingCoeff * d.leadingCoeff := by
  rw [leadingCoeff, wronskianPoly610_natDegree_eq_of_ne n d hn hd hneq]
  exact wronskianPoly610_coeff_top n d hn hd

theorem wronskianPoly610_natDegree_le_of_eq
    (n d : k[X]) (hn : n ≠ 0) (hd : d ≠ 0)
    (heq : n.natDegree = d.natDegree)
    (hpos : 0 < n.natDegree) :
    (wronskianPoly610 n d).natDegree ≤
      n.natDegree + d.natDegree - 2 := by
  have hle := wronskianPoly610_natDegree_le n d
  have hz : (wronskianPoly610 n d).coeff
      (n.natDegree + d.natDegree - 1) = 0 := by
    rw [wronskianPoly610_coeff_top n d hn hd, heq]
    ring
  by_cases htop : (wronskianPoly610 n d).natDegree =
      n.natDegree + d.natDegree - 1
  · have hlc : (wronskianPoly610 n d).leadingCoeff = 0 := by
      rw [leadingCoeff, htop, hz]
    have hW0 : wronskianPoly610 n d = 0 := leadingCoeff_eq_zero.mp hlc
    have : (wronskianPoly610 n d).natDegree = 0 := by simp [hW0]
    have hsum : n.natDegree + d.natDegree - 1 = 0 := this ▸ htop.symm
    omega
  · omega

/-- Cleared polynomial form of the rational ODE
`2 H Q' + Q H' = 2 j` on `Q = n/d`. -/
def quadraticOdeCleared610 (H n d : k[X]) (j : k) : Prop :=
  C (2 : k) * H * wronskianPoly610 n d + n * H.derivative * d =
    C (2 : k) * C j * d ^ 2

/-- The polynomial identity `2 H (n'd - n d') + n H' d = 2 j d²` has
no solution for `j ≠ 0` when `H.natDegree = 2`. -/
theorem quadraticCoreOde_no_polynomial_solution610
    (H n d : k[X]) (j : k)
    (hH : H.natDegree = 2) (hd : d ≠ 0) (hj : j ≠ 0)
    (hide : quadraticOdeCleared610 H n d j) : False := by
  have hHne : H ≠ 0 := fun h0 => by simp [h0] at hH
  have h2 : (2 : k) ≠ 0 := by norm_num
  have hc : H.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hHne
  have hHpos : 0 < H.natDegree := by simp [hH]
  have hHd : H.derivative ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hHpos)
  have hHddeg : H.derivative.natDegree = 1 := by
    simpa [hH] using natDegree_derivative_eq610 H hHpos
  have hHdlc : H.derivative.leadingCoeff =
      (2 : k) * H.leadingCoeff := by
    simpa [hH] using leadingCoeff_derivative_eq610 H hHpos
  have hd2ne : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hC2j : C (2 : k) * C j ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr h2) (C_ne_zero.mpr hj)
  have hRHS : C (2 : k) * C j * d ^ 2 ≠ 0 :=
    mul_ne_zero hC2j hd2ne
  have hRHSdeg : (C (2 : k) * C j * d ^ 2).natDegree = 2 * d.natDegree := by
    rw [natDegree_mul hC2j hd2ne, natDegree_mul (C_ne_zero.mpr h2)
      (C_ne_zero.mpr hj), natDegree_C, natDegree_C, natDegree_pow (n := 2)]
    simp
  have hRHSlc : (C (2 : k) * C j * d ^ 2).leadingCoeff =
      (2 : k) * j * d.leadingCoeff ^ 2 := by
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_C,
      leadingCoeff_pow]
    try ring
  by_cases hn0 : n = 0
  · have hLHS : C (2 : k) * H * wronskianPoly610 n d +
        n * H.derivative * d = 0 := by
      simp [wronskianPoly610, hn0]
    have : (0 : k[X]) = C (2 : k) * C j * d ^ 2 := by
      simpa [quadraticOdeCleared610, hLHS] using hide
    exact hRHS this.symm
  · set a := n.natDegree
    set b := d.natDegree
    have ha : n.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hn0
    have hb : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd
    by_cases heq : a = b
    · by_cases ha0 : a = 0
      · have hb0 : b = 0 := heq.symm.trans ha0
        have hn00 : n.natDegree = 0 := ha0
        have hd00 : d.natDegree = 0 := hb0
        have hW : wronskianPoly610 n d = 0 :=
          wronskianPoly610_zero_of_constants n d hn00 hd00
        have hnddeg : (n * H.derivative * d).natDegree = 1 := by
          rw [natDegree_mul (mul_ne_zero hn0 hHd) hd, natDegree_mul hn0 hHd,
            hn00, hHddeg, hd00]
        have hLHSdeg :
            (C (2 : k) * H * wronskianPoly610 n d +
              n * H.derivative * d).natDegree = 1 := by
          rw [hW, mul_zero, zero_add, hnddeg]
        have hdeq :
            (C (2 : k) * H * wronskianPoly610 n d +
              n * H.derivative * d).natDegree =
              (C (2 : k) * C j * d ^ 2).natDegree :=
          congrArg natDegree hide
        rw [hLHSdeg, hRHSdeg, hb0] at hdeq
        exact (Nat.succ_ne_zero 0 hdeq).elim
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
        have hWle : (wronskianPoly610 n d).natDegree ≤ a + b - 2 :=
          wronskianPoly610_natDegree_le_of_eq n d hn0 hd heq hapos
        have hHWle : (C (2 : k) * H * wronskianPoly610 n d).natDegree ≤
            2 * a := by
          have hle : (C (2 : k) * H * wronskianPoly610 n d).natDegree ≤
              (C (2 : k) * H).natDegree + (wronskianPoly610 n d).natDegree :=
            natDegree_mul_le
          have hCH : (C (2 : k) * H).natDegree = 2 := by
            rw [natDegree_C_mul h2, hH]
          have hsum : (C (2 : k) * H).natDegree +
              (wronskianPoly610 n d).natDegree ≤ 2 + (a + b - 2) :=
            add_le_add (le_of_eq hCH) hWle
          have h2a : 2 + (a + b - 2) = 2 * a := by
            have : b = a := heq.symm
            omega
          exact hle.trans (hsum.trans (le_of_eq h2a))
        have hnddeg : (n * H.derivative * d).natDegree = 2 * a + 1 := by
          rw [natDegree_mul (mul_ne_zero hn0 hHd) hd, natDegree_mul hn0 hHd,
            hHddeg]
          have : b = a := heq.symm
          omega
        have hlt : (C (2 : k) * H * wronskianPoly610 n d).natDegree <
            (n * H.derivative * d).natDegree :=
          lt_of_le_of_lt hHWle (by omega)
        have hLHSdeg :
            (C (2 : k) * H * wronskianPoly610 n d +
              n * H.derivative * d).natDegree = 2 * a + 1 := by
          rw [add_comm, natDegree_add_eq_left_of_natDegree_lt hlt, hnddeg]
        have hdeq :
            (C (2 : k) * H * wronskianPoly610 n d +
              n * H.derivative * d).natDegree =
              (C (2 : k) * C j * d ^ 2).natDegree :=
          congrArg natDegree hide
        rw [hLHSdeg, hRHSdeg, heq.symm] at hdeq
        exact (Nat.succ_ne_self (2 * a) hdeq).elim
    · have hWdeg : (wronskianPoly610 n d).natDegree = a + b - 1 :=
        wronskianPoly610_natDegree_eq_of_ne n d hn0 hd heq
      have hWne : wronskianPoly610 n d ≠ 0 := by
        intro hW0
        have hcoeff := wronskianPoly610_coeff_top n d hn0 hd
        have h0 : (wronskianPoly610 n d).coeff
            (n.natDegree + d.natDegree - 1) = 0 := by
          simp [hW0]
        have hcast : (a : k) ≠ (b : k) :=
          (Nat.cast_injective (R := k)).ne heq
        have hsub : (a : k) - (b : k) ≠ 0 := sub_ne_zero.mpr hcast
        apply hsub
        have hprod := hcoeff.symm.trans h0
        rcases mul_eq_zero.mp hprod with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact h'
          · exact (ha h').elim
        · exact (hb h).elim
      have hWlc : (wronskianPoly610 n d).leadingCoeff =
          ((a : k) - (b : k)) * n.leadingCoeff * d.leadingCoeff :=
        wronskianPoly610_leadingCoeff_of_ne n d hn0 hd heq
      have hHWne : C (2 : k) * H * wronskianPoly610 n d ≠ 0 :=
        mul_ne_zero (mul_ne_zero (C_ne_zero.mpr h2) hHne) hWne
      have hHWdeg : (C (2 : k) * H * wronskianPoly610 n d).natDegree =
          a + b + 1 := by
        rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr h2) hHne) hWne,
          natDegree_C_mul h2, hH, hWdeg]
        have : 2 + (a + b - 1) = a + b + 1 := by omega
        simpa [add_comm] using this
      have hHWlc : (C (2 : k) * H * wronskianPoly610 n d).leadingCoeff =
          (2 : k) * H.leadingCoeff * ((a : k) - (b : k)) *
            n.leadingCoeff * d.leadingCoeff := by
        rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, hWlc]
        ring
      have hndne : n * H.derivative * d ≠ 0 :=
        mul_ne_zero (mul_ne_zero hn0 hHd) hd
      have hnddeg : (n * H.derivative * d).natDegree = a + b + 1 := by
        rw [natDegree_mul (mul_ne_zero hn0 hHd) hd, natDegree_mul hn0 hHd,
          hHddeg]
        omega
      have hndlc : (n * H.derivative * d).leadingCoeff =
          n.leadingCoeff * ((2 : k) * H.leadingCoeff) * d.leadingCoeff := by
        rw [leadingCoeff_mul, leadingCoeff_mul, hHdlc]
        try ring
      have htop :
          (C (2 : k) * H * wronskianPoly610 n d +
              n * H.derivative * d).coeff (a + b + 1) =
            (2 : k) * H.leadingCoeff * ((a : k) - (b : k) + 1) *
              n.leadingCoeff * d.leadingCoeff := by
        have h1 :
            (C (2 : k) * H * wronskianPoly610 n d).coeff (a + b + 1) =
              (C (2 : k) * H * wronskianPoly610 n d).leadingCoeff := by
          rw [← hHWdeg, coeff_natDegree]
        have h2c :
            (n * H.derivative * d).coeff (a + b + 1) =
              (n * H.derivative * d).leadingCoeff := by
          rw [← hnddeg, coeff_natDegree]
        rw [coeff_add, h1, h2c, hHWlc, hndlc]
        ring
      by_cases hshift : a + 1 = b
      · have hvan :
            (C (2 : k) * H * wronskianPoly610 n d +
                n * H.derivative * d).coeff (a + b + 1) = 0 := by
          have hab : (a : k) + 1 = (b : k) := by exact_mod_cast hshift
          have : (a : k) - (b : k) + 1 = 0 := by linear_combination hab
          simp [htop, this]
        have hdegab : a + b + 1 = 2 * b := by omega
        have hLHScoeff :
            (C (2 : k) * H * wronskianPoly610 n d +
                n * H.derivative * d).coeff (2 * b) = 0 := by
          simpa [hdegab] using hvan
        have hRHScoeff : (C (2 : k) * C j * d ^ 2).coeff (2 * b) ≠ 0 := by
          have hbdeg : 2 * b = 2 * d.natDegree := rfl
          rw [hbdeg, ← hRHSdeg, coeff_natDegree, hRHSlc]
          exact mul_ne_zero (mul_ne_zero h2 hj) (pow_ne_zero 2 hb)
        have hcoeff :
            (C (2 : k) * H * wronskianPoly610 n d +
                n * H.derivative * d).coeff (2 * b) =
              (C (2 : k) * C j * d ^ 2).coeff (2 * b) :=
          congrArg (fun p : k[X] => p.coeff (2 * b)) hide
        exact hRHScoeff (hcoeff.symm.trans hLHScoeff)
      · have hcomb : (a : k) - (b : k) + 1 ≠ 0 := by
          intro hz
          have hab : (a : k) + 1 = (b : k) := by linear_combination hz
          exact hshift (by exact_mod_cast hab)
        have htopne :
            (C (2 : k) * H * wronskianPoly610 n d +
                n * H.derivative * d).coeff (a + b + 1) ≠ 0 := by
          intro hz
          apply hcomb
          have hprod := htop.symm.trans hz
          rcases mul_eq_zero.mp hprod with h | h
          · rcases mul_eq_zero.mp h with h' | h'
            · rcases mul_eq_zero.mp h' with h'' | h''
              · rcases mul_eq_zero.mp h'' with h2' | hc'
                · exact (h2 h2').elim
                · exact (hc hc').elim
              · exact h''
            · exact (ha h').elim
          · exact (hb h).elim
        have hLHSdeg :
            (C (2 : k) * H * wronskianPoly610 n d +
                n * H.derivative * d).natDegree = a + b + 1 := by
          have hge := le_natDegree_of_ne_zero htopne
          have hle :=
            (natDegree_add_le (C (2 : k) * H * wronskianPoly610 n d)
              (n * H.derivative * d)).trans
              (max_le (le_of_eq hHWdeg) (le_of_eq hnddeg))
          exact le_antisymm hle hge
        have hdeq :
            (C (2 : k) * H * wronskianPoly610 n d +
                n * H.derivative * d).natDegree =
              (C (2 : k) * C j * d ^ 2).natDegree :=
          congrArg natDegree hide
        rw [hLHSdeg, hRHSdeg] at hdeq
        have : a + b + 1 = 2 * b := by
          simpa [show d.natDegree = b from rfl] using hdeq
        exact hshift (by omega)

end QuadraticOdePolynomial610

/-! ## Sign flip of the weight-fifteen primitive -/

section AlignedNonsquarePrimitiveAlgebra610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 8000000 in
theorem degreeZeroBaseGroup610_signFlip
    (L A B C0 D0 E0 : F) :
    degreeZeroBaseGroup610 (-L) A (-B) C0 (-D0) E0 =
      - degreeZeroBaseGroup610 L A B C0 D0 E0 := by
  simp only [degreeZeroBaseGroup610]
  ring

theorem degreeZeroAlphaGroup610_signFlip
    (A B C0 D0 E0 : F) :
    degreeZeroAlphaGroup610 A (-B) C0 (-D0) E0 =
      - degreeZeroAlphaGroup610 A B C0 D0 E0 := by
  simp only [degreeZeroAlphaGroup610]
  ring

theorem degreeZeroBetaGroup610_signFlip
    (A B C0 D0 E0 : F) :
    degreeZeroBetaGroup610 A (-B) C0 (-D0) E0 =
      degreeZeroBetaGroup610 A B C0 D0 E0 := by
  simp only [degreeZeroBetaGroup610]
  ring

theorem degreeZeroDeltaGroup610_signFlip
    (A B C0 D0 : F) :
    degreeZeroDeltaGroup610 A (-B) C0 (-D0) =
      degreeZeroDeltaGroup610 A B C0 D0 := by
  simp only [degreeZeroDeltaGroup610]
  ring

theorem degreeZeroEpsilonGroup610_signFlip
    (A B C0 D0 : F) :
    degreeZeroEpsilonGroup610 A (-B) C0 (-D0) =
      - degreeZeroEpsilonGroup610 A B C0 D0 := by
  simp only [degreeZeroEpsilonGroup610]
  ring

theorem degreeZeroZetaGroup610_signFlip
    (A B C0 D0 : F) :
    degreeZeroZetaGroup610 A (-B) C0 (-D0) =
      degreeZeroZetaGroup610 A B C0 D0 := by
  simp only [degreeZeroZetaGroup610]
  ring

theorem degreeZeroEtaGroup610_signFlip
    (A B C0 D0 : F) :
    degreeZeroEtaGroup610 A (-B) C0 (-D0) =
      - degreeZeroEtaGroup610 A B C0 D0 := by
  simp only [degreeZeroEtaGroup610]
  ring

theorem degreeZeroThetaGroup610_signFlip
    (A B C0 E0 : F) :
    degreeZeroThetaGroup610 A (-B) C0 E0 =
      degreeZeroThetaGroup610 A B C0 E0 := by
  simp only [degreeZeroThetaGroup610]
  ring

theorem alphaResidual610_signFlip
    (A P : F) :
    alphaResidual610 A P = alphaResidual610 A P :=
  rfl

theorem betaResidual610_signFlip
    (L A B Q : F) :
    betaResidual610 (-L) A (-B) (-Q) =
      - betaResidual610 L A B Q := by
  simp only [betaResidual610]
  ring

theorem gammaResidual610_signFlip
    (L A B C0 P R : F) :
    gammaResidual610 (-L) A (-B) C0 P R =
      gammaResidual610 L A B C0 P R := by
  simp only [gammaResidual610]
  ring

theorem deltaResidual610_signFlip
    (L A B C0 D0 P Q S0 : F) :
    deltaResidual610 (-L) A (-B) C0 (-D0) P (-Q) (-S0) =
      - deltaResidual610 L A B C0 D0 P Q S0 := by
  simp only [deltaResidual610, alphaResidual610, betaResidual610]
  ring

set_option maxHeartbeats 4000000 in
theorem epsilonResidual610_signFlip
    (L A B C0 D0 E0 P Q R T0 : F) :
    epsilonResidual610 (-L) A (-B) C0 (-D0) E0 P (-Q) R T0 =
      epsilonResidual610 L A B C0 D0 E0 P Q R T0 := by
  simp only [epsilonResidual610, alphaResidual610, betaResidual610,
    gammaResidual610]
  ring

set_option maxHeartbeats 4000000 in
theorem zetaResidual610_signFlip
    (L A B C0 D0 E0 P Q R S0 U0 : F) :
    zetaResidual610 (-L) A (-B) C0 (-D0) E0 P (-Q) R (-S0) (-U0) =
      - zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 := by
  simp only [zetaResidual610, alphaResidual610, betaResidual610,
    gammaResidual610, deltaResidual610]
  ring

set_option maxHeartbeats 8000000 in
theorem etaResidual610_signFlip
    (L A B C0 D0 E0 P Q R S0 T0 V0 : F) :
    etaResidual610 (-L) A (-B) C0 (-D0) E0 P (-Q) R (-S0) T0 V0 =
      etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 := by
  simp only [etaResidual610, alphaResidual610, betaResidual610,
    gammaResidual610, deltaResidual610, epsilonResidual610]
  ring

set_option maxHeartbeats 8000000 in
theorem thetaResidual610_signFlip
    (L A B C0 D0 E0 P Q R S0 T0 U0 W0 : F) :
    thetaResidual610 (-L) A (-B) C0 (-D0) E0 P (-Q) R (-S0) T0
        (-U0) (-W0) =
      - thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0 := by
  simp only [thetaResidual610, alphaResidual610, betaResidual610,
    gammaResidual610, deltaResidual610, epsilonResidual610,
    zetaResidual610]
  ring

set_option maxHeartbeats 8000000 in
/-- The weight-fifteen primitive is odd in the odd letters. -/
theorem degreeZeroPrimitive610_signFlip
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 : F) :
    degreeZeroPrimitive610 (-L) A (-B) C0 (-D0) E0 P (-Q) R (-S0) T0
        (-U0) V0 (-W0) X0 =
      - degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 := by
  simp only [degreeZeroPrimitive610]
  rw [degreeZeroBaseGroup610_signFlip, degreeZeroAlphaGroup610_signFlip,
    degreeZeroBetaGroup610_signFlip, degreeZeroDeltaGroup610_signFlip,
    degreeZeroEpsilonGroup610_signFlip, degreeZeroZetaGroup610_signFlip,
    degreeZeroEtaGroup610_signFlip, degreeZeroThetaGroup610_signFlip,
    betaResidual610_signFlip, deltaResidual610_signFlip,
    epsilonResidual610_signFlip, zetaResidual610_signFlip,
    etaResidual610_signFlip, thetaResidual610_signFlip]
  ring

end AlignedNonsquarePrimitiveAlgebra610

/-! ## Quadratic field: derivative, odd descent, ODE -/

section AlignedNonsquarePrimitiveField610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F610" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticPrimitiveCharZero610 : CharZero F610 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F610).injective

/-- Affine centre of the aligned `(6,10)` depression in `k(x)(√H)`. -/
def alignedNonsquareDepressionR610 (p : k[X][X]) : F610 :=
  sexticDepressionR610
    (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
    (quadraticCoefficientMap46 H (p.coeff 5))

/-- Depressed sextic of a `(6,10)` source in the quadratic field. -/
def alignedNonsquareDepressedSextic610 (p : k[X][X]) : F610[X] :=
  affineDepress68
    (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
    (alignedNonsquareDepressionR610 (H := H) p)
    (sourceToQuadratic46 H p)

/-- Depressed decic of a `(6,10)` source in the quadratic field. -/
def alignedNonsquareDepressedDecic610 (p q : k[X][X]) : F610[X] :=
  affineDepress68
    (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
    (alignedNonsquareDepressionR610 (H := H) p)
    (sourceToQuadratic46 H q)

/-- Source-facing weight-fifteen primitive of an aligned nonsquare
`(6,10)` pair. -/
def alignedNonsquareDegreeZeroPrimitive610 (p q : k[X][X]) : F610 :=
  let f := alignedNonsquareDepressedSextic610 (H := H) p
  let g := alignedNonsquareDepressedDecic610 (H := H) p q
  degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
    (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
    (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
    (g.coeff 1) (g.coeff 0)

theorem alignedNonsquareRoot_sq_eq_map610 :
    AdjoinRoot.root (alignedQuadraticPolynomial46 H) ^ 2 =
      quadraticCoefficientMap46 H H := by
  rw [quadraticCoefficientMap46]
  exact alignedQuadraticRoot_sq46 H

theorem alignedNonsquareScale_ne_zero610 :
    AdjoinRoot.root (alignedQuadraticPolynomial46 H) ≠ 0 :=
  alignedQuadraticRoot_ne_zero68 (H := H)

theorem alignedNonsquareDepressionR610_odd (p : k[X][X]) :
    alignedQuadraticDeck46 H (alignedNonsquareDepressionR610 (H := H) p) =
      - alignedNonsquareDepressionR610 (H := H) p := by
  have hh : AdjoinRoot.root (alignedQuadraticPolynomial46 H) ≠ 0 :=
    alignedNonsquareScale_ne_zero610 (H := H)
  simp only [alignedNonsquareDepressionR610, sexticDepressionR610,
    sexticDepressionR68, map_div₀, map_mul, map_ofNat, map_pow,
    alignedQuadraticDeck46_root, alignedQuadraticDeck46_coefficient]
  field_simp [hh]

theorem alignedNonsquareDepressedSextic610_eq_raw
    (p : k[X][X]) (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3) :
    alignedNonsquareDepressedSextic610 (H := H) p =
      depressedSextic68
        (depressedA68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR610 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4)))
        (depressedB68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR610 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3)))
        (depressedC68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR610 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3))
          (quadraticCoefficientMap46 H (p.coeff 2)))
        (depressedD68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR610 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3))
          (quadraticCoefficientMap46 H (p.coeff 2))
          (quadraticCoefficientMap46 H (p.coeff 1)))
        (depressedE68
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR610 (H := H) p)
          (quadraticCoefficientMap46 H (p.coeff 5))
          (quadraticCoefficientMap46 H (p.coeff 4))
          (quadraticCoefficientMap46 H (p.coeff 3))
          (quadraticCoefficientMap46 H (p.coeff 2))
          (quadraticCoefficientMap46 H (p.coeff 1))
          (quadraticCoefficientMap46 H (p.coeff 0))) := by
  let h : F610 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hh : h ≠ 0 := alignedNonsquareScale_ne_zero610 (H := H)
  have hpTop : quadraticCoefficientMap46 H (p.coeff 6) = h ^ 6 := by
    rw [hp6, map_pow, ← alignedNonsquareRoot_sq_eq_map610 (H := H)]
    ring
  have hraw := sourceToQuadratic68_eq_rawSextic (H := H) p h hp hpTop
  rw [alignedNonsquareDepressedSextic610, hraw]
  exact affineDepress_rawSextic68 h
    (alignedNonsquareDepressionR610 (H := H) p)
    (quadraticCoefficientMap46 H (p.coeff 5))
    (quadraticCoefficientMap46 H (p.coeff 4))
    (quadraticCoefficientMap46 H (p.coeff 3))
    (quadraticCoefficientMap46 H (p.coeff 2))
    (quadraticCoefficientMap46 H (p.coeff 1))
    (quadraticCoefficientMap46 H (p.coeff 0)) hh rfl

theorem alignedNonsquareDepressedDecic610_high
    (p q : k[X][X]) (hq : q.natDegree = 10) (hq10 : q.coeff 10 = H ^ 5) :
    (alignedNonsquareDepressedDecic610 (H := H) p q).coeff 10 = 1 ∧
      (alignedNonsquareDepressedDecic610 (H := H) p q).coeff 9 =
        depressedL610
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))
          (alignedNonsquareDepressionR610 (H := H) p)
          (quadraticCoefficientMap46 H (q.coeff 9)) ∧
      (∀ n, 10 < n →
        (alignedNonsquareDepressedDecic610 (H := H) p q).coeff n = 0) := by
  let h : F610 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let r : F610 := alignedNonsquareDepressionR610 (H := H) p
  let src := sourceToQuadratic46 H q
  have hh : h ≠ 0 := alignedNonsquareScale_ne_zero610 (H := H)
  have hp10 : src.coeff 10 = h ^ 10 := by
    simp only [src, sourceToQuadratic46, coeff_map, hq10, map_pow]
    rw [← alignedNonsquareRoot_sq_eq_map610 (H := H)]
    ring
  have hp_high : ∀ n, 10 < n → src.coeff n = 0 := by
    intro n hn
    simp [src, sourceToQuadratic46, coeff_map,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (show q.natDegree < n by omega)]
  obtain ⟨hg10, hg9, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs610 src h r hh hp10 hp_high
  have hdef : alignedNonsquareDepressedDecic610 (H := H) p q =
      affineDepress68 h r src := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hdef]
    exact hg10
  · have hL :
        -10 * r + src.coeff 9 / h ^ 9 =
          depressedL610 h r (quadraticCoefficientMap46 H (q.coeff 9)) := by
      simp [depressedL610, depressedL810, src, sourceToQuadratic46,
        coeff_map]
    rw [hdef, hg9, hL]
  · intro n hn
    rw [hdef]
    exact hg_high n hn

theorem alignedNonsquareL_eq_zero610
    (p q : k[X][X])
    (hq : q.natDegree = 10) (hq10 : q.coeff 10 = H ^ 5)
    (haligned : (5 : k[X]) * p.coeff 5 * H ^ 2 -
      (3 : k[X]) * q.coeff 9 = 0) :
    (alignedNonsquareDepressedDecic610 (H := H) p q).coeff 9 = 0 := by
  let h : F610 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let a5 : F610 := quadraticCoefficientMap46 H (p.coeff 5)
  let b9 : F610 := quadraticCoefficientMap46 H (q.coeff 9)
  have hh : h ≠ 0 := alignedNonsquareScale_ne_zero610 (H := H)
  have hNrat : (5 : F610) * a5 * h ^ 4 - (3 : F610) * b9 = 0 := by
    have hmapped := congrArg (quadraticCoefficientMap46 H) haligned
    simp only [map_sub, map_mul, map_ofNat, map_zero] at hmapped
    have hH2 : quadraticCoefficientMap46 H (H ^ 2) = h ^ 4 := by
      rw [map_pow, ← alignedNonsquareRoot_sq_eq_map610 (H := H)]
      ring
    simpa [a5, b9, hH2] using hmapped
  have hLval :
      depressedL610 h (sexticDepressionR610 h a5) b9 = 0 :=
    alignedSquareL_eq_zero610 h a5 b9 hh hNrat
  have hgHigh :=
    alignedNonsquareDepressedDecic610_high (H := H) p q hq hq10
  have hg9 :
      (alignedNonsquareDepressedDecic610 (H := H) p q).coeff 9 =
        depressedL610 h (alignedNonsquareDepressionR610 (H := H) p) b9 :=
    hgHigh.2.1
  have hr : alignedNonsquareDepressionR610 (H := H) p =
      sexticDepressionR610 h a5 := rfl
  rw [hg9, hr, hLval]

/-- Step 1: the monic bridge realises `d ρ = j / √H`. -/
theorem alignedNonsquareDegreeZeroPrimitive610_deriv
    (p q : k[X][X]) (j : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned : (5 : k[X]) * p.coeff 5 * H ^ 2 -
      (3 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    quadraticDerivation46 H
        (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q) =
      algebraMap k F610 j /
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) := by
  let h : F610 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let r : F610 := alignedNonsquareDepressionR610 (H := H) p
  let f := alignedNonsquareDepressedSextic610 (H := H) p
  let g := alignedNonsquareDepressedDecic610 (H := H) p q
  have hh : h ≠ 0 := alignedNonsquareScale_ne_zero610 (H := H)
  have hfEq :=
    alignedNonsquareDepressedSextic610_eq_raw (H := H) p hp hp6
  have hgHigh :=
    alignedNonsquareDepressedDecic610_high (H := H) p q hq hq10
  have hf6 : f.coeff 6 = 1 := by
    dsimp [f]
    rw [hfEq, coeff_depressedSextic68_six]
  have hf5 : f.coeff 5 = 0 := by
    dsimp [f]
    rw [hfEq, coeff_depressedSextic68_five]
  have hf_high : ∀ n, 6 < n → f.coeff n = 0 := by
    intro n hn
    dsimp [f]
    rw [hfEq, coeff_depressedSextic68_of_gt_six _ _ _ _ _ hn]
  have hg10 : g.coeff 10 = 1 := by
    dsimp [g]
    exact hgHigh.1
  have hg_high : ∀ n, 10 < n → g.coeff n = 0 := by
    intro n hn
    dsimp [g]
    exact hgHigh.2.2 n hn
  have hLval : g.coeff 9 = 0 := by
    dsimp [g]
    exact alignedNonsquareL_eq_zero610 (H := H) p q hq hq10 haligned
  have hL : quadraticDerivation46 H (g.coeff 9) = 0 := by
    rw [hLval]
    simp [quadraticDerivation46_apply]
  have hbracket :=
    differentialJacobian_affineDepress_sourceToQuadratic68 (H := H)
      p q j h r hh hD
  have hjac :
      differentialJacobian (quadraticDerivation46 H) f g =
        C (algebraMap k F610 j / h) := by
    simpa [f, g, alignedNonsquareDepressedSextic610,
      alignedNonsquareDepressedDecic610] using hbracket
  simpa [alignedNonsquareDegreeZeroPrimitive610, f, g] using
    degreeZeroPrimitive610_deriv_eq_constant_of_monic_differentialJacobian
      (quadraticDerivation46 H) f g (algebraMap k F610 j / h)
      hf_high hf6 hf5 hg_high hg10 hL hjac

/-- The quadratic deck is an involution. -/
theorem alignedQuadraticDeck46_involutive610 (z : F610) :
    alignedQuadraticDeck46 H (alignedQuadraticDeck46 H z) = z := by
  obtain ⟨c0, c1, hz⟩ := alignedQuadratic_eq_add_mul_root68 (H := H) z
  set rt := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hrt : alignedQuadraticDeck46 H rt = -rt :=
    alignedQuadraticDeck46_root H
  have hneg : alignedQuadraticDeck46 H (-rt) = rt := by
    rw [map_neg, hrt, neg_neg]
  rw [hz]
  simp only [map_add, map_mul, alignedQuadraticDeck46_base, hrt]
  rw [hneg]

/-- Deck of the logarithmic derivative of `√H`. -/
theorem alignedQuadraticDeck46_deriv_root610 :
    alignedQuadraticDeck46 H
        (quadraticDerivation46 H
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H))) =
      - quadraticDerivation46 H
          (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) := by
  set rt := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hrt := quadraticDerivation46_root68 (H := H)
  have hrt0 : rt ≠ 0 := alignedNonsquareScale_ne_zero610 (H := H)
  have h2 : (2 : F610) ≠ 0 := two_ne_zero
  rw [hrt]
  have hmap :
      alignedQuadraticDeck46 H
          (algebraMap (RatFunc k) F610
            (algebraMap k[X] (RatFunc k) H.derivative) / (2 * rt)) =
        algebraMap (RatFunc k) F610
          (algebraMap k[X] (RatFunc k) H.derivative) /
            (2 * alignedQuadraticDeck46 H rt) := by
    simp only [map_div₀, map_mul, map_ofNat, alignedQuadraticDeck46_base]
  rw [hmap, alignedQuadraticDeck46_root]
  have hden : (2 : F610) * (-rt) = -((2 : F610) * rt) := by ring
  rw [hden, div_neg]

/-- The quadratic deck commutes with the selected derivation. -/
theorem alignedQuadraticDeck46_deriv610 (z : F610) :
    quadraticDerivation46 H (alignedQuadraticDeck46 H z) =
      alignedQuadraticDeck46 H (quadraticDerivation46 H z) := by
  obtain ⟨c0, c1, hz⟩ := alignedQuadratic_eq_add_mul_root68 (H := H) z
  set rt := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hbase (c : RatFunc k) :
      alignedQuadraticDeck46 H (algebraMap (RatFunc k) F610 c) =
        algebraMap (RatFunc k) F610 c :=
    alignedQuadraticDeck46_base H c
  have hfix (c : RatFunc k) :
      alignedQuadraticDeck46 H
          (quadraticDerivation46 H (algebraMap (RatFunc k) F610 c)) =
        quadraticDerivation46 H (algebraMap (RatFunc k) F610 c) := by
    rw [quadraticDerivation46_algebraMap_ratFunc68 H c]
    exact alignedQuadraticDeck46_base H _
  have hrtσ : alignedQuadraticDeck46 H rt = -rt :=
    alignedQuadraticDeck46_root H
  have hσdrt := alignedQuadraticDeck46_deriv_root610 (H := H)
  rw [hz]
  have hdeckz :
      alignedQuadraticDeck46 H
          (algebraMap (RatFunc k) F610 c0 +
            algebraMap (RatFunc k) F610 c1 * rt) =
        algebraMap (RatFunc k) F610 c0 -
          algebraMap (RatFunc k) F610 c1 * rt := by
    simp only [map_add, map_mul, hbase, hrtσ]
    ring
  rw [hdeckz]
  have hLHS :
      quadraticDerivation46 H
          (algebraMap (RatFunc k) F610 c0 -
            algebraMap (RatFunc k) F610 c1 * rt) =
        quadraticDerivation46 H (algebraMap (RatFunc k) F610 c0) -
          (algebraMap (RatFunc k) F610 c1 * quadraticDerivation46 H rt +
            rt * quadraticDerivation46 H (algebraMap (RatFunc k) F610 c1)) := by
    rw [map_sub]
    have hmul := Derivation.leibniz (quadraticDerivation46 H)
      (algebraMap (RatFunc k) F610 c1) rt
    simp only [smul_eq_mul] at hmul
    rw [hmul]
    try ring
  have hRHS :
      alignedQuadraticDeck46 H
          (quadraticDerivation46 H
            (algebraMap (RatFunc k) F610 c0 +
              algebraMap (RatFunc k) F610 c1 * rt)) =
        quadraticDerivation46 H (algebraMap (RatFunc k) F610 c0) -
          (algebraMap (RatFunc k) F610 c1 * quadraticDerivation46 H rt +
            rt * quadraticDerivation46 H (algebraMap (RatFunc k) F610 c1)) := by
    have hsum := map_add (quadraticDerivation46 H)
      (algebraMap (RatFunc k) F610 c0)
      (algebraMap (RatFunc k) F610 c1 * rt)
    rw [hsum]
    have hmul := Derivation.leibniz (quadraticDerivation46 H)
      (algebraMap (RatFunc k) F610 c1) rt
    simp only [smul_eq_mul] at hmul
    rw [hmul]
    simp only [map_add, map_mul, hbase, hfix, hrtσ]
    have hσdrt' :
        alignedQuadraticDeck46 H (quadraticDerivation46 H rt) =
          - quadraticDerivation46 H rt := hσdrt
    rw [hσdrt']
    ring
  rw [hLHS, hRHS]

/-- Odd part of the weight-fifteen primitive: `ρ − σρ` is deck-odd. -/
theorem alignedNonsquareDegreeZeroPrimitive610_oddPart
    (p q : k[X][X]) :
    alignedQuadraticDeck46 H
        (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q -
          alignedQuadraticDeck46 H
            (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q)) =
      - (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q -
          alignedQuadraticDeck46 H
            (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q)) := by
  simp only [map_sub, alignedQuadraticDeck46_involutive610]
  ring

/-- Odd descent of the odd part: `ρ − σρ = Q · √H`. -/
theorem alignedNonsquareDegreeZeroPrimitive610_eq_mul_root
    (p q : k[X][X]) :
    ∃ Q : RatFunc k,
      alignedNonsquareDegreeZeroPrimitive610 (H := H) p q -
          alignedQuadraticDeck46 H
            (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q) =
        algebraMap (RatFunc k) F610 Q *
          AdjoinRoot.root (alignedQuadraticPolynomial46 H) :=
  alignedQuadratic_odd_eq_mul_root68 (H := H)
    (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q -
      alignedQuadraticDeck46 H
        (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q))
    (alignedNonsquareDegreeZeroPrimitive610_oddPart (H := H) p q)

/-- Transport `d(Q · √H) = 2 j / √H` for the odd part. -/
theorem alignedNonsquareDegreeZeroPrimitive610_ratFuncOde
    (p q : k[X][X]) (j : k) (Q : RatFunc k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned : (5 : k[X]) * p.coeff 5 * H ^ 2 -
      (3 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j))
    (hQ : alignedNonsquareDegreeZeroPrimitive610 (H := H) p q -
        alignedQuadraticDeck46 H
          (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q) =
      algebraMap (RatFunc k) F610 Q *
        AdjoinRoot.root (alignedQuadraticPolynomial46 H)) :
    (2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
        Differential.deriv Q +
      Q * algebraMap k[X] (RatFunc k) H.derivative =
      (4 : RatFunc k) * algebraMap k (RatFunc k) j := by
  set rt := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hrt : rt ≠ 0 := alignedNonsquareScale_ne_zero610 (H := H)
  have hφ : Function.Injective (algebraMap (RatFunc k) F610) :=
    (algebraMap (RatFunc k) F610).injective
  have hsq := alignedQuadraticRoot_sq46 H
  have hderρ := alignedNonsquareDegreeZeroPrimitive610_deriv (H := H)
    p q j hp hq hp6 hq10 haligned hD
  have hder :
      quadraticDerivation46 H
          (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q -
            alignedQuadraticDeck46 H
              (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q)) =
        (2 : F610) * algebraMap k F610 j / rt := by
    have hcomm := alignedQuadraticDeck46_deriv610 (H := H)
      (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q)
    have hdeckpole :
        alignedQuadraticDeck46 H (algebraMap k F610 j / rt) =
          -(algebraMap k F610 j / rt) := by
      have hmap :
          alignedQuadraticDeck46 H (algebraMap k F610 j / rt) =
            algebraMap k F610 j / alignedQuadraticDeck46 H rt := by
        simp only [map_div₀, alignedQuadraticDeck46_ground]
      rw [hmap, alignedQuadraticDeck46_root, div_neg]
    have hsub :=
      map_sub (quadraticDerivation46 H)
        (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q)
        (alignedQuadraticDeck46 H
          (alignedNonsquareDegreeZeroPrimitive610 (H := H) p q))
    rw [hsub, hcomm, hderρ, hdeckpole]
    ring
  have hroot := quadraticDerivation46_root68 (H := H)
  have hQder := quadraticDerivation46_algebraMap_ratFunc68 H Q
  have hleibniz :
      quadraticDerivation46 H (algebraMap (RatFunc k) F610 Q * rt) =
        algebraMap (RatFunc k) F610 (Differential.deriv Q) * rt +
          algebraMap (RatFunc k) F610 Q *
            quadraticDerivation46 H rt := by
    have hmul := Derivation.leibniz (quadraticDerivation46 H)
      (algebraMap (RatFunc k) F610 Q) rt
    simp only [smul_eq_mul] at hmul
    rw [hmul, hQder]
    ring
  have hprim :
      quadraticDerivation46 H (algebraMap (RatFunc k) F610 Q * rt) =
        (2 : F610) * algebraMap k F610 j / rt := by
    rw [← hQ]
    exact hder
  have hsum :
      algebraMap (RatFunc k) F610 (Differential.deriv Q) * rt +
        algebraMap (RatFunc k) F610 Q *
          (algebraMap (RatFunc k) F610
            (algebraMap k[X] (RatFunc k) H.derivative) / (2 * rt)) =
        (2 : F610) * algebraMap k F610 j / rt := by
    have h := hleibniz.symm.trans hprim
    rw [hroot] at h
    exact h
  have h2ne : (2 : F610) ≠ 0 := two_ne_zero
  have h2rt : (2 : F610) * rt ≠ 0 := mul_ne_zero h2ne hrt
  have hcleared :
      (2 : F610) * algebraMap (RatFunc k) F610 (Differential.deriv Q) *
          (rt * rt) +
        algebraMap (RatFunc k) F610 Q *
          algebraMap (RatFunc k) F610
            (algebraMap k[X] (RatFunc k) H.derivative) =
        (4 : F610) * algebraMap k F610 j := by
    have := congrArg (fun z : F610 => (2 * rt) * z) hsum
    field_simp [h2ne, hrt, h2rt] at this
    linear_combination this
  have hleft :
      (2 : F610) * algebraMap (RatFunc k) F610 (Differential.deriv Q) *
          (rt * rt) +
        algebraMap (RatFunc k) F610 Q *
          algebraMap (RatFunc k) F610
            (algebraMap k[X] (RatFunc k) H.derivative) =
        algebraMap (RatFunc k) F610
          ((2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
            Differential.deriv Q +
            Q * algebraMap k[X] (RatFunc k) H.derivative) := by
    have hrt2 : rt * rt =
        algebraMap (RatFunc k) F610 (algebraMap k[X] (RatFunc k) H) := by
      simpa [pow_two] using hsq
    rw [hrt2]
    simp only [map_add, map_mul, map_ofNat]
    ring
  have hright :
      (4 : F610) * algebraMap k F610 j =
        algebraMap (RatFunc k) F610
          ((4 : RatFunc k) * algebraMap k (RatFunc k) j) := by
    rw [IsScalarTower.algebraMap_apply k (RatFunc k) F610, map_mul, map_ofNat]
  exact hφ (by rw [← hleft, hcleared, hright])

/-- Clearing the rational ODE on `Q = n/d` produces the polynomial
identity `2 H (n'd - nd') + n H' d = 2 j d²`. -/
theorem ratFuncOde_to_polynomial610
    (Q : RatFunc k) (j : k)
    (hode : (2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
        Differential.deriv Q +
      Q * algebraMap k[X] (RatFunc k) H.derivative =
      (2 : RatFunc k) * algebraMap k (RatFunc k) j) :
    quadraticOdeCleared610 H Q.num Q.denom j := by
  have hd : Q.denom ≠ 0 := Q.denom_ne_zero
  have hdφ : algebraMap k[X] (RatFunc k) Q.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero hd
  have hQder : Differential.deriv Q =
      (algebraMap k[X] (RatFunc k) Q.denom *
          algebraMap k[X] (RatFunc k) Q.num.derivative -
        algebraMap k[X] (RatFunc k) Q.num *
          algebraMap k[X] (RatFunc k) Q.denom.derivative) /
        algebraMap k[X] (RatFunc k) Q.denom ^ 2 := by
    letI : Algebra ℤ (RatFunc k) := Ring.toIntAlgebra (RatFunc k)
    have h := congrArg Differential.deriv Q.num_div_denom.symm
    rw [Derivation.leibniz_div, GCD369RatFuncDerivative,
      GCD369RatFuncDerivative] at h
    simpa [smul_eq_mul, div_eq_inv_mul] using h
  have hW :
      algebraMap k[X] (RatFunc k) (wronskianPoly610 Q.num Q.denom) =
        Differential.deriv Q *
          algebraMap k[X] (RatFunc k) Q.denom ^ 2 := by
    rw [hQder]
    field_simp [hdφ]
    simp [wronskianPoly610, map_sub, map_mul, mul_comm]
  have hn :
      algebraMap k[X] (RatFunc k) Q.num =
        Q * algebraMap k[X] (RatFunc k) Q.denom := by
    have := mul_div_cancel₀ (algebraMap k[X] (RatFunc k) Q.num) hdφ
    rw [Q.num_div_denom] at this
    rw [mul_comm] at this
    exact this.symm
  have hmul :
      algebraMap k[X] (RatFunc k)
          (C (2 : k) * H * wronskianPoly610 Q.num Q.denom +
            Q.num * H.derivative * Q.denom) =
        algebraMap k[X] (RatFunc k)
          (C (2 : k) * C j * Q.denom ^ 2) := by
    have hleft :
        algebraMap k[X] (RatFunc k)
            (C (2 : k) * H * wronskianPoly610 Q.num Q.denom +
              Q.num * H.derivative * Q.denom) =
          ((2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
              Differential.deriv Q +
            Q * algebraMap k[X] (RatFunc k) H.derivative) *
            algebraMap k[X] (RatFunc k) Q.denom ^ 2 := by
      simp only [map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_C]
      rw [hW, hn]
      ring
    have hright :
        algebraMap k[X] (RatFunc k) (C (2 : k) * C j * Q.denom ^ 2) =
          ((2 : RatFunc k) * algebraMap k (RatFunc k) j) *
            algebraMap k[X] (RatFunc k) Q.denom ^ 2 := by
      simp only [map_mul, map_pow, map_ofNat, RatFunc.algebraMap_C]
      rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k)]
      simp [RatFunc.algebraMap_C]
    rw [hleft, hode, hright]
  exact (FaithfulSMul.algebraMap_injective k[X] (RatFunc k)) hmul

/-- The odd descent of the weight-fifteen primitive yields a polynomial
solution of the cleared ODE. -/
theorem alignedNonsquareDegreeZeroPrimitive610_clearedOde
    (p q : k[X][X]) (j : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned : (5 : k[X]) * p.coeff 5 * H ^ 2 -
      (3 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    ∃ n d : k[X], d ≠ 0 ∧
      quadraticOdeCleared610 H n d (2 * j) := by
  obtain ⟨Q, hQ⟩ :=
    alignedNonsquareDegreeZeroPrimitive610_eq_mul_root (H := H) p q
  have hode := alignedNonsquareDegreeZeroPrimitive610_ratFuncOde
    (H := H) p q j Q hp hq hp6 hq10 haligned hD hQ
  have hode' :
      (2 : RatFunc k) * algebraMap k[X] (RatFunc k) H *
          Differential.deriv Q +
        Q * algebraMap k[X] (RatFunc k) H.derivative =
        (2 : RatFunc k) * algebraMap k (RatFunc k) (2 * j) := by
    have hrhs : (4 : RatFunc k) * algebraMap k (RatFunc k) j =
        (2 : RatFunc k) * algebraMap k (RatFunc k) (2 * j) := by
      rw [map_mul, map_ofNat]
      ring
    rw [hode, hrhs]
  have hide := ratFuncOde_to_polynomial610 (H := H) Q (2 * j) hode'
  exact ⟨Q.num, Q.denom, Q.denom_ne_zero, hide⟩

/-- Source-facing ODE kill on a quadratic nonsquare core. -/
theorem alignedNonsquareDegreeZeroPrimitive610_false
    (p q : k[X][X]) (j : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (haligned : (5 : k[X]) * p.coeff 5 * H ^ 2 -
      (3 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j))
    (hj : j ≠ 0) (hdeg : H.natDegree = 2) : False := by
  obtain ⟨n, d, hd, hide⟩ :=
    alignedNonsquareDegreeZeroPrimitive610_clearedOde (H := H)
      p q j hp hq hp6 hq10 haligned hD
  have h2j : (2 : k) * j ≠ 0 := mul_ne_zero (by norm_num) hj
  exact quadraticCoreOde_no_polynomial_solution610 H n d (2 * j) hdeg hd h2j hide

end AlignedNonsquarePrimitiveField610

/-! ## Chamber exclusion and scale-two closure -/

section AlignedNonsquareChamber610

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **CLOSED.** The remaining aligned-nonsquare exclusion of the
normalized `(6,10)` scale-two route. -/
theorem planeKeller610AlignedNonsquareExclusion_closed :
    PlaneKeller610AlignedNonsquareExclusion (K := K) := by
  intro P Q H hsource hnonsquare hN
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  letI : NonsquarePolynomial46 H := ⟨hnonsquare⟩
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp6src, hq10src, hKeller⟩
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6 : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6src
  have hq10 : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10src
  have haligned : (5 : K[X]) * p.coeff 5 * H ^ 2 -
      (3 : K[X]) * q.coeff 9 = 0 := by
    simpa only [p, q] using hN
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  exact alignedNonsquareDegreeZeroPrimitive610_false (H := H)
    p q j hp hq hp6 hq10 haligned hD hj hHdegree

/-- **CLOSED.** The remaining aligned scale-two source of the
normalized `(6,10)` route, modulo the leftover scale-zero residual. -/
theorem planeKellerNormalized610LowScaleRoute_of_scaleZero
    (hzero : ∀ (P Q : MvPolynomial (Fin 2) K) (H : K[X]),
      Normalized610LeadingCoreSource P Q H 0 → False) :
    PlaneKellerNormalized610LowScaleRoute (K := K) :=
  planeKellerNormalized610LowScaleRoute_of_alignedExclusions
    hzero
    planeKeller610AlignedSquareExclusion_closed
    planeKeller610AlignedNonsquareExclusion_closed

end AlignedNonsquareChamber610

#print axioms quadraticCoreOde_no_polynomial_solution610
#print axioms alignedNonsquareDegreeZeroPrimitive610_deriv
#print axioms alignedNonsquareDegreeZeroPrimitive610_eq_mul_root
#print axioms alignedNonsquareDegreeZeroPrimitive610_false
#print axioms planeKeller610AlignedNonsquareExclusion_closed
#print axioms planeKellerNormalized610LowScaleRoute_of_scaleZero

end Max11DegreeRoutes
