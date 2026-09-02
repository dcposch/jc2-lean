import Grok68AlignedSquareClearedNumeratorScratch
import LowScale68ScaleTwoLocalDerivativeRowTwo

/-! # Finite-order ceiling of the `(6,8)` aligned-square pole tower

Lane T of `Grok68AlignedSquareTowerPlanScratch.md`.  Parent (tracked,
green): `Grok68AlignedSquareClearedNumeratorScratch.lean`, which lands
`alignedSquareClearedNumerator68_eq_pow_mul_primitive` (`algebraMap N =
(algebraMap h0)^65 * (RatFunc.C 5642219814912 * primitive)`) and
`alignedSquarePrimitive68_scaledDeriv_eq_simplePole` (with
`rho' = C j / h0` as a hypothesis).  Native arithmetic is base order
`0`, remaining pole `65`, ceiling `65`.

This file restates the generic holomorphic-remainder induction of
`Grok610AlignedSquareTowerOrders69to75Scratch.lean` (lines ~95–207)
and the per-order head obstruction of
`Grok610AlignedSquareSourceWrapperScratch.lean` /
`Grok810DegreeZeroPoleAndClearingScratch.lean`, specialised only by
the `(6,8)` suffix.  The lemmas are degree-agnostic in the remaining
pole `n`.  Instantiating at `n = 65` on the lane-C clearing identity
gives `alignedSquareFace68_order65Grandchildren : False` on the same
hypotheses as `alignedSquareFace610_order75Grandchildren`: `hclear`,
`hderiv`, `hj`, with `h0` linear and a root `a`.

`hderiv` is kept as a hypothesis (lanes P1 + W supply it).  The
source-primitive identity is not re-proved here.  No chamber is closed.
There is no unused compact-numerator order after `65`.

No `sorry`, no new axioms, no finite-root shortcut, no closure
overclaim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Bookkeeping: base order `0`, remaining pole `65`, ceiling `65` -/

/-- Ordinary pole of `ρ'` supplied by the Jacobian: `ρ' = C(j)/h₀`. -/
def alignedSquareDerivativePoleOrder68 : ℕ := 1

/-- Lowest surviving power of `h` in the unpeeled compact numerator. -/
def alignedSquareBaseOrder68 : ℕ := 0

/-- Remaining pole of `ρ` with no MixedPair peel: `65 - 0 = 65`. -/
def alignedSquareRemainingPole68 : ℕ := 65

/-- Vanishing multiplicity of the compact numerator through the ceiling:
the holomorphic remainder is `h₀^{65}`. -/
def alignedSquareTowerCeilingDivisibility68 : ℕ := 65

/-- Remaining pole after the ceiling order. -/
def alignedSquareTowerRemainingPoleAfterCeiling68 : ℕ := 0

theorem alignedSquareDerivativePoleOrder68_eq :
    alignedSquareDerivativePoleOrder68 = 1 :=
  rfl

theorem alignedSquareBaseOrder68_eq :
    alignedSquareBaseOrder68 = 0 :=
  rfl

theorem alignedSquareRemainingPole68_eq :
    alignedSquareRemainingPole68 = 65 :=
  rfl

theorem alignedSquareTowerCeilingDivisibility68_eq :
    alignedSquareTowerCeilingDivisibility68 = 65 :=
  rfl

theorem alignedSquareTowerRemainingPoleAfterCeiling68_eq :
    alignedSquareTowerRemainingPoleAfterCeiling68 = 0 :=
  rfl

theorem alignedSquareRemainingPole68_eq_sub :
    alignedSquareRemainingPole68 =
      alignedSquareSourceClearingPower68 - alignedSquareBaseOrder68 :=
  rfl

theorem alignedSquareRemainingPole68_eq_ceiling :
    alignedSquareRemainingPole68 = alignedSquareTowerCeiling68 :=
  rfl

theorem alignedSquareTowerCeilingDivisibility68_eq_remaining :
    alignedSquareTowerCeilingDivisibility68 =
      alignedSquareRemainingPole68 :=
  rfl

theorem alignedSquareTowerCeiling68_eq_add :
    alignedSquareTowerCeiling68 =
      alignedSquareBaseOrder68 + alignedSquareRemainingPole68 :=
  rfl

#print axioms alignedSquareRemainingPole68_eq_sub
#print axioms alignedSquareRemainingPole68_eq_ceiling
#print axioms alignedSquareTowerCeilingDivisibility68_eq_remaining
#print axioms alignedSquareTowerCeiling68_eq_add

/-! ## Linear divisibility and clearing cancellation -/

section AlignedSquareTowerDvd68

variable {k : Type*} [Field k]

/-- A degree-one polynomial divides every polynomial vanishing at its
unique root. -/
theorem alignedSquare_linearPolynomial_dvd_of_eval_eq_zero68
    (h0 f : k[X]) (a : k) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hf : f.eval a = 0) : h0 ∣ f := by
  have hlinearRoot : X - C a ∣ f := Polynomial.dvd_iff_isRoot.mpr hf
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by simpa [← hlinear] using hroot
  have hd : d = -(c * a) := by linear_combination hca
  have hfactor : h0 = C c * (X - C a) := by
    calc
      h0 = C c * X + C d := hlinear.symm
      _ = C c * X - C (c * a) := by rw [hd, map_neg]; ring
      _ = C c * (X - C a) := by rw [mul_sub, ← map_mul]
  have hscaleDvd : h0 ∣ X - C a := by
    refine ⟨C c⁻¹, ?_⟩
    rw [hfactor]
    calc
      X - C a = 1 * (X - C a) := by rw [one_mul]
      _ = (C c * C c⁻¹) * (X - C a) := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]
      _ = C c * (X - C a) * C c⁻¹ := by ring
  exact hscaleDvd.trans hlinearRoot

/-- Cancel `m` polynomial powers from a pole-`(m+n)` clearing. -/
theorem alignedSquare_algebraMap_cancel_pow68
    (h0 Q : k[X]) (rho : RatFunc k) (m n : ℕ) (hh0 : h0 ≠ 0)
    (hclear :
      algebraMap k[X] (RatFunc k) (h0 ^ m * Q) =
        (algebraMap k[X] (RatFunc k) h0) ^ (m + n) * rho) :
    algebraMap k[X] (RatFunc k) Q =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero m hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ m * Q) =
        hRF ^ m * algebraMap k[X] (RatFunc k) Q := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ m * algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k) (h0 ^ m * Q) := hmapPow.symm
    _ = hRF ^ (m + n) * rho := hclear
    _ = hRF ^ m * (hRF ^ n * rho) := by
      rw [pow_add]
      ring

/-- Cancel one polynomial power of a linear clearing. -/
theorem alignedSquare_algebraMap_cancel_one_clearing68
    (h0 old new : k[X]) (rho : RatFunc k) (r : ℕ) (hh0 : h0 ≠ 0)
    (hfact : old = h0 * new)
    (hclear : algebraMap k[X] (RatFunc k) old =
      (algebraMap k[X] (RatFunc k) h0) ^ (r + 1) * rho) :
    algebraMap k[X] (RatFunc k) new =
      (algebraMap k[X] (RatFunc k) h0) ^ r * rho :=
  alignedSquare_algebraMap_cancel_pow68 h0 new rho 1 r hh0
    (by
      have hclear' :
          algebraMap k[X] (RatFunc k) (h0 * new) =
            (algebraMap k[X] (RatFunc k) h0) ^ (1 + r) * rho := by
        simpa [hfact, add_comm r 1] using hclear
      simpa [pow_one] using hclear')

#print axioms alignedSquare_linearPolynomial_dvd_of_eval_eq_zero68
#print axioms alignedSquare_algebraMap_cancel_pow68
#print axioms alignedSquare_algebraMap_cancel_one_clearing68

end AlignedSquareTowerDvd68

/-! ## Per-order head obstruction -/

section AlignedSquareLocalPole68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareLocalPoleHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Per-order head obstruction.  A rational function with a simple pole
`C j / h0` at a linear root cannot be `h0^n` times a holomorphic-at-the-root
object with nonvanishing head: if `h₀ⁿ ρ` is polynomial for `n ≠ 0` and
`ρ'` is the simple pole, then the exponent-`-n` Hahn coefficient of `ρ`
vanishes, so the numerator evaluates to zero at the linear root.  The
relevant derivative coefficient is at exponent `-(n+1)`, which is
distinct from `-1`. -/
theorem alignedSquare_localLinearPole_head_eval_zero68
    (n : ℕ) (hn : n ≠ 0) (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 := by
  obtain ⟨c, hc, hsingle, hscaleDeriv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 a hdegree hroot
  have hrhoBoundary := localHahn_coeff_neg_of_cleared a c h0 A0 rho n hc
    hsingle hclear
  have hderivBoundary := localHahn_deriv_coeff_neg_succ_of_cleared
    a c h0 A0 rho n hc hsingle hscaleDeriv hclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hderiv
  have hne : (-(n : ℚ) - 1) ≠ -(1 : ℚ) := by
    intro h
    have : -(n : ℚ) = 0 := by linear_combination h
    exact hn (Nat.cast_eq_zero.mp (neg_eq_zero.mp this))
  have hderivFar :
      (ratFuncAtHahn46 a (Differential.deriv rho)).coeff
        (-(n : ℚ) - 1) = 0 := by
    have hcoeff := congrArg
      (fun z : HahnSeries ℚ k ↦ z.coeff (-(n : ℚ) - 1)) hmapped
    simpa only [div_eq_mul_inv, map_mul, map_inv₀, ratFuncAtHahn46_C,
      hsingle, HahnSeries.inv_single, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, HahnSeries.coeff_single_of_ne hne,
      smul_zero] using hcoeff
  have hrhoZero : (ratFuncAtHahn46 a rho).coeff (-(n : ℚ)) = 0 := by
    have hnC : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [hderivFar, neg_mul] at hderivBoundary
    have hprod :
        (n : k) * (ratFuncAtHahn46 a rho).coeff (-(n : ℚ)) = 0 :=
      neg_eq_zero.mp hderivBoundary.symm
    exact (mul_eq_zero.mp hprod).resolve_left hnC
  rw [hrhoZero] at hrhoBoundary
  have hcinv : (c ^ n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero n hc)
  exact (mul_eq_zero.mp hrhoBoundary.symm).resolve_left hcinv

/-- Order-`65` specialisation matching the unpeeled remaining pole. -/
theorem alignedSquare_poleSixtyFive_head_eval_zero68
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole68 *
        rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 :=
  alignedSquare_localLinearPole_head_eval_zero68
    alignedSquareRemainingPole68 (by decide) a j h0 A0 rho hdegree
    hroot hclear hderiv

#print axioms alignedSquare_localLinearPole_head_eval_zero68
#print axioms alignedSquare_poleSixtyFive_head_eval_zero68

end AlignedSquareLocalPole68

/-! ## Holomorphic remainder (remaining pole `0`) -/

section AlignedSquarePoleZero68

variable {k : Type*} [Field k] [CharZero k]

/-- Cancel every polynomial power from a pole-`n` clearing.  The
remaining factor *is* `rho`. -/
theorem alignedSquare_algebraMap_cancel_all_clearing68
    (h0 Q : k[X]) (rho : RatFunc k) (n : ℕ) (hh0 : h0 ≠ 0)
    (hquot :
      algebraMap k[X] (RatFunc k) (h0 ^ n * Q) =
        (algebraMap k[X] (RatFunc k) h0) ^ n * rho) :
    algebraMap k[X] (RatFunc k) Q = rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero n hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ n * Q) =
        hRF ^ n * algebraMap k[X] (RatFunc k) Q := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ n * algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k) (h0 ^ n * Q) := hmapPow.symm
    _ = hRF ^ n * rho := hquot

/-- A rational function that is the image of a polynomial cannot have
derivative `C j / h0` with `j ≠ 0`: evaluating `h0 * (remaining)' = C j`
at the simple root forces `j = 0`. -/
theorem alignedSquare_C_eq_zero_of_deriv_eq_simplePole68
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k) (hh0 : h0 ≠ 0)
    (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 = rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    j = 0 := by
  have hhRF : algebraMap k[X] (RatFunc k) h0 ≠ 0 :=
    RatFunc.algebraMap_ne_zero hh0
  have hderivA :
      algebraMap k[X] (RatFunc k) (derivative A0) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hderiv, ← hclear, GCD369RatFuncDerivative]
  have hpoly : h0 * derivative A0 = Polynomial.C j := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    rw [map_mul, hderivA, mul_div_cancel₀ _ hhRF]
    simp only [RatFunc.algebraMap_C]
  have heval := congrArg (fun p : k[X] ↦ p.eval a) hpoly
  have heval' : (0 : k) = j := by
    simpa [hroot, Polynomial.eval_mul, Polynomial.eval_C] using heval
  exact heval'.symm

/-- Cancel-and-expose: if `h0^n` divides the cleared numerator, the
remaining factor *is* `rho`, so the simple-pole equation forces `j = 0`. -/
theorem alignedSquare_of_pow_dvd_simplePole_eval68
    (a j : k) (h0 A0 Q : k[X]) (rho : RatFunc k) (n : ℕ)
    (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0) (hA : A0 = h0 ^ n * Q)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    j = 0 :=
  alignedSquare_C_eq_zero_of_deriv_eq_simplePole68 a j h0 Q rho hh0
    hroot
    (alignedSquare_algebraMap_cancel_all_clearing68 h0 Q rho n hh0
      (by simpa [hA] using hclear))
    hderiv

/-- At the ceiling the leftover numerator is `rho` itself, and
`rho' = C j / h0` with `j ≠ 0` is False. -/
theorem alignedSquare_of_pow_dvd_simplePole_ne_zero68
    (a j : k) (h0 A0 Q : k[X]) (rho : RatFunc k) (n : ℕ)
    (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0) (hA : A0 = h0 ^ n * Q)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False :=
  hj (alignedSquare_of_pow_dvd_simplePole_eval68 a j h0 A0 Q rho n hh0
    hroot hA hclear hderiv)

/-- Successive remaining-numerator peels: a pole-`n` numerator of a
simple-pole rational function is divisible by `h₀^n`.  Each successor
step is the parent head obstruction plus one linear cancellation; the
`n = 0` remainder is the holomorphic case.  Instantiating up to the
ceiling `n = 65` is the native `(6,8)` remaining pole. -/
theorem alignedSquare_pow_dvd_of_remaining_pole68
    (h0 Q : k[X]) (rho : RatFunc k) (j a : k) (n : ℕ)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) Q =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ n ∣ Q := by
  induction n generalizing Q with
  | zero =>
    refine ⟨Q, ?_⟩
    simp
  | succ n ih =>
    have hQ0 : Q.eval a = 0 :=
      alignedSquare_localLinearPole_head_eval_zero68 (n + 1)
        (Nat.succ_ne_zero n) a j h0 Q rho hdegree hroot
        (by simpa [Nat.succ_eq_add_one] using hclear) hderiv
    obtain ⟨Qnew, hfact⟩ :=
      alignedSquare_linearPolynomial_dvd_of_eval_eq_zero68 h0 Q a
        hdegree hroot hQ0
    have hclear' :
        algebraMap k[X] (RatFunc k) Qnew =
          (algebraMap k[X] (RatFunc k) h0) ^ n * rho :=
      alignedSquare_algebraMap_cancel_one_clearing68 h0 Q Qnew rho n
        hh0 hfact
        (by simpa [Nat.succ_eq_add_one, add_comm n 1] using hclear)
    obtain ⟨R, hR⟩ := ih Qnew hclear'
    refine ⟨R, ?_⟩
    calc
      Q = h0 * Qnew := hfact
      _ = h0 * (h0 ^ n * R) := by rw [hR]
      _ = h0 ^ (n + 1) * R := by ring

#print axioms alignedSquare_algebraMap_cancel_all_clearing68
#print axioms alignedSquare_C_eq_zero_of_deriv_eq_simplePole68
#print axioms alignedSquare_of_pow_dvd_simplePole_eval68
#print axioms alignedSquare_of_pow_dvd_simplePole_ne_zero68
#print axioms alignedSquare_pow_dvd_of_remaining_pole68

end AlignedSquarePoleZero68

/-! ## Source-facing cancel-and-expose at the ceiling `n = 65` -/

section AlignedSquareTowerCeilingHeads68

variable {k : Type*} [Field k] [CharZero k]

/-- The compact numerator, as a pole-`65` numerator of a simple-pole
rational function, is divisible by `h₀^{65}`. -/
theorem alignedSquareClearedNumerator68_pow_sixtyFive_dvd
    (h0 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareClearedNumerator68 h0 a5 a4 a3 a2 a1 a0 b7 b6 b5
            b4 b3 b2 b1 b0) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole68 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ alignedSquareTowerCeilingDivisibility68 ∣
      alignedSquareClearedNumerator68 h0 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4
        b3 b2 b1 b0 := by
  simpa [alignedSquareTowerCeilingDivisibility68,
    alignedSquareRemainingPole68] using
    alignedSquare_pow_dvd_of_remaining_pole68 h0
      (alignedSquareClearedNumerator68 h0 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4
        b3 b2 b1 b0)
      rho j a 65 hh0 hdegree hroot hclear hderiv

#print axioms alignedSquareClearedNumerator68_pow_sixtyFive_dvd

/-- Source-facing joint order-`65` packet of the aligned-square `(6,8)`
compact numerator.  After `h₀^{65}` the remaining factor is `rho`;
`j ≠ 0` is impossible.  The chamber is not closed on the raw source
hypotheses: `hderiv` remains a hypothesis (lanes P1 + W), and the
lane-C identity identifying the compact numerator with a clearing of
the weight-13 primitive is not re-proved here. -/
theorem alignedSquareFace68_order65Grandchildren
    (h0 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareClearedNumerator68 h0 a5 a4 a3 a2 a1 a0 b7 b6 b5
            b4 b3 b2 b1 b0) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole68 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨Q, hQ⟩ :=
    alignedSquareClearedNumerator68_pow_sixtyFive_dvd h0 a5 a4 a3 a2 a1
      a0 b7 b6 b5 b4 b3 b2 b1 b0 rho j a hh0 hdegree hroot hclear hderiv
  have hclear65 :
      algebraMap k[X] (RatFunc k)
          (alignedSquareClearedNumerator68 h0 a5 a4 a3 a2 a1 a0 b7 b6 b5
            b4 b3 b2 b1 b0) =
        (algebraMap k[X] (RatFunc k) h0) ^ 65 * rho := by
    simpa [alignedSquareRemainingPole68] using hclear
  exact alignedSquare_of_pow_dvd_simplePole_ne_zero68 a j h0
    (alignedSquareClearedNumerator68 h0 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4
      b3 b2 b1 b0)
    Q rho 65 hh0 hroot hQ hclear65 hderiv hj

#print axioms alignedSquareFace68_order65Grandchildren

end AlignedSquareTowerCeilingHeads68

end Max11DegreeRoutes
