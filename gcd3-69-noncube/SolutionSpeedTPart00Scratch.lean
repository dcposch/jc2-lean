/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), OpenAI Codex agent (formalization)
-/
import Lean.Parser.Command
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Ring.RingNF

/-!
# The source-facing noncube gate at partial degrees `(6,9)`

This module starts from a literal normalized bivariate Keller source,
constructs and aligns its nontrivial cubic-Kummer branch, extracts the lower
rows, derives the invariant two-sheet split, and excludes the zero sheet, the
constant and nonconstant elliptic cases, and the special shifted
Davenport--Stothers fibre.  The reduced function-field presentations used in
the terminal exclusions are constructed internally.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option Elab.async false

open Polynomial
open scoped BigOperators

set_option maxHeartbeats 64000000 in
/-- The degree-six member of the aligned eight-high-row normal form. -/
noncomputable def GCD369AlignedF {K : Type*} [Field K]
    (a0 a1 a2 a3 a4 : K) : K[X] :=
  X ^ 6 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0

set_option maxHeartbeats 64000000 in
/-- The degree-nine member of the aligned eight-high-row normal form, with
the sole surviving high-row integration constant `kappa`. -/
noncomputable def GCD369AlignedG {K : Type*} [Field K]
    (a0 a1 a2 a3 a4 kappa : K) : K[X] :=
  X ^ 9
    + C (3 * a4 / 2) * X ^ 7
    + C (3 * a3 / 2) * X ^ 6
    + C (3 * (4 * a2 + a4 ^ 2) / 8) * X ^ 5
    + C (3 * (2 * a1 + a3 * a4) / 4) * X ^ 4
    + C ((24 * a0 + 12 * a2 * a4 + 6 * a3 ^ 2 - a4 ^ 3) / 16) * X ^ 3
    + C (3 * (4 * a1 * a4 + 4 * a2 * a3 - a3 * a4 ^ 2) / 16) * X ^ 2
    + C (3 * (32 * a0 * a4 + 32 * a1 * a3 + 16 * a2 ^ 2
        - 8 * a2 * a4 ^ 2 - 8 * a3 ^ 2 * a4 + a4 ^ 4) / 128) * X
    + C ((24 * a0 * a3 + 24 * a1 * a2 - 6 * a1 * a4 ^ 2
        - 12 * a2 * a3 * a4 - 2 * a3 ^ 3 + 3 * a3 * a4 ^ 3) / 32)
    + C kappa * (X ^ 3 + C (a4 / 2) * X + C (a3 / 2))

set_option maxHeartbeats 64000000 in
/-- A general monic, simultaneously depressed degree-nine member before the
eight high source rows have been integrated. -/
noncomputable def GCD369DepressedG {K : Type*} [Field K]
    (b0 b1 b2 b3 b4 b5 b6 b7 : K) : K[X] :=
  X ^ 9 + C b7 * X ^ 7 + C b6 * X ^ 6 + C b5 * X ^ 5
    + C b4 * X ^ 4 + C b3 * X ^ 3 + C b2 * X ^ 2 + C b1 * X + C b0

set_option maxHeartbeats 64000000 in
/-- Differentiate a bivariate source polynomial coefficientwise in its inner
`x` variable while retaining its outer `y` variable. -/
noncomputable def GCD369SourceXDeriv {k : Type*} [CommRing k]
    (p : k[X][X]) : k[X][X] :=
  PolynomialModule.equivPolynomialSelf (Polynomial.derivative'.mapCoeffs p)

set_option maxHeartbeats 64000000 in
@[simp] theorem GCD369SourceXDeriv_coeff {k : Type*} [CommRing k]
    (p : k[X][X]) (n : ℕ) :
    (GCD369SourceXDeriv p).coeff n = (p.coeff n).derivative := by
  rfl

set_option maxHeartbeats 64000000 in
/-- The complete aligned presentation produced from a Kummer source,
including coefficient weights, invariant `kappa`, terminal bracket, and the
two inessential constant target gauges. -/
def GCD369KummerAlignedPresentation
    {K : Type*} [Field K] [Differential K]
    (sigma : K ≃+* K) (omega s terminal : K) (P Q : K[X]) : Prop :=
  ∃ r a0 a1 a2 a3 a4 c6 kappa c0 : K,
    sigma r = omega * r ∧
    P.comp (C s⁻¹ * (X - C r)) = GCD369AlignedF a0 a1 a2 a3 a4 ∧
    sigma a0 = a0 ∧ sigma a1 = omega ^ 2 * a1 ∧
    sigma a2 = omega * a2 ∧ sigma a3 = a3 ∧
    sigma a4 = omega ^ 2 * a4 ∧ sigma kappa = kappa ∧
    Differential.deriv c6 = 0 ∧ Differential.deriv kappa = 0 ∧
    Differential.deriv c0 = 0 ∧
    (Differential.mapCoeffs (GCD369AlignedF a0 a1 a2 a3 a4) *
        derivative (GCD369AlignedG a0 a1 a2 a3 a4 kappa) -
      derivative (GCD369AlignedF a0 a1 a2 a3 a4) *
        Differential.mapCoeffs (GCD369AlignedG a0 a1 a2 a3 a4 kappa) =
      C (terminal / s)) ∧
    Q.comp (C s⁻¹ * (X - C r)) =
      GCD369AlignedG a0 a1 a2 a3 a4 kappa +
        C c6 * (P.comp (C s⁻¹ * (X - C r))) + C c0

set_option maxHeartbeats 64000000 in
/-- Ambient Kummer data together with the complete aligned presentation,
packaged for the literal polynomial-source theorem. -/
def GCD369KummerAlignedSourcePackage
    {k F K : Type*} [Field k] [Field F] [Field K]
    [Algebra k K] [Algebra F K] [Differential K]
    (sigma : K ≃+* K) (omega s h terminal : K) (P Q : K[X]) : Prop :=
  s ≠ 0 ∧ sigma s = omega * s ∧ s ^ 3 = h ∧
  (∀ u : F, sigma (algebraMap F K u) = algebraMap F K u) ∧
  (∀ c : K, Differential.deriv c = 0 →
    ∃ c0 : k, c = algebraMap k K c0) ∧
  (∀ c : K, Differential.deriv c = 0 → sigma c = c) ∧
  GCD369KummerAlignedPresentation sigma omega s terminal P Q

set_option maxHeartbeats 64000000 in
/-- Coefficient differentiation obeys the full chain rule for polynomial
composition.  The second summand records motion of the substituted
polynomial. -/
theorem GCD369MapCoeffsComp
    {K : Type*} [CommRing K] [Differential K] (p t : K[X]) :
    Differential.mapCoeffs (p.comp t) =
      (Differential.mapCoeffs p).comp t
        + (derivative p).comp t * Differential.mapCoeffs t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [add_comp, map_add, derivative_add, hp, hq]
      ring
  | monomial n a =>
      simp only [monomial_comp, Derivation.leibniz, Derivation.leibniz_pow,
        Differential.mapCoeffs_C, Differential.mapCoeffs_monomial,
        derivative_monomial, C_eq_natCast, mul_comp, C_comp, X_comp,
        pow_comp, map_mul]
      ring

set_option maxHeartbeats 64000000 in
/-- Simultaneous substitution in two differential polynomials cancels the
motion of the substituted variable in their coefficient bracket. -/
theorem GCD369BracketComp
    {K : Type*} [CommRing K] [Differential K] (p q t : K[X]) :
    Differential.mapCoeffs (p.comp t) * derivative (q.comp t)
        - derivative (p.comp t) * Differential.mapCoeffs (q.comp t) =
      derivative t *
        ((Differential.mapCoeffs p * derivative q
            - derivative p * Differential.mapCoeffs q).comp t) := by
  rw [GCD369MapCoeffsComp, GCD369MapCoeffsComp,
    derivative_comp, derivative_comp]
  simp only [sub_comp, mul_comp]
  ring

set_option maxHeartbeats 64000000 in
/-- For the source change of variable `y = s⁻¹ (z-r)`, the transformed
coefficient bracket is exactly `s⁻¹` times the transformed source
bracket.  In particular a constant Keller bracket `j` becomes `j/s`. -/
theorem GCD369AffineBracket
    {K : Type*} [Field K] [Differential K]
    (p q : K[X]) (s r j : K) (hs : s ≠ 0)
    (hD : Differential.mapCoeffs p * derivative q
        - derivative p * Differential.mapCoeffs q = C j) :
    let t : K[X] := C s⁻¹ * (X - C r)
    Differential.mapCoeffs (p.comp t) * derivative (q.comp t)
        - derivative (p.comp t) * Differential.mapCoeffs (q.comp t) =
      C (j / s) := by
  dsimp only
  rw [GCD369BracketComp, hD]
  simp only [derivative_mul, derivative_C, derivative_sub, derivative_X,
    zero_mul, zero_add, sub_zero, mul_one, C_comp]
  rw [← C_mul]
  congr 1
  field_simp

set_option maxHeartbeats 64000000 in
/-- Constant target shear and target translation do not change the
differential polynomial bracket. -/
theorem GCD369ConstantTargetShearBracket
    {K : Type*} [CommRing K] [Differential K]
    (f g : K[X]) (c6 c0 : K)
    (hc6 : Differential.deriv c6 = 0) (hc0 : Differential.deriv c0 = 0) :
    Differential.mapCoeffs f * derivative (g + C c6 * f + C c0)
        - derivative f * Differential.mapCoeffs (g + C c6 * f + C c0) =
      Differential.mapCoeffs f * derivative g
        - derivative f * Differential.mapCoeffs g := by
  simp [Derivation.leibniz, hc6, hc0]
  ring

set_option maxHeartbeats 64000000 in
/-- A degree-six source polynomial with leading rows `s⁶` and `6rs⁵`
becomes exactly the aligned monic degree-six form after the affine change
`y = s⁻¹(z-r)`. -/
theorem GCD369AffineDegreeSixNormalForm
    {K : Type*} [Field K] (p : K[X]) (s r : K) (hs : s ≠ 0)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = s ^ 6)
    (hp5 : p.coeff 5 = s ^ 5 * (6 * r)) :
    let t : K[X] := C s⁻¹ * (X - C r)
    ∃ a0 a1 a2 a3 a4 : K,
      p.comp t = GCD369AlignedF a0 a1 a2 a3 a4 := by
  dsimp only
  let t : K[X] := C s⁻¹ * (X - C r)
  let f := p.comp t
  have ht : t.natDegree = 1 := by
    dsimp [t]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hs),
      Polynomial.natDegree_X_sub_C]
  have hfdeg : f.natDegree ≤ 6 := by
    calc
      f.natDegree ≤ p.natDegree * t.natDegree := Polynomial.natDegree_comp_le
      _ = 6 := by rw [hp, ht]
  have hpExpand :
      p = ∑ i ∈ Finset.range 7, C (p.coeff i) * X ^ i :=
    p.as_sum_range_C_mul_X_pow' (by omega)
  have hcomp := congrArg (fun u : K[X] ↦ u.comp t) hpExpand
  norm_num [Finset.sum_range_succ] at hcomp
  rw [hp5, hp6] at hcomp
  let low : K[X] := C (p.coeff 0) + C (p.coeff 1) * t
    + C (p.coeff 2) * t ^ 2 + C (p.coeff 3) * t ^ 3
    + C (p.coeff 4) * t ^ 4
  let top : K[X] := C (s ^ 5 * (6 * r)) * t ^ 5 + C (s ^ 6) * t ^ 6
  have hdecomp : f = low + top := by
    dsimp [f, low, top]
    rw [hcomp]
    ring
  have htermZero (a : K) (i n : ℕ) (hi : i ≤ 4) (hn : 4 < n) :
      (C a * t ^ i).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc
      (C a * t ^ i).natDegree ≤ (C a).natDegree + (t ^ i).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + i * t.natDegree := by
        gcongr
        · rw [Polynomial.natDegree_C]
        · exact Polynomial.natDegree_pow_le
      _ = i := by rw [ht]; simp
      _ ≤ 4 := hi
      _ < n := hn
  have hlowCoeff (n : ℕ) (hn : 4 < n) : low.coeff n = 0 := by
    dsimp [low]
    simp only [coeff_add]
    have h0 : (C (p.coeff 0)).coeff n = 0 := by
      rw [coeff_C, if_neg (by omega)]
    have h1 : (C (p.coeff 1) * t).coeff n = 0 := by
      simpa using htermZero (p.coeff 1) 1 n (by norm_num) hn
    rw [h0, h1, htermZero (p.coeff 2) 2 n (by norm_num) hn,
      htermZero (p.coeff 3) 3 n (by norm_num) hn,
      htermZero (p.coeff 4) 4 n (by norm_num) hn]
    norm_num
  have hscale5 : C (s ^ 5 * (6 * r)) * C s⁻¹ ^ 5 = C (6 * r) := by
    rw [← C_pow, ← C_mul]
    congr 1
    field_simp [hs]
  have hscale6 : C (s ^ 6) * C s⁻¹ ^ 6 = 1 := by
    rw [← C_pow, ← C_mul]
    have hs6 : s ^ 6 * s⁻¹ ^ 6 = 1 := by field_simp [hs]
    rw [hs6, C_1]
  have htop : top = C (6 * r) * (X - C r) ^ 5 + (X - C r) ^ 6 := by
    dsimp [top, t]
    calc
      C (s ^ 5 * (6 * r)) * (C s⁻¹ * (X - C r)) ^ 5
            + C (s ^ 6) * (C s⁻¹ * (X - C r)) ^ 6 =
          (C (s ^ 5 * (6 * r)) * C s⁻¹ ^ 5) * (X - C r) ^ 5
            + (C (s ^ 6) * C s⁻¹ ^ 6) * (X - C r) ^ 6 := by ring
      _ = C (6 * r) * (X - C r) ^ 5 + (X - C r) ^ 6 := by
        rw [hscale5, hscale6, one_mul]
  have htopFactor : top = (X - C r) ^ 5 * (X + C (5 * r)) := by
    rw [htop]
    simp only [C_mul, C_ofNat, C_eq_natCast]
    ring
  have hmSub : (X - C r : K[X]).Monic := Polynomial.monic_X_sub_C r
  have hmAdd : (X + C (5 * r) : K[X]).Monic :=
    Polynomial.monic_X_add_C (5 * r)
  have hmPow : ((X - C r : K[X]) ^ 5).Monic := hmSub.pow 5
  have htopMonic : top.Monic := by
    rw [htopFactor]
    exact hmPow.mul hmAdd
  have htopDegree : top.natDegree = 6 := by
    rw [htopFactor, Polynomial.natDegree_mul hmPow.ne_zero hmAdd.ne_zero,
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
      Polynomial.natDegree_X_add_C]
  have htop6 : top.coeff 6 = 1 := by
    rw [← htopDegree, coeff_natDegree, htopMonic.leadingCoeff]
  have htop5 : top.coeff 5 = 0 := by
    have hnxt : top.nextCoeff = 0 := by
      rw [htopFactor, hmPow.nextCoeff_mul hmAdd, hmSub.nextCoeff_pow,
        Polynomial.nextCoeff_X_sub_C, Polynomial.nextCoeff_X_add_C]
      simp [nsmul_eq_mul]
    simpa [Polynomial.nextCoeff, htopDegree] using hnxt
  have hf6 : f.coeff 6 = 1 := by
    rw [hdecomp, coeff_add, hlowCoeff 6 (by norm_num), htop6, zero_add]
  have hf5 : f.coeff 5 = 0 := by
    rw [hdecomp, coeff_add, hlowCoeff 5 (by norm_num), htop5, add_zero]
  refine ⟨f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3, f.coeff 4, ?_⟩
  change f = GCD369AlignedF (f.coeff 0) (f.coeff 1) (f.coeff 2)
    (f.coeff 3) (f.coeff 4)
  apply Polynomial.ext
  intro n
  by_cases hn : n ≤ 6
  · interval_cases n <;>
      simp [GCD369AlignedF, hf5, hf6, coeff_add, coeff_C,
        coeff_mul_X_pow', coeff_X, coeff_X_pow]
  · have hfn : f.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
        (hfdeg.trans_lt (not_le.mp hn))
    rw [hfn]
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    have hn6 : n ≠ 6 := by omega
    simp [GCD369AlignedF, coeff_add, coeff_C, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow, hn0, hn1, hn2, hn3, hn4, hn6,
      show n - 4 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 2 ≠ 0 by omega, show 1 ≠ n by omega]

set_option maxHeartbeats 64000000 in
/-- A degree-nine source polynomial with leading rows `s⁹` and `9rs⁸`
becomes exactly the general monic depressed degree-nine form after the same
affine change `y = s⁻¹(z-r)`. -/
theorem GCD369AffineDegreeNineNormalForm
    {K : Type*} [Field K] (q : K[X]) (s r : K) (hs : s ≠ 0)
    (hq : q.natDegree = 9) (hq9 : q.coeff 9 = s ^ 9)
    (hq8 : q.coeff 8 = s ^ 8 * (9 * r)) :
    let t : K[X] := C s⁻¹ * (X - C r)
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : K,
      q.comp t = GCD369DepressedG b0 b1 b2 b3 b4 b5 b6 b7 := by
  dsimp only
  let t : K[X] := C s⁻¹ * (X - C r)
  let g := q.comp t
  have ht : t.natDegree = 1 := by
    dsimp [t]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hs),
      Polynomial.natDegree_X_sub_C]
  have hgdeg : g.natDegree ≤ 9 := by
    calc
      g.natDegree ≤ q.natDegree * t.natDegree := Polynomial.natDegree_comp_le
      _ = 9 := by rw [hq, ht]
  have hqExpand :
      q = ∑ i ∈ Finset.range 10, C (q.coeff i) * X ^ i :=
    q.as_sum_range_C_mul_X_pow' (by omega)
  have hcomp := congrArg (fun u : K[X] ↦ u.comp t) hqExpand
  norm_num [Finset.sum_range_succ] at hcomp
  rw [hq8, hq9] at hcomp
  let low : K[X] := C (q.coeff 0) + C (q.coeff 1) * t
    + C (q.coeff 2) * t ^ 2 + C (q.coeff 3) * t ^ 3
    + C (q.coeff 4) * t ^ 4 + C (q.coeff 5) * t ^ 5
    + C (q.coeff 6) * t ^ 6 + C (q.coeff 7) * t ^ 7
  let top : K[X] := C (s ^ 8 * (9 * r)) * t ^ 8 + C (s ^ 9) * t ^ 9
  have hdecomp : g = low + top := by
    dsimp [g, low, top]
    rw [hcomp]
    ring
  have htermZero (a : K) (i n : ℕ) (hi : i ≤ 7) (hn : 7 < n) :
      (C a * t ^ i).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc
      (C a * t ^ i).natDegree ≤ (C a).natDegree + (t ^ i).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + i * t.natDegree := by
        gcongr
        · rw [Polynomial.natDegree_C]
        · exact Polynomial.natDegree_pow_le
      _ = i := by rw [ht]; simp
      _ ≤ 7 := hi
      _ < n := hn
  have hlowCoeff (n : ℕ) (hn : 7 < n) : low.coeff n = 0 := by
    dsimp [low]
    simp only [coeff_add]
    have h0 : (C (q.coeff 0)).coeff n = 0 := by
      rw [coeff_C, if_neg (by omega)]
    have h1 : (C (q.coeff 1) * t).coeff n = 0 := by
      simpa using htermZero (q.coeff 1) 1 n (by norm_num) hn
    rw [h0, h1, htermZero (q.coeff 2) 2 n (by norm_num) hn,
      htermZero (q.coeff 3) 3 n (by norm_num) hn,
      htermZero (q.coeff 4) 4 n (by norm_num) hn,
      htermZero (q.coeff 5) 5 n (by norm_num) hn,
      htermZero (q.coeff 6) 6 n (by norm_num) hn,
      htermZero (q.coeff 7) 7 n (by norm_num) hn]
    norm_num
  have hscale8 : C (s ^ 8 * (9 * r)) * C s⁻¹ ^ 8 = C (9 * r) := by
    rw [← C_pow, ← C_mul]
    congr 1
    field_simp [hs]
  have hscale9 : C (s ^ 9) * C s⁻¹ ^ 9 = 1 := by
    rw [← C_pow, ← C_mul]
    have hs9 : s ^ 9 * s⁻¹ ^ 9 = 1 := by field_simp [hs]
    rw [hs9, C_1]
  have htop : top = C (9 * r) * (X - C r) ^ 8 + (X - C r) ^ 9 := by
    dsimp [top, t]
    calc
      C (s ^ 8 * (9 * r)) * (C s⁻¹ * (X - C r)) ^ 8
            + C (s ^ 9) * (C s⁻¹ * (X - C r)) ^ 9 =
          (C (s ^ 8 * (9 * r)) * C s⁻¹ ^ 8) * (X - C r) ^ 8
            + (C (s ^ 9) * C s⁻¹ ^ 9) * (X - C r) ^ 9 := by ring
      _ = C (9 * r) * (X - C r) ^ 8 + (X - C r) ^ 9 := by
        rw [hscale8, hscale9, one_mul]
  have htopFactor : top = (X - C r) ^ 8 * (X + C (8 * r)) := by
    rw [htop]
    simp only [C_mul, C_ofNat]
    ring
  have hmSub : (X - C r : K[X]).Monic := Polynomial.monic_X_sub_C r
  have hmAdd : (X + C (8 * r) : K[X]).Monic :=
    Polynomial.monic_X_add_C (8 * r)
  have hmPow : ((X - C r : K[X]) ^ 8).Monic := hmSub.pow 8
  have htopMonic : top.Monic := by
    rw [htopFactor]
    exact hmPow.mul hmAdd
  have htopDegree : top.natDegree = 9 := by
    rw [htopFactor, Polynomial.natDegree_mul hmPow.ne_zero hmAdd.ne_zero,
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
      Polynomial.natDegree_X_add_C]
  have htop9 : top.coeff 9 = 1 := by
    rw [← htopDegree, coeff_natDegree, htopMonic.leadingCoeff]
  have htop8 : top.coeff 8 = 0 := by
    have hnxt : top.nextCoeff = 0 := by
      rw [htopFactor, hmPow.nextCoeff_mul hmAdd, hmSub.nextCoeff_pow,
        Polynomial.nextCoeff_X_sub_C, Polynomial.nextCoeff_X_add_C]
      simp [nsmul_eq_mul]
    simpa [Polynomial.nextCoeff, htopDegree] using hnxt
  have hg9 : g.coeff 9 = 1 := by
    rw [hdecomp, coeff_add, hlowCoeff 9 (by norm_num), htop9, zero_add]
  have hg8 : g.coeff 8 = 0 := by
    rw [hdecomp, coeff_add, hlowCoeff 8 (by norm_num), htop8, add_zero]
  refine ⟨g.coeff 0, g.coeff 1, g.coeff 2, g.coeff 3, g.coeff 4,
    g.coeff 5, g.coeff 6, g.coeff 7, ?_⟩
  change g = GCD369DepressedG (g.coeff 0) (g.coeff 1) (g.coeff 2)
    (g.coeff 3) (g.coeff 4) (g.coeff 5) (g.coeff 6) (g.coeff 7)
  apply Polynomial.ext
  intro n
  by_cases hn : n ≤ 9
  · interval_cases n <;>
      simp [GCD369DepressedG, hg8, hg9, coeff_add, coeff_C,
        coeff_mul_X_pow', coeff_X, coeff_X_pow]
  · have hgn : g.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
        (hgdeg.trans_lt (not_le.mp hn))
    rw [hgn]
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    have hn5 : n ≠ 5 := by omega
    have hn6 : n ≠ 6 := by omega
    have hn7 : n ≠ 7 := by omega
    have hn9 : n ≠ 9 := by omega
    simp [GCD369DepressedG, coeff_add, coeff_C, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow, hn0, hn1, hn2, hn3, hn4,
      hn5, hn6, hn7, hn9, show n - 7 ≠ 0 by omega,
      show n - 6 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 2 ≠ 0 by omega, show 1 ≠ n by omega]

set_option maxHeartbeats 64000000 in
/-- The affine Kummer coordinate is equivariant: applying the deck action to
the coefficients is the same as scaling the new variable by `omega²`. -/
theorem GCD369AffineDeckCovariance
    {K : Type*} [Field K] (sigma : K ≃+* K) (omega s r : K)
    (p : K[X]) (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1)
    (hsigmaS : sigma s = omega * s) (hsigmaR : sigma r = omega * r)
    (hpfix : p.map sigma.toRingHom = p) :
    let t : K[X] := C s⁻¹ * (X - C r)
    (p.comp t).map sigma.toRingHom =
      (p.comp t).comp (C (omega ^ 2) * X) := by
  dsimp only
  let t : K[X] := C s⁻¹ * (X - C r)
  have homega0 : omega ≠ 0 := by
    intro h0
    simp [h0] at homega3
  have homegaInv : omega⁻¹ = omega ^ 2 := by
    apply mul_left_cancel₀ homega0
    rw [mul_inv_cancel₀ homega0]
    symm
    calc
      omega * omega ^ 2 = omega ^ 3 := by ring
      _ = 1 := homega3
  have htmap : t.map sigma.toRingHom = t.comp (C (omega ^ 2) * X) := by
    dsimp [t]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X,
      map_inv₀, mul_comp, sub_comp, C_comp, X_comp]
    change C (sigma s)⁻¹ * (X - C (sigma r)) =
      C s⁻¹ * (C (omega ^ 2) * X - C r)
    rw [hsigmaS, hsigmaR, mul_inv, homegaInv]
    have hconstant :
        omega ^ 2 * s⁻¹ * (omega * r) = s⁻¹ * r := by
      calc
        omega ^ 2 * s⁻¹ * (omega * r) = omega ^ 3 * (s⁻¹ * r) := by ring
        _ = s⁻¹ * r := by rw [homega3, one_mul]
    rw [mul_sub, mul_sub]
    simp only [← C_mul]
    rw [hconstant]
    have hCscale : C (omega ^ 2 * s⁻¹) = C s⁻¹ * C (omega ^ 2) := by
      rw [← C_mul]
      congr 1
      ring
    rw [hCscale]
    ring
  rw [Polynomial.map_comp, hpfix, htmap, Polynomial.comp_assoc]

set_option maxHeartbeats 64000000 in
/-- Consequently the coefficient of `z^n` in a Kummer-affine transform has
deck weight `omega^(2n)`, equivalently weight `-n mod 3`. -/
theorem GCD369AffineDeckCoefficientWeight
    {K : Type*} [Field K] (sigma : K ≃+* K) (omega s r : K)
    (p : K[X]) (n : ℕ) (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1)
    (hsigmaS : sigma s = omega * s) (hsigmaR : sigma r = omega * r)
    (hpfix : p.map sigma.toRingHom = p) :
    let t : K[X] := C s⁻¹ * (X - C r)
    sigma ((p.comp t).coeff n) =
      (omega ^ 2) ^ n * (p.comp t).coeff n := by
  dsimp only
  have hcov := GCD369AffineDeckCovariance sigma omega s r p
    homega3 homega hsigmaS hsigmaR hpfix
  have hc := congrArg (fun u : K[X] ↦ u.coeff n) hcov
  rw [Polynomial.coeff_map, Polynomial.comp_C_mul_X_coeff] at hc
  simpa [mul_comm] using hc

set_option maxHeartbeats 64000000 in
/-- Reading the coefficients of an aligned degree-six affine transform
recovers the five cubic-Kummer weights used by the lower-row argument. -/
theorem GCD369AlignedFCoefficientWeights
    {K : Type*} [Field K]
    (sigma : K ≃+* K) (omega s r : K) (p : K[X])
    (a0 a1 a2 a3 a4 : K)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1)
    (hsigmaS : sigma s = omega * s) (hsigmaR : sigma r = omega * r)
    (hpfix : p.map sigma.toRingHom = p)
    (hf : p.comp (C s⁻¹ * (X - C r)) =
      GCD369AlignedF a0 a1 a2 a3 a4) :
    sigma a0 = a0 ∧ sigma a1 = omega ^ 2 * a1 ∧
      sigma a2 = omega * a2 ∧ sigma a3 = a3 ∧
      sigma a4 = omega ^ 2 * a4 := by
  have hw2 : (omega ^ 2) ^ 2 = omega := by
    calc
      (omega ^ 2) ^ 2 = omega ^ 3 * omega := by ring
      _ = omega := by rw [homega3, one_mul]
  have hw3 : (omega ^ 2) ^ 3 = 1 := by
    calc
      (omega ^ 2) ^ 3 = (omega ^ 3) ^ 2 := by ring
      _ = 1 := by rw [homega3, one_pow]
  have hw4 : (omega ^ 2) ^ 4 = omega ^ 2 := by
    calc
      (omega ^ 2) ^ 4 = (omega ^ 3) ^ 2 * omega ^ 2 := by ring
      _ = omega ^ 2 := by rw [homega3, one_pow, one_mul]
  have weight (n : ℕ) := GCD369AffineDeckCoefficientWeight
    sigma omega s r p n homega3 homega hsigmaS hsigmaR hpfix
  dsimp only at weight
  rw [hf] at weight
  constructor
  · simpa [GCD369AlignedF] using weight 0
  constructor
  · simpa [GCD369AlignedF] using weight 1
  constructor
  · simpa [GCD369AlignedF, hw2] using weight 2
  constructor
  · simpa [GCD369AlignedF, hw3] using weight 3
  · simpa [GCD369AlignedF, hw4] using weight 4

set_option maxHeartbeats 64000000 in
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
/-- The eight high rows of an aligned noncube source integrate to the
five-coefficient normal form, up to the constant target shear and target
translation.  The Kummer weights kill the five nonzero-weight integration
constants; `c3` is the essential `kappa`. -/
theorem GCD369KummerHighRowsNormalize
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (sigma : K ≃+* K) (omega : K)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 b5 b6 b7 terminal : K)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1)
    (hfix : ∀ c : K, Differential.deriv c = 0 → sigma c = c)
    (ha0 : sigma a0 = a0) (ha1 : sigma a1 = omega ^ 2 * a1)
    (ha2 : sigma a2 = omega * a2) (ha3 : sigma a3 = a3)
    (ha4 : sigma a4 = omega ^ 2 * a4)
    (hb1 : sigma b1 = omega ^ 2 * b1)
    (hb2 : sigma b2 = omega * b2)
    (hb4 : sigma b4 = omega ^ 2 * b4)
    (hb5 : sigma b5 = omega * b5)
    (hb7 : sigma b7 = omega ^ 2 * b7)
    (hD :
      Differential.mapCoeffs (GCD369AlignedF a0 a1 a2 a3 a4)
          * derivative (GCD369DepressedG b0 b1 b2 b3 b4 b5 b6 b7)
        - derivative (GCD369AlignedF a0 a1 a2 a3 a4)
          * Differential.mapCoeffs (GCD369DepressedG b0 b1 b2 b3 b4 b5 b6 b7)
        = C terminal) :
    ∃ c6 c3 c0 : K,
      Differential.deriv c6 = 0 ∧ Differential.deriv c3 = 0
        ∧ Differential.deriv c0 = 0 ∧
      GCD369DepressedG b0 b1 b2 b3 b4 b5 b6 b7 =
        GCD369AlignedG a0 a1 a2 a3 a4 c3
          + C c6 * GCD369AlignedF a0 a1 a2 a3 a4 + C c0 := by
  have hnat (n : ℕ) : Differential.deriv (n : K) = 0 :=
    Differential.deriv.map_natCast n
  have hOfNat (n : ℕ) [n.AtLeastTwo] :
      Differential.deriv (ofNat(n) : K) = 0 := hnat n
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (Differential.mapCoeffs (GCD369AlignedF a0 a1 a2 a3 a4)
            * derivative (GCD369DepressedG b0 b1 b2 b3 b4 b5 b6 b7)
          - derivative (GCD369AlignedF a0 a1 a2 a3 a4)
            * Differential.mapCoeffs (GCD369DepressedG b0 b1 b2 b3 b4 b5 b6 b7)).coeff n = 0 := by
    have h := congrArg (fun p : K[X] ↦ p.coeff n) hD
    rw [coeff_C, if_neg hn] at h
    exact h
  have h12 := hcoeff 12 (by norm_num)
  have h11 := hcoeff 11 (by norm_num)
  have h10 := hcoeff 10 (by norm_num)
  have h9 := hcoeff 9 (by norm_num)
  have h8 := hcoeff 8 (by norm_num)
  have h7 := hcoeff 7 (by norm_num)
  have h6 := hcoeff 6 (by norm_num)
  have h5 := hcoeff 5 (by norm_num)
  rw [GCD369AlignedF, GCD369DepressedG] at h12 h11 h10 h9 h8 h7 h6 h5
  simp only [coeff_sub, coeff_mul, Differential.coeff_mapCoeffs, coeff_derivative]
    at h12 h11 h10 h9 h8 h7 h6 h5
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    at h12 h11 h10 h9 h8 h7 h6 h5
  simp only [mul_assoc] at h12 h11 h10 h9 h8 h7 h6 h5
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero,
    coeff_add, coeff_sub, coeff_zero, coeff_one,
    map_add, map_sub, map_zero, Derivation.map_one_eq_zero,
    ite_true, ite_false, zero_add, add_zero, zero_mul, mul_zero,
    one_mul, mul_one, sub_zero, zero_sub, sub_self, pow_zero, pow_one,
    nsmul_eq_mul, coeff_C, coeff_C_mul,
    coeff_mul_X_pow', coeff_X, coeff_X_pow]
    at h12 h11 h10 h9 h8 h7 h6 h5
  have homega2 : omega ^ 2 ≠ 1 := by
    intro h2
    apply homega
    calc
      omega = omega ^ 2 * omega := by rw [h2, one_mul]
      _ = omega ^ 3 := by ring
      _ = 1 := homega3
  have homega4 : omega ^ 4 = omega := by
    calc
      omega ^ 4 = omega ^ 3 * omega := by ring
      _ = omega := by rw [homega3, one_mul]
  have homega5 : omega ^ 5 = omega ^ 2 := by
    calc
      omega ^ 5 = omega ^ 3 * omega ^ 2 := by ring
      _ = omega ^ 2 := by rw [homega3, one_mul]
  have homega8 : omega ^ 8 = omega ^ 2 := by
    calc
      omega ^ 8 = (omega ^ 3) ^ 2 * omega ^ 2 := by ring
      _ = omega ^ 2 := by rw [homega3, one_pow, one_mul]
  have killWeightOne (c : K) (hc : Differential.deriv c = 0)
      (hsigma : sigma c = omega * c) : c = 0 := by
    have hfixed := hfix c hc
    have hprod : (omega - 1) * c = 0 := by
      rw [sub_mul, one_mul, ← hsigma, hfixed, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr homega)
  have killWeightTwo (c : K) (hc : Differential.deriv c = 0)
      (hsigma : sigma c = omega ^ 2 * c) : c = 0 := by
    have hfixed := hfix c hc
    have hprod : (omega ^ 2 - 1) * c = 0 := by
      rw [sub_mul, one_mul, ← hsigma, hfixed, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr homega2)
  let c7 := b7 - 3 * a4 / 2
  have hc7 : Differential.deriv c7 = 0 := by
    dsimp [c7]
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, hOfNat]
    linear_combination (-1 / 6) * h12
  have hsigmaC7 : sigma c7 = omega ^ 2 * c7 := by
    dsimp [c7]
    simp only [map_sub, map_div₀, map_mul, map_ofNat, hb7, ha4]
    ring
  have hc7zero : c7 = 0 := killWeightTwo c7 hc7 hsigmaC7
  have hb7form : b7 = 3 * a4 / 2 := by
    dsimp [c7] at hc7zero
    linear_combination hc7zero
  let c6 := b6 - 3 * a3 / 2
  have hc6 : Differential.deriv c6 = 0 := by
    dsimp [c6]
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, hOfNat]
    linear_combination (-1 / 6) * h11
  have hb6form : b6 = 3 * a3 / 2 + c6 := by
    dsimp [c6]
    ring
  let c5 := b5 - 3 * (4 * a2 + a4 ^ 2) / 8
  have hc5 : Differential.deriv c5 = 0 := by
    dsimp [c5]
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      Derivation.leibniz_pow, hOfNat]
    rw [hb7form] at h10
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, hOfNat] at h10
    linear_combination (-1 / 6) * h10
  have hsigmaC5 : sigma c5 = omega * c5 := by
    dsimp [c5]
    simp only [map_sub, map_add, map_div₀, map_mul, map_pow, map_ofNat,
      hb5, ha2, ha4]
    field_simp
    ring_nf
    rw [homega4]
  have hc5zero : c5 = 0 := killWeightOne c5 hc5 hsigmaC5
  have hb5form : b5 = 3 * (4 * a2 + a4 ^ 2) / 8 := by
    dsimp [c5] at hc5zero
    linear_combination hc5zero
  let c4 := b4 - 3 * (2 * a1 + a3 * a4) / 4 - a4 * c6
  have hc4 : Differential.deriv c4 = 0 := by
    dsimp [c4]
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, hOfNat, hc6]
    rw [hb7form, hb6form] at h9
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      hOfNat, hc6] at h9 ⊢
    linear_combination (-1 / 6) * h9
  have hsigmaC6 : sigma c6 = c6 := by
    exact hfix c6 hc6
  have hsigmaC4 : sigma c4 = omega ^ 2 * c4 := by
    dsimp [c4]
    simp only [map_sub, map_add, map_div₀, map_mul, map_ofNat,
      hb4, ha1, ha3, ha4, hsigmaC6]
    ring
  have hc4zero : c4 = 0 := killWeightTwo c4 hc4 hsigmaC4
  have hb4form : b4 = 3 * (2 * a1 + a3 * a4) / 4 + a4 * c6 := by
    dsimp [c4] at hc4zero
    linear_combination hc4zero
  let c3 := b3
      - (24 * a0 + 12 * a2 * a4 + 6 * a3 ^ 2 - a4 ^ 3) / 16
      - a3 * c6
  have hc3 : Differential.deriv c3 = 0 := by
    dsimp [c3]
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      Derivation.leibniz_pow, hOfNat, hc6]
    rw [hb7form, hb6form, hb5form] at h8
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      Derivation.leibniz_pow, hOfNat, hc6] at h8 ⊢
    linear_combination (-1 / 6) * h8
  have hb3form : b3 =
      (24 * a0 + 12 * a2 * a4 + 6 * a3 ^ 2 - a4 ^ 3) / 16
        + a3 * c6 + c3 := by
    dsimp [c3]
    ring
  let c2 := b2
      - 3 * (4 * a1 * a4 + 4 * a2 * a3 - a3 * a4 ^ 2) / 16
      - a2 * c6
  have hc2 : Differential.deriv c2 = 0 := by
    dsimp [c2]
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      Derivation.leibniz_pow, hOfNat, hc6]
    rw [hb7form, hb6form, hb5form, hb4form] at h7
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      Derivation.leibniz_pow, hOfNat, hc6] at h7 ⊢
    linear_combination (-1 / 6) * h7
  have hsigmaC2 : sigma c2 = omega * c2 := by
    dsimp [c2]
    simp only [map_sub, map_add, map_div₀, map_mul, map_pow, map_ofNat,
      hb2, ha1, ha2, ha3, ha4, hsigmaC6]
    field_simp
    ring_nf
    rw [homega4]
    ring
  have hc2zero : c2 = 0 := killWeightOne c2 hc2 hsigmaC2
  have hb2form : b2 =
      3 * (4 * a1 * a4 + 4 * a2 * a3 - a3 * a4 ^ 2) / 16
        + a2 * c6 := by
    dsimp [c2] at hc2zero
    linear_combination hc2zero
  let c1 := b1
      - 3 * (32 * a0 * a4 + 32 * a1 * a3 + 16 * a2 ^ 2
          - 8 * a2 * a4 ^ 2 - 8 * a3 ^ 2 * a4 + a4 ^ 4) / 128
      - a1 * c6 - a4 / 2 * c3
  have hc1 : Differential.deriv c1 = 0 := by
    dsimp [c1]
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      Derivation.leibniz_pow, hOfNat, hc6, hc3]
    rw [hb7form, hb6form, hb5form, hb4form, hb3form] at h6
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      Derivation.leibniz_pow, hOfNat, hc6, hc3] at h6 ⊢
    linear_combination (-1 / 6) * h6
  have hsigmaC3 : sigma c3 = c3 := hfix c3 hc3
  have hsigmaC1 : sigma c1 = omega ^ 2 * c1 := by
    dsimp [c1]
    simp only [map_sub, map_add, map_div₀, map_mul, map_pow, map_ofNat,
      hb1, ha0, ha1, ha2, ha3, ha4, hsigmaC6, hsigmaC3]
    field_simp
    ring_nf
    rw [homega5, homega8]
    ring
  have hc1zero : c1 = 0 := killWeightTwo c1 hc1 hsigmaC1
  have hb1form : b1 =
      3 * (32 * a0 * a4 + 32 * a1 * a3 + 16 * a2 ^ 2
          - 8 * a2 * a4 ^ 2 - 8 * a3 ^ 2 * a4 + a4 ^ 4) / 128
        + a1 * c6 + a4 / 2 * c3 := by
    dsimp [c1] at hc1zero
    linear_combination hc1zero
  let c0 := b0
      - (24 * a0 * a3 + 24 * a1 * a2 - 6 * a1 * a4 ^ 2
          - 12 * a2 * a3 * a4 - 2 * a3 ^ 3 + 3 * a3 * a4 ^ 3) / 32
      - a0 * c6 - a3 / 2 * c3
  have hc0 : Differential.deriv c0 = 0 := by
    dsimp [c0]
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      Derivation.leibniz_pow, hOfNat, hc6, hc3]
    rw [hb6form, hb5form, hb4form, hb3form, hb2form] at h5
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      Derivation.leibniz_pow, hOfNat, hc6, hc3] at h5 ⊢
    linear_combination (-1 / 6) * h5
  refine ⟨c6, c3, c0, hc6, hc3, hc0, ?_⟩
  rw [GCD369DepressedG, GCD369AlignedG, GCD369AlignedF,
    hb7form, hb6form, hb5form, hb4form, hb3form, hb2form, hb1form]
  dsimp [c0]
  simp only [C_mul, C_add, C_sub]
  ring

set_option maxHeartbeats 64000000 in
/-- Once the common affine translation parameter is known, an arbitrary
Kummer-equivariant degree-`(6,9)` source lands in the exact aligned normal
form.  The coefficient weights and the transformed Keller bracket are
derived here rather than assumed. -/
theorem GCD369AffineKummerHighRowsNormalize
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (sigma : K ≃+* K) (omega : K) (p q : K[X]) (s r j : K)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1) (hs : s ≠ 0)
    (hsigmaS : sigma s = omega * s) (hsigmaR : sigma r = omega * r)
    (hpfix : p.map sigma.toRingHom = p) (hqfix : q.map sigma.toRingHom = q)
    (hfix : ∀ c : K, Differential.deriv c = 0 → sigma c = c)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = s ^ 6)
    (hp5 : p.coeff 5 = s ^ 5 * (6 * r))
    (hq : q.natDegree = 9) (hq9 : q.coeff 9 = s ^ 9)
    (hq8 : q.coeff 8 = s ^ 8 * (9 * r))
    (hD : Differential.mapCoeffs p * derivative q
      - derivative p * Differential.mapCoeffs q = C j) :
    let t : K[X] := C s⁻¹ * (X - C r)
    ∃ a0 a1 a2 a3 a4 c6 c3 c0 : K,
      p.comp t = GCD369AlignedF a0 a1 a2 a3 a4 ∧
      Differential.deriv c6 = 0 ∧ Differential.deriv c3 = 0 ∧
      Differential.deriv c0 = 0 ∧
      q.comp t = GCD369AlignedG a0 a1 a2 a3 a4 c3
        + C c6 * (p.comp t) + C c0 := by
  dsimp only
  obtain ⟨a0, a1, a2, a3, a4, hf⟩ :=
    GCD369AffineDegreeSixNormalForm p s r hs hp hp6 hp5
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hg⟩ :=
    GCD369AffineDegreeNineNormalForm q s r hs hq hq9 hq8
  have hw2 : (omega ^ 2) ^ 2 = omega := by
    calc
      (omega ^ 2) ^ 2 = omega ^ 3 * omega := by ring
      _ = omega := by rw [homega3, one_mul]
  have hw3 : (omega ^ 2) ^ 3 = 1 := by
    calc
      (omega ^ 2) ^ 3 = (omega ^ 3) ^ 2 := by ring
      _ = 1 := by rw [homega3, one_pow]
  have hw4 : (omega ^ 2) ^ 4 = omega ^ 2 := by
    calc
      (omega ^ 2) ^ 4 = (omega ^ 3) ^ 2 * omega ^ 2 := by ring
      _ = omega ^ 2 := by rw [homega3, one_pow, one_mul]
  have hw5 : (omega ^ 2) ^ 5 = omega := by
    calc
      (omega ^ 2) ^ 5 = (omega ^ 3) ^ 3 * omega := by ring
      _ = omega := by rw [homega3, one_pow, one_mul]
  have hw7 : (omega ^ 2) ^ 7 = omega ^ 2 := by
    calc
      (omega ^ 2) ^ 7 = (omega ^ 3) ^ 4 * omega ^ 2 := by ring
      _ = omega ^ 2 := by rw [homega3, one_pow, one_mul]
  have ha0 : sigma a0 = a0 := by
    have h := GCD369AffineDeckCoefficientWeight sigma omega s r p 0
      homega3 homega hsigmaS hsigmaR hpfix
    dsimp only at h
    rw [hf] at h
    simpa [GCD369AlignedF] using h
  have ha1 : sigma a1 = omega ^ 2 * a1 := by
    have h := GCD369AffineDeckCoefficientWeight sigma omega s r p 1
      homega3 homega hsigmaS hsigmaR hpfix
    dsimp only at h
    rw [hf] at h
    simpa [GCD369AlignedF] using h
  have ha2 : sigma a2 = omega * a2 := by
    have h := GCD369AffineDeckCoefficientWeight sigma omega s r p 2
      homega3 homega hsigmaS hsigmaR hpfix
    dsimp only at h
    rw [hf] at h
    simpa [GCD369AlignedF, hw2] using h
  have ha3 : sigma a3 = a3 := by
    have h := GCD369AffineDeckCoefficientWeight sigma omega s r p 3
      homega3 homega hsigmaS hsigmaR hpfix
    dsimp only at h
    rw [hf] at h
    simpa [GCD369AlignedF, hw3] using h
  have ha4 : sigma a4 = omega ^ 2 * a4 := by
    have h := GCD369AffineDeckCoefficientWeight sigma omega s r p 4
      homega3 homega hsigmaS hsigmaR hpfix
    dsimp only at h
    rw [hf] at h
    simpa [GCD369AlignedF, hw4] using h
  have hb1 : sigma b1 = omega ^ 2 * b1 := by
    have h := GCD369AffineDeckCoefficientWeight sigma omega s r q 1
      homega3 homega hsigmaS hsigmaR hqfix
    dsimp only at h
    rw [hg] at h
    simpa [GCD369DepressedG] using h
  have hb2 : sigma b2 = omega * b2 := by
    have h := GCD369AffineDeckCoefficientWeight sigma omega s r q 2
      homega3 homega hsigmaS hsigmaR hqfix
    dsimp only at h
    rw [hg] at h
    simpa [GCD369DepressedG, hw2] using h
  have hb4 : sigma b4 = omega ^ 2 * b4 := by
    have h := GCD369AffineDeckCoefficientWeight sigma omega s r q 4
      homega3 homega hsigmaS hsigmaR hqfix
    dsimp only at h
    rw [hg] at h
    simpa [GCD369DepressedG, hw4] using h
  have hb5 : sigma b5 = omega * b5 := by
    have h := GCD369AffineDeckCoefficientWeight sigma omega s r q 5
      homega3 homega hsigmaS hsigmaR hqfix
    dsimp only at h
    rw [hg] at h
    simpa [GCD369DepressedG, hw5] using h
  have hb7 : sigma b7 = omega ^ 2 * b7 := by
    have h := GCD369AffineDeckCoefficientWeight sigma omega s r q 7
      homega3 homega hsigmaS hsigmaR hqfix
    dsimp only at h
    rw [hg] at h
    simpa [GCD369DepressedG, hw7] using h
  have hD' := GCD369AffineBracket p q s r j hs hD
  dsimp only at hD'
  rw [hf, hg] at hD'
  obtain ⟨c6, c3, c0, hc6, hc3, hc0, hgfinal⟩ :=
    GCD369KummerHighRowsNormalize sigma omega
      a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 b5 b6 b7 (j / s)
      homega3 homega hfix ha0 ha1 ha2 ha3 ha4 hb1 hb2 hb4 hb5 hb7 hD'
  refine ⟨a0, a1, a2, a3, a4, c6, c3, c0, hf, hc6, hc3, hc0, ?_⟩
  rw [hf, hg]
  exact hgfinal

set_option maxHeartbeats 64000000 in
/-- The coefficient of degree thirteen in the source bracket is precisely
the denominator-cleared first `(6,9)` alignment row. -/
theorem GCD369FirstSourceRow
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (p q : K[X]) (s a b j : K) (hs : s ≠ 0)
    (hp : p.natDegree = 6) (hq : q.natDegree = 9)
    (hp6 : p.coeff 6 = s ^ 6) (hp5 : p.coeff 5 = a)
    (hq9 : q.coeff 9 = s ^ 9) (hq8 : q.coeff 8 = b)
    (hD : Differential.mapCoeffs p * derivative q
      - derivative p * Differential.mapCoeffs q = C j) :
    3 * s ^ 4 * Differential.deriv a
        - 15 * s ^ 3 * a * Differential.deriv s
      - 2 * s * Differential.deriv b
        + 16 * b * Differential.deriv s = 0 := by
  have hpAbove (n : ℕ) (hn : 6 < n) : p.coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [hp] using hn)
  have hqAbove (n : ℕ) (hn : 9 < n) : q.coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [hq] using hn)
  have h13 := congrArg (fun u : K[X] ↦ u.coeff 13) hD
  rw [coeff_C, if_neg (by norm_num)] at h13
  simp only [coeff_sub, coeff_mul, Differential.coeff_mapCoeffs,
    coeff_derivative, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    at h13
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero,
    coeff_add, coeff_sub, coeff_zero, coeff_one,
    map_add, map_sub, map_zero, Derivation.map_one_eq_zero,
    ite_true, ite_false, zero_add, add_zero, zero_mul, mul_zero,
    one_mul, mul_one, sub_zero, zero_sub, sub_self, pow_zero, pow_one,
    nsmul_eq_mul, hpAbove, hqAbove, hp6, hp5, hq9, hq8,
    Derivation.leibniz_pow] at h13
  norm_num at h13
  have hfactor :
      9 * s ^ 9 * Differential.deriv a
          + 48 * b * s ^ 5 * Differential.deriv s
          - 45 * a * s ^ 8 * Differential.deriv s
          - 6 * s ^ 6 * Differential.deriv b =
        3 * s ^ 5 *
          (3 * s ^ 4 * Differential.deriv a
              - 15 * s ^ 3 * a * Differential.deriv s
            - 2 * s * Differential.deriv b
              + 16 * b * Differential.deriv s) := by ring
  have hprod :
      3 * s ^ 5 *
        (3 * s ^ 4 * Differential.deriv a
            - 15 * s ^ 3 * a * Differential.deriv s
          - 2 * s * Differential.deriv b
            + 16 * b * Differential.deriv s) = 0 := by
    rw [← hfactor]
    linear_combination h13
  exact (mul_eq_zero.mp hprod).resolve_left
    (mul_ne_zero (by norm_num) (pow_ne_zero 5 hs))

set_option maxHeartbeats 64000000 in
/-- The first denominator-cleared `(6,9)` source row makes the normalized
alignment discriminator differential-constant. -/
theorem GCD369AlignmentDiscriminatorDerivative
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (s a b : K) (hs : s ≠ 0)
    (hrow :
      3 * s ^ 4 * Differential.deriv a
          - 15 * s ^ 3 * a * Differential.deriv s
        - 2 * s * Differential.deriv b
          + 16 * b * Differential.deriv s = 0) :
    Differential.deriv (3 * a / s ^ 5 - 2 * b / s ^ 8) = 0 := by
  have hnat (n : ℕ) : Differential.deriv (n : K) = 0 :=
    Differential.deriv.map_natCast n
  have hOfNat (n : ℕ) [n.AtLeastTwo] :
      Differential.deriv (ofNat(n) : K) = 0 := hnat n
  calc
    Differential.deriv (3 * a / s ^ 5 - 2 * b / s ^ 8) =
        (3 * s ^ 4 * Differential.deriv a
            - 15 * s ^ 3 * a * Differential.deriv s
          - 2 * s * Differential.deriv b
            + 16 * b * Differential.deriv s) / s ^ 9 := by
      rw [map_sub]
      simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
        Derivation.leibniz_pow, hOfNat]
      field_simp [hs]
      ring
    _ = 0 := by rw [hrow, zero_div]

set_option maxHeartbeats 64000000 in
/-- On a nontrivial cubic Kummer branch, the same discriminator is both
differential-constant and weight one, hence vanishes. -/
theorem GCD369KummerAlignmentFromFirstRow
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (sigma : K ≃+* K) (omega s a b : K)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1) (hs : s ≠ 0)
    (hsigmaS : sigma s = omega * s)
    (hsigmaA : sigma a = a) (hsigmaB : sigma b = b)
    (hfix : ∀ c : K, Differential.deriv c = 0 → sigma c = c)
    (hrow :
      3 * s ^ 4 * Differential.deriv a
          - 15 * s ^ 3 * a * Differential.deriv s
        - 2 * s * Differential.deriv b
          + 16 * b * Differential.deriv s = 0) :
    3 * a / s ^ 5 - 2 * b / s ^ 8 = 0 := by
  let delta := 3 * a / s ^ 5 - 2 * b / s ^ 8
  have hconstant : Differential.deriv delta = 0 :=
    GCD369AlignmentDiscriminatorDerivative s a b hs hrow
  have hfixed : sigma delta = delta := hfix delta hconstant
  have hsigmaDelta : sigma delta = omega * delta := by
    have homega0 : omega ≠ 0 := by
      intro homega0
      simp [homega0] at homega3
    have homega9 : omega ^ 9 = 1 := by
      calc
        omega ^ 9 = (omega ^ 3) ^ 3 := by ring
        _ = 1 := by rw [homega3, one_pow]
    change sigma (3 * a / s ^ 5 - 2 * b / s ^ 8) =
      omega * (3 * a / s ^ 5 - 2 * b / s ^ 8)
    simp only [map_sub, map_div₀, map_mul, map_pow, map_ofNat,
      hsigmaS, hsigmaA, hsigmaB]
    field_simp [hs, homega0]
    ring_nf
    rw [homega3, homega9]
    ring
  have hprod : (omega - 1) * delta = 0 := by
    rw [sub_mul, one_mul, ← hsigmaDelta, hfixed]
    exact sub_self delta
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr homega)

set_option maxHeartbeats 64000000 in
/-- The first source row does more than give a scalar alignment equation:
it constructs the common translation parameter for degrees six and nine,
and that parameter has Kummer weight one. -/
theorem GCD369KummerCommonTranslation
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (sigma : K ≃+* K) (omega s a b : K)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1) (hs : s ≠ 0)
    (hsigmaS : sigma s = omega * s)
    (hsigmaA : sigma a = a) (hsigmaB : sigma b = b)
    (hfix : ∀ c : K, Differential.deriv c = 0 → sigma c = c)
    (hrow :
      3 * s ^ 4 * Differential.deriv a
          - 15 * s ^ 3 * a * Differential.deriv s
        - 2 * s * Differential.deriv b
          + 16 * b * Differential.deriv s = 0) :
    ∃ r : K, sigma r = omega * r ∧
      a = s ^ 5 * (6 * r) ∧ b = s ^ 8 * (9 * r) := by
  have halign := GCD369KummerAlignmentFromFirstRow sigma omega s a b
    homega3 homega hs hsigmaS hsigmaA hsigmaB hfix hrow
  let r : K := a / (6 * s ^ 5)
  have homega0 : omega ≠ 0 := by
    intro h0
    simp [h0] at homega3
  have hsigmaR : sigma r = omega * r := by
    have h6 : omega ^ 6 = 1 := by
      calc
        omega ^ 6 = (omega ^ 3) ^ 2 := by ring
        _ = 1 := by rw [homega3, one_pow]
    dsimp [r]
    simp only [map_div₀, map_mul, map_ofNat, map_pow, hsigmaA, hsigmaS]
    field_simp [hs, homega0]
    ring_nf
    rw [h6]
    simp
  have ha : a = s ^ 5 * (6 * r) := by
    dsimp [r]
    field_simp [hs]
  have hb : b = s ^ 8 * (9 * r) := by
    dsimp [r]
    field_simp [hs] at halign ⊢
    linear_combination (-3) * halign
  exact ⟨r, hsigmaR, ha, hb⟩

set_option maxHeartbeats 64000000 in
/-- A general Kummer-equivariant `(6,9)` Keller source with common leading
core lands in the exact aligned normal form.  This composes the first source
row, common translation, affine chain rule, deck weights, and all eight high
rows into one source-facing theorem. -/
theorem GCD369KummerSourceNormalize
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (sigma : K ≃+* K) (omega : K) (p q : K[X]) (s j : K)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1) (hs : s ≠ 0)
    (hsigmaS : sigma s = omega * s)
    (hpfix : p.map sigma.toRingHom = p) (hqfix : q.map sigma.toRingHom = q)
    (hfix : ∀ c : K, Differential.deriv c = 0 → sigma c = c)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = s ^ 6)
    (hq : q.natDegree = 9) (hq9 : q.coeff 9 = s ^ 9)
    (hD : Differential.mapCoeffs p * derivative q
      - derivative p * Differential.mapCoeffs q = C j) :
    ∃ r a0 a1 a2 a3 a4 c6 c3 c0 : K,
      sigma r = omega * r ∧
      p.coeff 5 = s ^ 5 * (6 * r) ∧
      q.coeff 8 = s ^ 8 * (9 * r) ∧
      p.comp (C s⁻¹ * (X - C r)) = GCD369AlignedF a0 a1 a2 a3 a4 ∧
      Differential.deriv c6 = 0 ∧ Differential.deriv c3 = 0 ∧
      Differential.deriv c0 = 0 ∧
      q.comp (C s⁻¹ * (X - C r)) =
        GCD369AlignedG a0 a1 a2 a3 a4 c3
          + C c6 * (p.comp (C s⁻¹ * (X - C r))) + C c0 := by
  have hp5fix : sigma (p.coeff 5) = p.coeff 5 := by
    have h := congrArg (fun u : K[X] ↦ u.coeff 5) hpfix
    simpa using h
  have hq8fix : sigma (q.coeff 8) = q.coeff 8 := by
    have h := congrArg (fun u : K[X] ↦ u.coeff 8) hqfix
    simpa using h
  have hrow := GCD369FirstSourceRow p q s (p.coeff 5) (q.coeff 8) j
    hs hp hq hp6 rfl hq9 rfl hD
  obtain ⟨r, hsigmaR, hp5, hq8⟩ :=
    GCD369KummerCommonTranslation sigma omega s (p.coeff 5) (q.coeff 8)
      homega3 homega hs hsigmaS hp5fix hq8fix hfix hrow
  have hnormal := GCD369AffineKummerHighRowsNormalize sigma omega p q s r j
    homega3 homega hs hsigmaS hsigmaR hpfix hqfix hfix
    hp hp6 hp5 hq hq9 hq8 hD
  dsimp only at hnormal
  obtain ⟨a0, a1, a2, a3, a4, c6, c3, c0,
    hf, hc6, hc3, hc0, hg⟩ := hnormal
  exact ⟨r, a0, a1, a2, a3, a4, c6, c3, c0,
    hsigmaR, hp5, hq8, hf, hc6, hc3, hc0, hg⟩

set_option maxHeartbeats 64000000 in
/-- The same source-facing normalization exposes every datum consumed by the
aligned noncube theorem: the five coefficient weights, invariant `kappa`,
and the unchanged terminal bracket after removing constant target gauges. -/
theorem GCD369KummerSourceAlignedPresentation
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (sigma : K ≃+* K) (omega : K) (p q : K[X]) (s j : K)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1) (hs : s ≠ 0)
    (hsigmaS : sigma s = omega * s)
    (hpfix : p.map sigma.toRingHom = p) (hqfix : q.map sigma.toRingHom = q)
    (hfix : ∀ c : K, Differential.deriv c = 0 → sigma c = c)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = s ^ 6)
    (hq : q.natDegree = 9) (hq9 : q.coeff 9 = s ^ 9)
    (hD : Differential.mapCoeffs p * derivative q
      - derivative p * Differential.mapCoeffs q = C j) :
    ∃ r a0 a1 a2 a3 a4 c6 kappa c0 : K,
      sigma r = omega * r ∧
      p.comp (C s⁻¹ * (X - C r)) = GCD369AlignedF a0 a1 a2 a3 a4 ∧
      sigma a0 = a0 ∧ sigma a1 = omega ^ 2 * a1 ∧
      sigma a2 = omega * a2 ∧ sigma a3 = a3 ∧
      sigma a4 = omega ^ 2 * a4 ∧ sigma kappa = kappa ∧
      Differential.deriv c6 = 0 ∧ Differential.deriv kappa = 0 ∧
      Differential.deriv c0 = 0 ∧
      (Differential.mapCoeffs (GCD369AlignedF a0 a1 a2 a3 a4) *
          derivative (GCD369AlignedG a0 a1 a2 a3 a4 kappa)
        - derivative (GCD369AlignedF a0 a1 a2 a3 a4) *
          Differential.mapCoeffs (GCD369AlignedG a0 a1 a2 a3 a4 kappa) =
        C (j / s)) ∧
      q.comp (C s⁻¹ * (X - C r)) =
        GCD369AlignedG a0 a1 a2 a3 a4 kappa +
          C c6 * (p.comp (C s⁻¹ * (X - C r))) + C c0 := by
  obtain ⟨r, a0, a1, a2, a3, a4, c6, kappa, c0,
      hsigmaR, _hp5, _hq8, hf, hc6, hkappa, hc0, hg⟩ :=
    GCD369KummerSourceNormalize sigma omega p q s j homega3 homega hs
      hsigmaS hpfix hqfix hfix hp hp6 hq hq9 hD
  obtain ⟨ha0, ha1, ha2, ha3, ha4⟩ :=
    GCD369AlignedFCoefficientWeights sigma omega s r p a0 a1 a2 a3 a4
      homega3 homega hsigmaS hsigmaR hpfix hf
  have hkappaSigma : sigma kappa = kappa := hfix kappa hkappa
  have hterminal := GCD369AffineBracket p q s r j hs hD
  dsimp only at hterminal
  rw [hf, hg, hf, GCD369ConstantTargetShearBracket _ _ c6 c0 hc6 hc0]
    at hterminal
  exact ⟨r, a0, a1, a2, a3, a4, c6, kappa, c0,
    hsigmaR, hf, ha0, ha1, ha2, ha3, ha4, hkappaSigma,
    hc6, hkappa, hc0, hterminal, hg⟩

set_option maxHeartbeats 64000000 in
/-- A noncube field element canonically produces the irreducible cubic
adjoin-root extension and its nontrivial Kummer deck action. -/
theorem GCD369NoncubeCubicKummerExtension
    {F : Type*} [Field F] (h omega : F)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1)
    (hnoncube : ¬ ∃ u : F, h = u ^ 3) :
    let p : F[X] := X ^ 3 - C h
    ∃ (_H : Irreducible p) (sigma : AdjoinRoot p ≃+* AdjoinRoot p),
      AdjoinRoot.root p ≠ 0 ∧
      AdjoinRoot.root p ^ 3 = algebraMap F (AdjoinRoot p) h ∧
      sigma (AdjoinRoot.root p) =
        algebraMap F (AdjoinRoot p) omega * AdjoinRoot.root p ∧
      sigma (AdjoinRoot.root p) ≠ AdjoinRoot.root p ∧
      ∀ c : F, sigma (algebraMap F (AdjoinRoot p) c) =
        algebraMap F (AdjoinRoot p) c := by
  dsimp only
  have hirr : Irreducible (X ^ 3 - C h : F[X]) := by
    apply X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 3)
    intro u hu
    exact hnoncube ⟨u, hu.symm⟩
  letI : Fact (Irreducible (X ^ 3 - C h : F[X])) := ⟨hirr⟩
  let eta : rootsOfUnity 3 F := rootsOfUnity.mkOfPowEq omega homega3
  let tau := autAdjoinRootXPowSubC 3 h eta
  have hroot0 : AdjoinRoot.root (X ^ 3 - C h : F[X]) ≠ 0 :=
    root_X_pow_sub_C_ne_zero' (by norm_num) (by
      intro hh
      apply hnoncube
      refine ⟨0, ?_⟩
      simp [hh])
  have haction : tau.toRingEquiv (AdjoinRoot.root (X ^ 3 - C h)) =
      algebraMap F (AdjoinRoot (X ^ 3 - C h)) omega *
        AdjoinRoot.root (X ^ 3 - C h) := by
    change tau (AdjoinRoot.root (X ^ 3 - C h)) = _
    dsimp [tau]
    rw [autAdjoinRootXPowSubC_root]
    simp [Algebra.smul_def, eta, rootsOfUnity.mkOfPowEq]
  refine ⟨hirr, tau.toRingEquiv, hroot0, root_X_pow_sub_C_pow 3 h,
    haction, ?_, ?_⟩
  · intro heq
    apply homega
    apply (algebraMap F (AdjoinRoot (X ^ 3 - C h))).injective
    apply mul_right_cancel₀ hroot0
    rw [map_one, one_mul, ← haction, heq]
  · intro c
    exact tau.commutes c

set_option maxHeartbeats 64000000 in
/-- The fixed field of the nontrivial cubic Kummer deck action is the base
field.  Expanding in the power basis `1,s,s²`, invariance kills the two
nonzero-weight coordinates. -/
theorem GCD369KummerFixedElementDescends
    {F : Type*} [Field F] (h omega : F)
    [Fact (Irreducible (X ^ 3 - C h : F[X]))]
    (sigma : AdjoinRoot (X ^ 3 - C h : F[X]) ≃+*
      AdjoinRoot (X ^ 3 - C h : F[X]))
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1)
    (hsigmaF : ∀ c : F, sigma (algebraMap F
      (AdjoinRoot (X ^ 3 - C h : F[X])) c) = algebraMap F _ c)
    (hsigmaS : sigma (AdjoinRoot.root (X ^ 3 - C h : F[X])) =
      algebraMap F _ omega * AdjoinRoot.root (X ^ 3 - C h : F[X]))
    (z : AdjoinRoot (X ^ 3 - C h : F[X])) (hz : sigma z = z) :
    ∃ c : F, z = algebraMap F _ c := by
  let pb := AdjoinRoot.powerBasis'
    (monic_X_pow_sub_C h (by norm_num : (3 : ℕ) ≠ 0))
  have hdim : pb.dim = 3 := by simp [pb]
  let B : Module.Basis (Fin 3) F (AdjoinRoot (X ^ 3 - C h : F[X])) :=
    pb.basis.reindex (finCongr hdim)
  let c0 : F := B.repr z 0
  let c1 : F := B.repr z 1
  let c2 : F := B.repr z 2
  have hB0 : B (0 : Fin 3) = 1 := by
    simp [B, pb]
  have hB1 : B (1 : Fin 3) = AdjoinRoot.root (X ^ 3 - C h : F[X]) := by
    simp [B, pb]
  have hB2 : B (2 : Fin 3) = AdjoinRoot.root (X ^ 3 - C h : F[X]) ^ 2 := by
    simp [B, pb]
  have hzexp : algebraMap F _ c0 + algebraMap F _ c1 *
        AdjoinRoot.root (X ^ 3 - C h : F[X]) +
      algebraMap F _ c2 * AdjoinRoot.root (X ^ 3 - C h : F[X]) ^ 2 = z := by
    have hsum := B.sum_repr z
    rw [Fin.sum_univ_three, hB0, hB1, hB2] at hsum
    simpa [c0, c1, c2, Algebra.smul_def, add_assoc] using hsum
  have hsigexp := congrArg sigma hzexp
  simp only [map_add, map_mul, map_pow, hsigmaF, hsigmaS] at hsigexp
  rw [hz, ← hzexp] at hsigexp
  have hexpB :
      c0 • B (0 : Fin 3) + (c1 * omega) • B (1 : Fin 3) +
          (c2 * omega ^ 2) • B (2 : Fin 3) =
        c0 • B (0 : Fin 3) + c1 • B (1 : Fin 3) + c2 • B (2 : Fin 3) := by
    rw [hB0, hB1, hB2]
    simp only [Algebra.smul_def, map_mul, map_pow]
    convert hsigexp using 1 <;> ring
  have hcoords := congrArg B.repr hexpB
  have h1 := congrArg (fun v => v (1 : Fin 3)) hcoords
  have h2 := congrArg (fun v => v (2 : Fin 3)) hcoords
  simp at h1 h2
  have homega2 : omega ^ 2 ≠ 1 := by
    intro h2
    apply homega
    calc
      omega = omega ^ 2 * omega := by rw [h2, one_mul]
      _ = omega ^ 3 := by ring
      _ = 1 := homega3
  have hc1 : c1 = 0 := by
    have hprod : c1 * (omega - 1) = 0 := by
      rw [mul_sub, mul_one, h1, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr homega)
  have hc2 : c2 = 0 := by
    have hprod : c2 * (omega ^ 2 - 1) = 0 := by
      rw [mul_sub, mul_one, h2, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr homega2)
  refine ⟨c0, ?_⟩
  rw [← hzexp, hc1, hc2]
  simp

set_option maxHeartbeats 64000000 in
/-- The weight-zero combination used as the elliptic fibre coordinate is
fixed by the cubic deck action. -/
theorem GCD369EllipticCoordinateFixed
    {K : Type*} [Field K] (sigma : K ≃+* K) (omega a2 a4 : K)
    (homega3 : omega ^ 3 = 1)
    (ha2 : sigma a2 = omega * a2)
    (ha4 : sigma a4 = omega ^ 2 * a4) :
    sigma (3 * a4 * (8 * a2 - 2 * a4 ^ 2)) =
      3 * a4 * (8 * a2 - 2 * a4 ^ 2) := by
  simp only [map_mul, map_sub, map_pow, map_ofNat, ha2, ha4]
  calc
    3 * (omega ^ 2 * a4) *
        (8 * (omega * a2) - 2 * (omega ^ 2 * a4) ^ 2) =
      omega ^ 3 * (3 * a4 * (8 * a2 - 2 * a4 ^ 2)) := by
        ring_nf
        rw [show omega ^ 6 = (omega ^ 3) ^ 2 by ring, homega3]
        ring
    _ = 3 * a4 * (8 * a2 - 2 * a4 ^ 2) := by rw [homega3, one_mul]

set_option maxHeartbeats 64000000 in
/-- Dividing a weight-two coefficient by the weight-two Kummer square
produces a deck-invariant rational quantity. -/
theorem GCD369ShiftParameterFixed
    {K : Type*} [Field K] (sigma : K ≃+* K) (omega s a4 : K)
    (homega3 : omega ^ 3 = 1) (hs0 : s ≠ 0)
    (hsigmaS : sigma s = omega * s)
    (ha4 : sigma a4 = omega ^ 2 * a4) :
    sigma (a4 / (4 * s ^ 2)) = a4 / (4 * s ^ 2) := by
  have homega0 : omega ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at homega3
    exact zero_ne_one homega3
  simp only [map_div₀, map_mul, map_ofNat, map_pow, hsigmaS, ha4]
  field_simp [hs0, homega0]

set_option maxHeartbeats 64000000 in
/-- Every rational function has its canonical reduced polynomial
numerator/denominator presentation, with no common finite zero. -/
theorem GCD369RatFuncReducedPresentation
    {k : Type*} [Field k] (r : RatFunc k) :
    ∃ N B : k[X], B ≠ 0 ∧
      r = algebraMap k[X] (RatFunc k) N / algebraMap k[X] (RatFunc k) B ∧
      ∀ z : k, eval z N = 0 → eval z B ≠ 0 := by
  refine ⟨r.num, r.denom, r.denom_ne_zero,
    (RatFunc.num_div_denom r).symm, ?_⟩
  intro z hnum hden
  obtain ⟨A, B, hbezout⟩ := r.isCoprime_num_denom
  have heval := congrArg (fun u : k[X] => eval z u) hbezout
  simp only [eval_add, eval_mul, eval_one, hnum, hden, mul_zero, add_zero]
    at heval
  exact zero_ne_one heval

set_option maxHeartbeats 64000000 in
/-- A polynomial that is not a cube remains a noncube in its rational
function field. -/
theorem GCD369PolynomialNoncubeInRatFunc
    {K : Type*} [Field K] (H : K[X])
    (hnoncube : ¬ ∃ u : K[X], H = u ^ 3) :
    ¬ ∃ r : RatFunc K, algebraMap K[X] (RatFunc K) H = r ^ 3 := by
  rintro ⟨r, hr⟩
  rw [← RatFunc.num_div_denom r] at hr
  field_simp [RatFunc.denom_ne_zero] at hr
  have hmap : algebraMap K[X] (RatFunc K) (H * r.denom ^ 3) =
      algebraMap K[X] (RatFunc K) (r.num ^ 3) := by
    simp only [map_mul, map_pow]
    exact hr
  have hpoly : H * r.denom ^ 3 = r.num ^ 3 :=
    (RatFunc.algebraMap_injective K) hmap
  have hdvd : r.denom ^ 3 ∣ r.num ^ 3 := by
    refine ⟨H, ?_⟩
    rw [← hpoly, mul_comm]
  have hcoprime : IsCoprime (r.num ^ 3) (r.denom ^ 3) :=
    (RatFunc.isCoprime_num_denom r).pow
  have hdpowUnit : IsUnit (r.denom ^ 3) :=
    hcoprime.symm.isUnit_of_dvd hdvd
  have hdUnit : IsUnit r.denom :=
    (isUnit_pow_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hdpowUnit
  have hd : r.denom = 1 := (RatFunc.monic_denom r).eq_one_of_isUnit hdUnit
  apply hnoncube
  refine ⟨r.num, ?_⟩
  simpa [hd] using hpoly

set_option maxHeartbeats 64000000 in
/-- Polynomial noncubeness therefore supplies the concrete cubic Kummer
extension over the rational function field. -/
theorem GCD369PolynomialNoncubeKummerExtension
    {K : Type*} [Field K] (H : K[X]) (omega : K)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1)
    (hnoncube : ¬ ∃ u : K[X], H = u ^ 3) :
    let h : RatFunc K := algebraMap K[X] (RatFunc K) H
    let zeta : RatFunc K := algebraMap K (RatFunc K) omega
    let p : (RatFunc K)[X] := X ^ 3 - C h
    ∃ (_Hp : Irreducible p) (sigma : AdjoinRoot p ≃+* AdjoinRoot p),
      AdjoinRoot.root p ≠ 0 ∧
      AdjoinRoot.root p ^ 3 = algebraMap (RatFunc K) (AdjoinRoot p) h ∧
      sigma (AdjoinRoot.root p) =
        algebraMap (RatFunc K) (AdjoinRoot p) zeta * AdjoinRoot.root p ∧
      sigma (AdjoinRoot.root p) ≠ AdjoinRoot.root p ∧
      ∀ c : RatFunc K, sigma (algebraMap (RatFunc K) (AdjoinRoot p) c) =
        algebraMap (RatFunc K) (AdjoinRoot p) c := by
  dsimp only
  have hzeta3 : (algebraMap K (RatFunc K) omega) ^ 3 = 1 := by
    rw [← map_pow, homega3, map_one]
  have hzeta : algebraMap K (RatFunc K) omega ≠ 1 := by
    intro hzeta
    apply homega
    apply (algebraMap K (RatFunc K)).injective
    simpa using hzeta
  exact GCD369NoncubeCubicKummerExtension
    (algebraMap K[X] (RatFunc K) H) (algebraMap K (RatFunc K) omega)
    hzeta3 hzeta (GCD369PolynomialNoncubeInRatFunc H hnoncube)

set_option maxHeartbeats 64000000 in
/-- The canonical differential structure on the cubic adjoin-root extension
differentiates the Kummer equation exactly. -/
theorem GCD369KummerRootDerivative
    {F : Type*} [Field F] [CharZero F] [Differential F]
    (h : F) [Fact (Irreducible (X ^ 3 - C h : F[X]))]
    [Fact (X ^ 3 - C h : F[X]).Monic] :
    let s := AdjoinRoot.root (X ^ 3 - C h : F[X])
    3 * s ^ 2 * Differential.deriv s =
      algebraMap F (AdjoinRoot (X ^ 3 - C h)) (Differential.deriv h) := by
  dsimp only
  have hpow := congrArg Differential.deriv (root_X_pow_sub_C_pow 3 h)
  change Differential.deriv (AdjoinRoot.root (X ^ 3 - C h) ^ 3) =
    Differential.deriv (algebraMap F (AdjoinRoot (X ^ 3 - C h)) h) at hpow
  rw [deriv_algebraMap] at hpow
  simpa [Derivation.leibniz_pow, mul_assoc] using hpow

set_option maxHeartbeats 64000000 in
/-- Every cubic Kummer deck automorphism commutes with the canonical
derivative on the separable adjoin-root extension. -/
theorem GCD369KummerDeckCommutesWithDerivative
    {F : Type*} [Field F] [CharZero F] [Differential F]
    (h : F) [Fact (Irreducible (X ^ 3 - C h : F[X]))]
    [Fact (X ^ 3 - C h : F[X]).Monic] (eta : rootsOfUnity 3 F) :
    ∀ z : AdjoinRoot (X ^ 3 - C h : F[X]),
      (autAdjoinRootXPowSubC 3 h eta) (Differential.deriv z) =
        Differential.deriv ((autAdjoinRootXPowSubC 3 h eta) z) := by
  letI : Algebra.IsIntegral F (AdjoinRoot (X ^ 3 - C h : F[X])) :=
    AdjoinRoot.isIntegral_of_monic Fact.out
  intro z
  exact Differential.algEquiv_deriv' (autAdjoinRootXPowSubC 3 h eta) z

set_option maxHeartbeats 64000000 in
/-- Any differential structure on `k(x)` that differentiates embedded
polynomials in the standard way has constant field exactly `k`. -/
theorem GCD369RatFuncConstantsOfPolynomialDerivative
    {k : Type*} [Field k] [CharZero k] [Differential (RatFunc k)]
    (hpoly : ∀ p : k[X],
      Differential.deriv (algebraMap k[X] (RatFunc k) p) =
        algebraMap k[X] (RatFunc k) p.derivative)
    (r : RatFunc k) (hr : Differential.deriv r = 0) :
    ∃ c : k, r = algebraMap k (RatFunc k) c := by
  letI : Algebra ℤ (RatFunc k) := Ring.toIntAlgebra (RatFunc k)
  have hquot :
      Differential.deriv
          (algebraMap k[X] (RatFunc k) r.num /
            algebraMap k[X] (RatFunc k) r.denom) = 0 := by
    rw [RatFunc.num_div_denom]
    exact hr
  rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
    hpoly, hpoly] at hquot
  simp only [smul_eq_mul] at hquot
  have hdenMap : algebraMap k[X] (RatFunc k) r.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero r.denom_ne_zero
  have hwmap :
      algebraMap k[X] (RatFunc k) r.denom *
          algebraMap k[X] (RatFunc k) r.num.derivative -
        algebraMap k[X] (RatFunc k) r.num *
          algebraMap k[X] (RatFunc k) r.denom.derivative = 0 := by
    field_simp [hdenMap] at hquot
    linear_combination hquot
  have hw : r.denom * r.num.derivative - r.num * r.denom.derivative = 0 := by
    apply (RatFunc.algebraMap_injective k)
    simpa only [map_sub, map_mul, map_zero] using hwmap
  have hdiv : r.denom ∣ r.denom.derivative := by
    have : r.denom ∣ r.num * r.denom.derivative := by
      use r.num.derivative
      rw [← sub_eq_zero.mp hw]
    exact r.isCoprime_num_denom.symm.dvd_of_dvd_mul_left this
  have hdenDeriv : r.denom.derivative = 0 := by
    by_contra hd
    have hle : r.denom.natDegree ≤ r.denom.derivative.natDegree :=
      natDegree_le_of_dvd hdiv hd
    have hlt : r.denom.derivative.natDegree < r.denom.natDegree :=
      natDegree_derivative_lt (fun hdegree ↦ by
        apply hd
        exact Polynomial.derivative_eq_zero.mpr hdegree)
    exact (Nat.not_lt_of_ge hle) hlt
  have hnumDeriv : r.num.derivative = 0 := by
    have hprod : r.denom * r.num.derivative = 0 := by
      simpa [hdenDeriv] using hw
    exact (mul_eq_zero.mp hprod).resolve_left r.denom_ne_zero
  let cn : k := r.num.coeff 0
  let cd : k := r.denom.coeff 0
  have hnumC : r.num = C cn := eq_C_of_derivative_eq_zero hnumDeriv
  have hdenC : r.denom = C cd := eq_C_of_derivative_eq_zero hdenDeriv
  refine ⟨cn / cd, ?_⟩
  calc
    r = algebraMap k[X] (RatFunc k) r.num /
        algebraMap k[X] (RatFunc k) r.denom := (RatFunc.num_div_denom r).symm
    _ = algebraMap k[X] (RatFunc k) (C cn) /
        algebraMap k[X] (RatFunc k) (C cd) := by rw [hnumC, hdenC]
    _ = algebraMap k (RatFunc k) (cn / cd) := by
      rw [RatFunc.algebraMap_C, RatFunc.algebraMap_C, map_div₀]
      rfl

set_option maxHeartbeats 64000000 in
private noncomputable def gcd369RatFuncDerivativeRaw
    {k : Type*} [Field k] (r : RatFunc k) : RatFunc k :=
  r.liftOn'
    (fun p q ↦
      (algebraMap k[X] (RatFunc k) q * algebraMap k[X] (RatFunc k) p.derivative -
        algebraMap k[X] (RatFunc k) p * algebraMap k[X] (RatFunc k) q.derivative) /
        algebraMap k[X] (RatFunc k) q ^ 2)
    (by
      intro p q a hq ha
      have hma : algebraMap k[X] (RatFunc k) a ≠ 0 :=
        RatFunc.algebraMap_ne_zero ha
      have hmq : algebraMap k[X] (RatFunc k) q ≠ 0 :=
        RatFunc.algebraMap_ne_zero hq
      simp only [derivative_mul, map_mul, map_add]
      field_simp [hma, hmq]
      ring)

set_option maxHeartbeats 64000000 in
private theorem gcd369RatFuncDerivativeRaw_div
    {k : Type*} [Field k] (p q : k[X]) (_hq : q ≠ 0) :
    gcd369RatFuncDerivativeRaw (algebraMap k[X] (RatFunc k) p /
      algebraMap k[X] (RatFunc k) q) =
      (algebraMap k[X] (RatFunc k) q * algebraMap k[X] (RatFunc k) p.derivative -
        algebraMap k[X] (RatFunc k) p * algebraMap k[X] (RatFunc k) q.derivative) /
        algebraMap k[X] (RatFunc k) q ^ 2 := by
  unfold gcd369RatFuncDerivativeRaw
  rw [RatFunc.liftOn'_div]
  intro p
  simp

set_option maxHeartbeats 64000000 in
private theorem gcd369RatFuncDerivativeRaw_add
    {k : Type*} [Field k] (r t : RatFunc k) :
    gcd369RatFuncDerivativeRaw (r + t) =
      gcd369RatFuncDerivativeRaw r + gcd369RatFuncDerivativeRaw t := by
  induction r using RatFunc.induction_on with
  | f p q hq =>
    induction t using RatFunc.induction_on with
    | f u v hv =>
      have hqmap : algebraMap k[X] (RatFunc k) q ≠ 0 :=
        RatFunc.algebraMap_ne_zero hq
      have hvmap : algebraMap k[X] (RatFunc k) v ≠ 0 :=
        RatFunc.algebraMap_ne_zero hv
      rw [div_add_div _ _ hqmap hvmap, ← map_mul, ← map_mul, ← map_add, ← map_mul]
      rw [gcd369RatFuncDerivativeRaw_div _ _ (mul_ne_zero hq hv),
        gcd369RatFuncDerivativeRaw_div _ _ hq,
        gcd369RatFuncDerivativeRaw_div _ _ hv]
      simp only [derivative_mul, map_add, map_mul]
      field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero hv]
      ring

set_option maxHeartbeats 64000000 in
private theorem gcd369RatFuncDerivativeRaw_mul
    {k : Type*} [Field k] (r t : RatFunc k) :
    gcd369RatFuncDerivativeRaw (r * t) =
      r * gcd369RatFuncDerivativeRaw t + t * gcd369RatFuncDerivativeRaw r := by
  induction r using RatFunc.induction_on with
  | f p q hq =>
    induction t using RatFunc.induction_on with
    | f u v hv =>
      rw [div_mul_div_comm, ← map_mul, ← map_mul]
      rw [gcd369RatFuncDerivativeRaw_div _ _ (mul_ne_zero hq hv),
        gcd369RatFuncDerivativeRaw_div _ _ hq,
        gcd369RatFuncDerivativeRaw_div _ _ hv]
      simp only [derivative_mul, map_add, map_mul]
      field_simp [RatFunc.algebraMap_ne_zero hq, RatFunc.algebraMap_ne_zero hv]
      ring

set_option maxHeartbeats 64000000 in
private theorem gcd369RatFuncDerivativeRaw_C
    {k : Type*} [Field k] (c : k) :
    gcd369RatFuncDerivativeRaw (algebraMap k (RatFunc k) c) = 0 := by
  change gcd369RatFuncDerivativeRaw (RatFunc.C c) = 0
  rw [← RatFunc.algebraMap_C]
  conv_lhs =>
    rw [← div_one (algebraMap k[X] (RatFunc k) (C c)),
      ← (algebraMap k[X] (RatFunc k)).map_one]
  rw [gcd369RatFuncDerivativeRaw_div _ _ one_ne_zero]
  simp

set_option maxHeartbeats 64000000 in
private theorem gcd369RatFuncDerivativeRaw_smul
    {k : Type*} [Field k] (c : k) (r : RatFunc k) :
    gcd369RatFuncDerivativeRaw (c • r) = c • gcd369RatFuncDerivativeRaw r := by
  rw [Algebra.smul_def, gcd369RatFuncDerivativeRaw_mul,
    gcd369RatFuncDerivativeRaw_C]
  simp [Algebra.smul_def]

set_option maxHeartbeats 64000000 in
private noncomputable def gcd369RatFuncDerivativeLinear
    (k : Type*) [Field k] : RatFunc k →ₗ[k] RatFunc k where
  toFun := gcd369RatFuncDerivativeRaw
  map_add' := gcd369RatFuncDerivativeRaw_add
  map_smul' := gcd369RatFuncDerivativeRaw_smul

set_option maxHeartbeats 64000000 in
private noncomputable def gcd369RatFuncDerivation
    (k : Type*) [Field k] : Derivation k (RatFunc k) (RatFunc k) :=
  Derivation.mk' (gcd369RatFuncDerivativeLinear k) (by
    intro r t
    exact gcd369RatFuncDerivativeRaw_mul r t)

set_option maxHeartbeats 64000000 in
private noncomputable def gcd369RatFuncDifferential
    (k : Type*) [Field k] : Differential (RatFunc k) := by
  letI : Algebra ℤ (RatFunc k) := Ring.toIntAlgebra (RatFunc k)
  exact ⟨(gcd369RatFuncDerivation k).restrictScalars ℤ⟩

set_option maxHeartbeats 64000000 in
private theorem gcd369RatFuncDifferential_poly
    {k : Type*} [Field k] (p : k[X]) :
    letI : Differential (RatFunc k) := gcd369RatFuncDifferential k
    Differential.deriv (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (RatFunc k) p.derivative := by
  letI : Differential (RatFunc k) := gcd369RatFuncDifferential k
  change gcd369RatFuncDerivativeRaw (algebraMap k[X] (RatFunc k) p) = _
  conv_lhs =>
    rw [← div_one (algebraMap k[X] (RatFunc k) p),
      ← (algebraMap k[X] (RatFunc k)).map_one]
  rw [gcd369RatFuncDerivativeRaw_div _ _ one_ne_zero]
  simp

set_option maxHeartbeats 64000000 in
/-- The standard quotient-rule differential structure exists on `k(x)` and
has constant field exactly `k`. -/
theorem GCD369RatFuncStandardDifferential
    {k : Type*} [Field k] [CharZero k] :
    ∃ d : Differential (RatFunc k),
      (∀ p : k[X],
        @Differential.deriv (RatFunc k) _ d
            (algebraMap k[X] (RatFunc k) p) =
          algebraMap k[X] (RatFunc k) p.derivative) ∧
      (∀ r : RatFunc k, @Differential.deriv (RatFunc k) _ d r = 0 →
        ∃ c : k, r = algebraMap k (RatFunc k) c) := by
  refine ⟨gcd369RatFuncDifferential k, ?_, ?_⟩
  · exact gcd369RatFuncDifferential_poly
  · letI : Differential (RatFunc k) := gcd369RatFuncDifferential k
    exact GCD369RatFuncConstantsOfPolynomialDerivative
      gcd369RatFuncDifferential_poly

set_option maxHeartbeats 64000000 in
/-- The selected standard quotient-rule differential on `k(x)`. -/
noncomputable instance GCD369RatFuncDifferential
    (k : Type*) [Field k] [CharZero k] : Differential (RatFunc k) :=
  (GCD369RatFuncStandardDifferential (k := k)).choose

set_option maxHeartbeats 64000000 in
/-- The selected differential differentiates embedded polynomials by the
ordinary polynomial derivative. -/
theorem GCD369RatFuncDerivative
    {k : Type*} [Field k] [CharZero k] (p : k[X]) :
    Differential.deriv (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (RatFunc k) p.derivative :=
  (GCD369RatFuncStandardDifferential (k := k)).choose_spec.1 p

set_option maxHeartbeats 64000000 in
/-- The constants of the selected standard differential on `k(x)` are
exactly the elements of `k`. -/
theorem GCD369RatFuncConstants
    {k : Type*} [Field k] [CharZero k]
    (r : RatFunc k) (hr : Differential.deriv r = 0) :
    ∃ c : k, r = algebraMap k (RatFunc k) c :=
  (GCD369RatFuncStandardDifferential (k := k)).choose_spec.2 r hr

set_option maxHeartbeats 64000000 in
/-- Evaluation at the canonical function-field coordinate is exactly the
two-stage embedding `k[x] → k(x) → L`. -/
theorem GCD369CanonicalEval
    {k L : Type*} [Field k] [CharZero k]
    [Field L] [Algebra k L] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) L]
    (P : k[X]) :
    let phi : k[X] →+* L :=
      (algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))
    aeval (phi X) P = phi P := by
  dsimp only
  let phi : k[X] →+* L :=
    (algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))
  change aeval (phi X) P = phi P
  have hhom : (aeval (phi X)).toRingHom = phi := by
    apply Polynomial.ringHom_ext
    · intro c
      dsimp [phi]
      simp [IsScalarTower.algebraMap_apply k (RatFunc k) L]
    · simp
  exact DFunLike.congr_fun hhom P

set_option maxHeartbeats 64000000 in
/-- The canonical function-field coordinate differentiates to one in every
differential extension of the standard quotient-rule structure. -/
theorem GCD369CanonicalXDerivative
    {k L : Type*} [Field k] [CharZero k]
    [Field L] [Algebra k L] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) L]
    [Differential L] [DifferentialAlgebra (RatFunc k) L] :
    let phi : k[X] →+* L :=
      (algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))
    Differential.deriv (phi X) = 1 := by
  dsimp only
  change Differential.deriv
    (algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) X)) = 1
  rw [deriv_algebraMap, GCD369RatFuncDerivative, derivative_X, map_one, map_one]

set_option maxHeartbeats 64000000 in
/-- The ground field remains differential-constant after passing through
`k(x)` to a differential extension. -/
theorem GCD369BaseConstants
    {k L : Type*} [Field k] [CharZero k]
    [Field L] [Algebra k L] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) L]
    [Differential L] [DifferentialAlgebra (RatFunc k) L]
    (c : k) :
    Differential.deriv (algebraMap k L c) = 0 := by
  rw [IsScalarTower.algebraMap_apply k (RatFunc k) L, deriv_algebraMap]
  have hc := GCD369RatFuncDerivative (C c : k[X])
  simpa using hc

set_option maxHeartbeats 64000000 in
/-- After embedding `k[x]` through `k(x)` into a differential extension,
ordinary inner polynomial differentiation becomes coefficientwise
differentiation in that extension. -/
theorem GCD369MapSourceXDeriv
    {k L : Type*} [Field k] [CharZero k]
    [Field L] [Algebra (RatFunc k) L] [Differential L]
    [DifferentialAlgebra (RatFunc k) L]
    (p : k[X][X]) :
    let phi : k[X] →+* L :=
      (algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))
    Differential.mapCoeffs (p.map phi) = (GCD369SourceXDeriv p).map phi := by
  dsimp only
  let phi : k[X] →+* L :=
    (algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))
  change Differential.mapCoeffs (p.map phi) = (GCD369SourceXDeriv p).map phi
  apply Polynomial.ext
  intro n
  rw [Differential.coeff_mapCoeffs, coeff_map, coeff_map,
    GCD369SourceXDeriv_coeff]
  dsimp [phi]
  rw [deriv_algebraMap, GCD369RatFuncDerivative]

set_option maxHeartbeats 64000000 in
/-- Consequently a literal bivariate source bracket maps to the differential
polynomial bracket used throughout the Kummer normalization. -/
theorem GCD369MapSourceBracket
    {k L : Type*} [Field k] [CharZero k]
    [Field L] [Algebra (RatFunc k) L] [Differential L]
    [DifferentialAlgebra (RatFunc k) L]
    (p q : k[X][X]) (J : k[X])
    (hD : GCD369SourceXDeriv p * derivative q
      - derivative p * GCD369SourceXDeriv q = C J) :
    let phi : k[X] →+* L :=
      (algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))
    Differential.mapCoeffs (p.map phi) * derivative (q.map phi)
        - derivative (p.map phi) * Differential.mapCoeffs (q.map phi) =
      C (phi J) := by
  dsimp only
  let phi : k[X] →+* L :=
    (algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))
  change Differential.mapCoeffs (p.map phi) * derivative (q.map phi)
      - derivative (p.map phi) * Differential.mapCoeffs (q.map phi) = C (phi J)
  rw [show Differential.mapCoeffs (p.map phi) =
      (GCD369SourceXDeriv p).map phi by exact GCD369MapSourceXDeriv p]
  rw [show Differential.mapCoeffs (q.map phi) =
      (GCD369SourceXDeriv q).map phi by exact GCD369MapSourceXDeriv q]
  rw [Polynomial.derivative_map, Polynomial.derivative_map]
  simpa only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C] using
    congrArg (Polynomial.map phi) hD

set_option maxHeartbeats 64000000 in
/-- A normalized literal bivariate source lifts to degree six and nine over
the Kummer differential field, with leading coefficients `s⁶,s⁹` and the
same mapped Keller bracket. -/
theorem GCD369LiftSourceData
    {k L : Type*} [Field k] [CharZero k]
    [Field L] [Algebra (RatFunc k) L] [Differential L]
    [DifferentialAlgebra (RatFunc k) L]
    (p q : k[X][X]) (H J : k[X]) (s : L)
    (hp : p.natDegree = 6) (hq : q.natDegree = 9)
    (hp6 : p.coeff 6 = H ^ 2) (hq9 : q.coeff 9 = H ^ 3)
    (hs : s ^ 3 = ((algebraMap (RatFunc k) L).comp
      (algebraMap k[X] (RatFunc k))) H)
    (hD : GCD369SourceXDeriv p * derivative q
      - derivative p * GCD369SourceXDeriv q = C J) :
    let phi : k[X] →+* L :=
      (algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))
    let P := p.map phi
    let Q := q.map phi
    P.natDegree = 6 ∧ Q.natDegree = 9 ∧
      P.coeff 6 = s ^ 6 ∧ Q.coeff 9 = s ^ 9 ∧
      (Differential.mapCoeffs P * derivative Q -
        derivative P * Differential.mapCoeffs Q = C (phi J)) := by
  dsimp only
  let phi : k[X] →+* L :=
    (algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))
  have hphi : Function.Injective phi :=
    (algebraMap (RatFunc k) L).injective.comp (RatFunc.algebraMap_injective k)
  have hPdeg : (p.map phi).natDegree = 6 := by
    rw [Polynomial.natDegree_map_eq_of_injective hphi, hp]
  have hQdeg : (q.map phi).natDegree = 9 := by
    rw [Polynomial.natDegree_map_eq_of_injective hphi, hq]
  have hP6 : (p.map phi).coeff 6 = s ^ 6 := by
    rw [coeff_map, hp6, map_pow, ← hs]
    ring
  have hQ9 : (q.map phi).coeff 9 = s ^ 9 := by
    rw [coeff_map, hq9, map_pow, ← hs]
    ring
  have hbr := GCD369MapSourceBracket (L := L) p q J hD
  dsimp only at hbr
  change Differential.mapCoeffs (p.map phi) * derivative (q.map phi) -
      derivative (p.map phi) * Differential.mapCoeffs (q.map phi) = C (phi J)
    at hbr
  change (p.map phi).natDegree = 6 ∧ (q.map phi).natDegree = 9 ∧
    (p.map phi).coeff 6 = s ^ 6 ∧ (q.map phi).coeff 9 = s ^ 9 ∧
    (Differential.mapCoeffs (p.map phi) * derivative (q.map phi) -
      derivative (p.map phi) * Differential.mapCoeffs (q.map phi) = C (phi J))
  exact ⟨hPdeg, hQdeg, hP6, hQ9, hbr⟩

set_option maxHeartbeats 64000000 in
/-- A literal normalized bivariate source over `k[x]`, once placed in any
cubic-Kummer differential extension with its deck action, lands in the full
aligned presentation consumed by the noncube exclusion. -/
theorem GCD369LiftedSourceAlignedPresentation
    {k L : Type*} [Field k] [CharZero k]
    [Field L] [CharZero L] [Algebra (RatFunc k) L] [Differential L]
    [DifferentialAlgebra (RatFunc k) L]
    (sigma : L ≃+* L) (omega s : L)
    (p q : k[X][X]) (H J : k[X])
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1) (hs0 : s ≠ 0)
    (hsigmaS : sigma s = omega * s)
    (hsigmaPhi : ∀ a : k[X], sigma (((algebraMap (RatFunc k) L).comp
      (algebraMap k[X] (RatFunc k))) a) =
        ((algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))) a)
    (hfix : ∀ c : L, Differential.deriv c = 0 → sigma c = c)
    (hp : p.natDegree = 6) (hq : q.natDegree = 9)
    (hp6 : p.coeff 6 = H ^ 2) (hq9 : q.coeff 9 = H ^ 3)
    (hs : s ^ 3 = ((algebraMap (RatFunc k) L).comp
      (algebraMap k[X] (RatFunc k))) H)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C J) :
    let phi : k[X] →+* L :=
      (algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))
    let P := p.map phi
    let Q := q.map phi
    ∃ r a0 a1 a2 a3 a4 c6 kappa c0 : L,
      sigma r = omega * r ∧
      P.comp (C s⁻¹ * (X - C r)) = GCD369AlignedF a0 a1 a2 a3 a4 ∧
      sigma a0 = a0 ∧ sigma a1 = omega ^ 2 * a1 ∧
      sigma a2 = omega * a2 ∧ sigma a3 = a3 ∧
      sigma a4 = omega ^ 2 * a4 ∧ sigma kappa = kappa ∧
      Differential.deriv c6 = 0 ∧ Differential.deriv kappa = 0 ∧
      Differential.deriv c0 = 0 ∧
      (Differential.mapCoeffs (GCD369AlignedF a0 a1 a2 a3 a4) *
          derivative (GCD369AlignedG a0 a1 a2 a3 a4 kappa) -
        derivative (GCD369AlignedF a0 a1 a2 a3 a4) *
          Differential.mapCoeffs (GCD369AlignedG a0 a1 a2 a3 a4 kappa) =
        C ((((algebraMap (RatFunc k) L).comp
          (algebraMap k[X] (RatFunc k))) J) / s)) ∧
      Q.comp (C s⁻¹ * (X - C r)) =
        GCD369AlignedG a0 a1 a2 a3 a4 kappa +
          C c6 * (P.comp (C s⁻¹ * (X - C r))) + C c0 := by
  dsimp only
  let phi : k[X] →+* L :=
    (algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))
  let P := p.map phi
  let Q := q.map phi
  have hpfix : P.map sigma.toRingHom = P := by
    apply Polynomial.ext
    intro n
    simp only [P, coeff_map]
    exact hsigmaPhi (p.coeff n)
  have hqfix : Q.map sigma.toRingHom = Q := by
    apply Polynomial.ext
    intro n
    simp only [Q, coeff_map]
    exact hsigmaPhi (q.coeff n)
  have hlift := GCD369LiftSourceData (L := L) p q H J s
    hp hq hp6 hq9 hs hD
  dsimp only at hlift
  change P.natDegree = 6 ∧ Q.natDegree = 9 ∧
    P.coeff 6 = s ^ 6 ∧ Q.coeff 9 = s ^ 9 ∧
    (Differential.mapCoeffs P * derivative Q -
      derivative P * Differential.mapCoeffs Q = C (phi J)) at hlift
  obtain ⟨hP, hQ, hP6, hQ9, hbr⟩ := hlift
  exact GCD369KummerSourceAlignedPresentation sigma omega P Q s (phi J)
    homega3 homega hs0 hsigmaS hpfix hqfix hfix hP hP6 hQ hQ9 hbr

set_option maxHeartbeats 64000000 in
/-- Constants do not enlarge in an algebraic differential extension when the
base constant field is algebraically closed. -/
theorem GCD369AlgebraicDifferentialConstantsDescend
    {k F L : Type*} [Field k] [IsAlgClosed k]
    [Field F] [CharZero F] [Differential F]
    [Field L] [Algebra k F] [Algebra F L] [Algebra k L]
    [IsScalarTower k F L] [Differential L] [DifferentialAlgebra F L]
    [Algebra.IsAlgebraic F L]
    (hFconstants : ∀ a : F, Differential.deriv a = 0 →
      ∃ a0 : k, a = algebraMap k F a0)
    (c : L) (hc : Differential.deriv c = 0) :
    ∃ c0 : k, c = algebraMap k L c0 := by
  let p : F[X] := minpoly F c
  have hcIntegralF : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  have hpEval : aeval c p = 0 := minpoly.aeval F c
  have hpDerivEval : aeval c (Differential.mapCoeffs p) = 0 := by
    have h := congrArg Differential.deriv hpEval
    rw [map_zero, Differential.deriv_aeval_eq, hc, mul_zero, add_zero] at h
    exact h
  have hpDvd : p ∣ Differential.mapCoeffs p := minpoly.dvd F c hpDerivEval
  have hpMapZero : Differential.mapCoeffs p = 0 := by
    by_contra hpMap
    have hdegree : (Differential.mapCoeffs p).degree < (p.natDegree : WithBot ℕ) := by
      rw [degree_lt_iff_coeff_zero]
      intro m hm
      rw [Differential.coeff_mapCoeffs]
      by_cases htop : m = p.natDegree
      · subst m
        rw [coeff_natDegree, minpoly.monic hcIntegralF |>.leadingCoeff]
        simp
      · have hmgt : p.natDegree < m := lt_of_le_of_ne hm (Ne.symm htop)
        rw [coeff_eq_zero_of_natDegree_lt hmgt]
        exact map_zero Differential.deriv
    have hnatDegree : (Differential.mapCoeffs p).natDegree < p.natDegree :=
      (natDegree_lt_iff_degree_lt hpMap).mpr hdegree
    have hle : p.natDegree ≤ (Differential.mapCoeffs p).natDegree :=
      natDegree_le_of_dvd hpDvd hpMap
    exact (Nat.not_lt_of_ge hle) hnatDegree
  have hpCoeffConstant (n : ℕ) : Differential.deriv (p.coeff n) = 0 := by
    have h := congrArg (fun q : F[X] ↦ q.coeff n) hpMapZero
    simpa using h
  choose coeff0 hcoeff0 using fun n ↦ hFconstants (p.coeff n) (hpCoeffConstant n)
  let q : k[X] := ∑ n ∈ p.support, monomial n (coeff0 n)
  have hqMap : q.map (algebraMap k F) = p := by
    calc
      q.map (algebraMap k F) =
          ∑ n ∈ p.support, monomial n (algebraMap k F (coeff0 n)) := by
            dsimp [q]
            simp_rw [Polynomial.map_sum, map_monomial]
      _ = ∑ n ∈ p.support, monomial n (p.coeff n) := by
        simp_rw [hcoeff0]
      _ = p := p.as_sum_support.symm
  have hqMonic : q.Monic := by
    apply Polynomial.monic_of_injective (algebraMap k F).injective
    rw [hqMap]
    exact minpoly.monic hcIntegralF
  have hqEval : aeval c q = 0 := by
    rw [← Polynomial.aeval_map_algebraMap F c q, hqMap]
    exact hpEval
  have hcIntegralK : IsIntegral k c := ⟨q, hqMonic, hqEval⟩
  refine ⟨-(minpoly k c).coeff 0, ?_⟩
  have hlead : (minpoly k c).leadingCoeff = 1 := minpoly.monic hcIntegralK
  have hdegree : (minpoly k c).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hcIntegralK)
  have heval : aeval c (minpoly k c) = 0 := minpoly.aeval k c
  rw [eq_X_add_C_of_degree_eq_one hdegree, hlead, C_1, one_mul, aeval_add,
    aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at heval
  exact heval.trans (map_neg (algebraMap k L) ((minpoly k c).coeff 0)).symm

set_option maxHeartbeats 64000000 in
/-- A base-fixing automorphism of such an algebraic differential extension
fixes every differential constant. -/
theorem GCD369BaseFixingAutomorphismFixesConstants
    {k F L : Type*} [Field k] [IsAlgClosed k]
    [Field F] [CharZero F] [Differential F]
    [Field L] [Algebra k F] [Algebra F L] [Algebra k L]
    [IsScalarTower k F L] [Differential L] [DifferentialAlgebra F L]
    [Algebra.IsAlgebraic F L]
    (sigma : L ≃+* L)
    (hsigmaF : ∀ a : F, sigma (algebraMap F L a) = algebraMap F L a)
    (hFconstants : ∀ a : F, Differential.deriv a = 0 →
      ∃ a0 : k, a = algebraMap k F a0) :
    ∀ c : L, Differential.deriv c = 0 → sigma c = c := by
  intro c hc
  obtain ⟨c0, hc0⟩ :=
    GCD369AlgebraicDifferentialConstantsDescend hFconstants c hc
  rw [hc0, IsScalarTower.algebraMap_apply k F L, hsigmaF]

set_option maxHeartbeats 64000000 in
/-- The first source row aligns an algebraic Kummer extension directly from
the base constant-field theorem and the base-fixing deck action. -/
theorem GCD369KummerAlignmentFromBaseConstants
    {k F L : Type*} [Field k] [IsAlgClosed k]
    [Field F] [CharZero F] [Differential F]
    [Field L] [CharZero L] [Algebra k F] [Algebra F L] [Algebra k L]
    [IsScalarTower k F L] [Differential L] [DifferentialAlgebra F L]
    [Algebra.IsAlgebraic F L]
    (sigma : L ≃+* L) (omega s a b : L)
    (hsigmaF : ∀ u : F, sigma (algebraMap F L u) = algebraMap F L u)
    (hFconstants : ∀ u : F, Differential.deriv u = 0 →
      ∃ u0 : k, u = algebraMap k F u0)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1) (hs : s ≠ 0)
    (hsigmaS : sigma s = omega * s)
    (hsigmaA : sigma a = a) (hsigmaB : sigma b = b)
    (hrow :
      3 * s ^ 4 * Differential.deriv a
          - 15 * s ^ 3 * a * Differential.deriv s
        - 2 * s * Differential.deriv b
          + 16 * b * Differential.deriv s = 0) :
    3 * a / s ^ 5 - 2 * b / s ^ 8 = 0 := by
  exact GCD369KummerAlignmentFromFirstRow sigma omega s a b
    homega3 homega hs hsigmaS hsigmaA hsigmaB
    (GCD369BaseFixingAutomorphismFixesConstants sigma hsigmaF hFconstants) hrow

set_option maxHeartbeats 64000000 in
/-- A polynomial noncube supplies the complete differential Kummer package:
the irreducible cubic extension, deck action, constant descent, and first-row
alignment. -/
theorem GCD369PolynomialNoncubeDifferentialKummerPackage
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (H : k[X]) (omega : k)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1)
    (hnoncube : ¬ ∃ u : k[X], H = u ^ 3) :
    ∃ Hp : Irreducible
        (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]),
      letI : Fact (Irreducible
          (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])) := ⟨Hp⟩
      letI : Fact
          (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]).Monic :=
        ⟨monic_X_pow_sub_C _ (by norm_num)⟩
      ∃ sigma : AdjoinRoot
          (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) ≃+*
        AdjoinRoot
          (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]),
        AdjoinRoot.root
            (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) ≠ 0 ∧
        AdjoinRoot.root
              (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) ^ 3 =
          algebraMap (RatFunc k)
            (AdjoinRoot
              (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]))
            (algebraMap k[X] (RatFunc k) H) ∧
        sigma (AdjoinRoot.root
            (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])) =
          algebraMap (RatFunc k)
              (AdjoinRoot
                (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]))
              (algebraMap k (RatFunc k) omega) *
            AdjoinRoot.root
              (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) ∧
        sigma (AdjoinRoot.root
            (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])) ≠
          AdjoinRoot.root
            (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) ∧
        (∀ u : RatFunc k,
          sigma (algebraMap (RatFunc k)
              (AdjoinRoot
                (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])) u) =
            algebraMap (RatFunc k)
              (AdjoinRoot
                (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])) u) ∧
        (3 * AdjoinRoot.root
                (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) ^ 2 *
            Differential.deriv (AdjoinRoot.root
              (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])) =
          algebraMap (RatFunc k)
              (AdjoinRoot
                (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]))
            (Differential.deriv (algebraMap k[X] (RatFunc k) H))) ∧
        (∀ z : AdjoinRoot
            (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]),
          sigma (Differential.deriv z) = Differential.deriv (sigma z)) ∧
        (∀ c : AdjoinRoot
            (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]),
          Differential.deriv c = 0 →
          ∃ c0 : k, c = algebraMap k
            (AdjoinRoot
              (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])) c0) ∧
        (∀ c : AdjoinRoot
            (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]),
          Differential.deriv c = 0 → sigma c = c) ∧
        (∀ a b : AdjoinRoot
            (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]),
          sigma a = a → sigma b = b →
          3 * AdjoinRoot.root
                (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) ^ 4 *
                Differential.deriv a
              - 15 * AdjoinRoot.root
                  (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) ^ 3 *
                a * Differential.deriv (AdjoinRoot.root
                  (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]))
              - 2 * AdjoinRoot.root
                  (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) *
                Differential.deriv b
              + 16 * b * Differential.deriv (AdjoinRoot.root
                  (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])) = 0 →
          3 * a / AdjoinRoot.root
                  (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) ^ 5 -
              2 * b / AdjoinRoot.root
                  (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) ^ 8 = 0) := by
  obtain ⟨Hp, sigma, hs0, hs3, hsigmaS, hsigmaNe, hsigmaF⟩ :=
    GCD369PolynomialNoncubeKummerExtension H omega homega3 homega hnoncube
  refine ⟨Hp, ?_⟩
  letI : Fact (Irreducible
      (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])) := ⟨Hp⟩
  letI : Fact
      (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]).Monic :=
    ⟨monic_X_pow_sub_C _ (by norm_num)⟩
  letI : Algebra.IsIntegral (RatFunc k)
      (AdjoinRoot
      (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])) :=
    AdjoinRoot.isIntegral_of_monic Fact.out
  letI : CharZero
      (AdjoinRoot
        (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])) :=
    charZero_of_injective_algebraMap
      (algebraMap (RatFunc k)
        (AdjoinRoot
          (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]))).injective
  have hFconstants : ∀ r : RatFunc k, Differential.deriv r = 0 →
      ∃ c : k, r = algebraMap k (RatFunc k) c :=
    GCD369RatFuncConstants
  refine ⟨sigma, hs0, hs3, hsigmaS, hsigmaNe, hsigmaF,
    GCD369KummerRootDerivative _, ?_, ?_, ?_, ?_⟩
  · let sigmaAlg :
        AdjoinRoot
            (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X])
          ≃ₐ[RatFunc k]
        AdjoinRoot
            (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]) :=
      { sigma with commutes' := hsigmaF }
    intro z
    exact Differential.algEquiv_deriv' sigmaAlg z
  · exact GCD369AlgebraicDifferentialConstantsDescend hFconstants
  · exact GCD369BaseFixingAutomorphismFixesConstants sigma hsigmaF
      hFconstants
  · intro a b ha hb hrow
    have hzeta3 : (algebraMap k (RatFunc k) omega) ^ 3 = 1 := by
      rw [← map_pow, homega3, map_one]
    have hzeta : algebraMap k (RatFunc k) omega ≠ 1 := by
      intro hzeta
      apply homega
      apply (algebraMap k (RatFunc k)).injective
      simpa using hzeta
    have homegaL3 :
        (algebraMap (RatFunc k)
            (AdjoinRoot
              (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]))
            (algebraMap k (RatFunc k) omega)) ^ 3 = 1 := by
      rw [← map_pow, hzeta3, map_one]
    have homegaL :
        algebraMap (RatFunc k)
            (AdjoinRoot
              (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]))
            (algebraMap k (RatFunc k) omega) ≠ 1 := by
      intro hL
      apply hzeta
      apply (algebraMap (RatFunc k)
        (AdjoinRoot
          (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]))).injective
      simpa using hL
    exact GCD369KummerAlignmentFromBaseConstants sigma
      (algebraMap (RatFunc k)
        (AdjoinRoot
          (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]))
        (algebraMap k (RatFunc k) omega))
      (AdjoinRoot.root
        (X ^ 3 - C (algebraMap k[X] (RatFunc k) H) : (RatFunc k)[X]))
      a b hsigmaF hFconstants homegaL3 homegaL hs0 hsigmaS ha hb hrow

set_option maxHeartbeats 64000000 in
/-- A literal normalized `(6,9)` source with noncube polynomial core now
constructs its own differential Kummer extension and lands in the complete
aligned presentation.  No aligned coefficients, affine translation, deck
weights, or high-row integration constants are assumed. -/
theorem GCD369PolynomialNoncubeSourceAlignedPresentation
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (H : k[X]) (omega : k) (p q : k[X][X]) (J : k[X])
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1)
    (hnoncube : ¬ ∃ u : k[X], H = u ^ 3)
    (hp : p.natDegree = 6) (hq : q.natDegree = 9)
    (hp6 : p.coeff 6 = H ^ 2) (hq9 : q.coeff 9 = H ^ 3)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C J) :
    let hF : RatFunc k := algebraMap k[X] (RatFunc k) H
    let f : (RatFunc k)[X] := X ^ 3 - C hF
    ∃ Hp : Irreducible f,
      letI : Fact (Irreducible f) := ⟨Hp⟩
      letI : Fact f.Monic := ⟨monic_X_pow_sub_C _ (by norm_num)⟩
      ∃ sigma : AdjoinRoot f ≃+* AdjoinRoot f,
        let s := AdjoinRoot.root f
        let zeta := algebraMap (RatFunc k) (AdjoinRoot f)
          (algebraMap k (RatFunc k) omega)
        let phi : k[X] →+* AdjoinRoot f :=
          (algebraMap (RatFunc k) (AdjoinRoot f)).comp
            (algebraMap k[X] (RatFunc k))
        GCD369KummerAlignedSourcePackage (k := k) (F := RatFunc k)
          sigma zeta s (phi H) (phi J) (p.map phi) (q.map phi) := by
  dsimp only
  obtain ⟨Hp, hpackage⟩ :=
    GCD369PolynomialNoncubeDifferentialKummerPackage H omega
      homega3 homega hnoncube
  refine ⟨Hp, ?_⟩
  let f : (RatFunc k)[X] :=
    X ^ 3 - C (algebraMap k[X] (RatFunc k) H)
  letI : Fact (Irreducible f) := ⟨Hp⟩
  letI : Fact f.Monic := ⟨monic_X_pow_sub_C _ (by norm_num)⟩
  letI : Algebra.IsIntegral (RatFunc k) (AdjoinRoot f) :=
    AdjoinRoot.isIntegral_of_monic Fact.out
  letI : CharZero (AdjoinRoot f) :=
    charZero_of_injective_algebraMap
      (algebraMap (RatFunc k) (AdjoinRoot f)).injective
  change (∃ sigma : AdjoinRoot f ≃+* AdjoinRoot f,
    GCD369KummerAlignedSourcePackage (k := k) (F := RatFunc k) sigma
      (algebraMap (RatFunc k) (AdjoinRoot f)
        (algebraMap k (RatFunc k) omega))
      (AdjoinRoot.root f)
      (((algebraMap (RatFunc k) (AdjoinRoot f)).comp
        (algebraMap k[X] (RatFunc k))) H)
      (((algebraMap (RatFunc k) (AdjoinRoot f)).comp
        (algebraMap k[X] (RatFunc k))) J)
      (p.map ((algebraMap (RatFunc k) (AdjoinRoot f)).comp
        (algebraMap k[X] (RatFunc k))))
      (q.map ((algebraMap (RatFunc k) (AdjoinRoot f)).comp
        (algebraMap k[X] (RatFunc k)))))
  change (∃ sigma : AdjoinRoot f ≃+* AdjoinRoot f,
    AdjoinRoot.root f ≠ 0 ∧ _) at hpackage
  obtain ⟨sigma, hs0, hs3, hsigmaS, _hsigmaNe, hsigmaF,
    _hrootD, _hcomm, hconstants, hfix, _halign⟩ := hpackage
  refine ⟨sigma, ?_⟩
  let s := AdjoinRoot.root f
  let zeta := algebraMap (RatFunc k) (AdjoinRoot f)
    (algebraMap k (RatFunc k) omega)
  let phi : k[X] →+* AdjoinRoot f :=
    (algebraMap (RatFunc k) (AdjoinRoot f)).comp
      (algebraMap k[X] (RatFunc k))
  have hzeta3 : (algebraMap k (RatFunc k) omega) ^ 3 = 1 := by
    rw [← map_pow, homega3, map_one]
  have hzeta : algebraMap k (RatFunc k) omega ≠ 1 := by
    intro h
    apply homega
    apply (algebraMap k (RatFunc k)).injective
    simpa using h
  have homegaL3 : zeta ^ 3 = 1 := by
    calc
      zeta ^ 3 = algebraMap (RatFunc k) (AdjoinRoot f)
          ((algebraMap k (RatFunc k) omega) ^ 3) := by
        rw [map_pow]
      _ = algebraMap (RatFunc k) (AdjoinRoot f) 1 := by rw [hzeta3]
      _ = 1 := map_one _
  have homegaL : zeta ≠ 1 := by
    dsimp [zeta]
    intro h
    apply hzeta
    apply (algebraMap (RatFunc k) (AdjoinRoot f)).injective
    simpa using h
  have hsigmaPhi : ∀ a : k[X], sigma (phi a) = phi a := by
    intro a
    exact hsigmaF (algebraMap k[X] (RatFunc k) a)
  have haligned := GCD369LiftedSourceAlignedPresentation
    sigma zeta s p q H J homegaL3 homegaL hs0 hsigmaS hsigmaPhi hfix
      hp hq hp6 hq9 hs3 hD
  dsimp only at haligned
  change GCD369KummerAlignedSourcePackage (k := k) (F := RatFunc k)
    sigma zeta s (phi H) (phi J) (p.map phi) (q.map phi)
  unfold GCD369KummerAlignedSourcePackage
  refine ⟨hs0, hsigmaS, hs3, hsigmaF, hconstants, hfix, ?_⟩
  change GCD369KummerAlignedPresentation sigma zeta s (phi J)
    (p.map phi) (q.map phi)
  simpa only [GCD369KummerAlignedPresentation] using haligned
