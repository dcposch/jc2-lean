/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), OpenAI Codex agent (formalization)
-/
import Mathlib
import Mathlib.FieldTheory.Differential.Basic

/-!
# Challenge: aligned noncube exclusion at partial degrees `(6,9)`

The theorem excludes the noncube core of an aligned Keller pair after its
standard cubic-Kummer and rational function-field data have been exposed.
-/

open Polynomial

/-- The degree-six member of the aligned eight-high-row normal form. -/
noncomputable def GCD369AlignedF {K : Type*} [Field K]
    (a0 a1 a2 a3 a4 : K) : K[X] :=
  X ^ 6 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0

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
  sorry

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
  sorry

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
  sorry

/-- A polynomial that is not a cube remains a noncube in its rational
function field. -/
theorem GCD369PolynomialNoncubeInRatFunc
    {K : Type*} [Field K] (H : K[X])
    (hnoncube : ¬ ∃ u : K[X], H = u ^ 3) :
    ¬ ∃ r : RatFunc K, algebraMap K[X] (RatFunc K) H = r ^ 3 := by
  sorry

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
  sorry

/-- The canonical differential structure on the cubic adjoin-root extension
differentiates the Kummer equation exactly. -/
theorem GCD369KummerRootDerivative
    {F : Type*} [Field F] [CharZero F] [Differential F]
    (h : F) [Fact (Irreducible (X ^ 3 - C h : F[X]))]
    [Fact (X ^ 3 - C h : F[X]).Monic] :
    let s := AdjoinRoot.root (X ^ 3 - C h : F[X])
    3 * s ^ 2 * Differential.deriv s =
      algebraMap F (AdjoinRoot (X ^ 3 - C h)) (Differential.deriv h) := by
  sorry

/-- Every cubic Kummer deck automorphism commutes with the canonical
derivative on the separable adjoin-root extension. -/
theorem GCD369KummerDeckCommutesWithDerivative
    {F : Type*} [Field F] [CharZero F] [Differential F]
    (h : F) [Fact (Irreducible (X ^ 3 - C h : F[X]))]
    [Fact (X ^ 3 - C h : F[X]).Monic] (eta : rootsOfUnity 3 F) :
    ∀ z : AdjoinRoot (X ^ 3 - C h : F[X]),
      (autAdjoinRootXPowSubC 3 h eta) (Differential.deriv z) =
        Differential.deriv ((autAdjoinRootXPowSubC 3 h eta) z) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- No aligned Keller pair in the nontrivial cubic-Kummer branch can have a
noncube polynomial core under the displayed function-field presentations. -/
theorem GCD369AlignedNoncubeExclusion
    {k L : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    [Field L] [CharZero L] [Algebra k L] [Differential L]
    (sigma : L ≃+* L)
    (omega x s h q a0 a1 a2 a3 a4 kappa terminal : L) (j : k)
    (H NY DY Nq Bq : k[X])
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1) (homega2 : omega ^ 2 ≠ 1)
    (hfix : ∀ c : L, Differential.deriv c = 0 → sigma c = c)
    (ha0 : sigma a0 = a0) (ha1 : sigma a1 = omega ^ 2 * a1)
    (ha2 : sigma a2 = omega * a2) (ha3 : sigma a3 = a3)
    (ha4 : sigma a4 = omega ^ 2 * a4)
    (hkappaSigma : sigma kappa = kappa)
    (hkappaDot : Differential.deriv kappa = 0)
    (hconstants : ∀ c : L, Differential.deriv c = 0 →
      ∃ c0 : k, c = algebraMap k L c0)
    (hconst : ∀ c : k, Differential.deriv (algebraMap k L c) = 0)
    (hx : Differential.deriv x = 1)
    (hinj : Function.Injective (aeval x : k[X] → L))
    (hterminal :
      Differential.mapCoeffs (GCD369AlignedF a0 a1 a2 a3 a4)
          * derivative (GCD369AlignedG a0 a1 a2 a3 a4 kappa)
        - derivative (GCD369AlignedF a0 a1 a2 a3 a4)
          * Differential.mapCoeffs (GCD369AlignedG a0 a1 a2 a3 a4 kappa)
        = C terminal)
    (hs : s ^ 3 = h) (hKeller : s * terminal = algebraMap k L j) (hj : j ≠ 0)
    (hh : h = aeval x H) (hH : H ≠ 0) (hdegreeDiv : 3 ∣ H.natDegree)
    (hnoncube : ¬ ∃ u : k[X], H = u ^ 3)
    (hY : 3 * a4 * (8 * a2 - 2 * a4 ^ 2) = aeval x NY / aeval x DY)
    (hDY : DY ≠ 0)
    (hYreduced : ∀ z : k, eval z NY = 0 → eval z DY ≠ 0)
    (hlambda : a4 / 4 = s ^ 2 * q)
    (hq : q = aeval x Nq / aeval x Bq)
    (hNq : Nq ≠ 0) (hBq : Bq ≠ 0)
    (hqreduced : ∀ z : k, eval z Nq = 0 → eval z Bq ≠ 0) : False := by
  sorry
