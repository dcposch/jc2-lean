import FaberNormalForm

noncomputable section
open Polynomial

/-! # Literal Faber lower rows

This module identifies the five remaining rows of the normalized Jacobian
with the derivatives of the explicit Laurent invariants `r₁, …, r₅`.
-/

/-- The complete constant-parameter Faber polynomial. -/
noncomputable def GCD369CubeFaberNormalPolynomial
    {K : Type*} [Field K]
    (a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0 : K) : K[X] :=
  GCD369CubeFaberNine a0 a1 a2 a3 a4 +
    C d * GCD369CubeFaberEight a0 a1 a2 a3 a4 +
    C c7 * GCD369CubeFaberSeven a0 a1 a2 a3 a4 +
    C c6 * GCD369CubeFaberSix a0 a1 a2 a3 a4 +
    C c5 * GCD369CubeFaberFive a0 a1 a2 a3 a4 +
    C c4 * GCD369CubeFaberFour a0 a1 a2 a3 a4 +
    C c3 * GCD369CubeFaberThree a0 a1 a2 a3 a4 +
    C c2 * GCD369CubeFaberTwo a0 a1 a2 a3 a4 +
    C c1 * GCD369CubeFaberOne a0 a1 a2 a3 a4 + C c0

/-- Polynomial part multiplying `D r₁` in the lower Jacobian rows. -/
noncomputable def GCD369CubeFaberLowerBasisOne
    {K : Type*} [Field K] (a2 a3 a4 : K) : K[X] :=
  monomial 4 6 + monomial 2 (3 * a4) + monomial 1 (2 * a3) +
    monomial 0 (a2 - a4 ^ 2 / 12)

/-- Polynomial part multiplying `D r₂` in the lower Jacobian rows. -/
noncomputable def GCD369CubeFaberLowerBasisTwo
    {K : Type*} [Field K] (a3 a4 : K) : K[X] :=
  monomial 3 6 + monomial 1 (2 * a4) + monomial 0 a3

/-- Polynomial part multiplying `D r₃` in the lower Jacobian rows. -/
noncomputable def GCD369CubeFaberLowerBasisThree
    {K : Type*} [Field K] (a4 : K) : K[X] :=
  monomial 2 6 + monomial 0 a4

/-- Polynomial part multiplying `D r₄` in the lower Jacobian rows. -/
noncomputable def GCD369CubeFaberLowerBasisFour
    {K : Type*} [Field K] : K[X] :=
  monomial 1 6

/-- Polynomial part multiplying `D r₅` in the lower Jacobian rows. -/
noncomputable def GCD369CubeFaberLowerBasisFive
    {K : Type*} [Field K] : K[X] :=
  monomial 0 6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Once the high Faber rows vanish, the complete normalized Jacobian is
the triangular combination of the derivatives of the five explicit Laurent
invariants.  The two gauge parameters `c₆,c₀` disappear identically. -/
theorem GCD369CubeFaberLowerRows
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 d c7 c6 c5 c4 c3 c2 c1 c0 : RatFunc k)
    (hd : GCD369CubeRatFuncDerivative d = 0)
    (hc7 : GCD369CubeRatFuncDerivative c7 = 0)
    (hc6 : GCD369CubeRatFuncDerivative c6 = 0)
    (hc5 : GCD369CubeRatFuncDerivative c5 = 0)
    (hc4 : GCD369CubeRatFuncDerivative c4 = 0)
    (hc3 : GCD369CubeRatFuncDerivative c3 = 0)
    (hc2 : GCD369CubeRatFuncDerivative c2 = 0)
    (hc1 : GCD369CubeRatFuncDerivative c1 = 0)
    (hc0 : GCD369CubeRatFuncDerivative c0 = 0)
    (hhigh :
      (GCD369CubeRatFuncJacobian
        (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
        (GCD369CubeFaberNormalPolynomial a0 a1 a2 a3 a4
          d c7 c6 c5 c4 c3 c2 c1 c0)).natDegree ≤ 4) :
    GCD369CubeRatFuncJacobian
        (GCD369CubeDepressedSextic a0 a1 a2 a3 a4)
        (GCD369CubeFaberNormalPolynomial a0 a1 a2 a3 a4
          d c7 c6 c5 c4 c3 c2 c1 c0) =
      GCD369CubeRatFuncDerivative
          (GCD369CubeFaberR1 a0 a1 a2 a3 a4
            d c7 c5 c4 c3 c2 c1) •
        GCD369CubeFaberLowerBasisOne a2 a3 a4 +
      GCD369CubeRatFuncDerivative
          (GCD369CubeFaberR2 a0 a1 a2 a3 a4
            d c7 c5 c4 c3 c2 c1) •
        GCD369CubeFaberLowerBasisTwo a3 a4 +
      GCD369CubeRatFuncDerivative
          (GCD369CubeFaberR3 a0 a1 a2 a3 a4
            d c7 c5 c4 c3 c2 c1) •
        GCD369CubeFaberLowerBasisThree a4 +
      GCD369CubeRatFuncDerivative
          (GCD369CubeFaberR4 a0 a1 a2 a3 a4
            d c7 c5 c4 c3 c2 c1) •
        GCD369CubeFaberLowerBasisFour +
      GCD369CubeRatFuncDerivative
          (GCD369CubeFaberR5 a0 a1 a2 a3 a4
            d c7 c5 c4 c3 c2 c1) •
        GCD369CubeFaberLowerBasisFive := by
  let rhs : (RatFunc k)[X] :=
    GCD369CubeRatFuncDerivative
        (GCD369CubeFaberR1 a0 a1 a2 a3 a4
          d c7 c5 c4 c3 c2 c1) •
      GCD369CubeFaberLowerBasisOne a2 a3 a4 +
    GCD369CubeRatFuncDerivative
        (GCD369CubeFaberR2 a0 a1 a2 a3 a4
          d c7 c5 c4 c3 c2 c1) •
      GCD369CubeFaberLowerBasisTwo a3 a4 +
    GCD369CubeRatFuncDerivative
        (GCD369CubeFaberR3 a0 a1 a2 a3 a4
          d c7 c5 c4 c3 c2 c1) •
      GCD369CubeFaberLowerBasisThree a4 +
    GCD369CubeRatFuncDerivative
        (GCD369CubeFaberR4 a0 a1 a2 a3 a4
          d c7 c5 c4 c3 c2 c1) •
      GCD369CubeFaberLowerBasisFour +
    GCD369CubeRatFuncDerivative
        (GCD369CubeFaberR5 a0 a1 a2 a3 a4
          d c7 c5 c4 c3 c2 c1) •
      GCD369CubeFaberLowerBasisFive
  have hrhs : rhs.natDegree ≤ 4 := by
    dsimp only [rhs, GCD369CubeFaberLowerBasisOne,
      GCD369CubeFaberLowerBasisTwo, GCD369CubeFaberLowerBasisThree,
      GCD369CubeFaberLowerBasisFour, GCD369CubeFaberLowerBasisFive]
    compute_degree
  change _ = rhs
  ext n
  by_cases hn : n ≤ 4
  · interval_cases n <;>
      rw [GCD369CubeRatFuncJacobian_coeff] <;>
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;>
      norm_num [Finset.sum_range_succ, rhs,
        GCD369CubeFaberNormalPolynomial,
        GCD369CubeDepressedSextic,
        GCD369CubeFaberNine, GCD369CubeFaberEight,
        GCD369CubeFaberSeven, GCD369CubeFaberSix,
        GCD369CubeFaberFive, GCD369CubeFaberFour,
        GCD369CubeFaberThree, GCD369CubeFaberTwo,
        GCD369CubeFaberOne,
        GCD369CubeFaberLowerBasisOne,
        GCD369CubeFaberLowerBasisTwo,
        GCD369CubeFaberLowerBasisThree,
        GCD369CubeFaberLowerBasisFour,
        GCD369CubeFaberLowerBasisFive,
        coeff_add, coeff_C_mul, coeff_monomial, coeff_smul] <;>
      simp only [GCD369CubeFaberR1, GCD369CubeFaberR2,
        GCD369CubeFaberR3, GCD369CubeFaberR4, GCD369CubeFaberR5,
        GCD369CubeRatFuncDerivative_add,
        GCD369CubeRatFuncDerivative_mul,
        GCD369CubeRatFuncDerivative_sub,
        GCD369CubeRatFuncDerivative_pow,
        GCD369CubeRatFuncDerivative_div_general,
        OfNat.ofNat,
        GCD369CubeRatFuncDerivative_natCast,
        hd, hc7, hc6, hc5, hc4, hc3, hc2, hc1, hc0,
        nsmul_eq_mul] <;>
      ring
  · have hn4 : 4 < n := by omega
    rw [natDegree_le_iff_coeff_eq_zero.mp hhigh n hn4,
      natDegree_le_iff_coeff_eq_zero.mp hrhs n hn4]

namespace GCD369CubePolynomialSource

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Any certified Faber normal form of the literal source produces the
complete five lower-row system: four first integrals and the exact terminal
derivative `j/s`. -/
theorem faberLowerRowsOfNormalForm
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (N : GCD369CubeFaberNormalForm
      (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
      (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
      (S.normalizedP.coeff 4) S.normalizedQ) :
    GCD369CubeRatFuncDerivative
        (GCD369CubeFaberR1
          (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
          (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
          (S.normalizedP.coeff 4)
          N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) = 0 ∧
    GCD369CubeRatFuncDerivative
        (GCD369CubeFaberR2
          (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
          (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
          (S.normalizedP.coeff 4)
          N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) = 0 ∧
    GCD369CubeRatFuncDerivative
        (GCD369CubeFaberR3
          (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
          (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
          (S.normalizedP.coeff 4)
          N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) = 0 ∧
    GCD369CubeRatFuncDerivative
        (GCD369CubeFaberR4
          (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
          (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
          (S.normalizedP.coeff 4)
          N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) = 0 ∧
    6 * GCD369CubeRatFuncDerivative
        (GCD369CubeFaberR5
          (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
          (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
          (S.normalizedP.coeff 4)
          N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) =
      algebraMap k (RatFunc k) S.j / S.sRat := by
  have hq : S.normalizedQ =
      GCD369CubeFaberNormalPolynomial
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        N.d N.c7 N.c6 N.c5 N.c4 N.c3 N.c2 N.c1 N.c0 := by
    simpa only [GCD369CubeFaberNormalPolynomial] using N.hq
  have hjac :
      GCD369CubeRatFuncJacobian
          (GCD369CubeDepressedSextic
            (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
            (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
            (S.normalizedP.coeff 4))
          (GCD369CubeFaberNormalPolynomial
            (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
            (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
            (S.normalizedP.coeff 4)
            N.d N.c7 N.c6 N.c5 N.c4 N.c3 N.c2 N.c1 N.c0) =
        C (algebraMap k (RatFunc k) S.j / S.sRat) := by
    rw [← S.normalizedP_eq_depressed, ← hq]
    exact S.normalized_jacobian
  have hhigh :
      (GCD369CubeRatFuncJacobian
          (GCD369CubeDepressedSextic
            (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
            (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
            (S.normalizedP.coeff 4))
          (GCD369CubeFaberNormalPolynomial
            (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
            (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
            (S.normalizedP.coeff 4)
            N.d N.c7 N.c6 N.c5 N.c4 N.c3 N.c2 N.c1 N.c0)).natDegree ≤ 4 := by
    rw [hjac, natDegree_C]
    norm_num
  have hlower := GCD369CubeFaberLowerRows
    (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
    (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
    (S.normalizedP.coeff 4)
    N.d N.c7 N.c6 N.c5 N.c4 N.c3 N.c2 N.c1 N.c0
    N.hd N.hc7 N.hc6 N.hc5 N.hc4 N.hc3 N.hc2 N.hc1 N.hc0 hhigh
  have htri := hlower.symm.trans hjac
  apply (GCD369CubeLowerRowTriangularity
    (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
    (S.normalizedP.coeff 4)
    (GCD369CubeRatFuncDerivative
      (GCD369CubeFaberR1
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1))
    (GCD369CubeRatFuncDerivative
      (GCD369CubeFaberR2
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1))
    (GCD369CubeRatFuncDerivative
      (GCD369CubeFaberR3
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1))
    (GCD369CubeRatFuncDerivative
      (GCD369CubeFaberR4
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1))
    (GCD369CubeRatFuncDerivative
      (GCD369CubeFaberR5
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1))
    (algebraMap k (RatFunc k) S.j / S.sRat)).mp
  simpa only [GCD369CubeFaberLowerBasisOne,
    GCD369CubeFaberLowerBasisTwo, GCD369CubeFaberLowerBasisThree,
    GCD369CubeFaberLowerBasisFour, GCD369CubeFaberLowerBasisFive] using htri

end GCD369CubePolynomialSource

#print axioms GCD369CubeFaberLowerRows
#print axioms GCD369CubePolynomialSource.faberLowerRowsOfNormalForm
