import LowScale68SecondaryResidualDoubleLoadWall
import LowScale68SecondaryRelaxedCanonical

/-! # Canonical expanded wrapper for the mixed residual double load wall `n = 3g`

The checked extraction in `LowScale68SecondaryResidualDoubleLoadWall` packages
the five mixed wall scalars as `ResidualDoubleLoadWallFace68`.  Source input
is `IntegratedPolynomialLowerSystem68` on `A,B,C0,D,E`.  After the canonical
expansion `Ae := expand k 60 A` (and likewise `Be,Ce,De,Ee`), rows two and
one remain zero, but row zero becomes `C terminal * (60 * X^59)`.  Expanded
coordinates therefore must **not** be repackaged as
`IntegratedPolynomialLowerSystem68`.

This wrapper rebuilds the expanded identities as in
`LowScale68SecondaryRelaxedCanonical`, rewrites I4/I3/rows through the
tracked mixed-wall coefficient lemmas, disposes of the terminal monomial
at the collided index `12n-1`, and classifies
`ResidualDoubleLoadWallFace68` to force `l = 0`.  The wall `n = 3g`
with `g > 0` implies `2g < n`, so the already-checked
`maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68`
closes the branch.  No residual-support premise is required.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualDoubleLoadWallCanonical68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Wall index versus the expanded terminal monomial -/

theorem residualDoubleLoadWallRowZeroIndex68_gt_fiftyNine
    (n g : ℕ) (hn : 10 ≤ n) (hwall : 3 * g = n) :
    59 < 12 * n - 1 := by
  omega

/-! ## Generalized wall extraction: exact I4/I3, rows, target coefficient -/

set_option maxHeartbeats 4000000 in
theorem polynomialResidualDoubleLoadWallInvariants68
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B C0 c D E d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hD0 : D = (1 / 3 : k) • (A * B) + d)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3) :
    residualDoubleLoadWallFourNumerator68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (e.coeff (6 * n - 2 * g)) l = 0 ∧
      residualDoubleThreeHom68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (e.coeff (6 * n - 2 * g)) = 0 := by
  have ht4 : 8 * n ≠ 0 := by omega
  have ht3 : 9 * n ≠ 0 := by omega
  have hfour := congrArg (fun p : k[X] => p.coeff (8 * n)) hI4
  rw [hC0, hE0, firstIntegralFourPolynomial68_cubicCoordinates, hD0,
    cubicFirstIntegralFourPolynomial68_coeff_residualDoubleLoadWall
      l beta gamma delta epsilon zeta A B c d e n g hg hwall
      hA hB hc hd he] at hfour
  simp only [coeff_C, ite_eq_right ht4] at hfour
  have hthree := congrArg (fun p : k[X] => p.coeff (9 * n)) hI3
  rw [hC0, hE0, firstIntegralThreePolynomial68_cubicCoordinates, hD0,
    cubicFirstIntegralThreePolynomial68_coeff_residualDoubleLoadWall
      l beta gamma delta epsilon zeta A B c d e n g hg hwall
      hA hB hc hd he] at hthree
  simp only [coeff_C, ite_eq_right ht3] at hthree
  constructor
  · have hsc := residualDoubleLoadWallFourScalar68_eq_numerator
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (e.coeff (6 * n - 2 * g)) l
    rw [hsc] at hfour
    exact (div_eq_zero_iff.mp hfour).resolve_right (by norm_num)
  · exact (mul_eq_zero.mp hthree).resolve_left (by norm_num)

set_option maxHeartbeats 4000000 in
theorem integratedLowerRowTwoPolynomial68_coeff_residualDoubleLoadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d))
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      B ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (10 * n - 1) =
      residualDoubleLoadWallTwoScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (e.coeff (6 * n - 2 * g)) l := by
  let D0 := (1 / 3 : k) • (A * B) + d
  have hD : D0.natDegree ≤ 5 * n - g := by
    simp only [D0]
    compute_degree
    omega
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D0 e
  rw [hcoords.s_eq, hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowTwoPolynomial68_split, coeff_add,
    show cubicHomogeneousRowTwoPolynomial68 A B c D0 e =
        secondaryResidualRowTwoPolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowTwoPolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowTwoPolynomial68_coeff_doubleLoadWall A B c d e n g
      hn hg hwall hA hB hc hd he,
    cubicLoadRowTwoPolynomial68_coeff_residualDoubleLoadWall
      l alpha beta gamma delta epsilon zeta eta A B c D0 e n g
      hn hg hwall hA hB hc hD he]
  exact (residualDoubleLoadWallTwoScalar68_eq_hom_add_load (n : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
    (e.coeff (6 * n - 2 * g)) l).symm

set_option maxHeartbeats 4000000 in
theorem integratedLowerRowOnePolynomial68_coeff_residualDoubleLoadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (11 * n - 1) =
      (8 / 27 : k) *
        (3 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (g : k) *
            d.coeff (5 * n - 2 * g) -
          10 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (n : k) *
            d.coeff (5 * n - 2 * g) +
          2 * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 * (n : k) *
            c.coeff (4 * n - g) -
          9 * A.coeff (2 * n) * (g : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          30 * A.coeff (2 * n) * (n : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          3 * (g : k) * c.coeff (4 * n - g) ^ 3 -
          12 * (n : k) * c.coeff (4 * n - g) ^ 3) := by
  let D0 := (1 / 3 : k) • (A * B) + d
  have hD : D0.natDegree ≤ 5 * n - g := by
    simp only [D0]
    compute_degree
    omega
  have htwo : 2 * g < n := residualDoubleLoadWall_twoGap n g hg hwall
  have hidx : 12 * n - 3 * g - 1 = 11 * n - 1 :=
    residualDoubleLoadWall_oneIndex n g hwall
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D0 e
  have hload :
      (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c D0 e).natDegree < 11 * n - 1 := by
    have hlt := cubicLoadRowOnePolynomial68_degree_lt_residualDouble_of_twoGap
      l alpha beta gamma delta epsilon zeta eta A B c D0 e n g
      hg htwo hA hB hc hD he
    simpa only [hidx] using hlt
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq, cubicRowOnePolynomial68_split,
    coeff_add,
    show cubicHomogeneousRowOnePolynomial68 A B c D0 e =
        secondaryResidualRowOnePolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowOnePolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowOnePolynomial68_coeff_doubleLoadWall A B c d e n g
      hg hwall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 4000000 in
theorem integratedLowerRowZeroPolynomial68_coeff_residualDoubleLoadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (12 * n - 1) =
      residualDoubleLoadWallZeroScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (e.coeff (6 * n - 2 * g)) l := by
  let D0 := (1 / 3 : k) • (A * B) + d
  have hD : D0.natDegree ≤ 5 * n - g := by
    simp only [D0]
    compute_degree
    omega
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D0 e
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split, coeff_add,
    show cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
        secondaryResidualRowZeroPolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowZeroPolynomial68_coeff_doubleLoadWall A B c d e n g
      hg hwall hA hB hc hd he,
    cubicLoadRowZeroPolynomial68_coeff_residualDoubleLoadWall
      l alpha beta gamma delta epsilon zeta eta A B c D0 e n g
      hn hg hwall hA hB hc hD he]
  exact (residualDoubleLoadWallZeroScalar68_eq_hom_add_load (n : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
    (e.coeff (6 * n - 2 * g)) l).symm

set_option maxHeartbeats 4000000 in
/-- Exact I4/I3 together with vanishing row-two/row-one polynomials and a
single vanishing target coefficient of row zero supply the five mixed
wall equations. -/
theorem polynomialResidualDoubleLoadWallFace68
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hD0 : D = (1 / 3 : k) • (A * B) + d)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3)
    (hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B C0 D)
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) B C0 D E = 0)
    (hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) C0 D E = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) D E).coeff (12 * n - 1) = 0) :
    ResidualDoubleLoadWallFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (e.coeff (6 * n - 2 * g)) l := by
  have hinv := polynomialResidualDoubleLoadWallInvariants68
    l beta gamma delta epsilon zeta i4 i3 A B C0 c D E d e n g
    hn hg hwall hA hB hc hd he hC0 hD0 hE0 hI4 hI3
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have h2 := hrowTwo
  rw [hC0, hD0, hE0] at h2
  have htwo := congrArg
    (fun p : k[X] => p.coeff (10 * n - 1)) h2
  rw [integratedLowerRowTwoPolynomial68_coeff_residualDoubleLoadWall
    l alpha beta gamma delta epsilon zeta eta A B c d e n g
    hn hg hwall hA hB hc hd he] at htwo
  simp only [coeff_zero] at htwo
  have htwoNum : residualDoubleLoadWallTwoNumerator68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (e.coeff (6 * n - 2 * g)) l = 0 := by
    simp only [residualDoubleLoadWallTwoScalar68] at htwo
    have hdiv := div_eq_zero_iff.mp htwo
    have hprod : (n : k) *
        residualDoubleLoadWallTwoNumerator68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
          (e.coeff (6 * n - 2 * g)) l = 0 :=
      hdiv.resolve_right (by norm_num)
    exact (mul_eq_zero.mp hprod).resolve_left hncast
  have h1 := hrowOne
  rw [hC0, hD0, hE0] at h1
  have hone := congrArg
    (fun p : k[X] => p.coeff (11 * n - 1)) h1
  rw [integratedLowerRowOnePolynomial68_coeff_residualDoubleLoadWall
    l alpha beta gamma delta epsilon zeta eta A B c d e n g
    hn hg hwall hA hB hc hd he] at hone
  simp only [coeff_zero] at hone
  have hone0 :
      3 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (g : k) *
          d.coeff (5 * n - 2 * g) -
        10 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (n : k) *
          d.coeff (5 * n - 2 * g) +
        2 * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 * (n : k) *
          c.coeff (4 * n - g) -
        9 * A.coeff (2 * n) * (g : k) * c.coeff (4 * n - g) *
          e.coeff (6 * n - 2 * g) +
        30 * A.coeff (2 * n) * (n : k) * c.coeff (4 * n - g) *
          e.coeff (6 * n - 2 * g) +
        3 * (g : k) * c.coeff (4 * n - g) ^ 3 -
        12 * (n : k) * c.coeff (4 * n - g) ^ 3 = 0 :=
    (mul_eq_zero.mp hone).resolve_left (by norm_num)
  have h0 := hrowZero
  rw [hC0, hD0, hE0] at h0
  rw [integratedLowerRowZeroPolynomial68_coeff_residualDoubleLoadWall
    l alpha beta gamma delta epsilon zeta eta A B c d e n g
    hn hg hwall hA hB hc hd he] at h0
  have hzeroNum : residualDoubleLoadWallZeroNumerator68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (e.coeff (6 * n - 2 * g)) l = 0 := by
    simp only [residualDoubleLoadWallZeroScalar68] at h0
    have hdiv := div_eq_zero_iff.mp h0
    have hprod : (n : k) * A.coeff (2 * n) *
        residualDoubleLoadWallZeroNumerator68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
          (e.coeff (6 * n - 2 * g)) l = 0 :=
      hdiv.resolve_right (by norm_num)
    have hfactor : (n : k) * A.coeff (2 * n) ≠ 0 :=
      mul_ne_zero hncast ha
    exact (mul_eq_zero.mp hprod).resolve_left hfactor
  exact ⟨hinv.1, hinv.2, htwoNum, hone0, hzeroNum⟩

/-! ## Canonical maximal-expanded wrapper -/

set_option maxHeartbeats 4000000 in
/-- On the canonical expanded system, the mixed residual double load wall
`n = 3g` forces `l = 0` and is therefore empty: `g > 0` yields `2g < n`,
so the residual load-zero endgame applies. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualDoubleLoadWall_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * g = n)
    (hdouble :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.natDegree ≤ 5 * n - 2 * g ∧ ee.natDegree ≤ 6 * n - 2 * g) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change 3 * g = n at hwall
  change d.natDegree ≤ 5 * n - 2 * g ∧
    ee.natDegree ≤ 6 * n - 2 * g at hdouble
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnlarge : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E hn
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (12 * n - 1) = 0 :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal _ _ _ _ _ h0e
      (residualDoubleLoadWallRowZeroIndex68_gt_fiftyNine n g hnlarge hwall)
  have hface := polynomialResidualDoubleLoadWallFace68
    l alpha beta gamma delta epsilon zeta eta i4 i3
    Ae Be Ce ce De Ee d ee n g hn hg hwall hA hB hc
    hdouble.1 hdouble.2 ha hCrec hDrec hErec hi4e hi3e h2e h1e h0target
  have hclass :=
    residualDoubleLoadWallFace68_classify_of_three_mul_gap_eq_radius
      n g (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) l ha hn hwall hface
  have hl0 : l = 0 := hclass.1
  have htwo : 2 * g < n := residualDoubleLoadWall_twoGap n g hg hwall
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hl0 (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using htwo)

end ResidualDoubleLoadWallCanonical68

#print axioms residualDoubleLoadWallRowZeroIndex68_gt_fiftyNine
#print axioms polynomialResidualDoubleLoadWallInvariants68
#print axioms integratedLowerRowTwoPolynomial68_coeff_residualDoubleLoadWall
#print axioms integratedLowerRowOnePolynomial68_coeff_residualDoubleLoadWall
#print axioms integratedLowerRowZeroPolynomial68_coeff_residualDoubleLoadWall
#print axioms polynomialResidualDoubleLoadWallFace68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualDoubleLoadWall_impossible68

end Max11DegreeRoutes
