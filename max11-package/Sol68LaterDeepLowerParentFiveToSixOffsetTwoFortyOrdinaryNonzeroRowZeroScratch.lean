import Sol68LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryPairZeroScratch
import Sol68LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryRowZeroScratch

/-! # First independent ordinary row at offset 240

In the contracted `(4,0,2,0,2)` chart, row-zero coefficients `9` and `8`
are the face and its I4 jet.  Coefficient `7` (expanded index `479`) is the
first independent row.  It fixes the exact I4 scalar while preserving the
all-nonzero discriminant face.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzero68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 12000000 in
/-- Source-facing row-zero coefficient `7` on the offset-`240` nonzero
face.  No coefficient nonzero is divided away; the output is the exact
rigid I4 value needed by the next independent row. -/
theorem fiveToSix_offsetTwoForty_nonzero_rowZero_source_packet68
    (alpha gamma epsilon eta i4 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 2)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hcTop : c.coeff 2 ≠ 0)
    (hx : d.coeff 0 ≠ 0) (hy : e.coeff 2 ≠ 0)
    (hface : B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 = 0)
    (hdisc : A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow : (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 7 = 0) :
    27 * A.coeff 4 * i4 + 32 * A.coeff 4 * B.coeff 0 ^ 3 = 0 := by
  have hd1 : d.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have he3 : e.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hBcubeDeg : (B ^ 3).natDegree ≤ 0 := by compute_degree; omega
  have hBcube1 : (B ^ 3).coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hBcubeDeg.trans_lt (by norm_num))
  have hBcube0 : (B ^ 3).coeff 0 = B.coeff 0 ^ 3 := by
    simp only [pow_succ, mul_coeff_zero]
    norm_num [coeff_one]
  have hcoeff1 := congrArg (fun p : k[X] => p.coeff 1) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
      at hcoeff1
  norm_num [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, mul_coeff_one, hB1, hd1, hBcube1,
    coeff_C] at hcoeff1
  have hfirst : (8 / 3 : k) *
      (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0) = 0 := by
    linear_combination hcoeff1
  have hcoeff0 := congrArg (fun p : k[X] => p.coeff 0) hi4
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
      at hcoeff0
  norm_num [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, mul_coeff_zero, hBcube0, coeff_C] at hcoeff0
  have hconstant : (-8 / 27 : k) * B.coeff 0 ^ 3 +
      (8 / 3 : k) *
        (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
      2 * epsilon * B.coeff 0 + 4 * gamma * d.coeff 0 = i4 := by
    linear_combination hcoeff0
  have htopZero : B.coeff 0 * e.coeff 3 +
      c.coeff 2 * d.coeff 1 = 0 := by rw [he3, hd1]; ring
  have hres := secondaryResidualRowZeroPolynomial68_coeff_seven_ordinaryOneEighty68
    A B c d e hA hB hc (hd.trans (by norm_num))
      (he.trans (by norm_num)) htopZero
      (by simpa only [hd1, mul_zero, add_zero] using hface)
  have hload := cubicLoadRowZeroPolynomial68_coeff_seven_ordinaryOneEighty68
    alpha gamma epsilon eta A B c d e hA hB hc
      (hd.trans (by norm_num)) (he.trans (by norm_num))
  rw [coeff_add, hres, hload, hd1, he3, mul_zero, add_zero] at hrow
  have hrigid := fiveToSix_ordinaryOneEighty_rowZero_i4_residual68
    (A.coeff 4) (A.coeff 3) (B.coeff 0) (c.coeff 2)
    0 (e.coeff 2) (d.coeff 0) (e.coeff 0) (e.coeff 1)
    (c.coeff 0) (c.coeff 1) gamma epsilon i4 ha hdisc
    (by simpa only [mul_zero, add_zero] using hfirst) hconstant
    (by linear_combination hrow)
  linear_combination hrigid

#print axioms fiveToSix_offsetTwoForty_nonzero_rowZero_source_packet68

end LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzero68

end Max11DegreeRoutes
