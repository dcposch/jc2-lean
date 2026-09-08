import Sol68LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryRowOneScratch

/-! # Row-two coefficient `5` at ordinary offset 180 is a face shadow

In the contracted `(4,0,2,1,3)` chart the first one-form row (row two)
has degree `6`.  Its top coefficient `6` is `(8/9)*a*(b*y+c*x)`, the
already-spent incidence multiple.  Coefficient `5` is consumed here: its
homogeneous part is the exact incidence multiple `(4/3)*a₃*(b*y+c*x)`
(the two `F₂`-jet contributions cancel between the graded products) and
its literal source load vanishes identically — the whole `alpha` load
cancels, while the surviving `gamma`/`epsilon` load compacts to
`(4/3*gamma)*(A*d') - (2/3*gamma)*(A'*d) - (4/3*gamma)*(B*c)' -
(1/3*epsilon)*(A'*B) + (2/3*epsilon)*(A*B') + (2*epsilon)*d'`,
of degree at most `4`.  On the face locus `b*y+c*x=0` the
coefficient-`5` row equation is therefore satisfied identically: the
row imposes no new condition, no branch is collapsed, and every sibling
survives unchanged.  The next unused row is row-two coefficient `4`,
the first row-two coefficient with a surviving literal load
(`-(4/3)*gamma*a*x` against the homogeneous `F₂`/`F₁` jets).
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryRowTwo68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Homogeneous row-two coefficient `5` is an exact `a₃`-weighted
incidence multiple: the `F.coeff 2` contributions of the two graded
products cancel without any face assumption. -/
theorem secondaryResidualRowTwoPolynomial68_coeff_five_ordinaryOneEighty68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff 5 =
      (4 / 3 : k) * A.coeff 3 *
        (B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1) := by
  let F : k[X] := B * e + c * d
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hF : F.natDegree ≤ 3 := by simp only [F]; compute_degree; omega
  have hderF : (derivative F).natDegree ≤ 2 :=
    (natDegree_derivative_le F).trans (by omega)
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hBe3 : (B * e).coeff 3 = B.coeff 0 * e.coeff 3 := by
    rw [hBC]
    simp
  have hcd3 := coeff_mul_at_bounds68 c d 2 1 hc hd
  norm_num at hcd3
  have hF3 : F.coeff 3 =
      B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1 := by
    simp only [F, coeff_add, hBe3, hcd3]
  have hAFraw := congrArg (fun p : k[X] => p.coeff 1)
    (reflect_mul A (derivative F) hA hderF)
  rw [mul_coeff_one] at hAFraw
  norm_num [coeff_reflect, coeff_derivative] at hAFraw
  have hAF5 : (A * derivative F).coeff 5 =
      2 * A.coeff 4 * F.coeff 2 + 3 * A.coeff 3 * F.coeff 3 := by
    linear_combination hAFraw
  have hdAFraw := congrArg (fun p : k[X] => p.coeff 1)
    (reflect_mul (derivative A) F hderA hF)
  rw [mul_coeff_one] at hdAFraw
  norm_num [coeff_reflect, coeff_derivative] at hdAFraw
  have hdAF5 : (derivative A * F).coeff 5 =
      4 * A.coeff 4 * F.coeff 2 + 3 * A.coeff 3 * F.coeff 3 := by
    linear_combination hdAFraw
  have hlow1 : (derivative A * B ^ 3).natDegree < 5 := by
    compute_degree
    omega
  have hlow2 : (B ^ 2 * derivative d).natDegree < 5 := by
    compute_degree
    omega
  have hlow3 : (B * derivative B * d).natDegree < 5 := by
    compute_degree
    omega
  have hlow4 : (B * c * derivative c).natDegree < 5 := by
    compute_degree
    omega
  have hlow5 : (derivative B * c ^ 2).natDegree < 5 := by
    compute_degree
    omega
  have hlow6 : (d * derivative e).natDegree < 5 := by
    compute_degree
    omega
  have hlow7 : (derivative d * e).natDegree < 5 := by
    compute_degree
    omega
  have hrowEq : secondaryResidualRowTwoPolynomial68 A B c d e =
      (-4 / 27 : k) •
        ((3 : k) • (derivative A * F) - (6 : k) • (A * derivative F) -
          derivative A * B ^ 3 + (6 : k) • (B ^ 2 * derivative d) +
          (12 : k) • (B * derivative B * d) +
          (12 : k) • (B * c * derivative c) +
          (6 : k) • (derivative B * c ^ 2) -
          (18 : k) • (d * derivative e) -
          (18 : k) • (derivative d * e)) := by
    simp only [secondaryResidualRowTwoPolynomial68, F, derivative_add,
      derivative_mul, Polynomial.smul_eq_C_mul]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  rw [hrowEq]
  simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul, hAF5, hdAF5,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7]
  linear_combination (4 / 3 : k) * A.coeff 3 * hF3

/-- The literal row-two load vanishes identically at coefficient `5`:
the entire `alpha` load cancels and the compact `gamma`/`epsilon` load
has degree at most `4`. -/
theorem cubicLoadRowTwoPolynomial68_coeff_five_ordinaryOneEighty68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 5 = 0 := by
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  have hloadEq :
      cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c D0 e =
      (4 / 3 * gamma : k) • (A * derivative d) -
        (2 / 3 * gamma : k) • (derivative A * d) -
        (4 / 3 * gamma : k) • (B * derivative c) -
        (4 / 3 * gamma : k) • (c * derivative B) -
        (1 / 3 * epsilon : k) • (derivative A * B) +
        (2 / 3 * epsilon : k) • (A * derivative B) +
        (2 * epsilon : k) • derivative d := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
      cubicLoadTPolynomial68, cubicLoadUPolynomial68,
      cubicLoadVPolynomial68, D0,
      zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
      derivative_add, derivative_sub, derivative_mul, derivative_pow,
      derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
      map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hderB : derivative B = 0 := derivative_eq_zero.mpr (by omega)
  have hlow1 : (A * derivative d).natDegree < 5 := by
    compute_degree
    omega
  have hlow2 : (derivative A * d).natDegree < 5 := by
    compute_degree
    omega
  have hlow3 : (B * derivative c).natDegree < 5 := by
    compute_degree
    omega
  have hlow4 : (derivative A * B).natDegree < 5 := by
    compute_degree
    omega
  have hlow5 : (derivative d).natDegree < 5 := by
    compute_degree
    omega
  change (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 5 = 0
  rw [hloadEq]
  simp only [hderB, mul_zero, smul_zero, coeff_add, coeff_sub,
    coeff_smul, coeff_zero, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5]
  ring

/-- Source row-two coefficient `5`, backwired through the four literal
integrated coefficients: an exact incidence multiple with no residual
load.  No face assumption is used. -/
theorem fiveToSix_offsetOneEighty_rowTwo_coeff_five_incidence68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (lowerRowTwoPolynomial68
        (integratedSPolynomial68 0 alpha 0 0 A B
          ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d))
        (integratedTPolynomial68 0 alpha 0 gamma epsilon A B
          ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
        (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B
          ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A B
          ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
        B ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff 5 =
      (4 / 3 : k) * A.coeff 3 *
        (B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1) := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon 0 eta A B c
    ((1 / 3 : k) • (A * B) + d) e
  rw [hcoords.s_eq, hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowTwoPolynomial68_split,
    cubicHomogeneousRowTwoPolynomial68_residualCoordinates,
    coeff_add,
    secondaryResidualRowTwoPolynomial68_coeff_five_ordinaryOneEighty68
      A B c d e hA hB hc hd he,
    cubicLoadRowTwoPolynomial68_coeff_five_ordinaryOneEighty68
      alpha gamma epsilon eta A B c d e hA hB hc hd he,
    add_zero]

/-- Contracted row-two packet at coefficient `5`.  The coefficient is a
face shadow: given the incidence relation it vanishes identically, so
the row equation carries no new constraint.  The predecessor frontier —
the rigid I4 residual, the edge cubic and the exact constant-I3 row —
is preserved verbatim, and no sibling branch is consumed. -/
theorem fiveToSix_offsetOneEighty_nonzero_rowTwo_source_packet68
    (alpha gamma epsilon eta i4 i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hcTop : c.coeff 2 ≠ 0)
    (hx : d.coeff 1 ≠ 0) (hy : e.coeff 3 ≠ 0)
    (hface : B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1 = 0)
    (hdisc : A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0)
    (hi4rigid : 27 * A.coeff 4 * i4 +
      32 * A.coeff 4 * B.coeff 0 ^ 3 +
        216 * d.coeff 1 * e.coeff 3 = 0)
    (hedge : 9 * e.coeff 3 ^ 2 - 4 * c.coeff 2 ^ 3 = 0)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    (27 * A.coeff 4 * i4 + 32 * A.coeff 4 * B.coeff 0 ^ 3 +
        216 * d.coeff 1 * e.coeff 3 = 0) ∧
      (9 * e.coeff 3 ^ 2 - 4 * c.coeff 2 ^ 3 = 0) ∧
      (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3) ∧
      ((lowerRowTwoPolynomial68
          (integratedSPolynomial68 0 alpha 0 0 A B
            ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d))
          (integratedTPolynomial68 0 alpha 0 gamma epsilon A B
            ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
            ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
          (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B
            ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
            ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
          (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A B
            ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
            ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
          B ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff 5 =
        0) := by
  refine ⟨hi4rigid, hedge, hi3, ?_⟩
  rw [fiveToSix_offsetOneEighty_rowTwo_coeff_five_incidence68
      alpha gamma epsilon eta A B c d e hA hB hc hd he,
    hface, mul_zero]

#print axioms secondaryResidualRowTwoPolynomial68_coeff_five_ordinaryOneEighty68
#print axioms cubicLoadRowTwoPolynomial68_coeff_five_ordinaryOneEighty68
#print axioms fiveToSix_offsetOneEighty_rowTwo_coeff_five_incidence68
#print axioms fiveToSix_offsetOneEighty_nonzero_rowTwo_source_packet68

end LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryRowTwo68

end Max11DegreeRoutes
