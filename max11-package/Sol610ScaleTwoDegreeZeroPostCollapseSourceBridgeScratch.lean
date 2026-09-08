import Sol610ScaleTwoDegreeZeroDifferentialBridgeScratch
import Sol610ScaleTwoDegreeZeroPostCollapseJetScratch
import Sol610ScaleTwoDegreeZeroLocalPoleScratch

/-! # Source bridge for the `(6,10)` degree-zero post-collapse head

This module connects the three independent pieces: weighted homogeneity of
the degree-zero primitive, the exact order-`69` compact source quotient, and
the local pole-six obstruction.  The resulting head-vanishing theorem is
conditional only on the displayed ordinary derivative equation; a final
wrapper obtains that equation from the monic differential Jacobian.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section DegreeZeroWeightedScale610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- Weight fifteen of the primitive, with source-scale weight five per unit
of residual weight. -/
theorem degreeZeroPrimitive610_weightedScale
    (h L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 : F) :
    degreeZeroPrimitive610 (h ^ 5 * L) (h ^ 10 * A) (h ^ 15 * B)
        (h ^ 20 * C0) (h ^ 25 * D0) (h ^ 30 * E0) (h ^ 10 * P)
        (h ^ 15 * Q) (h ^ 20 * R) (h ^ 25 * S0) (h ^ 30 * T0)
        (h ^ 35 * U0) (h ^ 40 * V0) (h ^ 45 * W0) (h ^ 50 * X0) =
      h ^ 75 * degreeZeroPrimitive610 L A B C0 D0 E0 P Q R S0 T0 U0
        V0 W0 X0 := by
  simp only [degreeZeroPrimitive610, degreeZeroBaseGroup610,
    degreeZeroAlphaGroup610, degreeZeroBetaGroup610,
    degreeZeroDeltaGroup610, degreeZeroEpsilonGroup610,
    degreeZeroZetaGroup610, degreeZeroEtaGroup610,
    degreeZeroThetaGroup610, alphaResidual610, betaResidual610,
    gammaResidual610, deltaResidual610, epsilonResidual610,
    zetaResidual610, etaResidual610, thetaResidual610]
  ring

/-- The literal depressed primitive on the authoritative post-collapse
source coordinates. -/
def degreeZeroPostCollapsePrimitive610
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : F) : F :=
  degreeZeroPrimitive610 (-lambda / 3)
    (postCollapseNuA610 w1 a42 / 12)
    (postCollapseNuB610 h w1 a42 p32 / (54 * h))
    (postCollapseNuC610 h w1 a42 p32 p21 / (144 * h))
    (postCollapseNuD610 h w1 a42 p32 p21 p1 / (324 * h))
    (postCollapseNuE610 h w1 a42 p32 p21 p1 p0 / (46656 * h))
    (postCollapseNuP610 w1 s2 lambda / 4)
    (postCollapseNuQ610 h w1 s2 u2 lambda / (9 * h))
    (postCollapseNuR610 h w1 s2 u2 b63 lambda / (432 * h))
    (postCollapseNuS610 h w1 s2 u2 b63 q53 lambda / (216 * h ^ 2))
    (postCollapseNuT610 h w1 s2 u2 b63 q53 q41 lambda /
      (7776 * h ^ 3))
    (postCollapseNuU610 h w1 s2 u2 b63 q53 q41 q3 lambda /
      (11664 * h ^ 3))
    (postCollapseNuV610 h w1 s2 u2 b63 q53 q41 q3 q2 lambda /
      (186624 * h ^ 3))
    (postCollapseNuW610 h w1 s2 u2 b63 q53 q41 q3 q2 q1 lambda /
      (5038848 * h ^ 3)) 0

set_option maxHeartbeats 800000000 in
/-- The exact algebraic bridge from the order-`69` quotient to the
source-level primitive. -/
theorem degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive
    (h w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda : F)
    (hh : h ≠ 0) :
    degreeZeroPostCollapseJetQuotient610 h w1 a42 p32 p21 p1 p0 s2 u2
        b63 q53 q41 q3 q2 q1 lambda / h ^ 6 =
      58498535041007616 * degreeZeroPostCollapsePrimitive610 h w1 a42
        p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda := by
  let A := postCollapseNuA610 w1 a42
  let B := postCollapseNuB610 h w1 a42 p32
  let C0 := postCollapseNuC610 h w1 a42 p32 p21
  let D0 := postCollapseNuD610 h w1 a42 p32 p21 p1
  let E0 := postCollapseNuE610 h w1 a42 p32 p21 p1 p0
  let P := postCollapseNuP610 w1 s2 lambda
  let Q := postCollapseNuQ610 h w1 s2 u2 lambda
  let R := postCollapseNuR610 h w1 s2 u2 b63 lambda
  let S0 := postCollapseNuS610 h w1 s2 u2 b63 q53 lambda
  let T0 := postCollapseNuT610 h w1 s2 u2 b63 q53 q41 lambda
  let U0 := postCollapseNuU610 h w1 s2 u2 b63 q53 q41 q3 lambda
  let V0 := postCollapseNuV610 h w1 s2 u2 b63 q53 q41 q3 q2 lambda
  let W0 := postCollapseNuW610 h w1 s2 u2 b63 q53 q41 q3 q2 q1 lambda
  have hfactor := degreeZeroClearedCompact610_postCollapse_factored h w1
    a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda
  have hcompact := degreeZeroPrimitive610_eq_clearedCompact
    (h ^ 10 * A) (h ^ 14 * B) (h ^ 19 * C0) (h ^ 24 * D0)
    (h ^ 29 * E0) (h ^ 10 * P) (h ^ 14 * Q) (h ^ 19 * R)
    (h ^ 23 * S0) (h ^ 27 * T0) (h ^ 32 * U0) (h ^ 37 * V0)
    (h ^ 42 * W0) (h ^ 5 * lambda)
  have hscale := degreeZeroPrimitive610_weightedScale h (-lambda / 3)
    (A / 12) (B / (54 * h)) (C0 / (144 * h)) (D0 / (324 * h))
    (E0 / (46656 * h)) (P / 4) (Q / (9 * h)) (R / (432 * h))
    (S0 / (216 * h ^ 2)) (T0 / (7776 * h ^ 3))
    (U0 / (11664 * h ^ 3)) (V0 / (186624 * h ^ 3))
    (W0 / (5038848 * h ^ 3)) 0
  have hscale' :
      degreeZeroPrimitive610 (-(h ^ 5 * lambda) / 3)
          (h ^ 10 * A / 12) (h ^ 14 * B / 54) (h ^ 19 * C0 / 144)
          (h ^ 24 * D0 / 324) (h ^ 29 * E0 / 46656)
          (h ^ 10 * P / 4) (h ^ 14 * Q / 9) (h ^ 19 * R / 432)
          (h ^ 23 * S0 / 216) (h ^ 27 * T0 / 7776)
          (h ^ 32 * U0 / 11664) (h ^ 37 * V0 / 186624)
          (h ^ 42 * W0 / 5038848) 0 =
        h ^ 75 * degreeZeroPostCollapsePrimitive610 h w1 a42 p32 p21
          p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda := by
    dsimp only [degreeZeroPostCollapsePrimitive610]
    convert hscale using 2 <;> field_simp [hh] <;> ring
  calc
    degreeZeroPostCollapseJetQuotient610 h w1 a42 p32 p21 p1 p0 s2 u2
          b63 q53 q41 q3 q2 q1 lambda / h ^ 6 =
        (h ^ 69 * degreeZeroPostCollapseJetQuotient610 h w1 a42 p32 p21
          p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda) / h ^ 75 := by
      field_simp [hh]
    _ = degreeZeroClearedCompact610 (h ^ 10 * A) (h ^ 14 * B)
          (h ^ 19 * C0) (h ^ 24 * D0) (h ^ 29 * E0) (h ^ 10 * P)
          (h ^ 14 * Q) (h ^ 19 * R) (h ^ 23 * S0) (h ^ 27 * T0)
          (h ^ 32 * U0) (h ^ 37 * V0) (h ^ 42 * W0)
          (h ^ 5 * lambda) / h ^ 75 := by
      rw [hfactor]
    _ = (58498535041007616 *
          degreeZeroPrimitive610 (-(h ^ 5 * lambda) / 3)
            (h ^ 10 * A / 12) (h ^ 14 * B / 54) (h ^ 19 * C0 / 144)
            (h ^ 24 * D0 / 324) (h ^ 29 * E0 / 46656)
            (h ^ 10 * P / 4) (h ^ 14 * Q / 9) (h ^ 19 * R / 432)
            (h ^ 23 * S0 / 216) (h ^ 27 * T0 / 7776)
            (h ^ 32 * U0 / 11664) (h ^ 37 * V0 / 186624)
            (h ^ 42 * W0 / 5038848) 0) / h ^ 75 := by rw [hcompact]
    _ = 58498535041007616 * degreeZeroPostCollapsePrimitive610 h w1 a42
          p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda := by
      rw [hscale']
      field_simp [hh]

#print axioms degreeZeroPrimitive610_weightedScale
#print axioms degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive

end DegreeZeroWeightedScale610

section DegreeZeroSourceHead610

variable {k : Type*} [Field k] [CharZero k]

/-- The exact post-collapse head vanishes once the cleared primitive has the
ordinary simple-pole derivative supplied by the depressed source Jacobian. -/
theorem degreeZeroPostCollapseJetHead610_zero_of_primitiveDeriv
    (h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hderiv :
      Differential.deriv
          ((58498535041007616 : RatFunc k) *
            degreeZeroPostCollapsePrimitive610
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) a42)
              (algebraMap k[X] (RatFunc k) p32)
              (algebraMap k[X] (RatFunc k) p21)
              (algebraMap k[X] (RatFunc k) p1)
              (algebraMap k[X] (RatFunc k) p0)
              (algebraMap k[X] (RatFunc k) s2)
              (algebraMap k[X] (RatFunc k) u2)
              (algebraMap k[X] (RatFunc k) b63)
              (algebraMap k[X] (RatFunc k) q53)
              (algebraMap k[X] (RatFunc k) q41)
              (algebraMap k[X] (RatFunc k) q3)
              (algebraMap k[X] (RatFunc k) q2)
              (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    degreeZeroPostCollapseJetHead610 (p32.eval a) (q41.eval a) = 0 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let quotient : k[X] := degreeZeroPostCollapseJetQuotient610 h0 w1 a42
    p32 p21 p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 (Polynomial.C lambda)
  let rho : RatFunc k :=
    (58498535041007616 : RatFunc k) *
      degreeZeroPostCollapsePrimitive610 hRF
        (algebraMap k[X] (RatFunc k) w1)
        (algebraMap k[X] (RatFunc k) a42)
        (algebraMap k[X] (RatFunc k) p32)
        (algebraMap k[X] (RatFunc k) p21)
        (algebraMap k[X] (RatFunc k) p1)
        (algebraMap k[X] (RatFunc k) p0)
        (algebraMap k[X] (RatFunc k) s2)
        (algebraMap k[X] (RatFunc k) u2)
        (algebraMap k[X] (RatFunc k) b63)
        (algebraMap k[X] (RatFunc k) q53)
        (algebraMap k[X] (RatFunc k) q41)
        (algebraMap k[X] (RatFunc k) q3)
        (algebraMap k[X] (RatFunc k) q2)
        (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda)
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hbridge := degreeZeroPostCollapseJetQuotient610_div_eq_clearedPrimitive
    hRF (algebraMap k[X] (RatFunc k) w1)
    (algebraMap k[X] (RatFunc k) a42)
    (algebraMap k[X] (RatFunc k) p32)
    (algebraMap k[X] (RatFunc k) p21)
    (algebraMap k[X] (RatFunc k) p1)
    (algebraMap k[X] (RatFunc k) p0)
    (algebraMap k[X] (RatFunc k) s2)
    (algebraMap k[X] (RatFunc k) u2)
    (algebraMap k[X] (RatFunc k) b63)
    (algebraMap k[X] (RatFunc k) q53)
    (algebraMap k[X] (RatFunc k) q41)
    (algebraMap k[X] (RatFunc k) q3)
    (algebraMap k[X] (RatFunc k) q2)
    (algebraMap k[X] (RatFunc k) q1) (RatFunc.C lambda) hhRF
  have hmap := degreeZeroPostCollapseJetQuotient610_map
    (algebraMap k[X] (RatFunc k)) h0 w1 a42 p32 p21 p1 p0 s2 u2 b63 q53
      q41 q3 q2 q1 (Polynomial.C lambda)
  have hclear : algebraMap k[X] (RatFunc k) quotient = hRF ^ 6 * rho := by
    dsimp only [quotient, rho]
    rw [hmap]
    simp only [RatFunc.algebraMap_C]
    rw [mul_comm (hRF ^ 6), ← div_eq_iff (pow_ne_zero 6 hhRF)]
    simpa only [hRF] using hbridge
  have hquotientZero : quotient.eval a = 0 :=
    localLinearPoleSix_head_eval_zero_of_deriv_eq_simplePole610 a j h0
      quotient rho hdegree hroot hclear (by simpa [rho, hRF] using hderiv)
  rw [← degreeZeroPostCollapseJetQuotient610_eval_root h0 w1 a42 p32 p21
    p1 p0 s2 u2 b63 q53 q41 q3 q2 q1 lambda a hroot]
  exact hquotientZero

#print axioms degreeZeroPostCollapseJetHead610_zero_of_primitiveDeriv

end DegreeZeroSourceHead610

end Max11DegreeRoutes
