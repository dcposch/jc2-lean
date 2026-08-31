import Sol810PiLeftUnsolvedUniformBridgeScratch

/-! # Source power bridge for the unsolved `(8,10)` pi head

This file keeps the final analytic input separate from the polynomial jet.
If the depressed degree-one integral `pi` is a ground-field constant in the
rational function field, the source-clearing identity makes its integer
numerator a scalar times `h^112`.  The polynomial-uniform left factorization
can then be peeled at every root of `h`, without replacing any scalar
coordinate by a solve that only holds modulo `h`. -/

noncomputable section

namespace Max11DegreeRoutes

open scoped Polynomial

section PiSourcePowerBridge810

set_option maxHeartbeats 400000000 in
/-- The cleared `pi` numerator commutes with arbitrary commutative-ring maps.
This isolates the only large syntactic transport needed to descend from the
rational-function clearing identity back to source polynomials. -/
theorem map_localClearedSixteenthDefect810
    {R S : Type*} [CommRing R] [CommRing S] (phi : R →+* S)
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) :
    phi (localClearedSixteenthDefect810 h a7 a6 a5 a4 a3 a2 a1 a0
      b8 b7 b6 b5 b4 b3 b2 b1 lambda) =
      localClearedSixteenthDefect810 (phi h) (phi a7) (phi a6) (phi a5)
        (phi a4) (phi a3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7)
        (phi b6) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1)
        (phi lambda) := by
  simp only [localClearedSixteenthDefect810,
    localClearedSixteenthDefectCore810,
    localClearedSixteenthDefectBlock0_810,
    localClearedSixteenthDefectBlock1_810,
    localClearedSixteenthDefectBlock2_810,
    localClearedSixteenthDefectBlock3_810,
    localClearedSixteenthDefectBlock4_810,
    localClearedSixteenthDefectBlock5_810,
    localClearedSixteenthDefectBlock6_810,
    localClearedSixteenthDefectBlock7_810,
    localClearedSixteenthDefectBlock8_810,
    localClearedSixteenthDefectBlock9_810,
    localClearedSixteenthDefectBlock10_810,
    localClearedSixteenthDefectBlock11_810,
    localClearedSixteenthDefectBlock12_810,
    localClearedSixteenthDefectBlock13_810,
    localClearedSixteenthDefectBlock14_810,
    localClearedSixteenthDefectBlock15_810,
    localClearedSixteenthDefectBlock16_810,
    localClearedSixteenthDefectBlock17_810,
    localClearedSixteenthDefectBlock18_810,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]

/-- The depressed degree-one integral in source coordinates over a field. -/
def sourcePiResidual810
    {F : Type*} [Field F] [CharZero F]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1
      lambda : F) : F :=
  piResidual810
    (depressedL810 h (octicDepressionR810 h a7) b9)
    (depressedA810 h (octicDepressionR810 h a7) a7 a6)
    (depressedB810 h (octicDepressionR810 h a7) a7 a6 a5)
    (depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4)
    (depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3)
    (depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2)
    (depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1)
    (depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 a0)
    (depressedP810 h (octicDepressionR810 h a7) b9 b8)
    (depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7)
    (depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6)
    (depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5)
    (depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4)
    (depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3)
    (depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2)
    (depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2 b1)

variable {k : Type*} [Field k] [CharZero k]

/-- A scalar value of the depressed `pi` integral gives the exact source
power relation needed by the unsolved left peel. -/
theorem piSourcePowerRelation810_of_residual_eq_C
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (lambda eta : k) (hh : h ≠ 0)
    (hN :
      5 * a7 * h ^ 2 - 4 * b9 = Polynomial.C lambda * h ^ 9)
    (hpi :
      sourcePiResidual810
          (algebraMap k[X] (RatFunc k) h)
          (algebraMap k[X] (RatFunc k) a7)
          (algebraMap k[X] (RatFunc k) a6)
          (algebraMap k[X] (RatFunc k) a5)
          (algebraMap k[X] (RatFunc k) a4)
          (algebraMap k[X] (RatFunc k) a3)
          (algebraMap k[X] (RatFunc k) a2)
          (algebraMap k[X] (RatFunc k) a1)
          (algebraMap k[X] (RatFunc k) a0)
          (algebraMap k[X] (RatFunc k) b9)
          (algebraMap k[X] (RatFunc k) b8)
          (algebraMap k[X] (RatFunc k) b7)
          (algebraMap k[X] (RatFunc k) b6)
          (algebraMap k[X] (RatFunc k) b5)
          (algebraMap k[X] (RatFunc k) b4)
          (algebraMap k[X] (RatFunc k) b3)
          (algebraMap k[X] (RatFunc k) b2)
          (algebraMap k[X] (RatFunc k) b1)
          (RatFunc.C lambda) = algebraMap k (RatFunc k) eta) :
    localClearedSixteenthDefect810 h a7 a6 a5 a4 a3 a2 a1 a0
        b8 b7 b6 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
      Polynomial.C (17592186044416 * eta) * h ^ 112 := by
  let phi : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)
  have hhRat : phi h ≠ 0 := RatFunc.algebraMap_ne_zero hh
  have hNrat :
      5 * phi a7 * (phi h) ^ 2 - 4 * phi b9 =
        RatFunc.C lambda * (phi h) ^ 9 := by
    have hmapped := congrArg phi hN
    simpa [phi, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hclear :=
    piSourceClearingBridge810 (F := RatFunc k)
      (phi h) (phi a7) (phi a6) (phi a5) (phi a4) (phi a3) (phi a2)
      (phi a1) (phi a0) (phi b9) (phi b8) (phi b7) (phi b6) (phi b5)
      (phi b4) (phi b3) (phi b2) (phi b1) (RatFunc.C lambda) hhRat hNrat
  have htarget :
      phi (localClearedSixteenthDefect810 h a7 a6 a5 a4 a3 a2 a1 a0
        b8 b7 b6 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
      phi (Polynomial.C (17592186044416 * eta) * h ^ 112) := by
    rw [map_localClearedSixteenthDefect810]
    rw [show phi (Polynomial.C lambda) = RatFunc.C lambda from
      RatFunc.algebraMap_C lambda]
    rw [← hclear]
    change
      (17592186044416 : RatFunc k) * (phi h) ^ 112 *
          sourcePiResidual810 (phi h) (phi a7) (phi a6) (phi a5)
            (phi a4) (phi a3) (phi a2) (phi a1) (phi a0) (phi b9)
            (phi b8) (phi b7) (phi b6) (phi b5) (phi b4) (phi b3)
            (phi b2) (phi b1) (RatFunc.C lambda) =
        phi (Polynomial.C (17592186044416 * eta) * h ^ 112)
    rw [hpi]
    simp [phi, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat]
    ring
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- Source-facing root peel for the polynomial-uniform left head.  Its only
non-jet input is that the depressed `pi` residual is a scalar. -/
theorem piLeftUnsolvedHead810_eval_root_of_source_residual
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 b9 : k[X])
    (lambda eta x : k) (hh : h ≠ 0) (hroot : h.eval x = 0)
    (hN :
      5 * (h ^ 6 * t0) * h ^ 2 - 4 * b9 =
        Polynomial.C lambda * h ^ 9)
    (hpi :
      sourcePiResidual810
          (algebraMap k[X] (RatFunc k) h)
          (algebraMap k[X] (RatFunc k) (h ^ 6 * t0))
          (algebraMap k[X] (RatFunc k) (h ^ 4 * v1))
          (algebraMap k[X] (RatFunc k) (h ^ 2 * u1))
          (algebraMap k[X] (RatFunc k) a4)
          (algebraMap k[X] (RatFunc k) a3)
          (algebraMap k[X] (RatFunc k) a2)
          (algebraMap k[X] (RatFunc k) a1)
          (algebraMap k[X] (RatFunc k) a0)
          (algebraMap k[X] (RatFunc k) b9)
          (algebraMap k[X] (RatFunc k) (h ^ 6 * s1))
          (algebraMap k[X] (RatFunc k) (h ^ 4 * w1))
          (algebraMap k[X] (RatFunc k) (h ^ 2 * b62))
          (algebraMap k[X] (RatFunc k) b5)
          (algebraMap k[X] (RatFunc k) b4)
          (algebraMap k[X] (RatFunc k) b3)
          (algebraMap k[X] (RatFunc k) b2)
          (algebraMap k[X] (RatFunc k) b1)
          (RatFunc.C lambda) = algebraMap k (RatFunc k) eta) :
    (piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval x = 0 := by
  apply piLeftUnsolvedHead810_eval_root_of_power h t0 v1 u1 a4 a3 a2 a1 a0
    s1 w1 b62 b5 b4 b3 b2 b1 lambda (17592186044416 * eta) x hh hroot
  exact piSourcePowerRelation810_of_residual_eq_C h (h ^ 6 * t0)
    (h ^ 4 * v1) (h ^ 2 * u1) a4 a3 a2 a1 a0 b9 (h ^ 6 * s1)
    (h ^ 4 * w1) (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda eta hh hN hpi

#print axioms map_localClearedSixteenthDefect810
#print axioms piSourcePowerRelation810_of_residual_eq_C
#print axioms piLeftUnsolvedHead810_eval_root_of_source_residual

end PiSourcePowerBridge810

end Max11DegreeRoutes
