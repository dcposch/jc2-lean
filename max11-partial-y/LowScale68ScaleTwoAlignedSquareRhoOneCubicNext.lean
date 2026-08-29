import LowScale68ScaleTwoAlignedSquareRhoOne
import LowScale68ScaleTwoRhoOneTransverse
import LowScale68ScaleTwoAfterRhoOneNextBox

/-! # The first informative zero-septic rows on the rho-one cubic component

For a nonzero septic, the coefficient at exponent `-8` in the fourth first
integral is the transverse scalar `(35/1728) * L * a^4`.  Here `L = 0`, so
that coefficient is identically zero.  After passing to the cubic defects,
the first potentially informative coefficients are instead I4 at `-7` and
I3 at `-8`.  This file computes both exact rows and transports them to the
aligned square source.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicNext68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneCubicNextHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The first nontrivial I4 row after the zero-septic cubic leading face. -/
def rhoOneZeroLCubicNextFour68 (a b c d e : k) : k :=
  (-16 / 9 : k) * a * b * c + (8 / 3 : k) * c * d +
    (8 / 3 : k) * b * e

/-- The first nontrivial I3 row after the zero-septic cubic leading face. -/
def rhoOneZeroLCubicNextThree68 (a b c d e : k) : k :=
  (4 / 3 : k) * d ^ 2 - (16 / 9 : k) * a * b * d +
    (4 / 9 : k) * a ^ 2 * b ^ 2 - (8 / 9 : k) * a * c ^ 2 +
    (8 / 3 : k) * c * e

/-- Rewriting the I3 top face around the rational cubic core. -/
theorem firstIntegralThreeTopFaceHahn68_cubicDefects
    (A B C0 D E : HahnSeries ℚ k) :
    firstIntegralThreeTopFaceHahn68 A B C0 D E =
      weightedMonomial68 (4 / 3 : k) A B (rhoOneCDefectHahn68 A C0) D
        (rhoOneEDefectHahn68 A E) 0 0 0 2 0 +
      weightedMonomial68 (-16 / 9 : k) A B (rhoOneCDefectHahn68 A C0) D
        (rhoOneEDefectHahn68 A E) 1 1 0 1 0 +
      weightedMonomial68 (4 / 9 : k) A B (rhoOneCDefectHahn68 A C0) D
        (rhoOneEDefectHahn68 A E) 2 2 0 0 0 +
      weightedMonomial68 (-8 / 9 : k) A B (rhoOneCDefectHahn68 A C0) D
        (rhoOneEDefectHahn68 A E) 1 0 2 0 0 +
      weightedMonomial68 (-8 / 9 : k) A B (rhoOneCDefectHahn68 A C0) D
        (rhoOneEDefectHahn68 A E) 0 2 1 0 0 +
      weightedMonomial68 (8 / 3 : k) A B (rhoOneCDefectHahn68 A C0) D
        (rhoOneEDefectHahn68 A E) 0 0 1 0 1 := by
  simp only [firstIntegralThreeTopFaceHahn68, weightedMonomial68,
    rhoOneCDefectHahn68, rhoOneEDefectHahn68]
  simp only [map_add, map_sub, map_mul, map_div₀, map_neg, map_ofNat,
    map_one]
  ring

/-- At `L=0`, the old exponent `-8` I4 transverse row is a tautology. -/
theorem firstIntegralFour68_coeff_neg8_zero_of_zeroL_cubicBounds
    (beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hCdef : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 A C0).orderTop)
    (hD : (↑(-4 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hEdef : (↑(-5 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 A E).orderTop)
    (hCcoeff : C0.coeff (-4 : ℚ) = (A.coeff (-2 : ℚ)) ^ 2 / 3)
    (hEcoeff : E.coeff (-6 : ℚ) = (A.coeff (-2 : ℚ)) ^ 3 / 27) :
    (firstIntegralFour68 (HahnSeries.C 0) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-8 : ℚ) = 0 := by
  simpa using firstIntegralFour68_coeff_neg8_of_cubicBounds
    (0 : k) beta gamma delta epsilon zeta A B C0 D E hA hB hC hCdef
      hD hE hEdef hCcoeff hEcoeff

/-- The first informative I4 coefficient after the zero-septic cubic face. -/
theorem firstIntegralFour68_coeff_neg7_of_zeroL_cubicBounds
    (beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hCdef : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 A C0).orderTop)
    (hD : (↑(-4 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hEdef : (↑(-5 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 A E).orderTop) :
    (firstIntegralFour68 (HahnSeries.C 0) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-7 : ℚ) =
        rhoOneZeroLCubicNextFour68 (A.coeff (-2 : ℚ))
          (B.coeff (-2 : ℚ))
          ((rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ))
          (D.coeff (-4 : ℚ))
          ((rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)) := by
  let CR := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-7 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-2) +
        (aC : ℚ) * (-3) + (aD : ℚ) * (-4) + (aE : ℚ) * (-5)) :
      (weightedMonomial68 c A B CR D ER aA aB aC aD aE).coeff
          (-7 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B CR D ER
      aA aB aC aD aE (-2) (-2) (-3) (-4) (-5) (-7)
      hA hB (by simpa only [CR] using hCdef) hD
      (by simpa only [ER] using hEdef) hlt
  have hlead (c : k) (aA aB aC aD aE : ℕ)
      (hw : (aA : ℚ) * (-2) + (aB : ℚ) * (-2) +
          (aC : ℚ) * (-3) + (aD : ℚ) * (-4) + (aE : ℚ) * (-5) =
        -7) :
      (weightedMonomial68 c A B CR D ER aA aB aC aD aE).coeff
          (-7 : ℚ) =
        c * (A.coeff (-2 : ℚ)) ^ aA * (B.coeff (-2 : ℚ)) ^ aB *
          (CR.coeff (-3 : ℚ)) ^ aC * (D.coeff (-4 : ℚ)) ^ aD *
          (ER.coeff (-5 : ℚ)) ^ aE := by
    rw [← hw]
    exact weightedMonomial68_coeff_at_general_lower_next c A B CR D ER
      aA aB aC aD aE (-2) (-2) (-3) (-4) (-5) hA hB
      (by simpa only [CR] using hCdef) hD
      (by simpa only [ER] using hEdef)
  have ht1 := hzero (-8 / 27 : k) 0 3 0 0 0 (by norm_num)
  have ht2 := hlead (-16 / 9 : k) 1 1 1 0 0 (by norm_num)
  have ht3 := hlead (8 / 3 : k) 0 0 1 1 0 (by norm_num)
  have ht4 := hlead (8 / 3 : k) 0 1 0 0 1 (by norm_num)
  have hzeroHigher (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-7 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-2) +
        (aC : ℚ) * (-4) + (aD : ℚ) * (-4) + (aE : ℚ) * (-6)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-7 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE (-2) (-2) (-4) (-4) (-6) (-7)
      hA hB hC hD hE hlt
  have hh1 := hzeroHigher zeta 1 0 0 0 0 (by norm_num)
  have hh2 := hzeroHigher (2 * epsilon) 0 1 0 0 0 (by norm_num)
  have hh3 := hzeroHigher (3 * delta) 0 0 1 0 0 (by norm_num)
  have hh4 := hzeroHigher (4 * gamma) 0 0 0 1 0 (by norm_num)
  have hh5 := hzeroHigher (5 * beta) 0 0 0 0 1 (by norm_num)
  have hh6 := hzeroHigher (-(5 / 12 : k) * beta) 0 2 0 0 0 (by norm_num)
  have hh7 := hzeroHigher (-(3 / 4 : k) * delta) 2 0 0 0 0 (by norm_num)
  have hh9 := hzeroHigher ((35 / 216 : k) * beta) 3 0 0 0 0 (by norm_num)
  have hh13 := hzeroHigher (-(5 / 6 : k) * beta) 1 0 1 0 0 (by norm_num)
  have hh14 := hzeroHigher (-(4 / 3 : k) * gamma) 1 1 0 0 0 (by norm_num)
  have hhigher :
      (firstIntegralFourHigherHahn68 0 beta gamma delta epsilon zeta
        A B C0 D E).coeff (-7 : ℚ) = 0 := by
    simp only [firstIntegralFourHigherHahn68, HahnSeries.coeff_add]
    rw [hh1, hh2, hh3, hh4, hh5, hh6, hh7, hh9, hh13, hh14]
    simp [weightedMonomial68]
  rw [firstIntegralFour68_eq_localFaces, HahnSeries.coeff_add,
    firstIntegralFourTopFaceHahn68_cubicDefects]
  simp only [HahnSeries.coeff_add]
  rw [show rhoOneCDefectHahn68 A C0 = CR by rfl,
    show rhoOneEDefectHahn68 A E = ER by rfl,
    ht1, ht2, ht3, ht4]
  rw [hhigher]
  simp only [CR, ER, rhoOneZeroLCubicNextFour68]
  ring

/-- The first informative I3 coefficient after the zero-septic cubic face. -/
theorem firstIntegralThree68_coeff_neg8_of_zeroL_cubicBounds
    (beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hCdef : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 A C0).orderTop)
    (hD : (↑(-4 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hEdef : (↑(-5 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 A E).orderTop) :
    (firstIntegralThree68 (HahnSeries.C 0) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-8 : ℚ) =
        rhoOneZeroLCubicNextThree68 (A.coeff (-2 : ℚ))
          (B.coeff (-2 : ℚ))
          ((rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ))
          (D.coeff (-4 : ℚ))
          ((rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)) := by
  let CR := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-8 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-2) +
        (aC : ℚ) * (-3) + (aD : ℚ) * (-4) + (aE : ℚ) * (-5)) :
      (weightedMonomial68 c A B CR D ER aA aB aC aD aE).coeff
          (-8 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B CR D ER
      aA aB aC aD aE (-2) (-2) (-3) (-4) (-5) (-8)
      hA hB (by simpa only [CR] using hCdef) hD
      (by simpa only [ER] using hEdef) hlt
  have hlead (c : k) (aA aB aC aD aE : ℕ)
      (hw : (aA : ℚ) * (-2) + (aB : ℚ) * (-2) +
          (aC : ℚ) * (-3) + (aD : ℚ) * (-4) + (aE : ℚ) * (-5) =
        -8) :
      (weightedMonomial68 c A B CR D ER aA aB aC aD aE).coeff
          (-8 : ℚ) =
        c * (A.coeff (-2 : ℚ)) ^ aA * (B.coeff (-2 : ℚ)) ^ aB *
          (CR.coeff (-3 : ℚ)) ^ aC * (D.coeff (-4 : ℚ)) ^ aD *
          (ER.coeff (-5 : ℚ)) ^ aE := by
    rw [← hw]
    exact weightedMonomial68_coeff_at_general_lower_next c A B CR D ER
      aA aB aC aD aE (-2) (-2) (-3) (-4) (-5) hA hB
      (by simpa only [CR] using hCdef) hD
      (by simpa only [ER] using hEdef)
  have ht1 := hlead (4 / 3 : k) 0 0 0 2 0 (by norm_num)
  have ht2 := hlead (-16 / 9 : k) 1 1 0 1 0 (by norm_num)
  have ht3 := hlead (4 / 9 : k) 2 2 0 0 0 (by norm_num)
  have ht4 := hlead (-8 / 9 : k) 1 0 2 0 0 (by norm_num)
  have ht5 := hzero (-8 / 9 : k) 0 2 1 0 0 (by norm_num)
  have ht6 := hlead (8 / 3 : k) 0 0 1 0 1 (by norm_num)
  have hzeroHigher (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-8 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-2) +
        (aC : ℚ) * (-4) + (aD : ℚ) * (-4) + (aE : ℚ) * (-6)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-8 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE (-2) (-2) (-4) (-4) (-6) (-8)
      hA hB hC hD hE hlt
  have hh1 := hzeroHigher zeta 0 1 0 0 0 (by norm_num)
  have hh2 := hzeroHigher (2 * epsilon) 0 0 1 0 0 (by norm_num)
  have hh3 := hzeroHigher (3 * delta) 0 0 0 1 0 (by norm_num)
  have hh4 := hzeroHigher (4 * gamma) 0 0 0 0 1 (by norm_num)
  have hh6 := hzeroHigher (-(2 / 3 : k) * epsilon) 2 0 0 0 0 (by norm_num)
  have hh7 := hzeroHigher (-(2 / 3 : k) * gamma) 0 2 0 0 0 (by norm_num)
  have hh8 := hzeroHigher ((8 / 27 : k) * gamma) 3 0 0 0 0 (by norm_num)
  have hh10 := hzeroHigher (-(5 / 6 : k) * beta) 1 0 0 1 0 (by norm_num)
  have hh11 := hzeroHigher (-(5 / 6 : k) * beta) 0 1 1 0 0 (by norm_num)
  have hh12 := hzeroHigher (-(4 / 3 : k) * gamma) 1 0 1 0 0 (by norm_num)
  have hh13 := hzeroHigher (-(3 / 2 : k) * delta) 1 1 0 0 0 (by norm_num)
  have hh16 := hzeroHigher ((35 / 72 : k) * beta) 2 1 0 0 0 (by norm_num)
  have hhigher :
      (firstIntegralThreeHigherHahn68 0 beta gamma delta epsilon zeta
        A B C0 D E).coeff (-8 : ℚ) = 0 := by
    simp only [firstIntegralThreeHigherHahn68, HahnSeries.coeff_add]
    rw [hh1, hh2, hh3, hh4, hh6, hh7, hh8, hh10, hh11, hh12, hh13,
      hh16]
    simp [weightedMonomial68]
  rw [firstIntegralThree68_eq_localFaces, HahnSeries.coeff_add,
    firstIntegralThreeTopFaceHahn68_cubicDefects]
  simp only [HahnSeries.coeff_add]
  rw [show rhoOneCDefectHahn68 A C0 = CR by rfl,
    show rhoOneEDefectHahn68 A E = ER by rfl,
    ht1, ht2, ht3, ht4, ht5, ht6]
  rw [hhigher]
  simp only [CR, ER, rhoOneZeroLCubicNextThree68]
  ring

end AlignedSquareRhoOneCubicNext68

end Max11DegreeRoutes
