import Sol68ScaleTwoAlignedSquareSourceSelectorHierarchyScratch

/-! # Consuming the all-zero row-one early cubic sibling

The early cubic sibling inventory retains the exceptional row-one child
`RhoOneZeroLCubicNextSourcePacket68 ∧ b = c = d = e = 0` literally.  On
that child all four defect leading coefficients vanish, so each of the
four cleared coordinates gains one full order of vanishing at the root.
The next zero-septic integral rows then become informative again:

* `I4` at exponent `-6` degenerates to the single scalar
  `(5/72)·β·a³`, so the source constant `beta` is forced to vanish;
* `I3` at exponent `-6` regenerates `rhoOneZeroLCubicNextThree68`
  verbatim on the next coefficient vector — the `gamma` contributions
  cancel exactly (`4/27 + 8/27 - 4/9 = 0`);
* with `beta = 0`, `I4` at exponent `-5` regenerates
  `rhoOneZeroLCubicNextFour68` verbatim on the next coefficient vector.

Hence the limb is exactly self-similar: it reproduces the full
next-source-packet row system one exponent deeper, together with the
global pin `beta = 0`, and the level-zero component-split scalar lemmas
apply unchanged to the depth-one coefficients.  The refined sibling is
backwired through the full aligned-square selector hierarchy; every
other sibling is retained verbatim.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareRowOneAllZeroConsumer68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance alignedSquareRowOneAllZeroHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The improved `C`-defect order still pins the leading `C0`
coefficient to the cubic value `a²/3`. -/
theorem hahnC0Leading_of_rowOneAllZero68
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-3 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hCdef : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 A C0).orderTop) :
    C0.coeff (-4 : ℚ) = (1 / 3 : k) * (A.coeff (-2 : ℚ)) ^ 2 := by
  have hCR4 : (rhoOneCDefectHahn68 A C0).coeff (-4 : ℚ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hCdef)
  have hm : ((HahnSeries.C (1 / 3 : k)) * A ^ 2).coeff (-4 : ℚ) =
      (1 / 3 : k) * (A.coeff (-2 : ℚ)) ^ 2 := by
    have h : (weightedMonomial68 (1 / 3 : k) A B C0 D E 2 0 0 0 0).coeff
        (-4 : ℚ) =
        (1 / 3 : k) * (A.coeff (-2 : ℚ)) ^ 2 * (B.coeff (-1 : ℚ)) ^ 0 *
          (C0.coeff (-4 : ℚ)) ^ 0 * (D.coeff (-3 : ℚ)) ^ 0 *
          (E.coeff (-6 : ℚ)) ^ 0 := by
      conv_lhs => rw [show (-4 : ℚ) = ((2 : ℕ) : ℚ) * (-2) +
        ((0 : ℕ) : ℚ) * (-1) + ((0 : ℕ) : ℚ) * (-4) +
        ((0 : ℕ) : ℚ) * (-3) + ((0 : ℕ) : ℚ) * (-6) by norm_num]
      exact weightedMonomial68_coeff_at_general_lower_next (1 / 3 : k)
        A B C0 D E 2 0 0 0 0 (-2) (-1) (-4) (-3) (-6) hA hB hC hD hE
    simpa [weightedMonomial68] using h
  have hsub : (rhoOneCDefectHahn68 A C0).coeff (-4 : ℚ) =
      C0.coeff (-4 : ℚ) -
        ((HahnSeries.C (1 / 3 : k)) * A ^ 2).coeff (-4 : ℚ) := by
    simp only [rhoOneCDefectHahn68, HahnSeries.coeff_sub]
  rw [hCR4, hm] at hsub
  linear_combination -hsub

/-- The improved `E`-defect order still pins the leading `E`
coefficient to the cubic value `a³/27`. -/
theorem hahnELeading_of_rowOneAllZero68
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-3 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hEdef : (↑(-4 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 A E).orderTop) :
    E.coeff (-6 : ℚ) = (1 / 27 : k) * (A.coeff (-2 : ℚ)) ^ 3 := by
  have hER6 : (rhoOneEDefectHahn68 A E).coeff (-6 : ℚ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hEdef)
  have hm : ((HahnSeries.C (1 / 27 : k)) * A ^ 3).coeff (-6 : ℚ) =
      (1 / 27 : k) * (A.coeff (-2 : ℚ)) ^ 3 := by
    have h : (weightedMonomial68 (1 / 27 : k) A B C0 D E 3 0 0 0 0).coeff
        (-6 : ℚ) =
        (1 / 27 : k) * (A.coeff (-2 : ℚ)) ^ 3 * (B.coeff (-1 : ℚ)) ^ 0 *
          (C0.coeff (-4 : ℚ)) ^ 0 * (D.coeff (-3 : ℚ)) ^ 0 *
          (E.coeff (-6 : ℚ)) ^ 0 := by
      conv_lhs => rw [show (-6 : ℚ) = ((3 : ℕ) : ℚ) * (-2) +
        ((0 : ℕ) : ℚ) * (-1) + ((0 : ℕ) : ℚ) * (-4) +
        ((0 : ℕ) : ℚ) * (-3) + ((0 : ℕ) : ℚ) * (-6) by norm_num]
      exact weightedMonomial68_coeff_at_general_lower_next (1 / 27 : k)
        A B C0 D E 3 0 0 0 0 (-2) (-1) (-4) (-3) (-6) hA hB hC hD hE
    simpa [weightedMonomial68] using h
  have hsub : (rhoOneEDefectHahn68 A E).coeff (-6 : ℚ) =
      E.coeff (-6 : ℚ) -
        ((HahnSeries.C (1 / 27 : k)) * A ^ 3).coeff (-6 : ℚ) := by
    simp only [rhoOneEDefectHahn68, HahnSeries.coeff_sub]
  rw [hER6, hm] at hsub
  linear_combination -hsub

/-- Under the all-zero improved orders, `I4` at exponent `-6`
degenerates to the single `beta`-loaded scalar `(5/72)·β·a³`. -/
theorem firstIntegralFour68_coeff_neg6_of_rowOneAllZeroBounds
    (beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hCdef : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 A C0).orderTop)
    (hD : (↑(-3 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hEdef : (↑(-4 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 A E).orderTop) :
    (firstIntegralFour68 (HahnSeries.C 0) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-6 : ℚ) =
      (5 / 72 : k) * beta * (A.coeff (-2 : ℚ)) ^ 3 := by
  let CR := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  have hC0co := hahnC0Leading_of_rowOneAllZero68 A B C0 D E
    hA hB hC hD hE hCdef
  have hE6co := hahnELeading_of_rowOneAllZero68 A B C0 D E
    hA hB hC hD hE hEdef
  have hzeroTop (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-6 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-1) +
        (aC : ℚ) * (-2) + (aD : ℚ) * (-3) + (aE : ℚ) * (-4)) :
      (weightedMonomial68 c A B CR D ER aA aB aC aD aE).coeff
          (-6 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B CR D ER
      aA aB aC aD aE (-2) (-1) (-2) (-3) (-4) (-6)
      hA hB (by simpa only [CR] using hCdef) hD
      (by simpa only [ER] using hEdef) hlt
  have hzeroHigher (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-6 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-1) +
        (aC : ℚ) * (-4) + (aD : ℚ) * (-3) + (aE : ℚ) * (-6)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-6 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE (-2) (-1) (-4) (-3) (-6) (-6) hA hB hC hD hE hlt
  have hleadHigher (c : k) (aA aB aC aD aE : ℕ)
      (hw : (aA : ℚ) * (-2) + (aB : ℚ) * (-1) +
          (aC : ℚ) * (-4) + (aD : ℚ) * (-3) + (aE : ℚ) * (-6) = -6) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-6 : ℚ) =
        c * (A.coeff (-2 : ℚ)) ^ aA * (B.coeff (-1 : ℚ)) ^ aB *
          (C0.coeff (-4 : ℚ)) ^ aC * (D.coeff (-3 : ℚ)) ^ aD *
          (E.coeff (-6 : ℚ)) ^ aE := by
    conv_lhs => rw [← hw]
    exact weightedMonomial68_coeff_at_general_lower_next c A B C0 D E
      aA aB aC aD aE (-2) (-1) (-4) (-3) (-6) hA hB hC hD hE
  have hLzero (c0 : k) (aA aB aC aD aE : ℕ) :
      (weightedMonomial68 (c0 * 0) A B C0 D E aA aB aC aD aE).coeff
          (-6 : ℚ) = 0 := by
    simp [weightedMonomial68]
  have ht1 := hzeroTop (-8 / 27 : k) 0 3 0 0 0 (by norm_num)
  have ht2 := hzeroTop (-16 / 9 : k) 1 1 1 0 0 (by norm_num)
  have ht3 := hzeroTop (8 / 3 : k) 0 0 1 1 0 (by norm_num)
  have ht4 := hzeroTop (8 / 3 : k) 0 1 0 0 1 (by norm_num)
  have hh1 := hzeroHigher zeta 1 0 0 0 0 (by norm_num)
  have hh2 := hzeroHigher (2 * epsilon) 0 1 0 0 0 (by norm_num)
  have hh3 := hzeroHigher (3 * delta) 0 0 1 0 0 (by norm_num)
  have hh4 := hzeroHigher (4 * gamma) 0 0 0 1 0 (by norm_num)
  have hh5 := hleadHigher (5 * beta) 0 0 0 0 1 (by norm_num)
  have hh6 := hzeroHigher (-(5 / 12 : k) * beta) 0 2 0 0 0 (by norm_num)
  have hh7 := hzeroHigher (-(3 / 4 : k) * delta) 2 0 0 0 0 (by norm_num)
  have hh9 := hleadHigher ((35 / 216 : k) * beta) 3 0 0 0 0 (by norm_num)
  have hh13 := hleadHigher (-(5 / 6 : k) * beta) 1 0 1 0 0 (by norm_num)
  have hh14 := hzeroHigher (-(4 / 3 : k) * gamma) 1 1 0 0 0 (by norm_num)
  rw [firstIntegralFour68_eq_localFaces, HahnSeries.coeff_add,
    firstIntegralFourTopFaceHahn68_cubicDefects]
  simp only [firstIntegralFourHigherHahn68, HahnSeries.coeff_add]
  rw [show rhoOneCDefectHahn68 A C0 = CR by rfl,
    show rhoOneEDefectHahn68 A E = ER by rfl,
    ht1, ht2, ht3, ht4, hh1, hh2, hh3, hh4, hh5, hh6, hh7, hh9,
    hh13, hh14,
    hLzero ((7 / 12 : k)) 0 0 2 0 0,
    hLzero ((385 / 5184 : k)) 4 0 0 0 0,
    hLzero (-(35 / 72 : k)) 1 2 0 0 0,
    hLzero (-(35 / 72 : k)) 2 0 1 0 0,
    hLzero ((7 / 6 : k)) 1 0 0 0 1,
    hLzero ((7 / 6 : k)) 0 1 0 1 0,
    hE6co, hC0co]
  ring

/-- Under the all-zero improved orders, `I3` at exponent `-6`
regenerates the second next row verbatim on the depth-one coefficients;
the `gamma` contributions cancel exactly. -/
theorem firstIntegralThree68_coeff_neg6_of_rowOneAllZeroBounds
    (beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hCdef : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 A C0).orderTop)
    (hD : (↑(-3 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hEdef : (↑(-4 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 A E).orderTop) :
    (firstIntegralThree68 (HahnSeries.C 0) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-6 : ℚ) =
      rhoOneZeroLCubicNextThree68 (A.coeff (-2 : ℚ))
        (B.coeff (-1 : ℚ))
        ((rhoOneCDefectHahn68 A C0).coeff (-2 : ℚ))
        (D.coeff (-3 : ℚ))
        ((rhoOneEDefectHahn68 A E).coeff (-4 : ℚ)) := by
  let CR := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  have hC0co := hahnC0Leading_of_rowOneAllZero68 A B C0 D E
    hA hB hC hD hE hCdef
  have hE6co := hahnELeading_of_rowOneAllZero68 A B C0 D E
    hA hB hC hD hE hEdef
  have hzeroTop (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-6 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-1) +
        (aC : ℚ) * (-2) + (aD : ℚ) * (-3) + (aE : ℚ) * (-4)) :
      (weightedMonomial68 c A B CR D ER aA aB aC aD aE).coeff
          (-6 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B CR D ER
      aA aB aC aD aE (-2) (-1) (-2) (-3) (-4) (-6)
      hA hB (by simpa only [CR] using hCdef) hD
      (by simpa only [ER] using hEdef) hlt
  have hleadTop (c : k) (aA aB aC aD aE : ℕ)
      (hw : (aA : ℚ) * (-2) + (aB : ℚ) * (-1) +
          (aC : ℚ) * (-2) + (aD : ℚ) * (-3) + (aE : ℚ) * (-4) = -6) :
      (weightedMonomial68 c A B CR D ER aA aB aC aD aE).coeff
          (-6 : ℚ) =
        c * (A.coeff (-2 : ℚ)) ^ aA * (B.coeff (-1 : ℚ)) ^ aB *
          (CR.coeff (-2 : ℚ)) ^ aC * (D.coeff (-3 : ℚ)) ^ aD *
          (ER.coeff (-4 : ℚ)) ^ aE := by
    conv_lhs => rw [← hw]
    exact weightedMonomial68_coeff_at_general_lower_next c A B CR D ER
      aA aB aC aD aE (-2) (-1) (-2) (-3) (-4) hA hB
      (by simpa only [CR] using hCdef) hD
      (by simpa only [ER] using hEdef)
  have hzeroHigher (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-6 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-1) +
        (aC : ℚ) * (-4) + (aD : ℚ) * (-3) + (aE : ℚ) * (-6)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-6 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE (-2) (-1) (-4) (-3) (-6) (-6) hA hB hC hD hE hlt
  have hleadHigher (c : k) (aA aB aC aD aE : ℕ)
      (hw : (aA : ℚ) * (-2) + (aB : ℚ) * (-1) +
          (aC : ℚ) * (-4) + (aD : ℚ) * (-3) + (aE : ℚ) * (-6) = -6) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-6 : ℚ) =
        c * (A.coeff (-2 : ℚ)) ^ aA * (B.coeff (-1 : ℚ)) ^ aB *
          (C0.coeff (-4 : ℚ)) ^ aC * (D.coeff (-3 : ℚ)) ^ aD *
          (E.coeff (-6 : ℚ)) ^ aE := by
    conv_lhs => rw [← hw]
    exact weightedMonomial68_coeff_at_general_lower_next c A B C0 D E
      aA aB aC aD aE (-2) (-1) (-4) (-3) (-6) hA hB hC hD hE
  have hLzero (c0 : k) (aA aB aC aD aE : ℕ) :
      (weightedMonomial68 (c0 * 0) A B C0 D E aA aB aC aD aE).coeff
          (-6 : ℚ) = 0 := by
    simp [weightedMonomial68]
  have ht1 := hleadTop (4 / 3 : k) 0 0 0 2 0 (by norm_num)
  have ht2 := hleadTop (-16 / 9 : k) 1 1 0 1 0 (by norm_num)
  have ht3 := hleadTop (4 / 9 : k) 2 2 0 0 0 (by norm_num)
  have ht4 := hleadTop (-8 / 9 : k) 1 0 2 0 0 (by norm_num)
  have ht5 := hzeroTop (-8 / 9 : k) 0 2 1 0 0 (by norm_num)
  have ht6 := hleadTop (8 / 3 : k) 0 0 1 0 1 (by norm_num)
  have hj1 := hzeroHigher zeta 0 1 0 0 0 (by norm_num)
  have hj2 := hzeroHigher (2 * epsilon) 0 0 1 0 0 (by norm_num)
  have hj3 := hzeroHigher (3 * delta) 0 0 0 1 0 (by norm_num)
  have hj4 := hleadHigher (4 * gamma) 0 0 0 0 1 (by norm_num)
  have hj6 := hzeroHigher (-(2 / 3 : k) * epsilon) 2 0 0 0 0 (by norm_num)
  have hj7 := hzeroHigher (-(2 / 3 : k) * gamma) 0 2 0 0 0 (by norm_num)
  have hj8 := hleadHigher ((8 / 27 : k) * gamma) 3 0 0 0 0 (by norm_num)
  have hj10 := hzeroHigher (-(5 / 6 : k) * beta) 1 0 0 1 0 (by norm_num)
  have hj11 := hzeroHigher (-(5 / 6 : k) * beta) 0 1 1 0 0 (by norm_num)
  have hj12 := hleadHigher (-(4 / 3 : k) * gamma) 1 0 1 0 0 (by norm_num)
  have hj13 := hzeroHigher (-(3 / 2 : k) * delta) 1 1 0 0 0 (by norm_num)
  have hj16 := hzeroHigher ((35 / 72 : k) * beta) 2 1 0 0 0 (by norm_num)
  rw [firstIntegralThree68_eq_localFaces, HahnSeries.coeff_add,
    firstIntegralThreeTopFaceHahn68_cubicDefects]
  simp only [firstIntegralThreeHigherHahn68, HahnSeries.coeff_add]
  rw [show rhoOneCDefectHahn68 A C0 = CR by rfl,
    show rhoOneEDefectHahn68 A E = ER by rfl,
    ht1, ht2, ht3, ht4, ht5, ht6, hj1, hj2, hj3, hj4, hj6, hj7, hj8,
    hj10, hj11, hj12, hj13, hj16,
    hLzero (-(35 / 216 : k)) 0 3 0 0 0,
    hLzero (-(35 / 72 : k)) 2 0 0 1 0,
    hLzero ((7 / 6 : k)) 0 1 0 0 1,
    hLzero ((7 / 6 : k)) 0 0 1 1 0,
    hLzero ((385 / 1296 : k)) 3 1 0 0 0,
    hLzero (-(35 / 36 : k)) 1 1 1 0 0,
    hE6co, hC0co]
  simp only [CR, ER, rhoOneZeroLCubicNextThree68]
  ring

/-- With `beta = 0`, `I4` at exponent `-5` regenerates the first next
row verbatim on the depth-one coefficients. -/
theorem firstIntegralFour68_coeff_neg5_of_rowOneAllZeroBounds
    (gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-4 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hCdef : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 A C0).orderTop)
    (hD : (↑(-3 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-6 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hEdef : (↑(-4 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 A E).orderTop) :
    (firstIntegralFour68 (HahnSeries.C 0) A B C0 D E
      (HahnSeries.C 0) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-5 : ℚ) =
      rhoOneZeroLCubicNextFour68 (A.coeff (-2 : ℚ))
        (B.coeff (-1 : ℚ))
        ((rhoOneCDefectHahn68 A C0).coeff (-2 : ℚ))
        (D.coeff (-3 : ℚ))
        ((rhoOneEDefectHahn68 A E).coeff (-4 : ℚ)) := by
  let CR := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  have hzeroTop (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-5 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-1) +
        (aC : ℚ) * (-2) + (aD : ℚ) * (-3) + (aE : ℚ) * (-4)) :
      (weightedMonomial68 c A B CR D ER aA aB aC aD aE).coeff
          (-5 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B CR D ER
      aA aB aC aD aE (-2) (-1) (-2) (-3) (-4) (-5)
      hA hB (by simpa only [CR] using hCdef) hD
      (by simpa only [ER] using hEdef) hlt
  have hleadTop (c : k) (aA aB aC aD aE : ℕ)
      (hw : (aA : ℚ) * (-2) + (aB : ℚ) * (-1) +
          (aC : ℚ) * (-2) + (aD : ℚ) * (-3) + (aE : ℚ) * (-4) = -5) :
      (weightedMonomial68 c A B CR D ER aA aB aC aD aE).coeff
          (-5 : ℚ) =
        c * (A.coeff (-2 : ℚ)) ^ aA * (B.coeff (-1 : ℚ)) ^ aB *
          (CR.coeff (-2 : ℚ)) ^ aC * (D.coeff (-3 : ℚ)) ^ aD *
          (ER.coeff (-4 : ℚ)) ^ aE := by
    conv_lhs => rw [← hw]
    exact weightedMonomial68_coeff_at_general_lower_next c A B CR D ER
      aA aB aC aD aE (-2) (-1) (-2) (-3) (-4) hA hB
      (by simpa only [CR] using hCdef) hD
      (by simpa only [ER] using hEdef)
  have hzeroHigher (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-5 : ℚ) < (aA : ℚ) * (-2) + (aB : ℚ) * (-1) +
        (aC : ℚ) * (-4) + (aD : ℚ) * (-3) + (aE : ℚ) * (-6)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-5 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE (-2) (-1) (-4) (-3) (-6) (-5) hA hB hC hD hE hlt
  have hLzero (c0 : k) (aA aB aC aD aE : ℕ) :
      (weightedMonomial68 (c0 * 0) A B C0 D E aA aB aC aD aE).coeff
          (-5 : ℚ) = 0 := by
    simp [weightedMonomial68]
  have ht1 := hzeroTop (-8 / 27 : k) 0 3 0 0 0 (by norm_num)
  have ht2 := hleadTop (-16 / 9 : k) 1 1 1 0 0 (by norm_num)
  have ht3 := hleadTop (8 / 3 : k) 0 0 1 1 0 (by norm_num)
  have ht4 := hleadTop (8 / 3 : k) 0 1 0 0 1 (by norm_num)
  have hh1 := hzeroHigher zeta 1 0 0 0 0 (by norm_num)
  have hh2 := hzeroHigher (2 * epsilon) 0 1 0 0 0 (by norm_num)
  have hh3 := hzeroHigher (3 * delta) 0 0 1 0 0 (by norm_num)
  have hh4 := hzeroHigher (4 * gamma) 0 0 0 1 0 (by norm_num)
  have hh7 := hzeroHigher (-(3 / 4 : k) * delta) 2 0 0 0 0 (by norm_num)
  have hh14 := hzeroHigher (-(4 / 3 : k) * gamma) 1 1 0 0 0 (by norm_num)
  rw [firstIntegralFour68_eq_localFaces, HahnSeries.coeff_add,
    firstIntegralFourTopFaceHahn68_cubicDefects]
  simp only [firstIntegralFourHigherHahn68, HahnSeries.coeff_add]
  rw [show rhoOneCDefectHahn68 A C0 = CR by rfl,
    show rhoOneEDefectHahn68 A E = ER by rfl,
    ht1, ht2, ht3, ht4, hh1, hh2, hh3, hh4, hh7, hh14,
    hLzero (5 : k) 0 0 0 0 1,
    hLzero (-(5 / 12 : k)) 0 2 0 0 0,
    hLzero ((7 / 12 : k)) 0 0 2 0 0,
    hLzero ((35 / 216 : k)) 3 0 0 0 0,
    hLzero ((385 / 5184 : k)) 4 0 0 0 0,
    hLzero (-(35 / 72 : k)) 1 2 0 0 0,
    hLzero (-(35 / 72 : k)) 2 0 1 0 0,
    hLzero (-(5 / 6 : k)) 1 0 1 0 0,
    hLzero ((7 / 6 : k)) 1 0 0 0 1,
    hLzero ((7 / 6 : k)) 0 1 0 1 0]
  simp only [CR, ER, rhoOneZeroLCubicNextFour68]
  ring

/-- All four defect coordinates of the all-zero row-one child gain one
full order of vanishing at the root. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_rowOneAllZero_defect_orders
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hallzero :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      B.coeff (-2 : ℚ) = 0 ∧
        (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ) = 0 ∧
        D.coeff (-4 : ℚ) = 0 ∧
        (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    ((↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop) ∧
      ((↑(-2 : ℚ) : WithTop ℚ) ≤
        (rhoOneCDefectHahn68 A C0).orderTop) ∧
      ((↑(-3 : ℚ) : WithTop ℚ) ≤ D.orderTop) ∧
      ((↑(-4 : ℚ) : WithTop ℚ) ≤
        (rhoOneEDefectHahn68 A E).orderTop) := by
  dsimp only at hallzero ⊢
  have hbranch := P.1
  obtain ⟨cs, t, v, z, hcs, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ :=
    hbranch
  have hv' : v = z ^ 2 / 3 := by
    have h := (div_eq_iff (pow_ne_zero 2 hz)).mp hvcore
    calc v = (1 / 3 : k) * z ^ 2 := h
         _ = z ^ 2 / 3 := by ring
  have ht' : t = z ^ 3 / 27 := by
    have h := (div_eq_iff (pow_ne_zero 3 hz)).mp htcore
    calc t = (1 / 27 : k) * z ^ 3 := h
         _ = z ^ 3 / 27 := by ring
  have hgval : g.eval T.root = cs * z := by rw [hzdef]; field_simp [hcs]
  have huval : u.eval T.root = cs ^ 2 * v := by rw [hv]; field_simp [hcs]
  have hp3val : (p.coeff 3).eval T.root = cs ^ 3 * t := by
    rw [ht]; field_simp [hcs]
  let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2
  let ER : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * T.source.A ^ 3
  let A0 := localClearedA68RhoOne g u
  let B0 := localClearedB68RhoOne g u (p.coeff 3)
  let C0 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
  let D0 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1)
  let E0 := localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1) (p.coeff 0)
  let Cdef0 : k[X] := C0 - C (1 / 3 : k) * A0 ^ 2
  let Edef0 : k[X] := E0 - C (1 / 27 : k) * A0 ^ 3
  obtain ⟨hAclear, hBclear, hCclear, hDclear, hEclear⟩ :=
    T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero hH hp6 hp5 hp4
  change algebraMap k[X] (RatFunc k) A0 = _ at hAclear
  change algebraMap k[X] (RatFunc k) B0 = _ at hBclear
  change algebraMap k[X] (RatFunc k) C0 = _ at hCclear
  change algebraMap k[X] (RatFunc k) D0 = _ at hDclear
  change algebraMap k[X] (RatFunc k) E0 = _ at hEclear
  have hB0root : B0.eval T.root = 0 := by
    simp [B0, localClearedB68RhoOne, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  have hD0root : D0.eval T.root = 0 := by
    simp [D0, localClearedD68RhoOne, T.root_eq, hgval, huval, hp3val,
      hv', ht']
    field_simp [hcs]; ring
  have hCdef0root : Cdef0.eval T.root = 0 := by
    simp [Cdef0, C0, A0, localClearedC68RhoOne, localClearedA68RhoOne,
      T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  have hEdef0root : Edef0.eval T.root = 0 := by
    simp [Edef0, E0, A0, localClearedE68RhoOne, localClearedA68RhoOne,
      T.root_eq, hgval, huval, hp3val, hv', ht']
    field_simp [hcs]; ring
  obtain ⟨B1, hB1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 B0 T.root T.scale_degree T.root_eq hB0root
  obtain ⟨C1, hC1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 Cdef0 T.root T.scale_degree T.root_eq hCdef0root
  obtain ⟨D1, hD1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 D0 T.root T.scale_degree T.root_eq hD0root
  obtain ⟨E1, hE1⟩ := linearPolynomial_dvd_of_eval_eq_zero
    h0 Edef0 T.root T.scale_degree T.root_eq hEdef0root
  have hCdefclear : algebraMap k[X] (RatFunc k) Cdef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * CR := by
    dsimp only [Cdef0, CR]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hCclear, hAclear]; ring
  have hEdefclear : algebraMap k[X] (RatFunc k) Edef0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 6 * ER := by
    dsimp only [Edef0, ER]
    simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hEclear, hAclear]; ring
  have hBclear1 : algebraMap k[X] (RatFunc k) B1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * T.source.B := by
    have hc := algebraMap_cancel_factoredClearing
      h0 B0 B1 T.source.B 1 2 1 T.scale_ne_zero (by simpa using hB1) (by
        simpa only [Nat.mul_one, show 2 + 1 = 3 by omega] using hBclear)
    simpa only [Nat.mul_one] using hc
  have hCclear1 : algebraMap k[X] (RatFunc k) C1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 3 * CR := by
    have hc := algebraMap_cancel_factoredClearing
      h0 Cdef0 C1 CR 1 3 1 T.scale_ne_zero (by simpa using hC1) (by
        simpa only [Nat.mul_one, show 3 + 1 = 4 by omega] using hCdefclear)
    simpa only [Nat.mul_one] using hc
  have hDclear1 : algebraMap k[X] (RatFunc k) D1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 4 * T.source.D := by
    have hc := algebraMap_cancel_factoredClearing
      h0 D0 D1 T.source.D 1 4 1 T.scale_ne_zero (by simpa using hD1) (by
        simpa only [Nat.mul_one, show 4 + 1 = 5 by omega] using hDclear)
    simpa only [Nat.mul_one] using hc
  have hEclear1 : algebraMap k[X] (RatFunc k) E1 =
      (algebraMap k[X] (RatFunc k) h0) ^ 5 * ER := by
    have hc := algebraMap_cancel_factoredClearing
      h0 Edef0 E1 ER 1 5 1 T.scale_ne_zero (by simpa using hE1) (by
        simpa only [Nat.mul_one, show 5 + 1 = 6 by omega] using hEdefclear)
    simpa only [Nat.mul_one] using hc
  have hCRmap : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [CR, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ratFuncAtHahn46 T.root ER =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [ER, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  rcases hallzero with ⟨hzb, hzc, hzd, hze⟩
  have hBco1 := localHahn_coeff_neg_of_cleared T.root cs h0 B1
    T.source.B 2 hcs hsingle hBclear1
  have hCco1 := localHahn_coeff_neg_of_cleared T.root cs h0 C1
    CR 3 hcs hsingle hCclear1
  have hDco1 := localHahn_coeff_neg_of_cleared T.root cs h0 D1
    T.source.D 4 hcs hsingle hDclear1
  have hEco1 := localHahn_coeff_neg_of_cleared T.root cs h0 E1
    ER 5 hcs hsingle hEclear1
  norm_num at hBco1 hCco1 hDco1 hEco1
  have hB1root : B1.eval T.root = 0 := by
    have h := hBco1.symm.trans hzb
    exact (mul_eq_zero.mp h).resolve_left
      (inv_ne_zero (pow_ne_zero 2 hcs))
  have hzc' : (ratFuncAtHahn46 T.root CR).coeff (-3 : ℚ) = 0 := by
    rw [hCRmap]; exact hzc
  have hC1root : C1.eval T.root = 0 := by
    have h := hCco1.symm.trans hzc'
    exact (mul_eq_zero.mp h).resolve_left
      (inv_ne_zero (pow_ne_zero 3 hcs))
  have hD1root : D1.eval T.root = 0 := by
    have h := hDco1.symm.trans hzd
    exact (mul_eq_zero.mp h).resolve_left
      (inv_ne_zero (pow_ne_zero 4 hcs))
  have hze' : (ratFuncAtHahn46 T.root ER).coeff (-5 : ℚ) = 0 := by
    rw [hERmap]; exact hze
  have hE1root : E1.eval T.root = 0 := by
    have h := hEco1.symm.trans hze'
    exact (mul_eq_zero.mp h).resolve_left
      (inv_ne_zero (pow_ne_zero 5 hcs))
  have hBord1 : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop :=
    localHahn_orderTop_ge_one_better_of_cleared_root_zero
      T.root h0 B1 T.source.B 2 (by omega) T.scale_ne_zero T.scale_degree
      T.root_eq T.scale_order hBclear1 hB1root
  have hCord1 : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop := by
    rw [← hCRmap]
    exact localHahn_orderTop_ge_one_better_of_cleared_root_zero
      T.root h0 C1 CR 3 (by omega) T.scale_ne_zero T.scale_degree
      T.root_eq T.scale_order hCclear1 hC1root
  have hDord1 : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.D).orderTop :=
    localHahn_orderTop_ge_one_better_of_cleared_root_zero
      T.root h0 D1 T.source.D 4 (by omega) T.scale_ne_zero T.scale_degree
      T.root_eq T.scale_order hDclear1 hD1root
  have hEord1 : (↑(-4 : ℚ) : WithTop ℚ) ≤
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E)).orderTop := by
    rw [← hERmap]
    exact localHahn_orderTop_ge_one_better_of_cleared_root_zero
      T.root h0 E1 ER 5 (by omega) T.scale_ne_zero T.scale_degree
      T.root_eq T.scale_order hEclear1 hE1root
  exact ⟨hBord1, hCord1, hDord1, hEord1⟩

/-- Source transport of the three new rows: the `I4` exponent `-6` face
kills `beta`, and the next `I4`/`I3` faces regenerate the two next rows
verbatim on the depth-one coefficients. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_rowOneAllZero_beta_rows
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hallzero :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      B.coeff (-2 : ℚ) = 0 ∧
        (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ) = 0 ∧
        D.coeff (-4 : ℚ) = 0 ∧
        (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    T.source.beta = 0 ∧
      rhoOneZeroLCubicNextFour68 (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
        ((rhoOneCDefectHahn68 A C0).coeff (-2 : ℚ)) (D.coeff (-3 : ℚ))
        ((rhoOneEDefectHahn68 A E).coeff (-4 : ℚ)) = 0 ∧
      rhoOneZeroLCubicNextThree68 (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
        ((rhoOneCDefectHahn68 A C0).coeff (-2 : ℚ)) (D.coeff (-3 : ℚ))
        ((rhoOneEDefectHahn68 A E).coeff (-4 : ℚ)) = 0 := by
  dsimp only
  have hords := T.rhoOne_rowOneAllZero_defect_orders
    hp hH hp6 hp5 hp4 P hallzero
  dsimp only at hords
  obtain ⟨hBord1, hCord1, hDord1, hEord1⟩ := hords
  dsimp only [RhoOneZeroLCubicNextSourcePacket68,
    RhoOneZeroLCubicImprovedHahnBounds68] at P
  obtain ⟨_, ⟨hAord, hBord0, hCord0, hCdeford0, hDord0, hEord0,
    hEdeford0⟩, hAne, htaut, h4old, h3old, hsplitold⟩ := P
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi4H := congrArg (ratFuncAtHahn46 T.root) hi4
  have hi4H' :
      firstIntegralFour68 (HahnSeries.C 0) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i4 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi4H
  have hi3H := congrArg (ratFuncAtHahn46 T.root) hi3
  have hi3H' :
      firstIntegralThree68 (HahnSeries.C 0) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i3 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi3H
  have h4coeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-6 : ℚ)) hi4H'
  have h4const : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-6 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [h4const] at h4coeff
  have h4formula := firstIntegralFour68_coeff_neg6_of_rowOneAllZeroBounds
    T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hAord hBord1 hCord0 hCord1 hDord1
      hEord0 hEord1
  rw [h4formula] at h4coeff
  have hbeta : T.source.beta = 0 := by
    rcases mul_eq_zero.mp h4coeff with h1 | h2
    · rcases mul_eq_zero.mp h1 with h0' | hb
      · norm_num at h0'
      · exact hb
    · exact absurd h2 (pow_ne_zero 3 hAne)
  have h3coeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-6 : ℚ)) hi3H'
  have h3const : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-6 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [h3const] at h3coeff
  have h3formula := firstIntegralThree68_coeff_neg6_of_rowOneAllZeroBounds
    T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hAord hBord1 hCord0 hCord1 hDord1
      hEord0 hEord1
  rw [h3formula] at h3coeff
  rw [hbeta] at hi4H'
  have h5coeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-5 : ℚ)) hi4H'
  have h5const : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-5 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [h5const] at h5coeff
  have h5formula := firstIntegralFour68_coeff_neg5_of_rowOneAllZeroBounds
    T.source.gamma T.source.delta T.source.epsilon T.source.zeta
      AH BH CH DH EH hAord hBord1 hCord0 hCord1 hDord1 hEord0 hEord1
  rw [h5formula] at h5coeff
  exact ⟨hbeta, h5coeff, h3coeff⟩

/-- The complete consumer packet on the all-zero row-one child: the
retained source packet and vanishing face, the `beta` pin, the four
improved orders, both regenerated depth-one rows, and the exact
depth-one component residual. -/
def RhoOneAlignedSquareRowOneAllZeroConsumer68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let CD := rhoOneCDefectHahn68 A C0
  let ED := rhoOneEDefectHahn68 A E
  let a := A.coeff (-2 : ℚ)
  let b1 := B.coeff (-1 : ℚ)
  let c1 := CD.coeff (-2 : ℚ)
  let d1 := D.coeff (-3 : ℚ)
  let e1 := ED.coeff (-4 : ℚ)
  RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    (B.coeff (-2 : ℚ) = 0 ∧ CD.coeff (-3 : ℚ) = 0 ∧
      D.coeff (-4 : ℚ) = 0 ∧ ED.coeff (-5 : ℚ) = 0) ∧
    T.source.beta = 0 ∧
    ((↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
      (↑(-2 : ℚ) : WithTop ℚ) ≤ CD.orderTop ∧
      (↑(-3 : ℚ) : WithTop ℚ) ≤ D.orderTop ∧
      (↑(-4 : ℚ) : WithTop ℚ) ≤ ED.orderTop) ∧
    rhoOneZeroLCubicNextFour68 a b1 c1 d1 e1 = 0 ∧
    rhoOneZeroLCubicNextThree68 a b1 c1 d1 e1 = 0 ∧
    (((a * b1 = 3 * d1 ∧ 3 * e1 = a * c1) ∨
        (b1 = 0 ∧ c1 = 0 ∧ d1 = 0)) ∨
      a * b1 ^ 2 - b1 * d1 + 2 * c1 ^ 2 = 0)

/-- The all-zero row-one child converts to its full consumer packet:
the limb is exactly self-similar one exponent deeper, with `beta`
killed globally. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_rowOneAllZero_consumer
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hallzero :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      B.coeff (-2 : ℚ) = 0 ∧
        (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ) = 0 ∧
        D.coeff (-4 : ℚ) = 0 ∧
        (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ) = 0) :
    RhoOneAlignedSquareRowOneAllZeroConsumer68 T g u := by
  have hords := T.rhoOne_rowOneAllZero_defect_orders
    hp hH hp6 hp5 hp4 P hallzero
  have hrows := T.rhoOne_rowOneAllZero_beta_rows
    hp hH hp6 hp5 hp4 P hallzero
  dsimp only at hords hrows hallzero
  dsimp only [RhoOneAlignedSquareRowOneAllZeroConsumer68]
  obtain ⟨hbeta, h4row, h3row⟩ := hrows
  refine ⟨P, hallzero, hbeta, hords, h4row, h3row, ?_⟩
  rcases rhoOneZeroLCubicNext_rows_component_split68 _ _ _ _ _
      h4row h3row with hd1 | hsecond
  · have hfirst := rhoOneZeroLCubic_firstComponent_split68 _ _ _ _ _
      h4row hd1
    exact Or.inl (rhoOneZeroLCubic_firstComponent_I3_split68 _ _ _ _ _
      h3row hd1 hfirst)
  · exact Or.inr hsecond

/-- The early cubic sibling inventory with its all-zero row-one child
upgraded to the consumer packet.  Every other sibling is retained
verbatim. -/
def RhoOneAlignedSquareEarlyCubicSiblingRefined68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C ER
  let a := A.coeff (-2 : ℚ)
  let b := B.coeff (-2 : ℚ)
  let c := C.coeff (-3 : ℚ)
  RhoOneZeroLCubicSecondNextComponent68 T g u ∨
  RhoOneAlignedSquareRowOneAllZeroConsumer68 T g u ∨
  (RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    (a * b = 3 * D.coeff (-4 : ℚ) ∧
      3 * ER.coeff (-5 : ℚ) = a * c) ∧
    ((c = 0 ∧ b ≠ 0 ∧ F.coeff (-3 : ℚ) = 0 ∧
        -64 * b ^ 3 + 15 * T.source.beta * a ^ 3 +
          576 * b * G.coeff (-4 : ℚ) = 0) ∨
      (c ≠ 0 ∧ b ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
        rhoOneZeroLCubicMainTangentFour68 T.source.beta a b c
          (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0 ∧
        rhoOneZeroLCubicMainTangentThree68 a b c
          (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0)))

/-- Upgrade of the early cubic sibling inventory: only the all-zero
row-one child is transformed; the second component and both nonzero
main-tangent children pass through literally. -/
theorem RhoOneAlignedSquareEarlyCubicSibling68.refine_rowOneAllZero
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    {T : SquareZeroLIntegratedLocalRootData68 p q j h0}
    (hs : RhoOneAlignedSquareEarlyCubicSibling68 T g u)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    RhoOneAlignedSquareEarlyCubicSiblingRefined68 T g u := by
  dsimp only [RhoOneAlignedSquareEarlyCubicSibling68,
    RhoOneAlignedSquareEarlyCubicSiblingRefined68] at hs ⊢
  rcases hs with h1 | ⟨P, hz⟩ | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl
      (T.rhoOne_rowOneAllZero_consumer hp hH hp6 hp5 hp4 P hz))
  · exact Or.inr (Or.inr h3)

/-- The full aligned square-source selector hierarchy with the early
cubic sibling refined through the all-zero row-one consumer. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_rowOneAllZero_selectorHierarchy
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    ∃ g u : k[X],
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      ((h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
       RhoOneZeroLNoncubicSourcePacket68 T g u ∨
       RhoOneAlignedSquareEarlyCubicSiblingRefined68 T g u ∨
       RhoOneAlignedSquareExceptionalMainEntry68 T g u) := by
  obtain ⟨g, u, hp5, hp4, hroutes⟩ :=
    T.rhoOne_alignedSquare_sourceSelectorHierarchy hp hH hp6
  refine ⟨g, u, hp5, hp4, ?_⟩
  rcases hroutes with hdesc | hnon | hsib | hentry
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl hnon)
  · exact Or.inr (Or.inr (Or.inl
      (hsib.refine_rowOneAllZero hp hH hp6 hp5 hp4)))
  · exact Or.inr (Or.inr (Or.inr hentry))

/-- Normalized aligned-square source wrapper for the refined selector
hierarchy. -/
theorem normalized68ScaleTwo_alignedSquare_rowOneAllZero_sourceSelectorHierarchy
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ∃ (j : k) (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
        (g u : k[X]),
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      ((h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
       RhoOneZeroLNoncubicSourcePacket68 T g u ∨
       RhoOneAlignedSquareEarlyCubicSiblingRefined68 T g u ∨
       RhoOneAlignedSquareExceptionalMainEntry68 T g u) := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hsource.2.2.1
  have hp6 : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hsource.2.2.2.2.1
  obtain ⟨j, ⟨T⟩⟩ :=
    normalized68ScaleTwo_alignedSquareBranch_localRootData
      hsource hh0 hH haligned
  obtain ⟨g, u, hp5, hp4, hroutes⟩ :=
    T.rhoOne_alignedSquare_rowOneAllZero_selectorHierarchy hp hH hp6
  exact ⟨j, T, g, u, hp5, hp4, hroutes⟩

end AlignedSquareRowOneAllZeroConsumer68

end Max11DegreeRoutes
