import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapFourthTransportScratch

/-! # Arbitrary coefficient recurrence behind the aligned-square cap -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapConvolutionInduction68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareCapConvolutionHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

/-- The reduced third-integral series on the cap.  Its relevant source rows
start at absolute Laurent degree six. -/
def rhoOneCapReducedI3Series68 (epsilon : k)
    (C F G : LaurentSeries k) : LaurentSeries k :=
  4 * C * G + 2 * F ^ 2 + 3 * HahnSeries.C epsilon * C

/-- The reduced fourth-integral series on the cap.  Its relevant source rows
start at absolute Laurent degree ten. -/
def rhoOneCapReducedI4Series68 (epsilon : k)
    (B C F G : LaurentSeries k) : LaurentSeries k :=
  4 * B * G + 4 * C * F + 3 * HahnSeries.C epsilon * B

/-- Coordinate defect whose relative jets `T₀,T₁,…` are at absolute
degrees `14,15,…`. -/
def rhoOneCapCoordinateDefectSeries68
    (B C F : LaurentSeries k) : LaurentSeries k :=
  2 * C ^ 2 - B * F

/-- Global algebraic identity underlying every finite jet calculation. -/
theorem rhoOneCap_reduced_convolution_identity68
    (epsilon : k) (B C F G : LaurentSeries k) :
    B * rhoOneCapReducedI3Series68 epsilon C F G -
        C * rhoOneCapReducedI4Series68 epsilon B C F G =
      (-2 : LaurentSeries k) *
        (F * rhoOneCapCoordinateDefectSeries68 B C F) := by
  simp only [rhoOneCapReducedI3Series68, rhoOneCapReducedI4Series68,
    rhoOneCapCoordinateDefectSeries68]
  ring

/-- The same identity at an arbitrary Laurent coefficient.  This statement
does not assume that either reduced integral vanishes outside a finite
window. -/
theorem rhoOneCap_reduced_convolution_coeff68
    (n : ℤ) (epsilon : k) (B C F G : LaurentSeries k) :
    (B * rhoOneCapReducedI3Series68 epsilon C F G -
        C * rhoOneCapReducedI4Series68 epsilon B C F G).coeff n =
      ((-2 : LaurentSeries k) *
        (F * rhoOneCapCoordinateDefectSeries68 B C F)).coeff n := by
  exact congrArg (fun X : LaurentSeries k => X.coeff n)
    (rhoOneCap_reduced_convolution_identity68 epsilon B C F G)

/-- Arbitrary-index propagation.  At coefficient `m+3`, vanishing of the
two reduced-integral convolution faces and an order bound `ord H ≥ m`
isolate `F[3] H[m]`.  No global vanishing is assumed. -/
theorem rhoOneCap_coordinate_defect_propagate68
    (m : ℤ) (epsilon : k) (B C F G : LaurentSeries k)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hH : (↑m : WithTop ℤ) ≤
      (rhoOneCapCoordinateDefectSeries68 B C F).orderTop)
    (hf3 : F.coeff 3 ≠ 0)
    (hleft : (B * rhoOneCapReducedI3Series68 epsilon C F G).coeff
      (m + 3) = 0)
    (hright : (C * rhoOneCapReducedI4Series68 epsilon B C F G).coeff
      (m + 3) = 0) :
    (rhoOneCapCoordinateDefectSeries68 B C F).coeff m = 0 := by
  let H := rhoOneCapCoordinateDefectSeries68 B C F
  have hFHraw := laurent_coeff_mul_lower68 F H 3 m hF (by
    simpa only [H] using hH)
  have hFH : (F * H).coeff (m + 3) = F.coeff 3 * H.coeff m := by
    simpa only [add_comm] using hFHraw
  have hc := rhoOneCap_reduced_convolution_coeff68
    (m + 3) epsilon B C F G
  rw [HahnSeries.coeff_sub, hleft, hright] at hc
  have hminusTwo : (-2 : LaurentSeries k) = HahnSeries.C (-2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_neg, map_ofNat]
  rw [hminusTwo, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul] at hc
  simp only [zero_sub] at hc
  rw [hFH] at hc
  have hprod : F.coeff 3 * H.coeff m = 0 := by
    linear_combination (1 / 2 : k) * hc
  have := (mul_eq_zero.mp hprod).resolve_left hf3
  simpa only [H] using this

/-- Exact last pure cap step before the omitted `A B F` term enters I₃.
The hypotheses mean: `T₀,…,T₄` have raised `ord H` to 19;
I₃ rows through 11 have raised `ord R₃` to 12; and I₄ rows through
15 have raised `ord R₄` to 16.  Then the arbitrary recurrence forces
`T₅ = H[19] = 0`. -/
theorem rhoOneCap_coordinate_defect_endpoint_five68
    (epsilon : k) (B C F G : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (↑(7 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hR3 : (↑(12 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI3Series68 epsilon C F G).orderTop)
    (hR4 : (↑(16 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI4Series68 epsilon B C F G).orderTop)
    (hH : (↑(19 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCoordinateDefectSeries68 B C F).orderTop)
    (hf3 : F.coeff 3 ≠ 0) :
    (rhoOneCapCoordinateDefectSeries68 B C F).coeff 19 = 0 := by
  have hBR3 : (↑(23 : ℤ) : WithTop ℤ) ≤
      (B * rhoOneCapReducedI3Series68 epsilon C F G).orderTop := by
    have h := le_trans (add_le_add hB hR3) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hCR4 : (↑(23 : ℤ) : WithTop ℤ) ≤
      (C * rhoOneCapReducedI4Series68 epsilon B C F G).orderTop := by
    have h := le_trans (add_le_add hC hR4) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hleft : (B * rhoOneCapReducedI3Series68 epsilon C F G).coeff 22 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBR3)
  have hright : (C * rhoOneCapReducedI4Series68 epsilon B C F G).coeff 22 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hCR4)
  exact rhoOneCap_coordinate_defect_propagate68 19 epsilon B C F G
    hF hH hf3 (by simpa using hleft) (by simpa using hright)

/-- The precise support barrier: the discarded source monomial `A B F`
has lower degree `-2+11+3=12`.  Hence rows I₃[6]…I₃[11] are pure,
but I₃[12] is not covered by the reduced recurrence without restoring
the `A B F` coefficient. -/
theorem rhoOneCap_pure_i3_support_endpoint68 :
    (-2 : ℤ) + 11 + 3 = 12 ∧ (11 : ℤ) < 12 ∧ ¬ ((12 : ℤ) < 12) := by
  norm_num

end AlignedSquareTerminalGBoundaryCapConvolutionInduction68

end Max11DegreeRoutes
