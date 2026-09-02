import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapPostRestorationTransportScratch

/-! # Scalar-core realization of the corrected seventh coordinate jet -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapPostRestorationT668

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareCapPostRestorationT6HahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

def rhoOneI3CapTwelveReducedLaurentCore68
    (C F G : LaurentSeries k) : k :=
  C.coeff 7 * G.coeff 5 + C.coeff 8 * G.coeff 4 +
    C.coeff 9 * G.coeff 3 + C.coeff 10 * G.coeff 2 +
    C.coeff 11 * G.coeff 1 + C.coeff 12 * G.coeff 0 +
    C.coeff 13 * G.coeff (-1) + F.coeff 3 * F.coeff 9 +
    F.coeff 4 * F.coeff 8 + F.coeff 5 * F.coeff 7 +
    (1 / 2 : k) * F.coeff 6 ^ 2

def rhoOneI4CapSixteenLaurentCore68
    (B C F G : LaurentSeries k) : k :=
  B.coeff 11 * G.coeff 5 + B.coeff 12 * G.coeff 4 +
    B.coeff 13 * G.coeff 3 + B.coeff 14 * G.coeff 2 +
    B.coeff 15 * G.coeff 1 + B.coeff 16 * G.coeff 0 +
    B.coeff 17 * G.coeff (-1) + C.coeff 7 * F.coeff 9 +
    C.coeff 8 * F.coeff 8 + C.coeff 9 * F.coeff 7 +
    C.coeff 10 * F.coeff 6 + C.coeff 11 * F.coeff 5 +
    C.coeff 12 * F.coeff 4 + C.coeff 13 * F.coeff 3

def rhoOneCapCoordinateDefectT6LaurentCore68
    (B C F : LaurentSeries k) : k :=
  4 * C.coeff 7 * C.coeff 13 + 4 * C.coeff 8 * C.coeff 12 +
    4 * C.coeff 9 * C.coeff 11 + 2 * C.coeff 10 ^ 2 -
    B.coeff 17 * F.coeff 3 - B.coeff 16 * F.coeff 4 -
    B.coeff 15 * F.coeff 5 - B.coeff 14 * F.coeff 6 -
    B.coeff 13 * F.coeff 7 - B.coeff 12 * F.coeff 8 -
    B.coeff 11 * F.coeff 9

theorem rhoOneCap_reduced_i3_coeff_twelve_core68
    (epsilon : k) (C F G : LaurentSeries k)
    (hC : (↑(7 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop) :
    (rhoOneCapReducedI3Series68 epsilon C F G).coeff 12 =
      4 * rhoOneI3CapTwelveReducedLaurentCore68 C F G +
        3 * epsilon * C.coeff 12 := by
  have hCG := laurent_coeff_mul_lower_six68 C G 7 (-1) hC hG
  have hFF := laurent_coeff_mul_lower_six68 F F 3 3 hF hF
  norm_num at hCG hFF
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have h4 : (4 : LaurentSeries k) = HahnSeries.C (4 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have h2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have h3e : (3 : LaurentSeries k) * HahnSeries.C epsilon =
      HahnSeries.C (3 * epsilon) := by
    have h3 : (3 : LaurentSeries k) = HahnSeries.C (3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h3, ← map_mul]
  have h4CG : ((4 : LaurentSeries k) * C * G).coeff 12 =
      4 * (C * G).coeff 12 := by
    rw [mul_assoc, h4, hscale]
  have h2FF : ((2 : LaurentSeries k) * F ^ 2).coeff 12 =
      2 * (F * F).coeff 12 := by
    rw [pow_two, h2, hscale]
  have h3eC : ((3 : LaurentSeries k) * HahnSeries.C epsilon * C).coeff 12 =
      3 * epsilon * C.coeff 12 := by
    rw [h3e, hscale]
  dsimp only [rhoOneCapReducedI3Series68]
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add, h4CG, hCG,
    h2FF, hFF, h3eC]
  dsimp only [rhoOneI3CapTwelveReducedLaurentCore68]
  ring

theorem rhoOneCap_reduced_i4_coeff_sixteen_core68
    (epsilon : k) (B C F G : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (↑(7 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop) :
    (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 16 =
      4 * rhoOneI4CapSixteenLaurentCore68 B C F G +
        3 * epsilon * B.coeff 16 := by
  have hBG := laurent_coeff_mul_lower_six68 B G 11 (-1) hB hG
  have hCF := laurent_coeff_mul_lower_six68 C F 7 3 hC hF
  norm_num at hBG hCF
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have h4 : (4 : LaurentSeries k) = HahnSeries.C (4 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have h3e : (3 : LaurentSeries k) * HahnSeries.C epsilon =
      HahnSeries.C (3 * epsilon) := by
    have h3 : (3 : LaurentSeries k) = HahnSeries.C (3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h3, ← map_mul]
  have h4BG : ((4 : LaurentSeries k) * B * G).coeff 16 =
      4 * (B * G).coeff 16 := by
    rw [mul_assoc, h4, hscale]
  have h4CF : ((4 : LaurentSeries k) * C * F).coeff 16 =
      4 * (C * F).coeff 16 := by
    rw [mul_assoc, h4, hscale]
  have h3eB : ((3 : LaurentSeries k) * HahnSeries.C epsilon * B).coeff 16 =
      3 * epsilon * B.coeff 16 := by
    rw [h3e, hscale]
  dsimp only [rhoOneCapReducedI4Series68]
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add, h4BG, hBG,
    h4CF, hCF, h3eB]
  dsimp only [rhoOneI4CapSixteenLaurentCore68]
  ring

theorem rhoOneCap_coordinate_defect_coeff_twenty_core68
    (B C F : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (↑(7 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop) :
    (rhoOneCapCoordinateDefectSeries68 B C F).coeff 20 =
      rhoOneCapCoordinateDefectT6LaurentCore68 B C F := by
  have hCC := laurent_coeff_mul_lower_six68 C C 7 7 hC hC
  have hBF := laurent_coeff_mul_lower_six68 B F 11 3 hB hF
  norm_num at hCC hBF
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have h2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have h2CC : ((2 : LaurentSeries k) * C ^ 2).coeff 20 =
      2 * (C * C).coeff 20 := by
    rw [pow_two, h2, hscale]
  dsimp only [rhoOneCapCoordinateDefectSeries68]
  rw [HahnSeries.coeff_sub, h2CC, hCC, hBF]
  dsimp only [rhoOneCapCoordinateDefectT6LaurentCore68]
  ring

end AlignedSquareTerminalGBoundaryCapPostRestorationT668

end Max11DegreeRoutes
