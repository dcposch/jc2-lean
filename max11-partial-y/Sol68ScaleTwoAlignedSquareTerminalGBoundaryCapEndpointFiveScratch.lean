import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapI4FifteenScratch

/-! # Endpoint T₅ from the three finite order gains -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapEndpointFive68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapEndpointFiveHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

/-- Six consecutive pure I₃ rows raise its reduced series from order six
to order twelve. -/
theorem laurent_orderTop_gain_six_to_twelve68
    (X : LaurentSeries k)
    (h6 : (↑(6 : ℤ) : WithTop ℤ) ≤ X.orderTop)
    (h6z : X.coeff 6 = 0) (h7z : X.coeff 7 = 0)
    (h8z : X.coeff 8 = 0) (h9z : X.coeff 9 = 0)
    (h10z : X.coeff 10 = 0) (h11z : X.coeff 11 = 0) :
    (↑(12 : ℤ) : WithTop ℤ) ≤ X.orderTop := by
  have h7 := laurent_orderTop_ge_succ_of_coeff_zero68 X 6 h6 h6z
  have h8 := laurent_orderTop_ge_succ_of_coeff_zero68 X 7 (by simpa using h7) h7z
  have h9 := laurent_orderTop_ge_succ_of_coeff_zero68 X 8 (by simpa using h8) h8z
  have h10 := laurent_orderTop_ge_succ_of_coeff_zero68 X 9 (by simpa using h9) h9z
  have h11 := laurent_orderTop_ge_succ_of_coeff_zero68 X 10 (by simpa using h10) h10z
  have h12 := laurent_orderTop_ge_succ_of_coeff_zero68 X 11 (by simpa using h11) h11z
  simpa using h12

/-- Six consecutive pure I₄ rows raise its reduced series from order ten
to order sixteen. -/
theorem laurent_orderTop_gain_ten_to_sixteen68
    (X : LaurentSeries k)
    (h10 : (↑(10 : ℤ) : WithTop ℤ) ≤ X.orderTop)
    (h10z : X.coeff 10 = 0) (h11z : X.coeff 11 = 0)
    (h12z : X.coeff 12 = 0) (h13z : X.coeff 13 = 0)
    (h14z : X.coeff 14 = 0) (h15z : X.coeff 15 = 0) :
    (↑(16 : ℤ) : WithTop ℤ) ≤ X.orderTop := by
  have h11 := laurent_orderTop_ge_succ_of_coeff_zero68 X 10 h10 h10z
  have h12 := laurent_orderTop_ge_succ_of_coeff_zero68 X 11 (by simpa using h11) h11z
  have h13 := laurent_orderTop_ge_succ_of_coeff_zero68 X 12 (by simpa using h12) h12z
  have h14 := laurent_orderTop_ge_succ_of_coeff_zero68 X 13 (by simpa using h13) h13z
  have h15 := laurent_orderTop_ge_succ_of_coeff_zero68 X 14 (by simpa using h14) h14z
  have h16 := laurent_orderTop_ge_succ_of_coeff_zero68 X 15 (by simpa using h15) h15z
  simpa using h16

/-- T₀ through T₄ raise the coordinate defect from order fourteen to
order nineteen. -/
theorem laurent_orderTop_gain_fourteen_to_nineteen68
    (X : LaurentSeries k)
    (h14 : (↑(14 : ℤ) : WithTop ℤ) ≤ X.orderTop)
    (h14z : X.coeff 14 = 0) (h15z : X.coeff 15 = 0)
    (h16z : X.coeff 16 = 0) (h17z : X.coeff 17 = 0)
    (h18z : X.coeff 18 = 0) :
    (↑(19 : ℤ) : WithTop ℤ) ≤ X.orderTop := by
  have h15 := laurent_orderTop_ge_succ_of_coeff_zero68 X 14 h14 h14z
  have h16 := laurent_orderTop_ge_succ_of_coeff_zero68 X 15 (by simpa using h15) h15z
  have h17 := laurent_orderTop_ge_succ_of_coeff_zero68 X 16 (by simpa using h16) h16z
  have h18 := laurent_orderTop_ge_succ_of_coeff_zero68 X 17 (by simpa using h17) h17z
  have h19 := laurent_orderTop_ge_succ_of_coeff_zero68 X 18 (by simpa using h18) h18z
  simpa using h19

/-- The verified convolution endpoint applied after the three gains. -/
theorem rhoOneCap_endpoint_five_of_three_gains68
    (epsilon : k) (B C F G : LaurentSeries k)
    (hB : (↑(11 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (↑(7 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hf3 : F.coeff 3 ≠ 0)
    (hR3base : (↑(6 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI3Series68 epsilon C F G).orderTop)
    (hR36 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 6 = 0)
    (hR37 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 7 = 0)
    (hR38 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 8 = 0)
    (hR39 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 9 = 0)
    (hR310 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 10 = 0)
    (hR311 : (rhoOneCapReducedI3Series68 epsilon C F G).coeff 11 = 0)
    (hR4base : (↑(10 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapReducedI4Series68 epsilon B C F G).orderTop)
    (hR410 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 10 = 0)
    (hR411 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 11 = 0)
    (hR412 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 12 = 0)
    (hR413 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 13 = 0)
    (hR414 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 14 = 0)
    (hR415 : (rhoOneCapReducedI4Series68 epsilon B C F G).coeff 15 = 0)
    (hHbase : (↑(14 : ℤ) : WithTop ℤ) ≤
      (rhoOneCapCoordinateDefectSeries68 B C F).orderTop)
    (hH14 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 14 = 0)
    (hH15 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 15 = 0)
    (hH16 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 16 = 0)
    (hH17 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 17 = 0)
    (hH18 : (rhoOneCapCoordinateDefectSeries68 B C F).coeff 18 = 0) :
    (rhoOneCapCoordinateDefectSeries68 B C F).coeff 19 = 0 := by
  have hR3 := laurent_orderTop_gain_six_to_twelve68
    _ hR3base hR36 hR37 hR38 hR39 hR310 hR311
  have hR4 := laurent_orderTop_gain_ten_to_sixteen68
    _ hR4base hR410 hR411 hR412 hR413 hR414 hR415
  have hH := laurent_orderTop_gain_fourteen_to_nineteen68
    _ hHbase hH14 hH15 hH16 hH17 hH18
  exact rhoOneCap_coordinate_defect_endpoint_five68 epsilon B C F G
    hB hC hF hR3 hR4 hH hf3

/-- Scalar form of T₅, retained in the source packet. -/
def rhoOneCapCoordinateDefectT5Core68
    (B C F : HahnSeries ℚ k) : k :=
  4 * C.coeff 7 * C.coeff 12 + 4 * C.coeff 8 * C.coeff 11 +
    4 * C.coeff 9 * C.coeff 10 - B.coeff 16 * F.coeff 3 -
    B.coeff 15 * F.coeff 4 - B.coeff 14 * F.coeff 5 -
    B.coeff 13 * F.coeff 6 - B.coeff 12 * F.coeff 7 -
    B.coeff 11 * F.coeff 8

def RhoOneDoubleZeroTerminalGBoundaryCapEndpointFivePacket68
    (gamma epsilon i3 sold cs source0 source1 source2 : k)
    (A B C F G dA : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapI4FifteenPacket68
      gamma epsilon i3 sold cs source0 source1 source2 A B C F G dA ∧
    rhoOneCapCoordinateDefectT5Core68 B C F = 0

/-- I₃[12] is the first non-pure successor: the restored `A B F` face has
coefficient `A[-2] B[11] F[3]` and cannot be omitted. -/
def rhoOneI3CapTwelveRestoredCore68
    (A B C F G : HahnSeries ℚ k) : k :=
  -(4 / 3 : k) * A.coeff (-2 : ℚ) * B.coeff 11 * F.coeff 3 +
    4 * (C.coeff 7 * G.coeff 5 + C.coeff 8 * G.coeff 4 +
      C.coeff 9 * G.coeff 3 + C.coeff 10 * G.coeff 2 +
      C.coeff 11 * G.coeff 1 + C.coeff 12 * G.coeff 0 +
      C.coeff 13 * G.coeff (-1 : ℚ) + F.coeff 3 * F.coeff 9 +
      F.coeff 4 * F.coeff 8 + F.coeff 5 * F.coeff 7 +
      (1 / 2 : k) * F.coeff 6 ^ 2)

def RhoOneDoubleZeroTerminalGBoundaryCapI3TwelveRestoredTarget68
    (epsilon : k) (A B C F G : HahnSeries ℚ k) : Prop :=
  rhoOneI3CapTwelveRestoredCore68 A B C F G +
    3 * epsilon * C.coeff 12 = 0

theorem rhoOneCap_i3_twelve_restores_abf68 :
    (-2 : ℤ) + 11 + 3 = 12 ∧
      (-(4 / 3 : k) : k) ≠ 0 := by
  constructor
  · norm_num
  · norm_num

end AlignedSquareTerminalGBoundaryCapEndpointFive68

end Max11DegreeRoutes
