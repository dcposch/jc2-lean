import Sol68ScaleTwoAlignedSquareTerminalFourBoxBackwireScratch

/-! # Terminal split on the independent refined-G-zero B-gain child -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalBGain68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalBGainHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The earliest terminal coefficient in the independent B-gain child. -/
theorem rhoOneMainTangentTerminalFourHahn_coeff_negFive68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (0 : WithTop ℚ) ≤ F.orderTop)
    (hG : (0 : WithTop ℚ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (0 : WithTop ℚ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ)) :
    (rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG).coeff (-5 : ℚ) =
      (4 / 27 : k) * A.coeff (-2 : ℚ) ^ 2 * F.coeff (0 : ℚ) *
        (2 * C.coeff (0 : ℚ) + 3 * gamma) := by
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (-5 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (-5 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 (-5)
      h1 h2 h3 h4 h5 hlt
  have lead (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop) :=
    weightedMonomial68_coeff_at_general_lower_next s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
  have h1 := hz (-((2 / 3 : k) * gamma)) F dC A B C 1 1 0 0 0
    0 0 (-2) 2 0 hF hdC hA hB hC (by norm_num)
  have h2 := hz (-((1 / 3 : k) * epsilon)) F dA A B C 1 1 0 0 0
    0 (-3) (-2) 2 0 hF hdA hA hB hC (by norm_num)
  have h3 := hz (-(4 / 9 : k)) F G dA A B 1 1 1 0 0
    0 0 (-3) (-2) 2 hF hG hdA hA hB (by norm_num)
  have h4 := hz (-(4 / 9 : k)) F F dB A B 1 1 1 0 0
    0 0 0 (-2) 2 hF hF hdB hA hB (by norm_num)
  have h5 := hz (-(4 / 9 : k)) C F dC A B 1 1 1 0 0
    0 0 0 (-2) 2 hC hF hdC hA hB (by norm_num)
  have h6 := hz ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0
    2 0 (-2) 0 0 hB hdG hA hC hF (by norm_num)
  have h7 := hz (-(4 / 9 : k)) B F dF A C 1 1 1 0 0
    2 0 0 (-2) 0 hB hF hdF hA hC (by norm_num)
  have h8 := hz (4 / 9 : k) B C dG A F 1 1 1 0 0
    2 0 0 (-2) 0 hB hC hdG hA hF (by norm_num)
  have h9 := hz ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0
    2 0 (-3) (-2) 0 hB hC hdA hA hF (by norm_num)
  have h10 := hz (4 / 27 : k) B C C dA A 1 1 1 1 0
    2 0 0 (-3) (-2) hB hC hC hdA hA (by norm_num)
  have h11 := lead (-((2 / 9 : k) * gamma)) A F dA B C 1 1 1 0 0
    (-2) 0 (-3) 2 0 hA hF hdA hB hC
  have h12 := lead (-(4 / 27 : k)) A C F dA B 1 1 1 1 0
    (-2) 0 0 (-3) 2 hA hC hF hdA hB
  have h13 := hz (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0
    (-2) 2 (-3) 0 0 hA hB hdA hC hF (by norm_num)
  have h14 := hz (-(4 / 27 : k)) A B G dA C 1 1 1 1 0
    (-2) 2 0 (-3) 0 hA hB hG hdA hC (by norm_num)
  have h15 := hz (-(4 / 27 : k)) A B F dB C 1 1 1 1 0
    (-2) 2 0 0 0 hA hB hF hdB hC (by norm_num)
  have h16 := hz (-(4 / 27 : k)) A B B dF C 1 1 1 1 0
    (-2) 2 2 0 0 hA hB hB hdF hC (by norm_num)
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp only [rhoOneMainTangentTerminalFourHahn68, HahnSeries.coeff_add]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, hdAco]
  ring

end AlignedSquareTerminalBGain68

end Max11DegreeRoutes
