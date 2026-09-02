import Sol68ScaleTwoAlignedSquareTerminalBGainBackwireScratch

/-! # The terminal face on the upstream `G[-1] ≠ 0` residual -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGNonzero68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGNonzeroHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The order-minus-five terminal face remains unchanged when `G` has order
minus one.  The only new derivative requirement is `ord(dG) ≥ -2`. -/
theorem rhoOneMainTangentTerminalFourHahn_coeff_negFive_gBox68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (0 : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-2 : ℚ) : WithTop ℚ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ)) :
    (rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG).coeff (-5 : ℚ) =
      (4 / 27 : k) * A.coeff (-2 : ℚ) ^ 2 *
        (F.coeff (0 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * gamma) +
          2 * B.coeff (1 : ℚ) * G.coeff (-1 : ℚ)) := by
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
    0 0 (-2) 1 0 hF hdC hA hB hC (by norm_num)
  have h2 := hz (-((1 / 3 : k) * epsilon)) F dA A B C 1 1 0 0 0
    0 (-3) (-2) 1 0 hF hdA hA hB hC (by norm_num)
  have h3 := hz (-(4 / 9 : k)) F G dA A B 1 1 1 0 0
    0 (-1) (-3) (-2) 1 hF hG hdA hA hB (by norm_num)
  have h4 := hz (-(4 / 9 : k)) F F dB A B 1 1 1 0 0
    0 0 0 (-2) 1 hF hF hdB hA hB (by norm_num)
  have h5 := hz (-(4 / 9 : k)) C F dC A B 1 1 1 0 0
    0 0 0 (-2) 1 hC hF hdC hA hB (by norm_num)
  have h6 := hz ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0
    1 (-2) (-2) 0 0 hB hdG hA hC hF (by norm_num)
  have h7 := hz (-(4 / 9 : k)) B F dF A C 1 1 1 0 0
    1 0 0 (-2) 0 hB hF hdF hA hC (by norm_num)
  have h8 := hz (4 / 9 : k) B C dG A F 1 1 1 0 0
    1 0 (-2) (-2) 0 hB hC hdG hA hF (by norm_num)
  have h9 := hz ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0
    1 0 (-3) (-2) 0 hB hC hdA hA hF (by norm_num)
  have h10 := hz (4 / 27 : k) B C C dA A 1 1 1 1 0
    1 0 0 (-3) (-2) hB hC hC hdA hA (by norm_num)
  have h11 := lead (-((2 / 9 : k) * gamma)) A F dA B C 1 1 1 0 0
    (-2) 0 (-3) 1 0 hA hF hdA hB hC
  have h12 := lead (-(4 / 27 : k)) A C F dA B 1 1 1 1 0
    (-2) 0 0 (-3) 1 hA hC hF hdA hB
  have h13 := hz (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0
    (-2) 1 (-3) 0 0 hA hB hdA hC hF (by norm_num)
  have h14 := lead (-(4 / 27 : k)) A B G dA C 1 1 1 1 0
    (-2) 1 (-1) (-3) 0 hA hB hG hdA hC
  have h15 := hz (-(4 / 27 : k)) A B F dB C 1 1 1 1 0
    (-2) 1 0 0 0 hA hB hF hdB hC (by norm_num)
  have h16 := hz (-(4 / 27 : k)) A B B dF C 1 1 1 1 0
    (-2) 1 1 0 0 hA hB hB hdF hC (by norm_num)
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp only [rhoOneMainTangentTerminalFourHahn68, HahnSeries.coeff_add]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, hdAco]
  ring

/-- Combining the terminal face with the already-canonical `I₃` face
reduces the genuinely nonzero `G[-1]` sibling to a single quadratic scalar
wall. -/
theorem rhoOneDoubleZero_gNonzero_quadraticWall_of_terminal68
    (a b c f g gamma : k) (ha : a ≠ 0) (hg : g ≠ 0)
    (hterminal : f * (2 * c + 3 * gamma) + 2 * b * g = 0)
    (hi3 : rhoOneZeroLCubicDoubleZeroGZeroThree68
      gamma a b c f g = 0) :
    3 * (2 * c + 3 * gamma) ^ 2 + 4 * a * b ^ 2 = 0 := by
  have hgS : g *
      (3 * (2 * c + 3 * gamma) ^ 2 + 4 * a * b ^ 2) = 0 := by
    simp only [rhoOneZeroLCubicDoubleZeroGZeroThree68] at hi3
    calc
      g * (3 * (2 * c + 3 * gamma) ^ 2 + 4 * a * b ^ 2) =
          (2 * c + 3 * gamma) *
              (-2 * a * b * f + 3 * g * (2 * c + 3 * gamma)) -
            (-2 * a * b) *
              (f * (2 * c + 3 * gamma) + 2 * b * g) := by ring
      _ = 0 := by rw [hi3, hterminal]; ring
  exact (mul_eq_zero.mp hgS).resolve_left hg

end AlignedSquareTerminalGNonzero68

end Max11DegreeRoutes
