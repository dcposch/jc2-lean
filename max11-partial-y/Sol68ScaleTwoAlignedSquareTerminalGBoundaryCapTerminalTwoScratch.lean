import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapTerminalOneScratch

/-! # Terminal coefficient two above the nonzero cap -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapTerminalTwo68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapTerminalTwoHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The third integral jet above the lower face of a Laurent product. -/
theorem laurent_coeff_mul_lower_three68
    (X Y : LaurentSeries k) (m n : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
    (X * Y).coeff (m + n + 3) =
      X.coeff m * Y.coeff (n + 3) +
        X.coeff (m + 1) * Y.coeff (n + 2) +
          X.coeff (m + 2) * Y.coeff (n + 1) +
            X.coeff (m + 3) * Y.coeff n := by
  let Xt : LaurentSeries k := X - HahnSeries.single m (X.coeff m)
  have hsm : (↑m : WithTop ℤ) ≤
      (HahnSeries.single m (X.coeff m) : LaurentSeries k).orderTop := by
    by_cases hx : X.coeff m = 0
    · simp [hx]
    · rw [HahnSeries.orderTop_single hx]
  have hXt0 : Xt.coeff m = 0 := by simp [Xt]
  have hXtBase : (↑m : WithTop ℤ) ≤ Xt.orderTop := by
    exact le_trans (by simpa using min_le_min hX hsm)
      HahnSeries.min_orderTop_le_orderTop_sub
  have hXt := laurent_orderTop_ge_succ_of_coeff_zero68 Xt m hXtBase hXt0
  have htail := laurent_coeff_mul_lower_two68 Xt Y (m + 1) n hXt hY
  have htail' : (Xt * Y).coeff (m + n + 3) =
      Xt.coeff (m + 1) * Y.coeff (n + 2) +
        Xt.coeff (m + 2) * Y.coeff (n + 1) +
          Xt.coeff (m + 3) * Y.coeff n := by
    convert htail using 1 <;> ring
  have hXt1 : Xt.coeff (m + 1) = X.coeff (m + 1) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt2 : Xt.coeff (m + 2) = X.coeff (m + 2) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt3 : Xt.coeff (m + 3) = X.coeff (m + 3) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hlead :
      ((HahnSeries.single m (X.coeff m) : LaurentSeries k) * Y).coeff
          (m + n + 3) = X.coeff m * Y.coeff (n + 3) := by
    rw [HahnSeries.coeff_single_mul]
    have hi : m + n + 3 - m = n + 3 := by omega
    rw [hi]
  have hXdec : X = HahnSeries.single m (X.coeff m) + Xt := by simp [Xt]
  calc
    (X * Y).coeff (m + n + 3) =
        ((HahnSeries.single m (X.coeff m) + Xt) * Y).coeff
          (m + n + 3) := by rw [← hXdec]
    _ = _ := by
      rw [add_mul, HahnSeries.coeff_add, hlead, htail', hXt1, hXt2, hXt3]
      ring

/-- Coefficient three above the lower face of a Laurent triple product. -/
theorem laurent_coeff_mul_three_lower_three68
    (X Y Z : LaurentSeries k) (m n r : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
    (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop) :
    (X * Y * Z).coeff (m + n + r + 3) =
      X.coeff m * Y.coeff n * Z.coeff (r + 3) +
      X.coeff m * Y.coeff (n + 1) * Z.coeff (r + 2) +
      X.coeff (m + 1) * Y.coeff n * Z.coeff (r + 2) +
      X.coeff m * Y.coeff (n + 2) * Z.coeff (r + 1) +
      X.coeff (m + 1) * Y.coeff (n + 1) * Z.coeff (r + 1) +
      X.coeff (m + 2) * Y.coeff n * Z.coeff (r + 1) +
      X.coeff m * Y.coeff (n + 3) * Z.coeff r +
      X.coeff (m + 1) * Y.coeff (n + 2) * Z.coeff r +
      X.coeff (m + 2) * Y.coeff (n + 1) * Z.coeff r +
      X.coeff (m + 3) * Y.coeff n * Z.coeff r := by
  have hXY : (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
    le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  have houter := laurent_coeff_mul_lower_three68 (X * Y) Z (m + n) r hXY hZ
  have hzero := laurent_coeff_mul_lower68 X Y m n hX hY
  have hone := laurent_coeff_mul_lower_succ68 X Y m n hX hY
  have htwo := laurent_coeff_mul_lower_two68 X Y m n hX hY
  have hthree := laurent_coeff_mul_lower_three68 X Y m n hX hY
  rw [hzero, hone, htwo, hthree] at houter
  convert houter using 1 <;> ring

/-- Integral support gives coefficient two of `F dA`. -/
theorem rhoOneTerminal_cap_FdA_two68
    (root : k) (F dA : RatFunc k)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root dA).orderTop) :
    ((ratFuncAtHahn46 root F) * (ratFuncAtHahn46 root dA)).coeff 2 =
      (ratFuncAtHahn46 root F).coeff 3 *
          (ratFuncAtHahn46 root dA).coeff (-1 : ℚ) +
        (ratFuncAtHahn46 root F).coeff 4 *
          (ratFuncAtHahn46 root dA).coeff (-2 : ℚ) +
        (ratFuncAtHahn46 root F).coeff 5 *
          (ratFuncAtHahn46 root dA).coeff (-3 : ℚ) := by
  let FL := ratFuncAtLaurent46 root F
  let dAL := ratFuncAtLaurent46 root dA
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 3 hF
  have hdAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root dA (-3) hdA
  have h := laurent_coeff_mul_lower_two68 FL dAL 3 (-3) hFL hdAL
  norm_num at h
  have hp := ratFuncAtHahn46_coeff_int68 root (F * dA) 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hF5 := ratFuncAtHahn46_coeff_int68 root F 5
  have hd1 := ratFuncAtHahn46_coeff_int68 root dA (-1)
  have hd2 := ratFuncAtHahn46_coeff_int68 root dA (-2)
  have hd3 := ratFuncAtHahn46_coeff_int68 root dA (-3)
  norm_num at hp hF3 hF4 hF5 hd1 hd2 hd3
  dsimp only [FL, dAL] at h
  rw [← hF3, ← hF4, ← hF5, ← hd1, ← hd2, ← hd3] at h
  rw [hp]
  convert h using 1 <;> ring

/-- Integral support gives coefficient two of `F G dA`. -/
theorem rhoOneTerminal_cap_FGdA_three68
    (root : k) (F G dA : RatFunc k)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root dA).orderTop) :
    ((ratFuncAtHahn46 root F) * (ratFuncAtHahn46 root G) *
      (ratFuncAtHahn46 root dA)).coeff 2 =
      (ratFuncAtHahn46 root F).coeff 3 * (ratFuncAtHahn46 root G).coeff (-1 : ℚ) *
          (ratFuncAtHahn46 root dA).coeff 0 +
      (ratFuncAtHahn46 root F).coeff 3 * (ratFuncAtHahn46 root G).coeff 0 *
          (ratFuncAtHahn46 root dA).coeff (-1 : ℚ) +
      (ratFuncAtHahn46 root F).coeff 4 * (ratFuncAtHahn46 root G).coeff (-1 : ℚ) *
          (ratFuncAtHahn46 root dA).coeff (-1 : ℚ) +
      (ratFuncAtHahn46 root F).coeff 3 * (ratFuncAtHahn46 root G).coeff 1 *
          (ratFuncAtHahn46 root dA).coeff (-2 : ℚ) +
      (ratFuncAtHahn46 root F).coeff 4 * (ratFuncAtHahn46 root G).coeff 0 *
          (ratFuncAtHahn46 root dA).coeff (-2 : ℚ) +
      (ratFuncAtHahn46 root F).coeff 5 * (ratFuncAtHahn46 root G).coeff (-1 : ℚ) *
          (ratFuncAtHahn46 root dA).coeff (-2 : ℚ) +
      (ratFuncAtHahn46 root F).coeff 3 * (ratFuncAtHahn46 root G).coeff 2 *
          (ratFuncAtHahn46 root dA).coeff (-3 : ℚ) +
      (ratFuncAtHahn46 root F).coeff 4 * (ratFuncAtHahn46 root G).coeff 1 *
          (ratFuncAtHahn46 root dA).coeff (-3 : ℚ) +
      (ratFuncAtHahn46 root F).coeff 5 * (ratFuncAtHahn46 root G).coeff 0 *
          (ratFuncAtHahn46 root dA).coeff (-3 : ℚ) +
      (ratFuncAtHahn46 root F).coeff 6 * (ratFuncAtHahn46 root G).coeff (-1 : ℚ) *
          (ratFuncAtHahn46 root dA).coeff (-3 : ℚ) := by
  let FL := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let dAL := ratFuncAtLaurent46 root dA
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 3 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-1) hG
  have hdAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root dA (-3) hdA
  have h := laurent_coeff_mul_three_lower_three68 FL Gser dAL 3 (-1) (-3)
    hFL hGL hdAL
  norm_num at h
  have hp := ratFuncAtHahn46_coeff_int68 root (F * G * dA) 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hF5 := ratFuncAtHahn46_coeff_int68 root F 5
  have hF6 := ratFuncAtHahn46_coeff_int68 root F 6
  have hGm1 := ratFuncAtHahn46_coeff_int68 root G (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  have hG2 := ratFuncAtHahn46_coeff_int68 root G 2
  have hd0 := ratFuncAtHahn46_coeff_int68 root dA 0
  have hd1 := ratFuncAtHahn46_coeff_int68 root dA (-1)
  have hd2 := ratFuncAtHahn46_coeff_int68 root dA (-2)
  have hd3 := ratFuncAtHahn46_coeff_int68 root dA (-3)
  norm_num at hp hF3 hF4 hF5 hF6 hGm1 hG0 hG1 hG2 hd0 hd1 hd2 hd3
  dsimp only [FL, Gser, dAL] at h
  rw [← hF3, ← hF4, ← hF5, ← hF6, ← hGm1, ← hG0,
    ← hG1, ← hG2, ← hd0, ← hd1, ← hd2, ← hd3] at h
  rw [hp]
  convert h using 1 <;> ring

end AlignedSquareTerminalGBoundaryCapTerminalTwo68

end Max11DegreeRoutes
namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapTerminalTwoSource68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapTerminalTwoSourceHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- At coefficient two, only `epsilon F dA` and `F G dA` meet the cap. -/
theorem rhoOneMainTangentTerminalFourHahn_coeff_two_cap68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(11 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑(7 : ℚ) : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-2 : ℚ) : WithTop ℚ) ≤ dG.orderTop)
    (hFdA :
      (weightedMonomial68 (-((1 / 3 : k) * epsilon))
        F dA A B C 1 1 0 0 0).coeff 2 =
        (-((1 / 3 : k) * epsilon)) *
          (F.coeff 3 * dA.coeff (-1 : ℚ) +
           F.coeff 4 * dA.coeff (-2 : ℚ) +
           F.coeff 5 * dA.coeff (-3 : ℚ)))
    (hFGdA :
      (weightedMonomial68 (-(4 / 9 : k)) F G dA A B 1 1 1 0 0).coeff 2 =
        (-(4 / 9 : k)) *
          (F.coeff 3 * G.coeff (-1 : ℚ) * dA.coeff 0 +
           F.coeff 3 * G.coeff 0 * dA.coeff (-1 : ℚ) +
           F.coeff 4 * G.coeff (-1 : ℚ) * dA.coeff (-1 : ℚ) +
           F.coeff 3 * G.coeff 1 * dA.coeff (-2 : ℚ) +
           F.coeff 4 * G.coeff 0 * dA.coeff (-2 : ℚ) +
           F.coeff 5 * G.coeff (-1 : ℚ) * dA.coeff (-2 : ℚ) +
           F.coeff 3 * G.coeff 2 * dA.coeff (-3 : ℚ) +
           F.coeff 4 * G.coeff 1 * dA.coeff (-3 : ℚ) +
           F.coeff 5 * G.coeff 0 * dA.coeff (-3 : ℚ) +
           F.coeff 6 * G.coeff (-1 : ℚ) * dA.coeff (-3 : ℚ))) :
    (rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG).coeff 2 =
      (-((1 / 3 : k) * epsilon)) *
          (F.coeff 3 * dA.coeff (-1 : ℚ) +
           F.coeff 4 * dA.coeff (-2 : ℚ) +
           F.coeff 5 * dA.coeff (-3 : ℚ)) +
      (-(4 / 9 : k)) *
          (F.coeff 3 * G.coeff (-1 : ℚ) * dA.coeff 0 +
           F.coeff 3 * G.coeff 0 * dA.coeff (-1 : ℚ) +
           F.coeff 4 * G.coeff (-1 : ℚ) * dA.coeff (-1 : ℚ) +
           F.coeff 3 * G.coeff 1 * dA.coeff (-2 : ℚ) +
           F.coeff 4 * G.coeff 0 * dA.coeff (-2 : ℚ) +
           F.coeff 5 * G.coeff (-1 : ℚ) * dA.coeff (-2 : ℚ) +
           F.coeff 3 * G.coeff 2 * dA.coeff (-3 : ℚ) +
           F.coeff 4 * G.coeff 1 * dA.coeff (-3 : ℚ) +
           F.coeff 5 * G.coeff 0 * dA.coeff (-3 : ℚ) +
           F.coeff 6 * G.coeff (-1 : ℚ) * dA.coeff (-3 : ℚ)) := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hS' : (↑(7 : ℚ) : WithTop ℚ) ≤ S.orderTop := by simpa only [S] using hS
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (2 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5 n1 n2 n3 n4 n5).coeff 2 = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 2 h1 h2 h3 h4 h5 hlt
  have h1 := hz (-((2 / 3 : k) * gamma)) F dC A B C 1 1 0 0 0
    3 0 (-2) 11 0 hF hdC hA hB hC (by norm_num)
  have h4 := hz (-(4 / 9 : k)) F F dB A B 1 1 1 0 0
    3 3 0 (-2) 11 hF hF hdB hA hB (by norm_num)
  have h5 := hz (-(4 / 9 : k)) C F dC A B 1 1 1 0 0
    0 3 0 (-2) 11 hC hF hdC hA hB (by norm_num)
  have h6 := hz ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0
    11 (-2) (-2) 0 3 hB hdG hA hC hF (by norm_num)
  have h7 := hz (-(4 / 9 : k)) B F dF A C 1 1 1 0 0
    11 3 0 (-2) 0 hB hF hdF hA hC (by norm_num)
  have h8 := hz (4 / 9 : k) B C dG A F 1 1 1 0 0
    11 0 (-2) (-2) 3 hB hC hdG hA hF (by norm_num)
  have h9 := hz ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0
    11 0 (-3) (-2) 3 hB hC hdA hA hF (by norm_num)
  have h10 := hz (4 / 27 : k) B C C dA A 1 1 1 1 0
    11 0 0 (-3) (-2) hB hC hC hdA hA (by norm_num)
  have h11 := hz (-(2 / 27 : k)) A F dA S B 1 1 1 1 0
    (-2) 3 (-3) 7 11 hA hF hdA hS' hB (by norm_num)
  have h13 := hz (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0
    (-2) 11 (-3) 0 3 hA hB hdA hC hF (by norm_num)
  have h14 := hz (-(4 / 27 : k)) A B G dA C 1 1 1 1 0
    (-2) 11 (-1) (-3) 0 hA hB hG hdA hC (by norm_num)
  have h15 := hz (-(4 / 27 : k)) A B F dB C 1 1 1 1 0
    (-2) 11 3 0 0 hA hB hF hdB hC (by norm_num)
  have h16 := hz (-(4 / 27 : k)) A B B dF C 1 1 1 1 0
    (-2) 11 11 0 0 hA hB hB hdF hC (by norm_num)
  have hrewrite : rhoOneMainTangentTerminalFourHahn68 gamma epsilon
      A B C F G dA dB dC dF dG =
      weightedMonomial68 (-((2 / 3 : k) * gamma)) F dC A B C 1 1 0 0 0 +
      weightedMonomial68 (-((1 / 3 : k) * epsilon)) F dA A B C 1 1 0 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) F G dA A B 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) F F dB A B 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) C F dC A B 1 1 1 0 0 +
      weightedMonomial68 ((2 / 3 : k) * gamma) B dG A C F 1 1 0 0 0 +
      weightedMonomial68 (-(4 / 9 : k)) B F dF A C 1 1 1 0 0 +
      weightedMonomial68 (4 / 9 : k) B C dG A F 1 1 1 0 0 +
      weightedMonomial68 ((2 / 9 : k) * gamma) B C dA A F 1 1 1 0 0 +
      weightedMonomial68 (4 / 27 : k) B C C dA A 1 1 1 1 0 +
      weightedMonomial68 (-(2 / 27 : k)) A F dA S B 1 1 1 1 0 +
      weightedMonomial68 (-((1 / 9 : k) * epsilon)) A B dA C F 1 1 1 0 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B G dA C 1 1 1 1 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B F dB C 1 1 1 1 0 +
      weightedMonomial68 (-(4 / 27 : k)) A B B dF C 1 1 1 1 0 := by
    simp only [rhoOneMainTangentTerminalFourHahn68, S, weightedMonomial68,
      pow_zero, pow_one, mul_one, map_add, map_mul, map_neg, map_div₀,
      map_ofNat, map_one]
    ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add]
  rw [h1, hFdA, hFGdA, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14,
    h15, h16]
  ring

/-- Coefficient two of an embedded translated polynomial is its second
derivative divided by two. -/
theorem ratFuncAtHahn46_algebraMap_coeff_two68 (a : k) (p : k[X]) :
    (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) p)).coeff 2 =
      (1 / 2 : k) * p.derivative.derivative.eval a := by
  rw [ratFuncAtHahn46_algebraMap]
  rw [Polynomial.algebraMap_hahnSeries_apply]
  change (HahnSeries.ofPowerSeries ℚ k
      (↑(p.comp (X + C a)) : PowerSeries k)).coeff
        (↑(2 : ℕ) : ℚ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff, Polynomial.coeff_coe]
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff]
  have hfun := congrFun (Polynomial.factorial_smul_hasseDeriv (R := k) (k := 2)) p
  have heval := congrArg (fun q : k[X] => q.eval a) hfun
  norm_num [Function.iterate_succ_apply] at heval
  linear_combination (1 / 2 : k) * heval

/-- The third cleared-coordinate derivative coefficient, kept factored by
the actual local scale. -/
theorem localHahn_deriv_coeff_third_of_cleared_two68
    (a c : k) (h0 A0 : k[X]) (A : RatFunc k)
    (hsingle : ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0) =
      HahnSeries.single (1 : ℚ) c)
    (hderiv : ratFuncAtHahn46 a
      (Differential.deriv (algebraMap k[X] (RatFunc k) h0)) = HahnSeries.C c)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ 2 * A) :
    A0.derivative.derivative.derivative.eval a =
      2 * c ^ 2 * (ratFuncAtHahn46 a (Differential.deriv A)).coeff 0 +
      4 * c ^ 2 * (ratFuncAtHahn46 a A).coeff 1 := by
  have hdclear := congrArg Differential.deriv hclear
  rw [GCD369RatFuncDerivative] at hdclear
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hdclear
  have hmapped := congrArg (ratFuncAtHahn46 a) hdclear
  simp only [map_add, map_mul, map_pow, map_natCast, hsingle, hderiv] at hmapped
  norm_num [HahnSeries.C_apply, HahnSeries.single_mul_single, pow_two] at hmapped
  have htwoSingle :
      (2 : HahnSeries ℚ k) * HahnSeries.single (1 : ℚ) (c * c) =
        HahnSeries.single (1 : ℚ) (2 * c ^ 2) := by
    rw [two_mul, ← HahnSeries.single_add]
    congr 1
    ring
  rw [htwoSingle] at hmapped
  have hcoeff := congrArg (fun x : HahnSeries ℚ k => x.coeff (2 : ℚ)) hmapped
  rw [ratFuncAtHahn46_algebraMap_coeff_two68, HahnSeries.coeff_add] at hcoeff
  simp only [HahnSeries.coeff_single_mul, HahnSeries.coeff_mul_single] at hcoeff
  norm_num at hcoeff
  linear_combination 2 * hcoeff

/-- All three cleared-source derivatives substituted into terminal
coefficient two, with no division by the local scale. -/
theorem rhoOneTerminal_cap_two_cleared_source68
    (s source0 source1 source2 am a0 a1 f f' f'' f''' g g' g'' g'''
      d3 d2 d1 d0 epsilon : k)
    (hterminal : 3 * epsilon * (f * d1 + f' * d2 + f'' * d3) +
      4 * (f * g * d0 + (f * g' + f' * g) * d1 +
        (f * g'' + f' * g' + f'' * g) * d2 +
        (f * g''' + f' * g'' + f'' * g' + f''' * g) * d3) = 0)
    (hsource0 : source0 = s ^ 2 * d2 + 2 * s ^ 2 * am)
    (hsource1 : source1 = s ^ 2 * d1 + 2 * s ^ 2 * a0)
    (hsource2 : source2 = 2 * s ^ 2 * d0 + 4 * s ^ 2 * a1) :
    6 * epsilon * (f * (source1 - 2 * s ^ 2 * a0) +
        f' * (source0 - 2 * s ^ 2 * am) + s ^ 2 * f'' * d3) +
      4 * f * g * (source2 - 4 * s ^ 2 * a1) +
      8 * ((f * g' + f' * g) * (source1 - 2 * s ^ 2 * a0) +
        (f * g'' + f' * g' + f'' * g) * (source0 - 2 * s ^ 2 * am) +
        s ^ 2 * (f * g''' + f' * g'' + f'' * g' + f''' * g) * d3) = 0 := by
  linear_combination 2 * s ^ 2 * hterminal +
    (6 * epsilon * f' + 8 * (f * g'' + f' * g' + f'' * g)) * hsource0 +
    (6 * epsilon * f + 8 * (f * g' + f' * g)) * hsource1 +
    4 * f * g * hsource2

end AlignedSquareTerminalGBoundaryCapTerminalTwoSource68

end Max11DegreeRoutes
namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapTerminalTwoBackwire68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapTerminalTwoBackwireHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The coefficient-two packet keeps the full coefficient-one packet at the
same actual scale and adds the third cleared derivative. -/
def RhoOneDoubleZeroTerminalGBoundaryCapTerminalTwoPacket68
    (gamma epsilon i3 sold cs source0 source1 source2 : k)
    (A B C F G dA : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapTerminalOnePacket68
      gamma epsilon i3 sold cs source0 source1 A B C F G dA ∧
    source2 = 2 * cs ^ 2 * dA.coeff 0 + 4 * cs ^ 2 * A.coeff 1 ∧
    3 * epsilon * (F.coeff 3 * dA.coeff (-1 : ℚ) +
        F.coeff 4 * dA.coeff (-2 : ℚ) + F.coeff 5 * dA.coeff (-3 : ℚ)) +
      4 * (F.coeff 3 * G.coeff (-1 : ℚ) * dA.coeff 0 +
        (F.coeff 3 * G.coeff 0 + F.coeff 4 * G.coeff (-1 : ℚ)) * dA.coeff (-1 : ℚ) +
        (F.coeff 3 * G.coeff 1 + F.coeff 4 * G.coeff 0 +
          F.coeff 5 * G.coeff (-1 : ℚ)) * dA.coeff (-2 : ℚ) +
        (F.coeff 3 * G.coeff 2 + F.coeff 4 * G.coeff 1 +
          F.coeff 5 * G.coeff 0 + F.coeff 6 * G.coeff (-1 : ℚ)) *
            dA.coeff (-3 : ℚ)) = 0 ∧
    6 * epsilon *
        (F.coeff 3 * (source1 - 2 * cs ^ 2 * A.coeff 0) +
          F.coeff 4 * (source0 - 2 * cs ^ 2 * A.coeff (-1 : ℚ)) +
          cs ^ 2 * F.coeff 5 * dA.coeff (-3 : ℚ)) +
      4 * F.coeff 3 * G.coeff (-1 : ℚ) *
          (source2 - 4 * cs ^ 2 * A.coeff 1) +
      8 * ((F.coeff 3 * G.coeff 0 + F.coeff 4 * G.coeff (-1 : ℚ)) *
            (source1 - 2 * cs ^ 2 * A.coeff 0) +
        (F.coeff 3 * G.coeff 1 + F.coeff 4 * G.coeff 0 +
          F.coeff 5 * G.coeff (-1 : ℚ)) *
            (source0 - 2 * cs ^ 2 * A.coeff (-1 : ℚ)) +
        cs ^ 2 * (F.coeff 3 * G.coeff 2 + F.coeff 4 * G.coeff 1 +
          F.coeff 5 * G.coeff 0 + F.coeff 6 * G.coeff (-1 : ℚ)) *
            dA.coeff (-3 : ℚ)) = 0

def RhoOneDoubleZeroTerminalGBoundaryCapTerminalTwoResidual68
    (root j gamma epsilon : k) (A0 : k[X])
    (h0R AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapTerminalOneResidual68
      root j gamma epsilon A0 h0R AR BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧ 2 * C.coeff 0 + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 sold cs : k,
        RhoOneDoubleZeroTerminalGBoundaryCapTerminalTwoPacket68
          gamma epsilon i3 sold cs (A0.derivative.eval root)
            (A0.derivative.derivative.eval root)
            (A0.derivative.derivative.derivative.eval root)
            A B C F G (ratFuncAtHahn46 root (Differential.deriv AR)))

/-- Literal source backwire of terminal coefficient two and the third
cleared-source derivative coefficient. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapTerminalTwoResidual
    [IsAlgClosed k]
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let AR : RatFunc k := T.source.A
    let BR : RatFunc k := T.source.B
    let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
    let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
    let GR : RatFunc k :=
      (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
        RatFunc.C (1 / 3 : k) * AR * CR
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroTerminalGBoundaryCapTerminalTwoResidual68
        T.root j T.source.gamma T.source.epsilon (localClearedA68RhoOne g u)
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapTerminalTwoResidual68]
  have hprevRaw :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapTerminalOneResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprevRaw with hprev | htail
  · left
    refine ⟨hprev, ?_⟩
    intro hcoord hc1 hc2
    obtain ⟨i3, sold, cold, hold⟩ := hprev.2 hcoord hc1 hc2
    have hold' := hold
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapTerminalOnePacket68] at hold'
    rcases hold' with ⟨hbase, _, _, _, hterminal1, _⟩
    have hci3 := hbase.1.1.1.1.1
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68] at hci3
    rcases hci3 with
      ⟨hi3H, hc3, hc4, hc5, hc6, hb7, hb8, hb9, hb10,
        hS7, hB11, hcap3, hc7ne, hcap4, hb11ne, hBexact⟩
    have hi4res := hprev.1
    have hfinite := hi4res.1.1.1.1.1.1.1.1
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68] at hfinite
    rcases hfinite with ⟨hfact, hboundary | hrays⟩
    · rcases hboundary with ⟨hcurrent, hf2, hF3, hb4, hB5,
        hi4three, hf3ne⟩
      obtain ⟨cs, t, v, z, hcs, hsingle, ht, hv, hzdef, hz, hvcore,
        htcore⟩ := P.1
      let AR : RatFunc k := T.source.A
      let BR : RatFunc k := T.source.B
      let C0R : RatFunc k := T.source.C0
      let DR : RatFunc k := T.source.D
      let E0R : RatFunc k := T.source.E
      let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
      let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
      let FR : RatFunc k := DR - RatFunc.C (1 / 3 : k) * AR * BR
      let GR : RatFunc k := ER - RatFunc.C (1 / 3 : k) * AR * CR
      let A0 : k[X] := localClearedA68RhoOne g u
      have hAclear := (T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero
        hH hp6 hp5 hp4).1
      change algebraMap k[X] (RatFunc k) A0 =
        (algebraMap k[X] (RatFunc k) h0) ^ 2 * AR at hAclear
      obtain ⟨cs', hcs', hsingle', hderiv'⟩ :=
        ratFuncAtHahn68_linearRoot_single_deriv
          h0 T.root T.scale_degree T.root_eq
      have hcsEq : cs' = cs := by
        have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff (1 : ℚ))
          (hsingle'.symm.trans hsingle)
        simpa only [HahnSeries.coeff_single_same] using heq
      subst cs'
      have hsource0 := localHahn_deriv_coeff_next_of_cleared_two68
        T.root cs h0 A0 AR hcs hsingle hderiv' hAclear
      have hsource1 := localHahn_deriv_coeff_second_of_cleared_two68
        T.root cs h0 A0 AR hsingle hderiv' hAclear
      have hsource2 := localHahn_deriv_coeff_third_of_cleared_two68
        T.root cs h0 A0 AR hsingle hderiv' hAclear
      have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
        have hx := GCD369RatFuncDerivative (C x : k[X])
        simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
      have hlow := constantBracket_integrated68_lowerSystem
        ratFuncDerivation68 (RatFunc.C 0) T.source.A T.source.B
        T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
        (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
        (RatFunc.C T.source.zeta) (RatFunc.C T.source.eta)
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
        (hconst 0) (hconst T.source.alpha) (hconst T.source.beta)
        (hconst T.source.gamma) (hconst T.source.delta)
        (hconst T.source.epsilon) (hconst T.source.zeta)
        (hconst T.source.eta) T.source.bracket_eq
      rw [hbeta, hdelta, hzeta] at hlow
      have hCrec : AR ^ 2 / 3 + CR = C0R := by
        dsimp only [CR, AR, C0R]
        simp only [map_div₀, map_one, map_ofNat]
        ring
      have hDrec : AR * BR / 3 + FR = DR := by
        dsimp only [FR, AR, BR, DR]
        simp only [map_div₀, map_one, map_ofNat]
        ring
      have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = E0R := by
        dsimp only [GR, ER, CR, AR, C0R, E0R]
        simp only [map_div₀, map_one, map_ofNat]
        ring
      have hfactor := integratedTerminal_mainTangent_factorization68
        ratFuncDerivation68 (RatFunc.C T.source.alpha)
        (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
        (RatFunc.C T.source.eta) AR BR CR FR GR
        (hconst T.source.alpha) (hconst T.source.gamma)
        (hconst T.source.epsilon) (hconst T.source.eta)
      have hsparseR : rhoOneMainTangentTerminal68
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
          AR BR CR FR GR (ratFuncDerivation68 AR) (ratFuncDerivation68 BR)
          (ratFuncDerivation68 CR) (ratFuncDerivation68 FR)
          (ratFuncDerivation68 GR) =
          RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
        rw [← hfactor, hCrec, hDrec, hErec]
        simpa only [map_zero] using hlow.2.2.2.2
      have hsparseH := congrArg (ratFuncAtHahn46 T.root) hsparseR
      have hsparseH' : rhoOneMainTangentTerminal68
          (HahnSeries.C T.source.gamma) (HahnSeries.C T.source.epsilon)
          (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
          (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
          (ratFuncAtHahn46 T.root GR)
          (ratFuncAtHahn46 T.root (Differential.deriv AR))
          (ratFuncAtHahn46 T.root (Differential.deriv BR))
          (ratFuncAtHahn46 T.root (Differential.deriv CR))
          (ratFuncAtHahn46 T.root (Differential.deriv FR))
          (ratFuncAtHahn46 T.root (Differential.deriv GR)) =
          ratFuncAtHahn46 T.root
            (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
        simpa only [rhoOneMainTangentTerminal68, ratFuncDerivation68,
          ratFuncDerivation46_apply, map_add, map_mul, map_pow,
          ratFuncAtHahn46_C, map_div₀, map_neg, map_ofNat, map_one]
          using hsparseH
      have hCRmap : ratFuncAtHahn46 T.root CR =
          rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0) := by
        dsimp only [CR, C0R, AR, rhoOneCDefectHahn68]
        simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
      have hFRmap : ratFuncAtHahn46 T.root FR =
          rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D) := by
        dsimp only [FR, AR, BR, DR, rhoOneTangentDDefectHahn68]
        simp only [map_sub, map_mul, ratFuncAtHahn46_C]
      have hGRmap : ratFuncAtHahn46 T.root GR =
          rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E)) := by
        dsimp only [GR, ER, CR, C0R, E0R, AR,
          rhoOneTangentEDefectHahn68, rhoOneCDefectHahn68,
          rhoOneEDefectHahn68]
        simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
      have hbounds := P.2.1
      dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
      have hAH := hbounds.1
      have hBR : (↑(11 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root BR).orderTop := by simpa only [BR] using hB11
      have hCR : (0 : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root CR).orderTop := by rw [hCRmap]; exact hC
      have hFR : (↑(3 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root FR).orderTop := by rw [hFRmap]; exact hF3
      have hGR : (↑(-1 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root GR).orderTop := by rw [hGRmap]; exact hG
      have hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root (Differential.deriv AR)).orderTop := by
        dsimp only [AR]
        convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
          T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
      have hdB : (0 : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root (Differential.deriv BR)).orderTop :=
        ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root BR
          (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBR)
      have hdC : (0 : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root (Differential.deriv CR)).orderTop :=
        ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root CR hCR
      have hdF : (0 : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root (Differential.deriv FR)).orderTop :=
        ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root FR
          (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hFR)
      have hdG : (↑(-2 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root (Differential.deriv GR)).orderTop :=
        ratFuncAtHahn68_deriv_orderTop_ge_negTwo_of_ge_negOne
          T.root h0 GR T.scale_order hGR
      have hfd := rhoOneTerminal_cap_FdA_two68 T.root FR
        (Differential.deriv AR) hFR hdA
      have htri := rhoOneTerminal_cap_FGdA_three68 T.root FR GR
        (Differential.deriv AR) hFR hGR hdA
      have hscale (q : k) (X : HahnSeries ℚ k) :
          (HahnSeries.C q * X).coeff 2 = q * X.coeff 2 := by
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
      have hFdA :
          (weightedMonomial68 (-((1 / 3 : k) * T.source.epsilon))
            (ratFuncAtHahn46 T.root FR)
            (ratFuncAtHahn46 T.root (Differential.deriv AR))
            (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
            (ratFuncAtHahn46 T.root CR) 1 1 0 0 0).coeff 2 =
          (-((1 / 3 : k) * T.source.epsilon)) *
            ((ratFuncAtHahn46 T.root FR).coeff 3 *
                (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-1 : ℚ) +
             (ratFuncAtHahn46 T.root FR).coeff 4 *
                (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-2 : ℚ) +
             (ratFuncAtHahn46 T.root FR).coeff 5 *
                (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-3 : ℚ)) := by
        simp only [weightedMonomial68, pow_one, pow_zero, mul_one]
        rw [show HahnSeries.C (-((1 / 3 : k) * T.source.epsilon)) *
            ratFuncAtHahn46 T.root FR *
            ratFuncAtHahn46 T.root (Differential.deriv AR) =
            HahnSeries.C (-((1 / 3 : k) * T.source.epsilon)) *
              (ratFuncAtHahn46 T.root FR *
                ratFuncAtHahn46 T.root (Differential.deriv AR)) by ring]
        rw [hscale, hfd]
      have hFGdA :
          (weightedMonomial68 (-(4 / 9 : k))
            (ratFuncAtHahn46 T.root FR) (ratFuncAtHahn46 T.root GR)
            (ratFuncAtHahn46 T.root (Differential.deriv AR))
            (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
            1 1 1 0 0).coeff 2 =
          (-(4 / 9 : k)) * (
            (ratFuncAtHahn46 T.root FR * ratFuncAtHahn46 T.root GR *
              ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff 2) := by
        simp only [weightedMonomial68, pow_one, pow_zero, mul_one]
        rw [show HahnSeries.C (-(4 / 9 : k)) * ratFuncAtHahn46 T.root FR *
            ratFuncAtHahn46 T.root GR *
            ratFuncAtHahn46 T.root (Differential.deriv AR) =
            HahnSeries.C (-(4 / 9 : k)) *
              (ratFuncAtHahn46 T.root FR * ratFuncAtHahn46 T.root GR *
                ratFuncAtHahn46 T.root (Differential.deriv AR)) by ring]
        rw [hscale]
      rw [htri] at hFGdA
      have hcoeff := rhoOneMainTangentTerminalFourHahn_coeff_two_cap68
        T.source.gamma T.source.epsilon
        (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
        (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
        (ratFuncAtHahn46 T.root GR)
        (ratFuncAtHahn46 T.root (Differential.deriv AR))
        (ratFuncAtHahn46 T.root (Differential.deriv BR))
        (ratFuncAtHahn46 T.root (Differential.deriv CR))
        (ratFuncAtHahn46 T.root (Differential.deriv FR))
        (ratFuncAtHahn46 T.root (Differential.deriv GR))
        (by simpa only [AR] using hAH) hBR hCR hFR hGR
        (by rw [hCRmap]; exact hS7) hdA hdB hdC hdF hdG hFdA hFGdA
      have hrhs : (ratFuncAtHahn46 T.root
          (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff 2 = 0 := by
        rw [map_div₀, ratFuncAtHahn46_C, hsingle, div_eq_mul_inv,
          HahnSeries.inv_single, HahnSeries.C_apply,
          HahnSeries.single_mul_single]
        norm_num
      have hfourrow : rhoOneMainTangentTerminalFourHahn68
          T.source.gamma T.source.epsilon
          (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
          (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
          (ratFuncAtHahn46 T.root GR)
          (ratFuncAtHahn46 T.root (Differential.deriv AR))
          (ratFuncAtHahn46 T.root (Differential.deriv BR))
          (ratFuncAtHahn46 T.root (Differential.deriv CR))
          (ratFuncAtHahn46 T.root (Differential.deriv FR))
          (ratFuncAtHahn46 T.root (Differential.deriv GR)) =
          ratFuncAtHahn46 T.root
            (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
        rw [← rhoOneMainTangentTerminalFourHahn_eq68]
        exact hsparseH'
      have hzero := congrArg (fun X : HahnSeries ℚ k => X.coeff 2) hfourrow
      rw [hcoeff, hrhs] at hzero
      have hterminal2 :
          3 * T.source.epsilon *
              ((ratFuncAtHahn46 T.root FR).coeff 3 *
                  (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-1 : ℚ) +
               (ratFuncAtHahn46 T.root FR).coeff 4 *
                  (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-2 : ℚ) +
               (ratFuncAtHahn46 T.root FR).coeff 5 *
                  (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-3 : ℚ)) +
            4 * ((ratFuncAtHahn46 T.root FR).coeff 3 *
                  (ratFuncAtHahn46 T.root GR).coeff (-1 : ℚ) *
                  (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff 0 +
              ((ratFuncAtHahn46 T.root FR).coeff 3 *
                  (ratFuncAtHahn46 T.root GR).coeff 0 +
                (ratFuncAtHahn46 T.root FR).coeff 4 *
                  (ratFuncAtHahn46 T.root GR).coeff (-1 : ℚ)) *
                  (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-1 : ℚ) +
              ((ratFuncAtHahn46 T.root FR).coeff 3 *
                  (ratFuncAtHahn46 T.root GR).coeff 1 +
                (ratFuncAtHahn46 T.root FR).coeff 4 *
                  (ratFuncAtHahn46 T.root GR).coeff 0 +
                (ratFuncAtHahn46 T.root FR).coeff 5 *
                  (ratFuncAtHahn46 T.root GR).coeff (-1 : ℚ)) *
                  (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-2 : ℚ) +
              ((ratFuncAtHahn46 T.root FR).coeff 3 *
                  (ratFuncAtHahn46 T.root GR).coeff 2 +
                (ratFuncAtHahn46 T.root FR).coeff 4 *
                  (ratFuncAtHahn46 T.root GR).coeff 1 +
                (ratFuncAtHahn46 T.root FR).coeff 5 *
                  (ratFuncAtHahn46 T.root GR).coeff 0 +
                (ratFuncAtHahn46 T.root FR).coeff 6 *
                  (ratFuncAtHahn46 T.root GR).coeff (-1 : ℚ)) *
                  (ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-3 : ℚ)) = 0 := by
        linear_combination (-9 : k) * hzero
      have hterminal1cleared := rhoOneTerminal_cap_one_cleared_source68
        cs (A0.derivative.eval T.root) (A0.derivative.derivative.eval T.root)
        ((ratFuncAtHahn46 T.root AR).coeff (-1 : ℚ))
        ((ratFuncAtHahn46 T.root AR).coeff 0)
        ((ratFuncAtHahn46 T.root FR).coeff 3)
        ((ratFuncAtHahn46 T.root FR).coeff 4)
        ((ratFuncAtHahn46 T.root FR).coeff 5)
        ((ratFuncAtHahn46 T.root GR).coeff (-1 : ℚ))
        ((ratFuncAtHahn46 T.root GR).coeff 0)
        ((ratFuncAtHahn46 T.root GR).coeff 1)
        ((ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-3 : ℚ))
        ((ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-2 : ℚ))
        ((ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-1 : ℚ))
        T.source.epsilon (by
          rw [hFRmap, hGRmap]
          linear_combination hterminal1) hsource0 hsource1
      have hterminal2cleared := rhoOneTerminal_cap_two_cleared_source68
        cs (A0.derivative.eval T.root) (A0.derivative.derivative.eval T.root)
        (A0.derivative.derivative.derivative.eval T.root)
        ((ratFuncAtHahn46 T.root AR).coeff (-1 : ℚ))
        ((ratFuncAtHahn46 T.root AR).coeff 0)
        ((ratFuncAtHahn46 T.root AR).coeff 1)
        ((ratFuncAtHahn46 T.root FR).coeff 3)
        ((ratFuncAtHahn46 T.root FR).coeff 4)
        ((ratFuncAtHahn46 T.root FR).coeff 5)
        ((ratFuncAtHahn46 T.root FR).coeff 6)
        ((ratFuncAtHahn46 T.root GR).coeff (-1 : ℚ))
        ((ratFuncAtHahn46 T.root GR).coeff 0)
        ((ratFuncAtHahn46 T.root GR).coeff 1)
        ((ratFuncAtHahn46 T.root GR).coeff 2)
        ((ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-3 : ℚ))
        ((ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-2 : ℚ))
        ((ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff (-1 : ℚ))
        ((ratFuncAtHahn46 T.root (Differential.deriv AR)).coeff 0)
        T.source.epsilon hterminal2 hsource0 hsource1 hsource2
      rw [hFRmap, hGRmap] at hterminal1cleared hterminal2 hterminal2cleared
      have honeactual : RhoOneDoubleZeroTerminalGBoundaryCapTerminalOnePacket68
          T.source.gamma T.source.epsilon i3 sold cs
          (A0.derivative.eval T.root) (A0.derivative.derivative.eval T.root)
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D))
          (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E)))
          (ratFuncAtHahn46 T.root (Differential.deriv T.source.A)) := by
        dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapTerminalOnePacket68]
        simpa only [A0, AR] using
          ⟨hbase, hcs, hsource0, hsource1, hterminal1, hterminal1cleared⟩
      refine ⟨i3, sold, cs, ?_⟩
      dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapTerminalTwoPacket68]
      simpa only [A0, AR] using
        ⟨honeactual, hsource2, hterminal2, hterminal2cleared⟩
    · exact (hrays.1 hcoord.1).elim
  · exact Or.inr htail

end AlignedSquareTerminalGBoundaryCapTerminalTwoBackwire68

end Max11DegreeRoutes
