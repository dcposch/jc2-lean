import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroI3FourScratch

/-! # Terminal coefficient `-2` on the signed linear `D=0` cell -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroTerminalNegTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The third jet above the lower face of a fourfold Laurent product. -/
theorem laurent_coeff_mul_four_lower_three_boundary68
    (X Y Z W : LaurentSeries k) (m n r s : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
    (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop)
    (hW : (↑s : WithTop ℤ) ≤ W.orderTop) :
    (X * Y * Z * W).coeff (m + n + r + s + 3) =
      X.coeff m * Y.coeff n * Z.coeff r * W.coeff (s + 3) +
      (X.coeff (m + 1) * Y.coeff n * Z.coeff r +
        X.coeff m * Y.coeff (n + 1) * Z.coeff r +
        X.coeff m * Y.coeff n * Z.coeff (r + 1)) * W.coeff (s + 2) +
      (X.coeff (m + 2) * Y.coeff n * Z.coeff r +
        X.coeff (m + 1) * Y.coeff (n + 1) * Z.coeff r +
        X.coeff (m + 1) * Y.coeff n * Z.coeff (r + 1) +
        X.coeff m * Y.coeff (n + 2) * Z.coeff r +
        X.coeff m * Y.coeff (n + 1) * Z.coeff (r + 1) +
        X.coeff m * Y.coeff n * Z.coeff (r + 2)) * W.coeff (s + 1) +
      (X.coeff (m + 3) * Y.coeff n * Z.coeff r +
        X.coeff (m + 2) * Y.coeff (n + 1) * Z.coeff r +
        X.coeff (m + 2) * Y.coeff n * Z.coeff (r + 1) +
        X.coeff (m + 1) * Y.coeff (n + 2) * Z.coeff r +
        X.coeff (m + 1) * Y.coeff (n + 1) * Z.coeff (r + 1) +
        X.coeff (m + 1) * Y.coeff n * Z.coeff (r + 2) +
        X.coeff m * Y.coeff (n + 3) * Z.coeff r +
        X.coeff m * Y.coeff (n + 2) * Z.coeff (r + 1) +
        X.coeff m * Y.coeff (n + 1) * Z.coeff (r + 2) +
        X.coeff m * Y.coeff n * Z.coeff (r + 3)) * W.coeff s := by
  have hXYZ : (↑(m + n + r) : WithTop ℤ) ≤ (X * Y * Z).orderTop := by
    have hXY : (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
      le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
    exact le_trans (by simpa using add_le_add hXY hZ)
      HahnSeries.orderTop_add_le_mul
  have ho := laurent_coeff_mul_lower_three68
    (X * Y * Z) W (m + n + r) s hXYZ hW
  have h0 := laurent_coeff_mul_three_lower_terminal68 X Y Z m n r hX hY hZ
  have h1 := laurent_coeff_mul_three_lower_succ68 X Y Z m n r hX hY hZ
  have h2 := laurent_coeff_mul_three_lower_two68 X Y Z m n r hX hY hZ
  have h3 := laurent_coeff_mul_three_lower_three68 X Y Z m n r hX hY hZ
  rw [h0, h1, h2, h3] at ho
  convert ho using 1 <;> ring

omit [IsAlgClosed k] in
/-- The exact surviving scalar in terminal coefficient `-2`.  Derivative
jets remain explicit because this is a genuinely source-sensitive row. -/
def rhoOne_boundaryG_terminalNegTwoRaw68
    (epsilon a a1 a0 aOne b b3 b4 b5 c1 c2 c3
      f f1 f2 f3 g gm gp g1 d3 d2 d1 d0 : k) : k :=
  (-(1 / 3 : k) * epsilon) * (f * d2 + f1 * d3) +
  (-(4 / 9 : k)) *
    (f * g * d0 + (f1 * g + f * gm) * d1 +
      (f2 * g + f1 * gm + f * gp) * d2 +
      (f3 * g + f2 * gm + f1 * gp + f * g1) * d3) +
  (-(2 / 27 : k)) *
    (a0 * f * d3 * (2 * c1) + a1 * f1 * d3 * (2 * c1) +
      a1 * f * d2 * (2 * c1) + a1 * f * d3 * (2 * c2) +
      a * f2 * d3 * (2 * c1) + a * f1 * d2 * (2 * c1) +
      a * f1 * d3 * (2 * c2) + a * f * d1 * (2 * c1) +
      a * f * d2 * (2 * c2) + a * f * d3 * (2 * c3)) +
  (-(1 / 9 : k) * epsilon) *
    (a1 * b * d3 + a * b3 * d3 + a * b * d2) +
  (-(4 / 27 : k)) *
    (a * b * g * d0 +
      (a1 * b * g + a * b3 * g + a * b * gm) * d1 +
      (a0 * b * g + a1 * b3 * g + a1 * b * gm +
        a * b4 * g + a * b3 * gm + a * b * gp) * d2 +
      (aOne * b * g + a0 * b3 * g + a0 * b * gm +
        a1 * b4 * g + a1 * b3 * gm + a1 * b * gp +
        a * b5 * g + a * b4 * gm + a * b3 * gp + a * b * g1) * d3)

omit [IsAlgClosed k] in
/-- Exact terminal coefficient `-2` at orders
`A≥-2,B≥2,C≥0,F≥0,G≥-2`. -/
theorem rhoOneMainTangentTerminal_coeff_negTwo_gNegTwo68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℤ) : WithTop ℤ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℤ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℤ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℤ) ≤ dF.orderTop)
    (hdG : (↑(-3 : ℤ) : WithTop ℤ) ≤ dG.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0) :
    (rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG).coeff (-2) =
    rhoOne_boundaryG_terminalNegTwoRaw68 epsilon
      (A.coeff (-2)) (A.coeff (-1)) (A.coeff 0) (A.coeff 1)
      (B.coeff 2) (B.coeff 3) (B.coeff 4) (B.coeff 5)
      (C.coeff 1) (C.coeff 2) (C.coeff 3)
      (F.coeff 0) (F.coeff 1) (F.coeff 2) (F.coeff 3)
      (G.coeff (-2)) (G.coeff (-1)) (G.coeff 0) (G.coeff 1)
      (dA.coeff (-3)) (dA.coeff (-2)) (dA.coeff (-1)) (dA.coeff 0) := by
  let S : LaurentSeries k := 2 * C + HahnSeries.C (3 * gamma)
  have hSbase : (0 : WithTop ℤ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · rw [two_mul]
      exact (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
    · by_cases hx : 3 * gamma = 0
      · rw [hx, HahnSeries.C_zero]; simp
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hx]; simp
  have hSco0 : S.coeff 0 = 0 := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single_same]
    linear_combination hS0
  have hS := laurent_orderTop_ge_succ_of_coeff_zero68 S 0 hSbase hSco0
  have hSco (n : ℤ) (hn : n ≠ 0) : S.coeff n = 2 * C.coeff n := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single]
    rw [if_neg hn]
    ring
  have lower2 (X Y : LaurentSeries k) (m n : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
      (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
    le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  have lower3 (X Y Z : LaurentSeries k) (m n r : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
      (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop) :
      (↑(m + n + r) : WithTop ℤ) ≤ (X * Y * Z).orderTop :=
    lower2 (X * Y) Z (m + n) r (lower2 X Y m n hX hY) hZ
  have lower4 (X Y Z W : LaurentSeries k) (m n r s : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
      (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop)
      (hW : (↑s : WithTop ℤ) ≤ W.orderTop) :
      (↑(m + n + r + s) : WithTop ℤ) ≤ (X * Y * Z * W).orderTop :=
    lower2 (X * Y * Z) W (m + n + r) s
      (lower3 X Y Z m n r hX hY hZ) hW
  have zero_of_lower (X : LaurentSeries k) (n : ℤ)
      (hX : (↑n : WithTop ℤ) ≤ X.orderTop) (hlt : (-2 : ℤ) < n) :
      X.coeff (-2) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hlt) hX)
  have h1 := zero_of_lower (F * dC) 0 (lower2 F dC 0 0 hF hdC) (by omega)
  have h2 := laurent_coeff_mul_lower_succ68 F dA 0 (-3) hF hdA
  have h3 := laurent_coeff_mul_three_lower_three68 F G dA 0 (-2) (-3) hF hG hdA
  have h4 := zero_of_lower (F * F * dB) 0
    (lower3 F F dB 0 0 0 hF hF hdB) (by omega)
  have h5 := zero_of_lower (C * F * dC) 0
    (lower3 C F dC 0 0 0 hC hF hdC) (by omega)
  have h6 := zero_of_lower (B * dG) (-1) (lower2 B dG 2 (-3) hB hdG) (by omega)
  have h7 := zero_of_lower (B * F * dF) 2
    (lower3 B F dF 2 0 0 hB hF hdF) (by omega)
  have h8 := zero_of_lower (B * C * dG) (-1)
    (lower3 B C dG 2 0 (-3) hB hC hdG) (by omega)
  have h9 := zero_of_lower (B * C * dA) (-1)
    (lower3 B C dA 2 0 (-3) hB hC hdA) (by omega)
  have h10 := zero_of_lower (B * C * C * dA) (-1)
    (lower4 B C C dA 2 0 0 (-3) hB hC hC hdA) (by omega)
  have h11a := laurent_coeff_mul_three_lower_three68 A F dA (-2) 0 (-3)
    hA hF hdA
  have h11c := laurent_coeff_mul_four_lower_three_boundary68 A F dA C
    (-2) 0 (-3) 0 hA hF hdA hC
  have h12 := laurent_coeff_mul_three_lower_succ68 A B dA (-2) 2 (-3)
    hA hB hdA
  have h13 := laurent_coeff_mul_four_lower_three_boundary68 A B G dA
    (-2) 2 (-2) (-3) hA hB hG hdA
  have h14 := zero_of_lower (A * B * F * dB) 0
    (lower4 A B F dB (-2) 2 0 0 hA hB hF hdB) (by omega)
  have h15 := zero_of_lower (A * B * B * dF) 2
    (lower4 A B B dF (-2) 2 2 0 hA hB hB hdF) (by omega)
  norm_num at h2 h3 h11a h11c h12 h13
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hrewrite :
      rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
        (HahnSeries.C epsilon) A B C F G dA dB dC dF dG =
      HahnSeries.C (-(2 / 3 : k) * gamma) * (F * dC) +
      HahnSeries.C (-(1 / 3 : k) * epsilon) * (F * dA) +
      HahnSeries.C (-(4 / 9 : k)) * (F * G * dA) +
      HahnSeries.C (-(4 / 9 : k)) * (F * F * dB) +
      HahnSeries.C (-(4 / 9 : k)) * (C * F * dC) +
      HahnSeries.C ((2 / 3 : k) * gamma) * (B * dG) +
      HahnSeries.C (-(4 / 9 : k)) * (B * F * dF) +
      HahnSeries.C (4 / 9 : k) * (B * C * dG) +
      HahnSeries.C ((2 / 9 : k) * gamma) * (B * C * dA) +
      HahnSeries.C (4 / 27 : k) * (B * C * C * dA) +
      HahnSeries.C (-(2 / 9 : k) * gamma) * (A * F * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * F * dA * C) +
      HahnSeries.C (-(1 / 9 : k) * epsilon) * (A * B * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * G * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * F * dB) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * B * dF) := by
    simp only [rhoOneMainTangentTerminal68, HahnSeries.C_eq_algebraMap,
      map_mul, map_add, map_neg, map_div₀, map_ofNat, map_one]
    ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add, hscale]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11a, h11c,
    h12, h13, h14, h15]
  dsimp only [rhoOne_boundaryG_terminalNegTwoRaw68]
  linear_combination
    (-(2 / 27 : k)) *
      (A.coeff (-2) * F.coeff 0 * dA.coeff 0 +
        A.coeff (-2) * F.coeff 1 * dA.coeff (-1) +
        A.coeff (-1) * F.coeff 0 * dA.coeff (-1) +
        A.coeff (-2) * F.coeff 2 * dA.coeff (-2) +
        A.coeff (-1) * F.coeff 1 * dA.coeff (-2) +
        A.coeff 0 * F.coeff 0 * dA.coeff (-2) +
        A.coeff (-2) * F.coeff 3 * dA.coeff (-3) +
        A.coeff (-1) * F.coeff 2 * dA.coeff (-3) +
        A.coeff 0 * F.coeff 1 * dA.coeff (-3) +
        A.coeff 1 * F.coeff 0 * dA.coeff (-3)) * hS0

omit [IsAlgClosed k] in
/-- The literal source row supplied by terminal coefficient `-2`.  Keeping
the derivative jets visible is important: unlike the preceding invariant
row, this coefficient is sensitive to the cleared source coordinate. -/
def rhoOne_boundaryG_terminalNegTwoSourceRow68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : k :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let dA := ratFuncAtHahn46 T.root (Differential.deriv T.source.A)
  rhoOne_boundaryG_terminalNegTwoRaw68 T.source.epsilon
    (A.coeff (-2)) (A.coeff (-1)) (A.coeff 0) (A.coeff 1)
    (B.coeff 2) (B.coeff 3) (B.coeff 4) (B.coeff 5)
    (C.coeff 1) (C.coeff 2) (C.coeff 3)
    (F.coeff 0) (F.coeff 1) (F.coeff 2) (F.coeff 3)
    (G.coeff (-2)) (G.coeff (-1)) (G.coeff 0) (G.coeff 1)
    (dA.coeff (-3)) (dA.coeff (-2)) (dA.coeff (-1)) (dA.coeff 0)

/-- Source backwire for terminal coefficient `-2` throughout the exact
`G[-2]` boundary box. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_terminal_negTwo_source68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    rhoOne_boundaryG_terminalNegTwoSourceRow68 T = 0 := by
  have Qc := Q
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68] at Qc
  rcases Qc with ⟨Rm, hquadratic⟩
  have Rmc := Rm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68] at Rmc
  rcases Rmc with ⟨Rtf, hminor⟩
  have Rtfc := Rtf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rtfc
  rcases Rtfc with ⟨Rt, i3two, i4three, hi3twoSrc, hi4threeSrc, hdet⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hcross⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨Rbase, hi3zero, htermFour⟩
  have Rbasec := Rbase
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at Rbasec
  rcases Rbasec with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hfneg, hgneg, hb1, hS0, hscalar, hi4base⟩
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ := P.1
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  let A0 := localClearedA68RhoOne g u
  have hAclear := (T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero
    hH hp6 hp5 hp4).1
  change algebraMap k[X] (RatFunc k) A0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * A at hAclear
  obtain ⟨c', hc', hsingle', hderiv'⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
  have hcEq : c' = c := by
    have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff 1)
      (hsingle'.symm.trans hsingle)
    simpa only [HahnSeries.coeff_single_same] using heq
  subst c'
  have hCmap : ratFuncAtHahn46 T.root C =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, A, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : ratFuncAtHahn46 T.root F =
      rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, A, B, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hEmap : ratFuncAtHahn46 T.root E =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [E, A, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGmap : ratFuncAtHahn46 T.root G =
      rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, hCmap, map_mul, ratFuncAtHahn46_C]
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root A).orderTop := by simpa only [A] using P.2.1.1
  have hBH : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root B).orderTop := by simpa only [B] using hB
  have hCH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root C).orderTop := by
    rw [hCmap]; exact hC
  have hFH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root F).orderTop := by
    rw [hFmap]; exact hF
  have hGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (Polynomial.C x)
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
  have hCrec : A ^ 2 / 3 + C = T.source.C0 := by
    dsimp only [C, A]; simp only [map_div₀, map_one, map_ofNat]; ring
  have hDrec : A * B / 3 + F = T.source.D := by
    dsimp only [F, A, B]; simp only [map_div₀, map_one, map_ofNat]; ring
  have hErec : A ^ 3 / 27 + A * C / 3 + G = T.source.E := by
    dsimp only [G, E, C, A]; simp only [map_div₀, map_one, map_ofNat]; ring
  have hfactor := integratedTerminal_mainTangent_factorization68
    ratFuncDerivation68 (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.eta) A B C F G
      (hconst T.source.alpha) (hconst T.source.gamma)
      (hconst T.source.epsilon) (hconst T.source.eta)
  have hsparseR : rhoOneMainTangentTerminal68 (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.epsilon) A B C F G
      (ratFuncDerivation68 A) (ratFuncDerivation68 B) (ratFuncDerivation68 C)
      (ratFuncDerivation68 F) (ratFuncDerivation68 G) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hfactor, hCrec, hDrec, hErec]
    simpa only [map_zero] using hlow.2.2.2.2
  have hdAH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv A)).orderTop := by
    dsimp only [A]
    convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
      T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
  have hdBH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv B)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root B
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBH)
  have hdCH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv C)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root C hCH
  have hdFH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv F)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root F hFH
  have hdGH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv G)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negThree_of_ge_negTwo
      T.root h0 G T.scale_order hGH
  let AL := ratFuncAtLaurent46 T.root A
  let BL := ratFuncAtLaurent46 T.root B
  let CL := ratFuncAtLaurent46 T.root C
  let FL := ratFuncAtLaurent46 T.root F
  let GLa := ratFuncAtLaurent46 T.root G
  let dAL := ratFuncAtLaurent46 T.root (Differential.deriv A)
  let dBL := ratFuncAtLaurent46 T.root (Differential.deriv B)
  let dCL := ratFuncAtLaurent46 T.root (Differential.deriv C)
  let dFL := ratFuncAtLaurent46 T.root (Differential.deriv F)
  let dGL := ratFuncAtLaurent46 T.root (Differential.deriv G)
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root A (-2) hAH
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root B 2 hBH
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root C 0 hCH
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root F 0 hFH
  have hGLa := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root G (-2) hGH
  have hdAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv A) (-3) hdAH
  have hdBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv B) 0 hdBH
  have hdCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv C) 0 hdCH
  have hdFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv F) 0 hdFH
  have hdGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv G) (-3) hdGH
  have hcs (X : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 T.root X n
  have hS0L : 2 * CL.coeff 0 + 3 * T.source.gamma = 0 := by
    rw [← hcs C 0, hCmap]; exact hS0
  have hterm := rhoOneMainTangentTerminal_coeff_negTwo_gNegTwo68
    T.source.gamma T.source.epsilon AL BL CL FL GLa dAL dBL dCL dFL dGL
      hAL hBL hCL hFL hGLa hdAL hdBL hdCL hdFL hdGL hS0L
  have hsparseL := congrArg (ratFuncAtLaurent46 T.root) hsparseR
  have hsparseL' : rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
      (HahnSeries.C T.source.epsilon) AL BL CL FL GLa dAL dBL dCL dFL dGL =
      ratFuncAtLaurent46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    simpa only [AL, BL, CL, FL, GLa, dAL, dBL, dCL, dFL, dGL,
      rhoOneMainTangentTerminal68, ratFuncDerivation68,
      ratFuncDerivation46_apply, map_add, map_mul, map_pow, map_neg,
      map_div₀, map_ofNat, map_one, ratFuncAtLaurent46_C68] using hsparseL
  have hzeroH : (ratFuncAtHahn46 T.root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-2) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [T.terminal_order]
      exact WithTop.coe_lt_coe.mpr (by norm_num))
  have hzeroL : (ratFuncAtLaurent46 T.root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-2) = 0 := by
    rw [← hcs (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) (-2)]
    exact hzeroH
  have hleft := congrArg (fun X : LaurentSeries k => X.coeff (-2)) hsparseL'
  rw [hterm, hzeroL] at hleft
  have htoL (X : RatFunc k) (n : ℤ) :
      (ratFuncAtLaurent46 T.root X).coeff n =
        (ratFuncAtHahn46 T.root X).coeff n := by
    rw [hcs X n]
  have hleft' := hleft
  simp only [rhoOne_boundaryG_terminalNegTwoSourceRow68,
    AL, BL, CL, FL, GLa, dAL, ← hcs A (-2), ← hcs A (-1),
    ← hcs A 0, ← hcs A 1, ← hcs B 2, ← hcs B 3,
    ← hcs B 4, ← hcs B 5, ← hcs C 1, ← hcs C 2,
    ← hcs C 3, ← hcs F 0, ← hcs F 1, ← hcs F 2,
    ← hcs F 3, ← hcs G (-2), ← hcs G (-1), ← hcs G 0,
    ← hcs G 1, ← hcs (Differential.deriv A) (-3),
    ← hcs (Differential.deriv A) (-2),
    ← hcs (Differential.deriv A) (-1),
    ← hcs (Differential.deriv A) 0] at hleft' ⊢
  rw [hCmap, hFmap, hGmap] at hleft'
  norm_num at hleft' ⊢
  simpa only [A, B] using hleft'

/-- The exact D-zero packet with terminal coefficient `-2` adjoined.  The
predecessor remains a literal conjunct, so its `D≠0`, `Q0/R0`, coordinate
and nonsingular siblings are unchanged. -/
def RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegTwo68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroI3Four68 T ∧
    rhoOne_boundaryG_terminalNegTwoSourceRow68 T = 0

/-- Add the source-backed terminal row to the exact determinant-zero packet. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_negTwo68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDeterminantSolved68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegTwo68 T :=
  ⟨T.rhoOne_boundaryG_signedRay_linear_dZero_i3four68 Q R,
    T.rhoOne_boundaryG_terminal_negTwo_source68 hp hH hp6 hp5 hp4 Q⟩

/-- Outer source selector with only the determinant-solved linear child
strengthened; every other leaf is carried verbatim. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_linear_dZero_terminal_negTwo_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        (RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalNegTwo68 T ∨
          RhoOneAlignedSquareGNegTwoSignedRayQRResidual68 T)) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRay_linear_determinantSolved_selector68
      hp hH hp6 hp5 hp4 Q with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · rcases hsigned.2 with hlinear | hqr
    · exact Or.inr (Or.inl ⟨hsigned.1,
        Or.inl (T.rhoOne_boundaryG_signedRay_linear_dZero_terminal_negTwo68
          hp hH hp6 hp5 hp4 hsigned.1 hlinear)⟩)
    · exact Or.inr (Or.inl ⟨hsigned.1, Or.inr hqr⟩)
  · exact Or.inr (Or.inr hnon)
