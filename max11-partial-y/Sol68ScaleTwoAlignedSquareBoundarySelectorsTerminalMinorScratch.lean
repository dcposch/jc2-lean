import Sol68ScaleTwoAlignedSquareBoundarySelectorsTerminalFollowingScratch

/-! # Minor split and the selective terminal face on the square boundaries -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundarySelectorsTerminalMinor68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance boundarySelectorsTerminalMinorLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_minor_normalize68
    (a b f gm : k) (hscalar : 3 * f + a * b = 0) :
    81 * ((-(8 / 9 : k)) * a * f * f - (8 / 3 : k) * gm * gm) =
      -8 * (a ^ 3 * b ^ 2 + 27 * gm ^ 2) := by
  linear_combination 8 * a * (a * b - 3 * f) * hscalar

omit [IsAlgClosed k] in
theorem rhoOne_boundaryG_minor_transport68
    (x y q0 r0 qx qy rx ry : k)
    (hq : q0 + qx * x + qy * y = 0)
    (hr : r0 + rx * x + ry * y = 0) :
    let D := qx * ry - qy * rx
    D * x = qy * r0 - q0 * ry ∧
    D * y = rx * q0 - qx * r0 := by
  dsimp only
  constructor
  · linear_combination ry * hq - qy * hr
  · linear_combination qx * hr - rx * hq

omit [IsAlgClosed k] in
/-- The new F-boundary terminal scalar and the preceding finite equation
remove epsilon without opening another invariant jet. -/
theorem rhoOne_boundaryF_terminalFour_cross68
    (a a1 b b2 fm f0 gm gp c1 c2 epsilon i4 : k)
    (ha : a ≠ 0)
    (hraw : 4 * a1 * b * gm + 3 * a * b * epsilon +
      9 * epsilon * fm + 12 * f0 * gm = 0)
    (hrel : 3 * fm = 2 * a * b)
    (hterminal : 2 * a * c1 + 9 * gm = 0)
    (hfollowing : 3 * f0 = 2 * (a1 * b + a * b2))
    (hs1 : 27 * i4 = 32 * a * b * c1)
    (hold : 16 * a * b ^ 2 * gp + 6 * a * b2 * i4 +
      9 * a1 * b * i4 + 16 * a * b * c2 * fm +
      12 * a * epsilon * b ^ 2 = 0) :
    (24 * a1 * b * c1 + 16 * a * b2 * c1 - 81 * b * epsilon = 0) ∧
    (4 * a * b ^ 2 * gp + 2 * a * b2 * i4 + 3 * a1 * b * i4 +
      4 * a * b * c2 * fm = 0) := by
  have hmul : a *
      (24 * a1 * b * c1 + 16 * a * b2 * c1 - 81 * b * epsilon) = 0 := by
    linear_combination
      -9 * hraw + 4 * a1 * b * hterminal + 12 * f0 * hterminal +
      27 * epsilon * hrel - 8 * a * c1 * hfollowing
  have hnew : 24 * a1 * b * c1 + 16 * a * b2 * c1 -
      81 * b * epsilon = 0 :=
    (mul_eq_zero.mp hmul).resolve_left ha
  refine ⟨hnew, ?_⟩
  have haux : 2 * a * b2 * i4 + 3 * a1 * b * i4 -
      12 * a * epsilon * b ^ 2 = 0 := by
    linear_combination
      (4 / 27 : k) * a * b * hnew +
      (1 / 9 : k) * a1 * b * hs1 + (2 / 27 : k) * a * b2 * hs1
  linear_combination (1 / 4 : k) * hold + (1 / 4 : k) * haux

omit [IsAlgClosed k] in
/-- After the actual terminal `-4` face is inserted, the preceding `I4`
row loses every load and defect coefficient except the three adjacent
`B,C` transports. -/
theorem rhoOne_boundaryF_terminalFour_final_cross68
    (a a1 b b2 fm gp c1 c2 epsilon i4 : k)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hnew : 8 * a1 * c1 + 8 * a * c2 + 27 * epsilon + 36 * gp = 0)
    (hrel : 3 * fm = 2 * a * b)
    (hs1 : 27 * i4 = 32 * a * b * c1)
    (hold : 16 * a * b ^ 2 * gp + 6 * a * b2 * i4 +
      9 * a1 * b * i4 + 16 * a * b * c2 * fm +
      12 * a * epsilon * b ^ 2 = 0) :
    a * b * c2 + a * b2 * c1 + a1 * b * c1 = 0 := by
  have hmul : a * b *
      (64 * (a * b * c2 + a * b2 * c1 + a1 * b * c1)) = 0 := by
    linear_combination
      9 * hold - 4 * a * b ^ 2 * hnew -
        48 * a * b * c2 * hrel -
        (2 * a * b2 + 3 * a1 * b) * hs1
  rcases mul_eq_zero.mp hmul with hab | ht
  · exact False.elim ((mul_ne_zero ha hb) hab)
  · have h64 : (64 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp ht).resolve_left h64

omit [IsAlgClosed k] in
/-- Terminal coefficient `-4` on the genuine `F[-1]` limb. -/
theorem rhoOneMainTangentTerminal_coeff_negFour_fNegOne68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(1 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(-1 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℤ) : WithTop ℤ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℤ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℤ) ≤ dC.orderTop)
    (hdF : (↑(-2 : ℤ) : WithTop ℤ) ≤ dF.orderTop)
    (hdG : (↑(-2 : ℤ) : WithTop ℤ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3) = (-2 : k) * A.coeff (-2))
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hrel : 3 * F.coeff (-1) = 2 * A.coeff (-2) * B.coeff 1)
    (hterminal : 2 * A.coeff (-2) * C.coeff 1 + 9 * G.coeff (-1) = 0)
    (hfollowing : 3 * F.coeff 0 =
      2 * (A.coeff (-1) * B.coeff 1 + A.coeff (-2) * B.coeff 2)) :
    (rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG).coeff (-4) =
      (2 / 81 : k) * A.coeff (-2) ^ 2 * B.coeff 1 *
        (8 * A.coeff (-1) * C.coeff 1 + 8 * A.coeff (-2) * C.coeff 2 +
          27 * epsilon + 36 * G.coeff 0) := by
  let S : LaurentSeries k := 2 * C + HahnSeries.C (3 * gamma)
  have hSbase : (0 : WithTop ℤ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · rw [two_mul]
      exact (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
    · by_cases hx : 3 * gamma = 0
      · rw [hx, HahnSeries.C_zero]
        simp
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hx]
        simp
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
      (hX : (↑n : WithTop ℤ) ≤ X.orderTop) (hlt : (-4 : ℤ) < n) :
      X.coeff (-4) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hlt) hX)
  have h1 := zero_of_lower (F * dC) (-1) (lower2 F dC (-1) 0 hF hdC) (by omega)
  have h2 := laurent_coeff_mul_lower68 F dA (-1) (-3) hF hdA
  have h3 := laurent_coeff_mul_three_lower_succ68 F G dA (-1) (-1) (-3) hF hG hdA
  have h4 := zero_of_lower (F * F * dB) (-2) (lower3 F F dB (-1) (-1) 0 hF hF hdB) (by omega)
  have h5 := zero_of_lower (C * F * dC) (-1) (lower3 C F dC 0 (-1) 0 hC hF hdC) (by omega)
  have h6 := zero_of_lower (B * dG) (-1) (lower2 B dG 1 (-2) hB hdG) (by omega)
  have h7 := zero_of_lower (B * F * dF) (-2) (lower3 B F dF 1 (-1) (-2) hB hF hdF) (by omega)
  have h8 := zero_of_lower (B * C * dG) (-1) (lower3 B C dG 1 0 (-2) hB hC hdG) (by omega)
  have h9 := zero_of_lower (B * C * dA) (-2) (lower3 B C dA 1 0 (-3) hB hC hdA) (by omega)
  have h10 := zero_of_lower (B * C * C * dA) (-2) (lower4 B C C dA 1 0 0 (-3) hB hC hC hdA) (by omega)
  have hAFord := lower3 A F dA (-2) (-1) (-3) hA hF hdA
  have hAF0 := laurent_coeff_mul_three_lower_terminal68 A F dA (-2) (-1) (-3) hA hF hdA
  have hAF1 := laurent_coeff_mul_three_lower_succ68 A F dA (-2) (-1) (-3) hA hF hdA
  have h11 := laurent_coeff_mul_lower_succ68 (A * F * dA) S (-6) 1
    (by convert hAFord using 1 <;> norm_num) hS
  have h12 := laurent_coeff_mul_three_lower_terminal68 A B dA (-2) 1 (-3) hA hB hdA
  have h13 := laurent_coeff_mul_four_lower_succ_terminal68 A B G dA
    (-2) 1 (-1) (-3) hA hB hG hdA
  have h14 := zero_of_lower (A * B * F * dB) (-2) (lower4 A B F dB (-2) 1 (-1) 0 hA hB hF hdB) (by omega)
  have h15 := zero_of_lower (A * B * B * dF) (-2) (lower4 A B B dF (-2) 1 1 (-2) hA hB hB hdF) (by omega)
  norm_num at h2 h3 hAF0 hAF1 h11 h12 h13
  rw [hAF0, hAF1] at h11
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hrewrite : rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
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
      HahnSeries.C (-(2 / 27 : k)) * (A * F * dA * S) +
      HahnSeries.C (-(1 / 9 : k) * epsilon) * (A * B * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * G * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * F * dB) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * B * dF) := by
    simp only [rhoOneMainTangentTerminal68, S, HahnSeries.C_eq_algebraMap,
      map_mul, map_add, map_neg, map_div₀, map_ofNat, map_one]
    ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add, hscale]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, hdAco, hSco 1 (by norm_num), hSco 2 (by norm_num)]
  linear_combination
    (4 / 243 : k) *
        (2 * A.coeff (-2) ^ 2 * B.coeff 2 +
          2 * A.coeff (-2) * A.coeff (-1) * B.coeff 1 -
          A.coeff (-2) * B.coeff 1 * dA.coeff (-2) +
          6 * A.coeff (-2) * F.coeff 0 -
          3 * dA.coeff (-2) * F.coeff (-1)) * hterminal +
      (2 / 243 : k) * A.coeff (-2) *
        (12 * A.coeff (-2) * C.coeff 2 +
          12 * A.coeff (-1) * C.coeff 1 -
          2 * C.coeff 1 * dA.coeff (-2) + 27 * epsilon +
          36 * G.coeff 0) * hrel +
      (8 / 243 : k) * A.coeff (-2) ^ 2 * C.coeff 1 * hfollowing

/-- The `G[-2]` finite packet after resolving its `B[4],C[3]` minor.
The singular component is the displayed quadratic wall; off that wall
both unknown coefficients are transported uniquely. -/
def RhoOneAlignedSquareGNegTwoBoundaryMinor68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let Q0 := (-(8 / 9 : k)) *
      (A.coeff (-2) * B.coeff 2 * F.coeff 2 +
        (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) * F.coeff 1 +
        (A.coeff (-1) * B.coeff 3 + A.coeff 0 * B.coeff 2) * F.coeff 0) +
    (8 / 3 : k) * (C.coeff 1 * G.coeff 1 + C.coeff 2 * G.coeff 0 +
      C.coeff 4 * G.coeff (-2)) +
    (4 / 3 : k) * (2 * F.coeff 0 * F.coeff 2 + F.coeff 1 ^ 2) +
    2 * T.source.epsilon * C.coeff 2
  let R0 := B.coeff 2 * G.coeff 1 + B.coeff 3 * G.coeff 0 +
    B.coeff 5 * G.coeff (-2) + C.coeff 1 * F.coeff 2 +
    C.coeff 2 * F.coeff 1 + (3 / 4 : k) * T.source.epsilon * B.coeff 3
  let D := (-(8 / 9 : k)) * A.coeff (-2) * F.coeff 0 ^ 2 -
    (8 / 3 : k) * G.coeff (-1) ^ 2
  RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68 T g u ∧
  (A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 = 0 ∨
    (A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0 ∧
      D ≠ 0 ∧
      D * B.coeff 4 = (8 / 3 : k) * G.coeff (-1) * R0 - Q0 * F.coeff 0 ∧
      D * C.coeff 3 = G.coeff (-1) * Q0 -
        (-(8 / 9 : k)) * A.coeff (-2) * F.coeff 0 * R0))

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_minor68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68 T g u) :
    RhoOneAlignedSquareGNegTwoBoundaryMinor68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rc
  rcases Rc with ⟨Rt, i3old, i4old, hi3srcOld, hi4srcOld, hdetOld⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rf, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rfc := Rf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rfc
  rcases Rfc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hterminal⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨R0, hi3zero, hterminalOld⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at R0c
  rcases R0c with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hb1, hS, hscalar, hi4oldFace⟩
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  have hCmap : ratFuncAtHahn46 T.root C =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, A, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : ratFuncAtHahn46 T.root F =
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
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
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
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
  obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
    T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
  have hq := ratFunc_boundaryG_i3two68 T.root T.source.gamma
    T.source.epsilon i3 A B C F G hAH hBH hCH hFH hGH
      (by rw [hCmap]; exact hS) hi3f
  have hr := ratFunc_boundaryG_i4three68 T.root T.source.gamma
    T.source.epsilon i4 B C F G hBH hCH hFH hGH
      (by rw [hCmap]; exact hS) hi4f
  rw [hCmap, hFmap, hGmap] at hq hr
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := rhoOneCDefectHahn68 AH (ratFuncAtHahn46 T.root T.source.C0)
  let FH := rhoOneTangentDDefectHahn68 AH BH
    (ratFuncAtHahn46 T.root T.source.D)
  let GH := rhoOneTangentEDefectHahn68 AH CH
    (rhoOneEDefectHahn68 AH (ratFuncAtHahn46 T.root T.source.E))
  let Q0 := (-(8 / 9 : k)) *
      (AH.coeff (-2) * BH.coeff 2 * FH.coeff 2 +
        (AH.coeff (-2) * BH.coeff 3 + AH.coeff (-1) * BH.coeff 2) * FH.coeff 1 +
        (AH.coeff (-1) * BH.coeff 3 + AH.coeff 0 * BH.coeff 2) * FH.coeff 0) +
    (8 / 3 : k) * (CH.coeff 1 * GH.coeff 1 + CH.coeff 2 * GH.coeff 0 +
      CH.coeff 4 * GH.coeff (-2)) +
    (4 / 3 : k) * (2 * FH.coeff 0 * FH.coeff 2 + FH.coeff 1 ^ 2) +
    2 * T.source.epsilon * CH.coeff 2
  let R0 := BH.coeff 2 * GH.coeff 1 + BH.coeff 3 * GH.coeff 0 +
    BH.coeff 5 * GH.coeff (-2) + CH.coeff 1 * FH.coeff 2 +
    CH.coeff 2 * FH.coeff 1 + (3 / 4 : k) * T.source.epsilon * BH.coeff 3
  have hq' : Q0 + (-(8 / 9 : k) * AH.coeff (-2) * FH.coeff 0) *
      BH.coeff 4 + (8 / 3 : k) * GH.coeff (-1) * CH.coeff 3 = 0 := by
    dsimp only [Q0, AH, BH, CH, FH, GH]
    linear_combination hq
  have hr' : R0 + GH.coeff (-1) * BH.coeff 4 +
      FH.coeff 0 * CH.coeff 3 = 0 := by
    dsimp only [R0, AH, BH, CH, FH, GH]
    linear_combination hr
  have ht := rhoOne_boundaryG_minor_transport68 (BH.coeff 4) (CH.coeff 3)
    Q0 R0 (-(8 / 9 : k) * AH.coeff (-2) * FH.coeff 0)
    ((8 / 3 : k) * GH.coeff (-1)) (GH.coeff (-1)) (FH.coeff 0) hq' hr'
  dsimp only at ht
  by_cases hw : AH.coeff (-2) ^ 3 * BH.coeff 2 ^ 2 +
      27 * GH.coeff (-1) ^ 2 = 0
  · dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68]
    exact ⟨R, Or.inl hw⟩
  · have hDlocal : (-(8 / 9 : k)) * AH.coeff (-2) * FH.coeff 0 ^ 2 -
        (8 / 3 : k) * GH.coeff (-1) ^ 2 ≠ 0 := by
      intro hD
      have hD' : (-(8 / 9 : k)) * AH.coeff (-2) * FH.coeff 0 * FH.coeff 0 -
          (8 / 3 : k) * GH.coeff (-1) * GH.coeff (-1) = 0 := by
        convert hD using 1 <;> ring
      have hn := rhoOne_boundaryG_minor_normalize68
        (AH.coeff (-2)) (BH.coeff 2) (FH.coeff 0) (GH.coeff (-1)) hscalar
      rw [hD'] at hn
      have : AH.coeff (-2) ^ 3 * BH.coeff 2 ^ 2 +
          27 * GH.coeff (-1) ^ 2 = 0 := by
        have h8 : (-8 : k) ≠ 0 := by norm_num
        have hz : (-8 : k) * (AH.coeff (-2) ^ 3 * BH.coeff 2 ^ 2 +
            27 * GH.coeff (-1) ^ 2) = 0 := by simpa using hn.symm
        exact (mul_eq_zero.mp hz).resolve_left h8
      exact hw this
    have ht1 : ((-(8 / 9 : k)) * AH.coeff (-2) * FH.coeff 0 ^ 2 -
        (8 / 3 : k) * GH.coeff (-1) ^ 2) * BH.coeff 4 =
          (8 / 3 : k) * GH.coeff (-1) * R0 - Q0 * FH.coeff 0 := by
      convert ht.1 using 1 <;> ring
    have ht2 : ((-(8 / 9 : k)) * AH.coeff (-2) * FH.coeff 0 ^ 2 -
        (8 / 3 : k) * GH.coeff (-1) ^ 2) * CH.coeff 3 =
          GH.coeff (-1) * Q0 -
            (-(8 / 9 : k)) * AH.coeff (-2) * FH.coeff 0 * R0 := by
      convert ht.2 using 1 <;> ring
    dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68]
    refine ⟨R, Or.inr ?_⟩
    dsimp only [AH, BH, CH, FH, GH, Q0, R0] at hw hDlocal ht1 ht2 ⊢
    exact ⟨hw, hDlocal, ht1, ht2⟩

/-- The `F[-1]` finite packet after the source terminal coefficient `-4`.
Besides recording that terminal scalar, it compresses the preceding `I4`
row to a three-term adjacent-coefficient transport. -/
def RhoOneAlignedSquareFNegOneBoundaryMinor68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareFNegOneBoundaryTerminalFollowing68 T g u ∧
  (8 * A.coeff (-1) * C.coeff 1 + 8 * A.coeff (-2) * C.coeff 2 +
      27 * T.source.epsilon + 36 * G.coeff 0 = 0) ∧
  (A.coeff (-2) * B.coeff 1 * C.coeff 2 +
      A.coeff (-2) * B.coeff 2 * C.coeff 1 +
      A.coeff (-1) * B.coeff 1 * C.coeff 1 = 0)

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryF_minor68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareFNegOneBoundaryTerminalFollowing68 T g u) :
    RhoOneAlignedSquareFNegOneBoundaryMinor68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryTerminalFollowing68] at Rc
  rcases Rc with ⟨Rt, i4, hi4src, hi4row, hold⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4old, hi4srcOld, hs1, hs2, hs3⟩
  have hi4eq : i4 = i4old := by
    have hc : RatFunc.C i4 = RatFunc.C i4old := hi4src.symm.trans hi4srcOld
    have hh := congrArg (ratFuncAtHahn46 T.root) hc
    have hh0 := congrArg (fun X : HahnSeries ℚ k => X.coeff 0) hh
    simpa only [ratFuncAtHahn46_C, HahnSeries.C_apply,
      HahnSeries.coeff_single_same] using hh0
  subst i4old
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, hterminal⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, hfollowing⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryNext68] at Rnc
  rcases Rnc with ⟨R0, i4base, hi4base, hi4face, hnext⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryResidual68] at R0c
  rcases R0c with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hS, hb, hrel⟩
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
    ratFuncAtHahn68_linearRoot_single_deriv h0 T.root T.scale_degree T.root_eq
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
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
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
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, hCmap, map_mul, ratFuncAtHahn46_C]
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root A).orderTop := by simpa only [A] using P.2.1.1
  have hAne : (ratFuncAtHahn46 T.root A).coeff (-2) ≠ 0 := by
    simpa only [A] using P.2.2.1
  have hBH : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root B).orderTop := by simpa only [B] using hB
  have hCH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root C).orderTop := by
    rw [hCmap]; exact hC
  have hFH : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root F).orderTop := by rw [hFmap]; exact hF
  have hGH : (↑(-1 : ℚ) : WithTop ℚ) ≤
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
  have hdAcoH :
      (ratFuncAtHahn46 T.root (Differential.deriv A)).coeff (-3) =
        (-2 : k) * (ratFuncAtHahn46 T.root A).coeff (-2) := by
    dsimp only [A]
    convert localHahn_deriv_coeff_neg_succ_of_cleared T.root c h0 A0
      T.source.A 2 hc hsingle hderiv' hAclear using 1 <;> norm_num
  have hdBH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv B)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root B
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBH)
  have hdCH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv C)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root C hCH
  have hdFH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv F)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negTwo_of_ge_negOne
      T.root h0 F T.scale_order hFH
  have hdGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv G)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negTwo_of_ge_negOne
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
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root B 1 hBH
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root C 0 hCH
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root F (-1) hFH
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root G (-1) hGH
  have hdAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv A) (-3) hdAH
  have hdBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv B) 0 hdBH
  have hdCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv C) 0 hdCH
  have hdFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv F) (-2) hdFH
  have hdGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv G) (-2) hdGH
  have hcs (R0 : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 T.root R0 n
  have hdAcoL : dAL.coeff (-3) = (-2 : k) * AL.coeff (-2) := by
    rw [← hcs (Differential.deriv A) (-3), ← hcs A (-2)]
    exact hdAcoH
  have hS0L : 2 * CL.coeff 0 + 3 * T.source.gamma = 0 := by
    rw [← hcs C 0, hCmap]
    exact hS
  have hrelL : 3 * FL.coeff (-1) = 2 * AL.coeff (-2) * BL.coeff 1 := by
    rw [← hcs F (-1), ← hcs A (-2), ← hcs B 1, hFmap]
    exact hrel
  have hterminalL : 2 * AL.coeff (-2) * CL.coeff 1 +
      9 * GLa.coeff (-1) = 0 := by
    rw [← hcs A (-2), ← hcs C 1, ← hcs G (-1), hCmap, hGmap]
    exact hterminal
  have hfollowingL : 3 * FL.coeff 0 =
      2 * (AL.coeff (-1) * BL.coeff 1 + AL.coeff (-2) * BL.coeff 2) := by
    rw [← hcs F 0, ← hcs A (-1), ← hcs B 1,
      ← hcs A (-2), ← hcs B 2, hFmap]
    exact hfollowing
  have hterm := rhoOneMainTangentTerminal_coeff_negFour_fNegOne68
    T.source.gamma T.source.epsilon AL BL CL FL GLa dAL dBL dCL dFL dGL
      hAL hBL hCL hFL hGL hdAL hdBL hdCL hdFL hdGL hdAcoL hS0L
      hrelL hterminalL hfollowingL
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
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-4) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [T.terminal_order]
      exact WithTop.coe_lt_coe.mpr (by norm_num))
  have hzeroL : (ratFuncAtLaurent46 T.root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-4) = 0 := by
    rw [← hcs (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) (-4)]
    exact hzeroH
  have hleft := congrArg (fun X : LaurentSeries k => X.coeff (-4)) hsparseL'
  rw [hterm, hzeroL] at hleft
  have hBne : BL.coeff 1 ≠ 0 := by
    rw [← hcs B 1]
    dsimp only [B]
    exact hb
  have hAneL : AL.coeff (-2) ≠ 0 := by
    rw [← hcs A (-2)]
    exact hAne
  have hscale : (2 / 81 : k) * AL.coeff (-2) ^ 2 * BL.coeff 1 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hAneL)) hBne
  have hnewL : 8 * AL.coeff (-1) * CL.coeff 1 +
      8 * AL.coeff (-2) * CL.coeff 2 + 27 * T.source.epsilon +
      36 * GLa.coeff 0 = 0 :=
    (mul_eq_zero.mp hleft).resolve_left hscale
  have hnew := hnewL
  simp only [AL, BL, CL, FL, GLa, ← hcs A (-1), ← hcs A (-2),
    ← hcs C 1, ← hcs C 2, ← hcs G 0] at hnew
  rw [hCmap, hGmap] at hnew
  have hthree := rhoOne_boundaryF_terminalFour_final_cross68
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff 1)
    ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (-1))
    ((rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
    T.source.epsilon i4
    (by simpa only [A] using hAne)
    hb hnew hrel hs1 hold
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryMinor68]
  exact ⟨R, hnew, hthree⟩

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundarySelectors_terminal_minor
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareFNegOneBoundaryTerminalFollowing68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0)) :
    RhoOneAlignedSquareFNegOneBoundaryMinor68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryMinor68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0) := by
  rcases R with hF | hG | hbox
  · exact Or.inl (T.rhoOne_boundaryF_minor68 hp hH hp6 hp5 hp4 hF)
  · exact Or.inr (Or.inl (T.rhoOne_boundaryG_minor68 hG))
  · exact Or.inr (Or.inr hbox)

end AlignedSquareBoundarySelectorsTerminalMinor68

end Max11DegreeRoutes
