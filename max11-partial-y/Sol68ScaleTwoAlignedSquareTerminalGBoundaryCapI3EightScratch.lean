import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapDerivativeNextScratch
import Fable68ScaleTwoAlignedSquareC2BranchScratch

/-! # The `I₃[8]` jet above the terminal cap -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapI3Eight68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapI3EightHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The coefficient two integral jet above the lower face of a Laurent
product. -/
theorem laurent_coeff_mul_lower_two68
    (X Y : LaurentSeries k) (m n : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
    (X * Y).coeff (m + n + 2) =
      X.coeff m * Y.coeff (n + 2) +
        X.coeff (m + 1) * Y.coeff (n + 1) +
          X.coeff (m + 2) * Y.coeff n := by
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
  have htail := laurent_coeff_mul_lower_succ68 Xt Y (m + 1) n hXt hY
  have htail' : (Xt * Y).coeff (m + n + 2) =
      Xt.coeff (m + 1) * Y.coeff (n + 1) +
        Xt.coeff (m + 2) * Y.coeff n := by
    convert htail using 1 <;> ring
  have hXt1 : Xt.coeff (m + 1) = X.coeff (m + 1) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hXt2 : Xt.coeff (m + 2) = X.coeff (m + 2) := by
    simp only [Xt, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega)]
    ring
  have hlead :
      ((HahnSeries.single m (X.coeff m) : LaurentSeries k) * Y).coeff
          (m + n + 2) = X.coeff m * Y.coeff (n + 2) := by
    rw [HahnSeries.coeff_single_mul]
    have hi : m + n + 2 - m = n + 2 := by omega
    rw [hi]
  have hXdec : X = HahnSeries.single m (X.coeff m) + Xt := by simp [Xt]
  calc
    (X * Y).coeff (m + n + 2) =
        ((HahnSeries.single m (X.coeff m) + Xt) * Y).coeff
          (m + n + 2) := by rw [← hXdec]
    _ = _ := by
      rw [add_mul, HahnSeries.coeff_add, hlead, htail', hXt1, hXt2]
      ring

/-- Exact coefficient eight of the third first integral at the cap. -/
theorem rhoOneI3CapFactored_cap_coeff_eight68
    (root gamma epsilon i3 : k) (A B C F G : RatFunc k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(11 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root G).orderTop)
    (hS : (↑(7 : ℚ) : WithTop ℚ) ≤
      (2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma)).orderTop)
    (hfactor : rhoOneI3CapFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) A B C F G = RatFunc.C i3) :
    4 * ((ratFuncAtHahn46 root C).coeff (7 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (1 : ℚ) +
        (ratFuncAtHahn46 root C).coeff (8 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
        (ratFuncAtHahn46 root C).coeff (9 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (-1 : ℚ) +
        (ratFuncAtHahn46 root F).coeff (3 : ℚ) *
          (ratFuncAtHahn46 root F).coeff (5 : ℚ)) +
      2 * (ratFuncAtHahn46 root F).coeff (4 : ℚ) ^ 2 +
      3 * epsilon * (ratFuncAtHahn46 root C).coeff (8 : ℚ) = 0 := by
  let AL : LaurentSeries k := ratFuncAtLaurent46 root A
  let BL : LaurentSeries k := ratFuncAtLaurent46 root B
  let CL : LaurentSeries k := ratFuncAtLaurent46 root C
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let SR : RatFunc k := 2 * C + RatFunc.C (3 * gamma)
  let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * gamma)
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root A (-2) hA
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 11 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 3 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-1) hG
  have hSRH : ratFuncAtHahn46 root SR =
      2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma) := by
    dsimp only [SR]
    simp only [map_add, map_mul, map_ofNat, ratFuncAtHahn46_C]
  have hSRL : ratFuncAtLaurent46 root SR = SL := by
    dsimp only [SR, SL, CL]
    simp only [map_add, map_mul, map_ofNat, ratFuncAtLaurent46_C68]
  have hSL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root SR 7 (by
    rw [hSRH]
    exact hS)
  rw [hSRL] at hSL
  have hSG := laurent_coeff_mul_lower_two68 SL Gser 7 (-1) hSL hGL
  have hFF := laurent_coeff_mul_lower_two68 FL FL 3 3 hFL hFL
  norm_num at hSG hFF
  have hAB : (↑(9 : ℤ) : WithTop ℤ) ≤ (AL * BL).orderTop := by
    have h := le_trans (add_le_add hAL hBL) HahnSeries.orderTop_add_le_mul
    norm_num at h ⊢
    exact h
  have hABFOrder : (↑(12 : ℤ) : WithTop ℤ) ≤ (AL * BL * FL).orderTop := by
    have h := le_trans (add_le_add hAB hFL) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hzABF : (AL * BL * FL).coeff (8 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hABFOrder)
  have hzABF' : (AL * (BL * FL)).coeff (8 : ℤ) = 0 := by
    rw [← mul_assoc]
    exact hzABF
  have hBBOrder : (↑(22 : ℤ) : WithTop ℤ) ≤ (BL * BL).orderTop := by
    have h := le_trans (add_le_add hBL hBL) HahnSeries.orderTop_add_le_mul
    convert h using 1 <;> norm_num
  have hBBCOrder : (↑(22 : ℤ) : WithTop ℤ) ≤
      (BL * BL * CL).orderTop := by
    exact le_trans (add_le_add hBBOrder hCL) HahnSeries.orderTop_add_le_mul
  have hzBBC : (BL * BL * CL).coeff (8 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBBCOrder)
  have hzBBC' : (BL * (BL * CL)).coeff (8 : ℤ) = 0 := by
    rw [← mul_assoc]
    exact hzBBC
  have hzBB : (BL ^ 2).coeff (8 : ℤ) = 0 := by
    rw [pow_two]
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBBOrder)
  have hfactorL := congrArg (ratFuncAtLaurent46 root) hfactor
  have hfactorL' : rhoOneI3CapFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) AL BL CL FL Gser =
        HahnSeries.C i3 := by
    simpa only [rhoOneI3CapFactored68, AL, BL, CL, FL, Gser, map_add,
      map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_one,
      ratFuncAtLaurent46_C68] using hfactorL
  have hSLform : 2 * CL + 3 * HahnSeries.C gamma = SL := by
    dsimp only [SL]
    congr 1
    rw [HahnSeries.C_eq_algebraMap, map_mul, map_ofNat]
  rw [rhoOneI3CapFactored68, hSLform] at hfactorL'
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (8 : ℤ)) hfactorL'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub] at hc
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hs1 : ((-8 / 9 : LaurentSeries k) * AL * BL * FL).coeff 8 = 0 := by
    have hcst : (-8 / 9 : LaurentSeries k) = HahnSeries.C (-8 / 9 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
    rw [mul_assoc, mul_assoc, hcst, hscale, hzABF', mul_zero]
  have hs2 : ((8 / 9 : LaurentSeries k) * BL ^ 2 * CL).coeff 8 = 0 := by
    have hcst : (8 / 9 : LaurentSeries k) = HahnSeries.C (8 / 9 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [pow_two, mul_assoc, mul_assoc, hcst, hscale, hzBBC', mul_zero]
  have hs3 : ((4 / 3 : LaurentSeries k) * SL * Gser).coeff 8 =
      (4 / 3 : k) * (SL * Gser).coeff 8 := by
    have hcst : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [mul_assoc, hcst, hscale]
  have hs4 : ((4 / 3 : LaurentSeries k) * FL ^ 2).coeff 8 =
      (4 / 3 : k) * (FL * FL).coeff 8 := by
    have hcst : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [pow_two, hcst, hscale]
  have hs5 : ((2 / 3 : LaurentSeries k) * HahnSeries.C gamma * BL ^ 2).coeff 8 =
      0 := by
    have hcst : (2 / 3 : LaurentSeries k) * HahnSeries.C gamma =
        HahnSeries.C ((2 / 3 : k) * gamma) := by
      have h23 : (2 / 3 : LaurentSeries k) = HahnSeries.C (2 / 3 : k) := by
        rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
      rw [h23, ← map_mul]
    rw [hcst, hscale, hzBB, mul_zero]
  have hs6 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * CL).coeff 8 =
      (2 * epsilon) * CL.coeff 8 := by
    have hcst : (2 : LaurentSeries k) * HahnSeries.C epsilon =
        HahnSeries.C (2 * epsilon) := by
      have h2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
        rw [HahnSeries.C_eq_algebraMap, map_ofNat]
      rw [h2, ← map_mul]
    rw [hcst, hscale]
  have hright : (HahnSeries.C i3 : LaurentSeries k).coeff 8 = 0 := by
    simp [HahnSeries.C_apply]
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hright, hSG, hFF] at hc
  have hSL7 : SL.coeff 7 = 2 * CL.coeff 7 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL8 : SL.coeff 8 = 2 * CL.coeff 8 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL9 : SL.coeff 9 = 2 * CL.coeff 9 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL7, hSL8, hSL9] at hc
  have hC7 := ratFuncAtHahn46_coeff_int68 root C 7
  have hC8 := ratFuncAtHahn46_coeff_int68 root C 8
  have hC9 := ratFuncAtHahn46_coeff_int68 root C 9
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hF5 := ratFuncAtHahn46_coeff_int68 root F 5
  have hGm1 := ratFuncAtHahn46_coeff_int68 root G (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  norm_num at hC7 hC8 hC9 hF3 hF4 hF5 hGm1 hG0 hG1
  dsimp only [CL, FL, Gser] at hc
  rw [← hC7, ← hC8, ← hC9, ← hF3, ← hF4, ← hF5,
    ← hGm1, ← hG0, ← hG1] at hc
  linear_combination (3 / 2 : k) * hc

/-- Eliminating epsilon and `G[0]` between `I₃[7]` and `I₃[8]`
leaves the scale-free second jet. -/
theorem rhoOneI3_cap_eight_scale_free68
    (c c' c'' f f' f'' g g' g'' epsilon : k)
    (hseven : 4 * (c * g' + c' * g + f * f') + 3 * epsilon * c = 0)
    (height : 4 * (c * g'' + c' * g' + c'' * g + f * f'') +
      2 * f' ^ 2 + 3 * epsilon * c' = 0) :
    2 * c * (c * g'' + c'' * g + f * f'') + c * f' ^ 2 -
      2 * c' * (c' * g + f * f') = 0 := by
  linear_combination (1 / 2 : k) * c * height -
    (1 / 2 : k) * c' * hseven

/-- The source-sensitive cap packet augmented by `I₃[8]` and its
epsilon/`G[0]`-free second jet. -/
def RhoOneDoubleZeroTerminalGBoundaryCapI3EightPacket68
    (gamma epsilon i3 s source : k)
    (A B C F G dA : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextPacket68
      gamma epsilon i3 s source A B C F G dA ∧
    4 * (C.coeff (7 : ℚ) * G.coeff (1 : ℚ) +
          C.coeff (8 : ℚ) * G.coeff (0 : ℚ) +
          C.coeff (9 : ℚ) * G.coeff (-1 : ℚ) +
          F.coeff (3 : ℚ) * F.coeff (5 : ℚ)) +
        2 * F.coeff (4 : ℚ) ^ 2 +
      3 * epsilon * C.coeff (8 : ℚ) = 0 ∧
    2 * C.coeff (7 : ℚ) *
          (C.coeff (7 : ℚ) * G.coeff (1 : ℚ) +
            C.coeff (9 : ℚ) * G.coeff (-1 : ℚ) +
            F.coeff (3 : ℚ) * F.coeff (5 : ℚ)) +
        C.coeff (7 : ℚ) * F.coeff (4 : ℚ) ^ 2 -
      2 * C.coeff (8 : ℚ) *
        (C.coeff (8 : ℚ) * G.coeff (-1 : ℚ) +
          F.coeff (3 : ℚ) * F.coeff (4 : ℚ)) = 0

/-- Consolidation of the source derivative cap with the independently
closed `C[2]≠0` child. -/
def RhoOneDoubleZeroTerminalGBoundaryCapI3EightResidual68
    (root j gamma epsilon : k) (A0 : k[X])
    (h0R AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextResidual68
      root j gamma epsilon A0 h0R AR BR CR FR GR A B C F G ∧
    RhoOneDoubleZeroTerminalGBoundaryCapC2BranchResidual68
      root j gamma epsilon h0R BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧
        2 * C.coeff (0 : ℚ) + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 s : k, RhoOneDoubleZeroTerminalGBoundaryCapI3EightPacket68
        gamma epsilon i3 s (A0.derivative.eval root) A B C F G
          (ratFuncAtHahn46 root (Differential.deriv AR)))

/-- Literal source backwire of `I₃[8]`, while retaining the independent
`C[2]` deletion and every non-cap sibling. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapI3EightResidual
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
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
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
    let C := rhoOneCDefectHahn68 A
      (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroTerminalGBoundaryCapI3EightResidual68
        T.root j T.source.gamma T.source.epsilon
        (localClearedA68RhoOne g u)
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapI3EightResidual68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hGne | ⟨hGzero, hG0, htail⟩
  · have hderivRaw :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapDerivativeNextResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    have hc2Raw :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapC2BranchResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    rcases hderivRaw with hderiv | hbad
    · rcases hc2Raw with hc2res | hbad2
      · left
        refine ⟨hderiv, hc2res, ?_⟩
        intro hcoord hc1 hc2
        obtain ⟨i3, s, hpacket⟩ := hderiv.2 hcoord hc1 hc2
        have hparts := hpacket
        dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextPacket68,
          RhoOneDoubleZeroTerminalGBoundaryCapTerminalNextPacket68,
          RhoOneDoubleZeroTerminalGBoundaryCapNextJetPacket68,
          RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68] at hparts
        rcases hparts with
          ⟨⟨⟨⟨hi3H, hc3, hc4, hc5, hc6, hb7, hb8, hb9, hb10,
              hS7, hB11, hcap3, hc7ne, hcap4, hb11ne, hBexact⟩,
            hscalar, hrow7, hrow4, htransport⟩,
            hterminal, hdependency⟩,
          hs, hsource, hsourceScalar⟩
        have hfinite := hderiv.1.1.1.1.1.1
        dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68]
          at hfinite
        rcases hfinite with ⟨hfact, hboundary | hrays⟩
        · rcases hboundary with ⟨hcurrent, hf2, hF3, hb4, hB5,
            hi4three, hf3ne⟩
          let AR : RatFunc k := T.source.A
          let BR : RatFunc k := T.source.B
          let CR : RatFunc k :=
            T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
          let FR : RatFunc k :=
            T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
          let GR : RatFunc k :=
            (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
              RatFunc.C (1 / 3 : k) * AR * CR
          have hCRmap : ratFuncAtHahn46 T.root CR =
              rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0) := by
            dsimp only [CR, AR, rhoOneCDefectHahn68]
            simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
          have hFRmap : ratFuncAtHahn46 T.root FR =
              rhoOneTangentDDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.B)
                (ratFuncAtHahn46 T.root T.source.D) := by
            dsimp only [FR, AR, BR, rhoOneTangentDDefectHahn68]
            simp only [map_sub, map_mul, ratFuncAtHahn46_C]
          have hGRmap : ratFuncAtHahn46 T.root GR =
              rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E)) := by
            dsimp only [GR, CR, AR, rhoOneTangentEDefectHahn68,
              rhoOneCDefectHahn68, rhoOneEDefectHahn68]
            simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
          have hbounds := P.2.1
          dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
          have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
              (ratFuncAtHahn46 T.root AR).orderTop := by
            simpa only [AR] using hbounds.1
          have hi3R : rhoOneI3CapFactored68
              (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
              AR BR CR FR GR = RatFunc.C i3 := by
            apply ratFuncAtHahn46_injective T.root
            simpa only [rhoOneI3CapFactored68, map_add, map_sub, map_mul,
              map_pow, map_neg, map_div₀, map_ofNat, map_one,
              ratFuncAtHahn46_C, hCRmap, hFRmap, hGRmap, AR, BR] using hi3H
          have hrow8raw := rhoOneI3CapFactored_cap_coeff_eight68
            T.root T.source.gamma T.source.epsilon i3 AR BR CR FR GR
            hAH (by simpa only [BR] using hB11)
            (by rw [hCRmap]; exact hC) (by rw [hFRmap]; exact hF3)
            (by rw [hGRmap]; exact hG) (by rw [hCRmap]; exact hS7) hi3R
          rw [hCRmap, hFRmap, hGRmap] at hrow8raw
          have hrow8 := by simpa only [AR, BR] using hrow8raw
          have hscaleFree := rhoOneI3_cap_eight_scale_free68
            ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff (7 : ℚ))
            ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff (8 : ℚ))
            ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff (9 : ℚ))
            ((rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff (3 : ℚ))
            ((rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff (4 : ℚ))
            ((rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff (5 : ℚ))
            ((rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ))
            ((rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff (0 : ℚ))
            ((rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff (1 : ℚ))
            T.source.epsilon hrow7 hrow8
          refine ⟨i3, s, ?_⟩
          dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapI3EightPacket68]
          exact ⟨hpacket, hrow8, hscaleFree⟩
        · exact (hrays.1 hcoord.1).elim
      · exact (hGne hbad2.1).elim
    · exact (hGne hbad.1).elim
  · right
    refine ⟨hGzero, hG0, ?_⟩
    have hres :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalBGainResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only [RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68] at hres
    rcases hres with hbad | ⟨_, _, htail'⟩
    · exact (hbad hGzero).elim
    · exact htail'

end AlignedSquareTerminalGBoundaryCapI3Eight68

end Max11DegreeRoutes
