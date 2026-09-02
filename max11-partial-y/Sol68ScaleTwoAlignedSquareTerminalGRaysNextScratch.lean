import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapKSourceOrderScratch

/-! # The first unused fourth-integral jet on the two nonzero `G[-1]` rays -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGRaysNext68

variable {k : Type*} [Field k] [CharZero k]

local instance terminalGRaysNextLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

/-- The constant and linear coefficients of the globally zero fourth-integral
factor on the unraised `B,S,F,G` orders.  The second row is the first row not
retained by the earlier quadratic-wall packet. -/
theorem rhoOneI4ZeroFactored_ray_firstRows68
    (root gamma epsilon : k) (B C F G : RatFunc k)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hfactor : rhoOneI4ZeroFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = 0) :
    let BH := ratFuncAtHahn46 root B
    let CH := ratFuncAtHahn46 root C
    let FH := ratFuncAtHahn46 root F
    let GH := ratFuncAtHahn46 root G
    (2 * CH.coeff 0 + 3 * gamma) * FH.coeff 0 +
        2 * BH.coeff 1 * GH.coeff (-1) = 0 ∧
      4 * (BH.coeff 1 * GH.coeff 0 + BH.coeff 2 * GH.coeff (-1)) +
        2 * ((2 * CH.coeff 0 + 3 * gamma) * FH.coeff 1 +
          2 * CH.coeff 1 * FH.coeff 0) +
        3 * epsilon * BH.coeff 1 = 0 := by
  dsimp only
  let BL : LaurentSeries k := ratFuncAtLaurent46 root B
  let CL : LaurentSeries k := ratFuncAtLaurent46 root C
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let SR : RatFunc k := 2 * C + RatFunc.C (3 * gamma)
  let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * gamma)
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 1 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 0 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-1) hG
  have hSRH : ratFuncAtHahn46 root SR =
      2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma) := by
    dsimp only [SR]
    simp only [map_add, map_mul, map_ofNat, ratFuncAtHahn46_C]
  have hSRL : ratFuncAtLaurent46 root SR = SL := by
    dsimp only [SR, SL, CL]
    simp only [map_add, map_mul, map_ofNat, ratFuncAtLaurent46_C68]
  have hSH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root SR).orderTop := by
    rw [hSRH]
    apply hahnOrderTop_add_nonneg46
    · exact hahnOrderTop_mul_nonneg46 2 (ratFuncAtHahn46 root C)
        (by simpa only [map_ofNat] using
          hahnOrderTop_C_nonneg46 (k := k) (2 : k)) hC
    · exact hahnOrderTop_C_nonneg46 _
  have hSL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root SR 0 hSH
  rw [hSRL] at hSL
  have hBG0 := laurent_coeff_mul_lower68 BL Gser 1 (-1) hBL hGL
  have hBG1 := laurent_coeff_mul_lower_succ68 BL Gser 1 (-1) hBL hGL
  have hSF0 := laurent_coeff_mul_lower68 SL FL 0 0 hSL hFL
  have hSF1 := laurent_coeff_mul_lower_succ68 SL FL 0 0 hSL hFL
  norm_num at hBG0 hBG1 hSF0 hSF1
  have hBcubeOrder : (↑(3 : ℤ) : WithTop ℤ) ≤ (BL ^ 3).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow (x := BL) (n := 3)
    have htriple := nsmul_le_nsmul_right hBL 3
    norm_num at htriple
    exact le_trans htriple hp
  have hBcube0 : (BL ^ 3).coeff (0 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBcubeOrder)
  have hBcube1 : (BL ^ 3).coeff (1 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBcubeOrder)
  have hB0 : BL.coeff (0 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBL)
  have hfactorL := congrArg (ratFuncAtLaurent46 root) hfactor
  have hfactorL' : rhoOneI4ZeroFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) BL CL FL Gser = 0 := by
    simpa only [rhoOneI4ZeroFactored68, BL, CL, FL, Gser, map_add,
      map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtLaurent46_C68] using hfactorL
  have hSLform : 2 * CL + 3 * HahnSeries.C gamma = SL := by
    dsimp only [SL]
    congr 1
    rw [HahnSeries.C_eq_algebraMap, map_mul, map_ofNat]
  rw [rhoOneI4ZeroFactored68, hSLform] at hfactorL'
  have hc0 := congrArg (fun X : LaurentSeries k => X.coeff (0 : ℤ)) hfactorL'
  have hc1 := congrArg (fun X : LaurentSeries k => X.coeff (1 : ℤ)) hfactorL'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at hc0 hc1
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hc83 : (8 / 3 : LaurentSeries k) = HahnSeries.C (8 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc43 : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hsc1 (r : ℤ) :
      ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff r =
        (-8 / 27 : k) * (BL ^ 3).coeff r := by
    have hc : (-8 / 27 : LaurentSeries k) =
        HahnSeries.C (-8 / 27 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat,
        map_ofNat]
    rw [hc, hscale]
  have hsc2 (r : ℤ) :
      ((8 / 3 : LaurentSeries k) * BL * Gser).coeff r =
        (8 / 3 : k) * (BL * Gser).coeff r := by
    rw [mul_assoc, hc83, hscale]
  have hsc3 (r : ℤ) :
      ((4 / 3 : LaurentSeries k) * SL * FL).coeff r =
        (4 / 3 : k) * (SL * FL).coeff r := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 (r : ℤ) :
      ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff r =
        (2 * epsilon) * BL.coeff r := by
    have h2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h2, ← map_mul, hscale]
  rw [hsc1, hBcube0, mul_zero, hsc2, hsc3, hsc4,
    hBG0, hSF0, hB0] at hc0
  rw [hsc1, hBcube1, mul_zero, hsc2, hsc3, hsc4,
    hBG1, hSF1] at hc1
  have hSL0 : SL.coeff 0 = 2 * CL.coeff 0 + 3 * gamma := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL1 : SL.coeff 1 = 2 * CL.coeff 1 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0] at hc0
  rw [hSL0, hSL1] at hc1
  have hB1 := ratFuncAtHahn46_coeff_int68 root B 1
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hF0 := ratFuncAtHahn46_coeff_int68 root F 0
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hGm1 := ratFuncAtHahn46_coeff_int68 root G (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  norm_num at hB1 hB2 hC0 hC1 hF0 hF1 hGm1 hG0
  dsimp only [BL, CL, FL, Gser] at hc0 hc1
  rw [← hB1, ← hC0, ← hF0, ← hGm1] at hc0
  rw [← hB1, ← hB2, ← hC0, ← hC1,
    ← hF0, ← hF1, ← hGm1, ← hG0] at hc1
  constructor
  · linear_combination (3 / 4 : k) * hc0
  · linear_combination (3 / 2 : k) * hc1

/-- Both square-root rays share one sign-parametric terminal relation and one
sign-parametric next jet. -/
theorem rhoOneDoubleZero_gRay_nextScalar68
    (sigma r b s f g b2 g0 c1 f1 epsilon : k)
    (hsigma : sigma ^ 2 = 1)
    (hb : b ≠ 0)
    (hray : 3 * s = 2 * sigma * r * b)
    (hterminal : s * f + 2 * b * g = 0)
    (hnext : 4 * (b * g0 + b2 * g) +
      2 * (s * f1 + 2 * c1 * f) + 3 * epsilon * b = 0) :
    r * f + 3 * sigma * g = 0 ∧
      12 * b * g0 - 4 * sigma * r * b2 * f +
        4 * sigma * r * b * f1 + 12 * c1 * f +
        9 * epsilon * b = 0 := by
  have hlinmul : 2 * b * (r * f + 3 * sigma * g) = 0 := by
    calc
      2 * b * (r * f + 3 * sigma * g) =
          3 * sigma * (s * f + 2 * b * g) := by
        linear_combination (-sigma * f) * hray - 2 * r * b * f * hsigma
      _ = 0 := by rw [hterminal]; ring
  have hlin : r * f + 3 * sigma * g = 0 :=
    (mul_eq_zero.mp hlinmul).resolve_left (mul_ne_zero (by norm_num) hb)
  refine ⟨hlin, ?_⟩
  linear_combination 3 * hnext - 4 * b2 * sigma * hlin -
    2 * f1 * hray + 12 * b2 * g * hsigma

/-- The exact residual after refining branch I(a).  The deep boundary cap is
retained verbatim, while both nonzero rays carry the same signed next jet. -/
def RhoOneDoubleZeroTerminalGRaysNextPacket68
    (gamma epsilon : k) (A B C F G : HahnSeries ℚ k) : Prop :=
  ((B.coeff 1 = 0 ∧ 2 * C.coeff 0 + 3 * gamma = 0) ∧
      (B.coeff 2 * G.coeff (-1) + C.coeff 1 * F.coeff 0 = 0)) ∨
    (B.coeff 1 ≠ 0 ∧ 2 * C.coeff 0 + 3 * gamma ≠ 0 ∧
      ∃ r sigma : k, r ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
        sigma ^ 2 = 1 ∧
        3 * (2 * C.coeff 0 + 3 * gamma) =
          2 * sigma * r * B.coeff 1 ∧
        r * F.coeff 0 + 3 * sigma * G.coeff (-1) = 0 ∧
        12 * B.coeff 1 * G.coeff 0 -
            4 * sigma * r * B.coeff 2 * F.coeff 0 +
            4 * sigma * r * B.coeff 1 * F.coeff 1 +
            12 * C.coeff 1 * F.coeff 0 +
            9 * epsilon * B.coeff 1 = 0)

/-- Source-facing branch inventory: branch I(a) is strictly refined, the
highest boundary cap is unchanged, and the active `G[-1]=0` sibling remains
literal. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGRaysNextResidual
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
    let A0 := localClearedA68RhoOne g u
    let B0 := localClearedB68RhoOne g u (p.coeff 3)
    let C00 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    let D0 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
      (p.coeff 1)
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    ((RhoOneDoubleZeroTerminalGBoundaryCapKSourceOrderResidual68
          T.root j T.source.gamma T.source.epsilon h0 A0 B0 C00 D0
          (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∧
        rhoOneI4ZeroFactored68 (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.epsilon) BR CR FR GR = 0 ∧
        RhoOneDoubleZeroTerminalGRaysNextPacket68
          T.source.gamma T.source.epsilon A B C F G) ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F))) := by
  dsimp only
  have hcap :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapKSourceOrderResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hcap with hcap | hzero
  · have hnext :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGI4NextResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only at hnext
    rcases hnext with ⟨hfactor, hshape⟩ | hzero
    · left
      refine ⟨hcap, hfactor, ?_⟩
      rcases hshape with ⟨⟨hb1, hS0⟩, _, _, hboundary⟩ | hrays
      · exact Or.inl ⟨⟨hb1, hS0⟩, hboundary⟩
      · right
        rcases hrays with ⟨hb1, hS0, r, hr0, hr2, hray⟩
        let CR : RatFunc k := T.source.C0 -
          RatFunc.C (1 / 3 : k) * T.source.A ^ 2
        let FR : RatFunc k := T.source.D -
          RatFunc.C (1 / 3 : k) * T.source.A * T.source.B
        let GR : RatFunc k :=
          (T.source.E - RatFunc.C (1 / 27 : k) * T.source.A ^ 3) -
            RatFunc.C (1 / 3 : k) * T.source.A * CR
        have hCRmap : ratFuncAtHahn46 T.root CR =
            rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0) := by
          dsimp only [CR, rhoOneCDefectHahn68]
          simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
        have hFRmap : ratFuncAtHahn46 T.root FR =
            rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D) := by
          dsimp only [FR, rhoOneTangentDDefectHahn68]
          simp only [map_sub, map_mul, ratFuncAtHahn46_C]
        have hGRmap : ratFuncAtHahn46 T.root GR =
            rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E)) := by
          dsimp only [GR, CR, rhoOneTangentEDefectHahn68,
            rhoOneCDefectHahn68, rhoOneEDefectHahn68]
          simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
        have hrows := rhoOneI4ZeroFactored_ray_firstRows68
          T.root T.source.gamma T.source.epsilon T.source.B CR FR GR
          hB (by rw [hCRmap]; exact hC) (by rw [hFRmap]; exact hF)
          (by rw [hGRmap]; exact hG) (by simpa only [CR, FR, GR] using hfactor)
        dsimp only at hrows
        rw [hCRmap, hFRmap, hGRmap] at hrows
        rcases hrows with ⟨hterminal, hrow1⟩
        rcases hray with hray | hray
        · refine ⟨hb1, hS0, r, (1 : k), hr0, hr2, by norm_num,
              by simpa using hray, ?_⟩
          have hsigned := rhoOneDoubleZero_gRay_nextScalar68
            (sigma := (1 : k)) (r := r)
            (b := (ratFuncAtHahn46 T.root T.source.B).coeff 1)
            (s := 2 * (rhoOneCDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 0 +
                3 * T.source.gamma)
            (f := (rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
            (g := (rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
            (b2 := (ratFuncAtHahn46 T.root T.source.B).coeff 2)
            (g0 := (rhoOneTangentEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
            (c1 := (rhoOneCDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
            (f1 := (rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
            (epsilon := T.source.epsilon) (by norm_num) hb1
            (by simpa using hray) hterminal hrow1
          simpa using hsigned
        · refine ⟨hb1, hS0, r, (-1 : k), hr0, hr2, by norm_num,
              ?_, ?_⟩
          · simpa using hray
          · have hsigned := rhoOneDoubleZero_gRay_nextScalar68
              (sigma := (-1 : k)) (r := r)
              (b := (ratFuncAtHahn46 T.root T.source.B).coeff 1)
              (s := 2 * (rhoOneCDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0)).coeff 0 +
                  3 * T.source.gamma)
              (f := (rhoOneTangentDDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.B)
                (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
              (g := (rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
              (b2 := (ratFuncAtHahn46 T.root T.source.B).coeff 2)
              (g0 := (rhoOneTangentEDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0))
                (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
              (c1 := (rhoOneCDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
              (f1 := (rhoOneTangentDDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.B)
                (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
              (epsilon := T.source.epsilon) (by norm_num) hb1
              (by simpa using hray) hterminal hrow1
            simpa using hsigned
    · exact Or.inr hzero
  · exact Or.inr hzero

end AlignedSquareTerminalGRaysNext68

end Max11DegreeRoutes
