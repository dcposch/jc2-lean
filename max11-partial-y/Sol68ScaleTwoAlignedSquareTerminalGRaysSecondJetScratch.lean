import Sol68ScaleTwoAlignedSquareTerminalGRaysNextScratch

/-! # Coefficient two of the zero fourth-integral factor on the two rays -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGRaysSecondJet68

variable {k : Type*} [Field k] [CharZero k]

local instance terminalGRaysSecondJetLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

/-- Coefficient two is the next available source-independent row of the
zero fourth-integral factor.  The general terminal coefficient at the ray
orders has no earlier source-facing specialization in the existing stack. -/
theorem rhoOneI4ZeroFactored_ray_coeff_two68
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
    4 * (BH.coeff 1 * GH.coeff 1 + BH.coeff 2 * GH.coeff 0 +
        BH.coeff 3 * GH.coeff (-1)) +
      2 * ((2 * CH.coeff 0 + 3 * gamma) * FH.coeff 2 +
        2 * CH.coeff 1 * FH.coeff 1 + 2 * CH.coeff 2 * FH.coeff 0) +
      3 * epsilon * BH.coeff 2 = 0 := by
  dsimp only
  let BL : LaurentSeries k := ratFuncAtLaurent46 root B
  let CL : LaurentSeries k := ratFuncAtLaurent46 root C
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let SR : RatFunc k := 2 * C + RatFunc.C (3 * gamma)
  let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * gamma)
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 1 hB
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
  have hBG := laurent_coeff_mul_lower_two68 BL Gser 1 (-1) hBL hGL
  have hSF := laurent_coeff_mul_lower_two68 SL FL 0 0 hSL hFL
  norm_num at hBG hSF
  have hBcubeOrder : (↑(3 : ℤ) : WithTop ℤ) ≤ (BL ^ 3).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow (x := BL) (n := 3)
    have htriple := nsmul_le_nsmul_right hBL 3
    norm_num at htriple
    exact le_trans htriple hp
  have hBcube : (BL ^ 3).coeff (2 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBcubeOrder)
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
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (2 : ℤ)) hfactorL'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at hc
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hsc1 : ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff 2 =
      (-8 / 27 : k) * (BL ^ 3).coeff 2 := by
    have hs : (-8 / 27 : LaurentSeries k) =
        HahnSeries.C (-8 / 27 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat,
        map_ofNat]
    rw [hs, hscale]
  have hsc2 : ((8 / 3 : LaurentSeries k) * BL * Gser).coeff 2 =
      (8 / 3 : k) * (BL * Gser).coeff 2 := by
    have hs : (8 / 3 : LaurentSeries k) = HahnSeries.C (8 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [mul_assoc, hs, hscale]
  have hsc3 : ((4 / 3 : LaurentSeries k) * SL * FL).coeff 2 =
      (4 / 3 : k) * (SL * FL).coeff 2 := by
    have hs : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [mul_assoc, hs, hscale]
  have hsc4 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff 2 =
      (2 * epsilon) * BL.coeff 2 := by
    have h2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_ofNat]
    rw [h2, ← map_mul, hscale]
  rw [hsc1, hBcube, mul_zero, hsc2, hsc3, hsc4, hBG, hSF] at hc
  have hSL0 : SL.coeff 0 = 2 * CL.coeff 0 + 3 * gamma := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL1 : SL.coeff 1 = 2 * CL.coeff 1 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  have hSL2 : SL.coeff 2 = 2 * CL.coeff 2 := by
    dsimp only [SL]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSL0, hSL1, hSL2] at hc
  have hB1 := ratFuncAtHahn46_coeff_int68 root B 1
  have hB2 := ratFuncAtHahn46_coeff_int68 root B 2
  have hB3 := ratFuncAtHahn46_coeff_int68 root B 3
  have hC0 := ratFuncAtHahn46_coeff_int68 root C 0
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hF0 := ratFuncAtHahn46_coeff_int68 root F 0
  have hF1 := ratFuncAtHahn46_coeff_int68 root F 1
  have hF2 := ratFuncAtHahn46_coeff_int68 root F 2
  have hGm1 := ratFuncAtHahn46_coeff_int68 root G (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  have hG1 := ratFuncAtHahn46_coeff_int68 root G 1
  norm_num at hB1 hB2 hB3 hC0 hC1 hC2 hF0 hF1 hF2 hGm1 hG0 hG1
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB1, ← hB2, ← hB3, ← hC0, ← hC1, ← hC2,
    ← hF0, ← hF1, ← hF2, ← hGm1, ← hG0, ← hG1] at hc
  linear_combination (3 / 2 : k) * hc

/-- Signed elimination of the old terminal variables from coefficient two. -/
theorem rhoOneDoubleZero_gRay_secondScalar68
    (sigma r b s f g b2 b3 g0 g1 c1 c2 f1 f2 epsilon : k)
    (hsigma : sigma ^ 2 = 1)
    (hray : 3 * s = 2 * sigma * r * b)
    (hlinear : r * f + 3 * sigma * g = 0)
    (hrow : 4 * (b * g1 + b2 * g0 + b3 * g) +
      2 * (s * f2 + 2 * c1 * f1 + 2 * c2 * f) +
      3 * epsilon * b2 = 0) :
    12 * b * g1 + 12 * b2 * g0 - 4 * sigma * r * b3 * f +
      4 * sigma * r * b * f2 + 12 * c1 * f1 + 12 * c2 * f +
      9 * epsilon * b2 = 0 := by
  linear_combination 3 * hrow - 4 * b3 * sigma * hlinear -
    2 * f2 * hray + 12 * b3 * g * hsigma

def RhoOneDoubleZeroTerminalGRaysSecondJetPacket68
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
            9 * epsilon * B.coeff 1 = 0 ∧
        12 * B.coeff 1 * G.coeff 1 + 12 * B.coeff 2 * G.coeff 0 -
            4 * sigma * r * B.coeff 3 * F.coeff 0 +
            4 * sigma * r * B.coeff 1 * F.coeff 2 +
            12 * C.coeff 1 * F.coeff 1 + 12 * C.coeff 2 * F.coeff 0 +
            9 * epsilon * B.coeff 2 = 0)

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGRaysSecondJetResidual
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
        RhoOneDoubleZeroTerminalGRaysSecondJetPacket68
          T.source.gamma T.source.epsilon A B C F G) ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F))) := by
  dsimp only
  have hprev :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGRaysNextResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprev with ⟨hcap, hfactor, hpacket⟩ | hzero
  · left
    refine ⟨hcap, hfactor, ?_⟩
    rcases hpacket with hboundary | hray
    · exact Or.inl hboundary
    · right
      rcases hray with ⟨hb, hS, r, sigma, hr0, hr2, hsigma, hray,
        hlinear, hfirst⟩
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
      have hrow := rhoOneI4ZeroFactored_ray_coeff_two68
        T.root T.source.gamma T.source.epsilon T.source.B CR FR GR
        hB (by rw [hCRmap]; exact hC) (by rw [hFRmap]; exact hF)
        (by rw [hGRmap]; exact hG) (by simpa only [CR, FR, GR] using hfactor)
      dsimp only at hrow
      rw [hCRmap, hFRmap, hGRmap] at hrow
      have hsigned := rhoOneDoubleZero_gRay_secondScalar68
        sigma r
        ((ratFuncAtHahn46 T.root T.source.B).coeff 1)
        (2 * (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff 0 +
            3 * T.source.gamma)
        ((rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 0)
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-1))
        ((ratFuncAtHahn46 T.root T.source.B).coeff 2)
        ((ratFuncAtHahn46 T.root T.source.B).coeff 3)
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff 0)
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff 1)
        ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff 1)
        ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff 2)
        ((rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 1)
        ((rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff 2)
        T.source.epsilon hsigma hray hlinear hrow
      exact ⟨hb, hS, r, sigma, hr0, hr2, hsigma, hray, hlinear,
        hfirst, hsigned⟩
  · exact Or.inr hzero

end AlignedSquareTerminalGRaysSecondJet68

end Max11DegreeRoutes
