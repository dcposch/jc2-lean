import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapClassificationScratch

/-! # The first unused `I₄` jet above the finite terminal cap -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapI4Next68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapI4NextHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Coefficient five of the global zero-`I₄` factor, one integral jet above
the terminal cap face. -/
theorem rhoOneI4ZeroFactored_cap_coeff_five68
    (root gamma epsilon : k) (B C F G : RatFunc k)
    (hB : (↑(5 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root B).orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 root G).orderTop)
    (hS : (↑(1 : ℚ) : WithTop ℚ) ≤
      (2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma)).orderTop)
    (hfactor : rhoOneI4ZeroFactored68
      (RatFunc.C gamma) (RatFunc.C epsilon) B C F G = 0) :
    4 * ((ratFuncAtHahn46 root B).coeff (5 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (0 : ℚ) +
        (ratFuncAtHahn46 root B).coeff (6 : ℚ) *
          (ratFuncAtHahn46 root G).coeff (-1 : ℚ)) +
      4 * ((ratFuncAtHahn46 root C).coeff (1 : ℚ) *
          (ratFuncAtHahn46 root F).coeff (4 : ℚ) +
        (ratFuncAtHahn46 root C).coeff (2 : ℚ) *
          (ratFuncAtHahn46 root F).coeff (3 : ℚ)) +
      3 * epsilon * (ratFuncAtHahn46 root B).coeff (5 : ℚ) = 0 := by
  let BL : LaurentSeries k := ratFuncAtLaurent46 root B
  let CL : LaurentSeries k := ratFuncAtLaurent46 root C
  let FL : LaurentSeries k := ratFuncAtLaurent46 root F
  let Gser : LaurentSeries k := ratFuncAtLaurent46 root G
  let SR : RatFunc k := 2 * C + RatFunc.C (3 * gamma)
  let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * gamma)
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 5 hB
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 3 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-1) hG
  have hSRH : ratFuncAtHahn46 root SR =
      2 * ratFuncAtHahn46 root C + HahnSeries.C (3 * gamma) := by
    dsimp only [SR]
    simp only [map_add, map_mul, map_ofNat, ratFuncAtHahn46_C]
  have hSRL : ratFuncAtLaurent46 root SR = SL := by
    dsimp only [SR, SL, BL, CL, FL, Gser]
    simp only [map_add, map_mul, map_ofNat, ratFuncAtLaurent46_C68]
  have hSL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root SR 1 (by
    rw [hSRH]
    exact hS)
  rw [hSRL] at hSL
  have hBG := laurent_coeff_mul_lower_succ68 BL Gser 5 (-1) hBL hGL
  have hSF := laurent_coeff_mul_lower_succ68 SL FL 1 3 hSL hFL
  norm_num at hBG hSF
  have hBcubeOrder : (↑(15 : ℤ) : WithTop ℤ) ≤ (BL ^ 3).orderTop := by
    have hp := HahnSeries.orderTop_nsmul_le_orderTop_pow
      (x := BL) (n := 3)
    have htriple := nsmul_le_nsmul_right hBL 3
    norm_num at htriple
    exact le_trans htriple hp
  have hBcube : (BL ^ 3).coeff (5 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hBcubeOrder)
  have hfactorL := congrArg (ratFuncAtLaurent46 root) hfactor
  have hfactorL' : rhoOneI4ZeroFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) BL CL FL Gser = 0 := by
    simpa only [rhoOneI4ZeroFactored68, BL, CL, FL, Gser, map_add, map_mul,
      map_pow, map_neg, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtLaurent46_C68] using hfactorL
  have hSLform : 2 * CL + 3 * HahnSeries.C gamma = SL := by
    dsimp only [SL]
    congr 1
    rw [HahnSeries.C_eq_algebraMap, map_mul, map_ofNat]
  rw [rhoOneI4ZeroFactored68, hSLform] at hfactorL'
  have hc := congrArg (fun X : LaurentSeries k => X.coeff (5 : ℤ))
    hfactorL'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at hc
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      (HahnSeries.C s * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hc827 : (-8 / 27 : LaurentSeries k) =
      HahnSeries.C (-8 / 27 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc83 : (8 / 3 : LaurentSeries k) = HahnSeries.C (8 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc43 : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hsc1 :
      ((-8 / 27 : LaurentSeries k) * BL ^ 3).coeff (5 : ℤ) =
        (-8 / 27 : k) * (BL ^ 3).coeff (5 : ℤ) := by
    rw [hc827, hscale]
  have hsc2 :
      ((8 / 3 : LaurentSeries k) * BL * Gser).coeff (5 : ℤ) =
        (8 / 3 : k) * (BL * Gser).coeff (5 : ℤ) := by
    rw [mul_assoc, hc83, hscale]
  have hsc3 :
      ((4 / 3 : LaurentSeries k) * SL * FL).coeff (5 : ℤ) =
        (4 / 3 : k) * (SL * FL).coeff (5 : ℤ) := by
    rw [mul_assoc, hc43, hscale]
  have hsc4 :
      ((2 : LaurentSeries k) * HahnSeries.C epsilon * BL).coeff (5 : ℤ) =
        (2 * epsilon) * BL.coeff (5 : ℤ) := by
    rw [hc2, ← map_mul, hscale]
  rw [hsc1, hsc2, hsc3, hsc4] at hc
  have hSLone : SL.coeff (1 : ℤ) = 2 * CL.coeff (1 : ℤ) := by
    dsimp only [SL]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * CL).coeff (1 : ℤ) = 2 * CL.coeff (1 : ℤ) := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp [HahnSeries.C_apply]
  have hSLtwo : SL.coeff (2 : ℤ) = 2 * CL.coeff (2 : ℤ) := by
    dsimp only [SL]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * CL).coeff (2 : ℤ) = 2 * CL.coeff (2 : ℤ) := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp [HahnSeries.C_apply]
  rw [hBcube, hBG, hSF, hSLone, hSLtwo] at hc
  have hB5 := ratFuncAtHahn46_coeff_int68 root B 5
  have hB6 := ratFuncAtHahn46_coeff_int68 root B 6
  have hC1 := ratFuncAtHahn46_coeff_int68 root C 1
  have hC2 := ratFuncAtHahn46_coeff_int68 root C 2
  have hF3 := ratFuncAtHahn46_coeff_int68 root F 3
  have hF4 := ratFuncAtHahn46_coeff_int68 root F 4
  have hGm1 := ratFuncAtHahn46_coeff_int68 root G (-1)
  have hG0 := ratFuncAtHahn46_coeff_int68 root G 0
  norm_num at hB5 hB6 hC1 hC2 hF3 hF4 hGm1 hG0
  dsimp only [BL, CL, FL, Gser] at hc
  rw [← hB5, ← hB6, ← hC1, ← hC2, ← hF3, ← hF4, ← hGm1,
    ← hG0] at hc
  linear_combination (3 / 2 : k) * hc

/-- Cap classification refined by the first unused `I₄` jet. -/
def RhoOneDoubleZeroTerminalGBoundaryCapI4NextResidual68
    (root j gamma epsilon : k) (h0R BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapClassificationResidual68
      root j gamma epsilon h0R BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧
        2 * C.coeff (0 : ℚ) + 3 * gamma = 0) →
      (4 * (B.coeff (5 : ℚ) * G.coeff (0 : ℚ) +
            B.coeff (6 : ℚ) * G.coeff (-1 : ℚ)) +
          4 * (C.coeff (1 : ℚ) * F.coeff (4 : ℚ) +
            C.coeff (2 : ℚ) * F.coeff (3 : ℚ)) +
          3 * epsilon * B.coeff (5 : ℚ) = 0) ∧
        (((C.coeff (1 : ℚ) = 0 ∧ B.coeff (5 : ℚ) = 0 ∧
              (↑(6 : ℚ) : WithTop ℚ) ≤ B.orderTop) ∧
            ((C.coeff (2 : ℚ) = 0 ∧ B.coeff (6 : ℚ) = 0 ∧
                (↑(7 : ℚ) : WithTop ℚ) ≤ B.orderTop) ∨
             (C.coeff (2 : ℚ) ≠ 0 ∧ B.coeff (6 : ℚ) ≠ 0 ∧
                B.orderTop = (↑(6 : ℚ) : WithTop ℚ)))) ∨
          (C.coeff (1 : ℚ) ≠ 0 ∧ B.coeff (5 : ℚ) ≠ 0 ∧
            B.orderTop = (↑(5 : ℚ) : WithTop ℚ))))

/-- Literal source backwire of the coefficient-five `I₄` jet and its
second coordinate split. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapI4NextResidual
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
    RhoOneDoubleZeroTerminalGBoundaryCapI4NextResidual68
        T.root j T.source.gamma T.source.epsilon
        (algebraMap k[X] (RatFunc k) h0) BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapI4NextResidual68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hGne | ⟨hGzero, hG0, htail⟩
  · have hprev :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapClassificationResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    rcases hprev with hclass | hbad
    · left
      refine ⟨hclass, ?_⟩
      intro hcoordTarget
      have hclassTarget := hclass.2 hcoordTarget
      rcases hclassTarget with ⟨c, hc, hsingle, hscalar, hCsplit⟩
      have hfinite := hclass.1
      dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68] at hfinite
      rcases hfinite with ⟨hfact, hboundary | hrays⟩
      · rcases hboundary with ⟨hcurrent, hf2, hF3, hb4, hB5,
          hi4three, hf3ne⟩
        rcases hcurrent with ⟨hprev4, hb3, hB4, hi4two⟩
        rcases hprev4 with ⟨hprev3, hf1, hF2⟩
        rcases hprev3 with ⟨hprev2, hb2, hB3, hi4one⟩
        rcases hprev2 with ⟨hprev1, hf0, hF1⟩
        rcases hprev1 with ⟨hcoord, hB2, hS1, hi4zero⟩
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
        change rhoOneI4ZeroFactored68
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
          BR CR FR GR = 0 at hfact
        have hrowRaw := rhoOneI4ZeroFactored_cap_coeff_five68
          T.root T.source.gamma T.source.epsilon BR CR FR GR
          (by dsimp only [BR]; exact hB5)
          (by rw [hFRmap]; exact hF3) (by rw [hGRmap]; exact hG)
          (by rw [hCRmap]; exact hS1) hfact
        rw [hCRmap, hFRmap, hGRmap] at hrowRaw
        have hrow5 := by simpa only [BR] using hrowRaw
        refine ⟨hrow5, ?_⟩
        rcases hCsplit with hCzero | hCne
        · left
          rcases hCzero with ⟨hc1, hb5, hB6⟩
          refine ⟨⟨hc1, hb5, hB6⟩, ?_⟩
          have hface6 :
              (ratFuncAtHahn46 T.root T.source.B).coeff (6 : ℚ) *
                  (rhoOneTangentEDefectHahn68
                    (ratFuncAtHahn46 T.root T.source.A)
                    (rhoOneCDefectHahn68
                      (ratFuncAtHahn46 T.root T.source.A)
                      (ratFuncAtHahn46 T.root T.source.C0))
                    (rhoOneEDefectHahn68
                      (ratFuncAtHahn46 T.root T.source.A)
                      (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) +
                (rhoOneCDefectHahn68
                  (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0)).coeff (2 : ℚ) *
                  (rhoOneTangentDDefectHahn68
                    (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.B)
                    (ratFuncAtHahn46 T.root T.source.D)).coeff (3 : ℚ) = 0 := by
            rw [hc1, hb5] at hrow5
            norm_num at hrow5
            linear_combination (1 / 4 : k) * hrow5
          by_cases hc2 :
              (rhoOneCDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0)).coeff (2 : ℚ) = 0
          · left
            have hprod :
                (ratFuncAtHahn46 T.root T.source.B).coeff (6 : ℚ) *
                  (rhoOneTangentEDefectHahn68
                    (ratFuncAtHahn46 T.root T.source.A)
                    (rhoOneCDefectHahn68
                      (ratFuncAtHahn46 T.root T.source.A)
                      (ratFuncAtHahn46 T.root T.source.C0))
                    (rhoOneEDefectHahn68
                      (ratFuncAtHahn46 T.root T.source.A)
                      (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) = 0 := by
              simpa [hc2] using hface6
            have hb6 := (mul_eq_zero.mp hprod).resolve_right hGne
            have hB7 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
              T.root T.source.B 6 hB6 (by norm_num; exact hb6)
            norm_num at hB7
            exact ⟨hc2, hb6, hB7⟩
          · right
            have hb6ne :
                (ratFuncAtHahn46 T.root T.source.B).coeff (6 : ℚ) ≠ 0 := by
              intro hb6
              have hprod :
                  (rhoOneCDefectHahn68
                    (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.C0)).coeff (2 : ℚ) *
                  (rhoOneTangentDDefectHahn68
                    (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.B)
                    (ratFuncAtHahn46 T.root T.source.D)).coeff (3 : ℚ) = 0 := by
                simpa [hb6] using hface6
              rcases mul_eq_zero.mp hprod with hc2zero | hf3zero
              · exact hc2 hc2zero
              · exact hf3ne hf3zero
            have hBexact :
                (ratFuncAtHahn46 T.root T.source.B).orderTop =
                  (↑(6 : ℚ) : WithTop ℚ) :=
              le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hb6ne) hB6
            exact ⟨hc2, hb6ne, hBexact⟩
        · right
          exact hCne
      · exact (hrays.1 hcoordTarget.1).elim
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

end AlignedSquareTerminalGBoundaryCapI4Next68

end Max11DegreeRoutes
