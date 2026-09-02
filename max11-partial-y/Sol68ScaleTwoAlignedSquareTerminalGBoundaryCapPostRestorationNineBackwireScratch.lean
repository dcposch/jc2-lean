import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapPostRestorationNineScratch

/-! # Source backwire of the finite-window T₉ row -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapPostRestorationNineBackwire68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareCapPostRestorationNineBackwireHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

def RhoOneDoubleZeroTerminalGBoundaryCapPostRestorationNineResidual68
    (root j gamma epsilon : k) (A0 : k[X])
    (h0R AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapPostRestorationEightResidual68
      root j gamma epsilon A0 h0R AR BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧ 2 * C.coeff 0 + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 sold cs : k,
        (RhoOneDoubleZeroTerminalGBoundaryCapPostRestorationSevenPacket68
          gamma epsilon i3 sold cs (A0.derivative.eval root)
            (A0.derivative.derivative.eval root)
            (A0.derivative.derivative.derivative.eval root)
            A B C F G (ratFuncAtHahn46 root (Differential.deriv AR)) ∧
          let AL : LaurentSeries k := ratFuncAtLaurent46 root AR
          let BL : LaurentSeries k := ratFuncAtLaurent46 root BR
          let CL : LaurentSeries k := ratFuncAtLaurent46 root CR
          let CT : LaurentSeries k :=
            CL + HahnSeries.C ((3 / 2 : k) * gamma)
          let FL : LaurentSeries k := ratFuncAtLaurent46 root FR
          (rhoOneCapCoordinateDefectSeries68 BL CT FL).coeff 22 =
            -(4 / 3 : k) * AL.coeff (-2) * BL.coeff 11 * BL.coeff 13 -
              (2 / 3 : k) * AL.coeff (-2) * BL.coeff 12 ^ 2 -
              (4 / 3 : k) * AL.coeff (-1) * BL.coeff 11 * BL.coeff 12 -
              (2 / 3 : k) * AL.coeff 0 * BL.coeff 11 ^ 2) ∧
        let AL : LaurentSeries k := ratFuncAtLaurent46 root AR
        let BL : LaurentSeries k := ratFuncAtLaurent46 root BR
        let CL : LaurentSeries k := ratFuncAtLaurent46 root CR
        let CT : LaurentSeries k :=
          CL + HahnSeries.C ((3 / 2 : k) * gamma)
        let FL : LaurentSeries k := ratFuncAtLaurent46 root FR
        (rhoOneCapCoordinateDefectSeries68 BL CT FL).coeff 23 =
          -(4 / 3 : k) * AL.coeff (-2) * BL.coeff 11 * BL.coeff 14 -
            (4 / 3 : k) * AL.coeff (-2) * BL.coeff 12 * BL.coeff 13 -
            (4 / 3 : k) * AL.coeff (-1) * BL.coeff 11 * BL.coeff 13 -
            (2 / 3 : k) * AL.coeff (-1) * BL.coeff 12 ^ 2 -
            (4 / 3 : k) * AL.coeff 0 * BL.coeff 11 * BL.coeff 12 -
            (2 / 3 : k) * AL.coeff 1 * BL.coeff 11 ^ 2)

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapPostRestorationNineResidual
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
    RhoOneDoubleZeroTerminalGBoundaryCapPostRestorationNineResidual68
        T.root j T.source.gamma T.source.epsilon (localClearedA68RhoOne g u)
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapPostRestorationNineResidual68]
  have hprevRaw :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapPostRestorationEightResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprevRaw with hprev | htail
  · left
    refine ⟨hprev, ?_⟩
    intro hcoord hc1 hc2
    obtain ⟨i3, sold, cs, hseven⟩ := hprev.2 hcoord hc1 hc2
    have hpacket := hseven.1.1
    have hbase := hpacket.1
    have hfourth := hbase.1.1.1.1
    have hI3ten := hfourth.1.1
    have hthirdSource := hI3ten.1
    have hdet := hthirdSource.1
    have hI4thirteen := hdet.1
    have hI3nine := hI4thirteen.1
    have hT2packet := hI3nine.1
    have hT1packet := hT2packet.1
    have hI4twelve := hT1packet.1
    have hI3eight := hI4twelve.1
    have hderivative := hI3eight.1
    have hterminal := hderivative.1
    have hnext := hterminal.1
    have hci3 : RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68
        T.source.gamma T.source.epsilon i3
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
            (ratFuncAtHahn46 T.root T.source.E))) := hnext.1.1
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68] at hci3
    rcases hci3 with
      ⟨hi3H, hc3, hc4, hc5, hc6, hb7, hb8, hb9, hb10,
        hS7, hB11, hcap3, hc7ne, hcap4, hb11ne, hBexact⟩
    have hsourcePrev := hprev.1.1.1
    have hI3nineResidual := hsourcePrev.1.1.1.1.1.1.1.1
    have hterminalTwoResidual := hI3nineResidual.1
    have hterminalOneResidual := hterminalTwoResidual.1
    have hI4twelveResidual := hterminalOneResidual.1
    have hI3eightResidual := hI4twelveResidual.1
    have hderivativeResidual := hI3eightResidual.1
    have hterminalNextResidual := hderivativeResidual.1
    have hnextJetResidual := hterminalNextResidual.1
    have hci3Residual := hnextJetResidual.1
    have hi4nextResidual := hci3Residual.1
    have hclassificationResidual := hi4nextResidual.1
    have hfinite := hclassificationResidual.1
    rcases hfinite with ⟨hfact, hboundary | hrays⟩
    · rcases hboundary with ⟨hcurrent, hf2, hF3, hb4, hB5,
        hi4three, hf3ne⟩
      let AR : RatFunc k := T.source.A
      let BR : RatFunc k := T.source.B
      let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
      let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
      let GR : RatFunc k :=
        (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
          RatFunc.C (1 / 3 : k) * AR * CR
      have hCRmap : ratFuncAtHahn46 T.root CR =
          rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0) := by
        dsimp only [CR, AR, rhoOneCDefectHahn68]
        simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
      have hFRmap : ratFuncAtHahn46 T.root FR =
          rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D) := by
        dsimp only [FR, AR, BR, rhoOneTangentDDefectHahn68]
        simp only [map_sub, map_mul, ratFuncAtHahn46_C]
      have hGRmap : ratFuncAtHahn46 T.root GR =
          rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
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
      change rhoOneI4ZeroFactored68
        (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
        BR CR FR GR = 0 at hfact
      let AL := ratFuncAtLaurent46 T.root AR
      let BL := ratFuncAtLaurent46 T.root BR
      let CL := ratFuncAtLaurent46 T.root CR
      let FL := ratFuncAtLaurent46 T.root FR
      let Gser : LaurentSeries k := ratFuncAtLaurent46 T.root GR
      let SR : RatFunc k := 2 * CR + RatFunc.C (3 * T.source.gamma)
      let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * T.source.gamma)
      let CT : LaurentSeries k := CL + HahnSeries.C ((3 / 2 : k) * T.source.gamma)
      have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root AR (-2) hAH
      have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root BR 11 (by
        dsimp only [BR]
        norm_num at hB11 ⊢
        exact hB11)
      have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root CR 0 (by
        rw [hCRmap]
        exact hC)
      have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root FR 3 (by
        rw [hFRmap]
        exact hF3)
      have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root GR (-1) (by
        rw [hGRmap]
        exact hG)
      have hSRH : ratFuncAtHahn46 T.root SR =
          2 * ratFuncAtHahn46 T.root CR + HahnSeries.C (3 * T.source.gamma) := by
        dsimp only [SR]
        simp only [map_add, map_mul, map_ofNat, ratFuncAtHahn46_C]
      have hSRL : ratFuncAtLaurent46 T.root SR = SL := by
        dsimp only [SR, SL, CL]
        simp only [map_add, map_mul, map_ofNat, ratFuncAtLaurent46_C68]
      have hSL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root SR 7 (by
        rw [hSRH, hCRmap]
        exact hS7)
      rw [hSRL] at hSL
      have hhalfSL := laurent_orderTop_ge_const_mul68 (1 / 2 : k) SL 7 hSL
      have hCTscale : CT = HahnSeries.C (1 / 2 : k) * SL := by
        dsimp only [CT, SL]
        have hhalf : HahnSeries.C (1 / 2 : k) = (1 / 2 : LaurentSeries k) := by
          rw [map_div₀, map_one, map_ofNat]
        have hthreehalf : HahnSeries.C ((3 / 2 : k) * T.source.gamma) =
            (3 / 2 : LaurentSeries k) * HahnSeries.C T.source.gamma := by
          rw [map_mul]
          have h32 : HahnSeries.C (3 / 2 : k) = (3 / 2 : LaurentSeries k) := by
            rw [map_div₀, map_ofNat, map_ofNat]
          rw [h32]
        have hthree : HahnSeries.C (3 * T.source.gamma) =
            (3 : LaurentSeries k) * HahnSeries.C T.source.gamma := by
          rw [map_mul, map_ofNat]
        rw [hhalf, hthreehalf, hthree]
        field_simp
      have hCT : (↑(7 : ℤ) : WithTop ℤ) ≤ CT.orderTop := by
        rw [hCTscale]
        exact hhalfSL
      have hi3L : rhoOneI3CapFactored68 (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.epsilon) AL BL CL FL Gser = HahnSeries.C i3 := by
        have hm := congrArg (ratFuncAtLaurent46 T.root) hi3R
        simpa only [rhoOneI3CapFactored68, AL, BL, CL, FL, Gser, map_add,
          map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_one,
          ratFuncAtLaurent46_C68] using hm
      have hi4L : rhoOneI4ZeroFactored68 (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.epsilon) BL CL FL Gser = 0 := by
        have hm := congrArg (ratFuncAtLaurent46 T.root) hfact
        simpa only [rhoOneI4ZeroFactored68, BL, CL, FL, Gser, map_add,
          map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_zero, map_one,
          ratFuncAtLaurent46_C68] using hm
      have hR3 := rhoOneCap_reduced_i3_order_twelve_of_source_factor68
        T.source.gamma T.source.epsilon i3 AL BL CL CT FL Gser
        hAL hBL hCL hCT hFL hGL (by rfl) hi3L
      have hR4 := rhoOneCap_reduced_i4_order_sixteen_of_source_factor68
        T.source.gamma T.source.epsilon BL CL CT FL Gser
        hBL hCT hFL hGL (by rfl) hi4L
      have hgne :
          (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) ≠ 0 := by
        intro hg0
        rw [hg0, mul_zero, zero_add] at hcap4
        exact (mul_ne_zero hc7ne hf3ne) hcap4
      have hT0 : 2 *
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 7 ^ 2 -
          (ratFuncAtHahn46 T.root T.source.B).coeff 11 *
            (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 3 = 0 := by
        linear_combination -hnext.1.2.1
      have hT1 : 4 *
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 7 *
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 8 -
          (ratFuncAtHahn46 T.root T.source.B).coeff 12 *
            (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 3 -
          (ratFuncAtHahn46 T.root T.source.B).coeff 11 *
            (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 4 = 0 := by
        have hgT1 := hnext.1.2.2.2.2
        have hmul :
            (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) *
              (4 *
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0)).coeff 7 *
                (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                  (ratFuncAtHahn46 T.root T.source.C0)).coeff 8 -
                (ratFuncAtHahn46 T.root T.source.B).coeff 12 *
                  (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.B)
                    (ratFuncAtHahn46 T.root T.source.D)).coeff 3 -
                (ratFuncAtHahn46 T.root T.source.B).coeff 11 *
                  (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                    (ratFuncAtHahn46 T.root T.source.B)
                    (ratFuncAtHahn46 T.root T.source.D)).coeff 4) = 0 := by
          linear_combination
            2 * (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 8 * hcap3 +
            (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 3 * hgT1 -
            (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 4 * hcap4
        exact (mul_eq_zero.mp hmul).resolve_left hgne
      have hAcoeff (n : ℤ) : AL.coeff n =
          (ratFuncAtHahn46 T.root T.source.A).coeff (n : ℚ) := by
        have hm := ratFuncAtHahn46_coeff_int68 T.root AR n
        dsimp only [AL, AR]
        exact hm.symm
      have hBcoeff (n : ℤ) : BL.coeff n =
          (ratFuncAtHahn46 T.root T.source.B).coeff (n : ℚ) := by
        have hm := ratFuncAtHahn46_coeff_int68 T.root BR n
        dsimp only [BL, BR]
        exact hm.symm
      have hCcoeff (n : ℤ) (hn : n ≠ 0) : CT.coeff n =
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (n : ℚ) := by
        have hm := ratFuncAtHahn46_coeff_int68 T.root CR n
        rw [hCRmap] at hm
        dsimp only [CT, CL]
        simp only [HahnSeries.coeff_add, HahnSeries.C_apply,
          HahnSeries.coeff_single]
        rw [if_neg hn]
        simpa using hm.symm
      have hFcoeff (n : ℤ) : FL.coeff n =
          (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff (n : ℚ) := by
        have hm := ratFuncAtHahn46_coeff_int68 T.root FR n
        rw [hFRmap] at hm
        dsimp only [FL]
        exact hm.symm
      have hGcoeff (n : ℤ) : Gser.coeff n =
          (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (n : ℚ) := by
        have hm := ratFuncAtHahn46_coeff_int68 T.root GR n
        rw [hGRmap] at hm
        dsimp only [Gser]
        exact hm.symm
      have hT0L : 2 * CT.coeff 7 ^ 2 - BL.coeff 11 * FL.coeff 3 = 0 := by
        rw [hCcoeff 7 (by norm_num), hBcoeff 11, hFcoeff 3]
        exact hT0
      have hT1L : 4 * CT.coeff 7 * CT.coeff 8 - BL.coeff 12 * FL.coeff 3 -
          BL.coeff 11 * FL.coeff 4 = 0 := by
        rw [hCcoeff 7 (by norm_num), hCcoeff 8 (by norm_num),
          hBcoeff 12, hFcoeff 3, hBcoeff 11, hFcoeff 4]
        exact hT1
      have hT2L : 2 * CT.coeff 8 ^ 2 + 4 * CT.coeff 7 * CT.coeff 9 -
          BL.coeff 13 * FL.coeff 3 - BL.coeff 12 * FL.coeff 4 -
          BL.coeff 11 * FL.coeff 5 = 0 := by
        rw [hCcoeff 8 (by norm_num), hCcoeff 7 (by norm_num),
          hCcoeff 9 (by norm_num), hBcoeff 13, hFcoeff 3,
          hBcoeff 12, hFcoeff 4, hBcoeff 11, hFcoeff 5]
        exact hI3eight.2.2.1
      have hT3L : 4 * CT.coeff 7 * CT.coeff 10 + 4 * CT.coeff 8 * CT.coeff 9 -
          BL.coeff 14 * FL.coeff 3 - BL.coeff 13 * FL.coeff 4 -
          BL.coeff 12 * FL.coeff 5 - BL.coeff 11 * FL.coeff 6 = 0 := by
        rw [hCcoeff 7 (by norm_num), hCcoeff 10 (by norm_num),
          hCcoeff 8 (by norm_num), hCcoeff 9 (by norm_num),
          hBcoeff 14, hFcoeff 3, hBcoeff 13, hFcoeff 4,
          hBcoeff 12, hFcoeff 5, hBcoeff 11, hFcoeff 6]
        exact hI4thirteen.2.2.2.2
      have hT4L : 4 * CT.coeff 7 * CT.coeff 11 + 4 * CT.coeff 8 * CT.coeff 10 +
          2 * CT.coeff 9 ^ 2 - BL.coeff 15 * FL.coeff 3 -
          BL.coeff 14 * FL.coeff 4 - BL.coeff 13 * FL.coeff 5 -
          BL.coeff 12 * FL.coeff 6 - BL.coeff 11 * FL.coeff 7 = 0 := by
        rw [hCcoeff 7 (by norm_num), hCcoeff 11 (by norm_num),
          hCcoeff 8 (by norm_num), hCcoeff 10 (by norm_num),
          hCcoeff 9 (by norm_num), hBcoeff 15, hFcoeff 3,
          hBcoeff 14, hFcoeff 4, hBcoeff 13, hFcoeff 5,
          hBcoeff 12, hFcoeff 6, hBcoeff 11, hFcoeff 7]
        exact hfourth.1.2
      have hT5L : 4 * CT.coeff 7 * CT.coeff 12 + 4 * CT.coeff 8 * CT.coeff 11 +
          4 * CT.coeff 9 * CT.coeff 10 - BL.coeff 16 * FL.coeff 3 -
          BL.coeff 15 * FL.coeff 4 - BL.coeff 14 * FL.coeff 5 -
          BL.coeff 13 * FL.coeff 6 - BL.coeff 12 * FL.coeff 7 -
          BL.coeff 11 * FL.coeff 8 = 0 := by
        have ht5 := hbase.1.1.2
        dsimp only [rhoOneCapCoordinateDefectT5Core68] at ht5
        rw [hCcoeff 7 (by norm_num), hCcoeff 12 (by norm_num),
          hCcoeff 8 (by norm_num), hCcoeff 11 (by norm_num),
          hCcoeff 9 (by norm_num), hCcoeff 10 (by norm_num),
          hBcoeff 16, hFcoeff 3, hBcoeff 15, hFcoeff 4,
          hBcoeff 14, hFcoeff 5, hBcoeff 13, hFcoeff 6,
          hBcoeff 12, hFcoeff 7, hBcoeff 11, hFcoeff 8]
        exact ht5
      have hI3L : -(4 / 3 : k) * AL.coeff (-2) * BL.coeff 11 * FL.coeff 3 +
          4 * rhoOneI3CapTwelveReducedLaurentCore68 CT FL Gser +
          3 * T.source.epsilon * CT.coeff 12 = 0 := by
        have ht := hbase.1.2.1
        dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapI3TwelveRestoredTarget68,
          rhoOneI3CapTwelveRestoredCore68,
          rhoOneI3CapTwelveReducedCore68] at ht
        dsimp only [rhoOneI3CapTwelveReducedLaurentCore68]
        rw [hAcoeff (-2), hBcoeff 11, hFcoeff 3,
          hCcoeff 7 (by norm_num), hGcoeff 5,
          hCcoeff 8 (by norm_num), hGcoeff 4,
          hCcoeff 9 (by norm_num), hGcoeff 3,
          hCcoeff 10 (by norm_num), hGcoeff 2,
          hCcoeff 11 (by norm_num), hGcoeff 1,
          hCcoeff 12 (by norm_num), hGcoeff 0,
          hCcoeff 13 (by norm_num), hGcoeff (-1),
          hFcoeff 9, hFcoeff 4, hFcoeff 8, hFcoeff 5,
          hFcoeff 7, hFcoeff 6]
        exact ht
      have hI4L : 4 * rhoOneI4CapSixteenLaurentCore68 BL CT FL Gser +
          3 * T.source.epsilon * BL.coeff 16 = 0 := by
        have ht := hbase.2.1
        dsimp only [rhoOneI4CapSixteenCore68] at ht
        dsimp only [rhoOneI4CapSixteenLaurentCore68]
        rw [hBcoeff 11, hGcoeff 5, hBcoeff 12, hGcoeff 4,
          hBcoeff 13, hGcoeff 3, hBcoeff 14, hGcoeff 2,
          hBcoeff 15, hGcoeff 1, hBcoeff 16, hGcoeff 0,
          hBcoeff 17, hGcoeff (-1), hCcoeff 7 (by norm_num),
          hFcoeff 9, hCcoeff 8 (by norm_num), hFcoeff 8,
          hCcoeff 9 (by norm_num), hFcoeff 7,
          hCcoeff 10 (by norm_num), hFcoeff 6,
          hCcoeff 11 (by norm_num), hFcoeff 5,
          hCcoeff 12 (by norm_num), hFcoeff 4,
          hCcoeff 13 (by norm_num), hFcoeff 3]
        exact ht
      have hT6L := rhoOneCap_post_restoration_t6_of_rows68
        (AL.coeff (-2)) T.source.epsilon BL CT FL Gser
        hBL hCT hFL hGL (by rw [hFcoeff 3]; exact hf3ne)
        hR3 hR4 hT0L hT1L hT2L hT3L hT4L hT5L hI3L hI4L
      have hT6Coeff := rhoOneCap_coordinate_defect_coeff_twenty_core68
        BL CT FL hBL hCT hFL
      have hT6Series :
          (rhoOneCapCoordinateDefectSeries68 BL CT FL).coeff 20 =
            -(2 / 3 : k) * AL.coeff (-2) * BL.coeff 11 ^ 2 := by
        rw [hT6Coeff]
        exact hT6L
      let HH := rhoOneCapCoordinateDefectSeries68 BL CT FL
      have hCC0 := laurent_coeff_mul_lower68 CT CT 7 7 hCT hCT
      have hBF0 := laurent_coeff_mul_lower68 BL FL 11 3 hBL hFL
      have hCC1 := laurent_coeff_mul_lower_succ68 CT CT 7 7 hCT hCT
      have hBF1 := laurent_coeff_mul_lower_succ68 BL FL 11 3 hBL hFL
      have hCC2 := laurent_coeff_mul_lower_two68 CT CT 7 7 hCT hCT
      have hBF2 := laurent_coeff_mul_lower_two68 BL FL 11 3 hBL hFL
      have hCC3 := laurent_coeff_mul_lower_three68 CT CT 7 7 hCT hCT
      have hBF3 := laurent_coeff_mul_lower_three68 BL FL 11 3 hBL hFL
      have hCC4 := laurent_coeff_mul_lower_four68 CT CT 7 7 hCT hCT
      have hBF4 := laurent_coeff_mul_lower_four68 BL FL 11 3 hBL hFL
      have hCC5 := laurent_coeff_mul_lower_five68 CT CT 7 7 hCT hCT
      have hBF5 := laurent_coeff_mul_lower_five68 BL FL 11 3 hBL hFL
      norm_num at hCC0 hBF0 hCC1 hBF1 hCC2 hBF2 hCC3 hBF3 hCC4 hBF4 hCC5 hBF5
      have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
          (HahnSeries.C s * X).coeff r = s * X.coeff r := by
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
      have htwo : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
        rw [HahnSeries.C_eq_algebraMap, map_ofNat]
      have hHH14 : HH.coeff 14 = 0 := by
        dsimp only [HH, rhoOneCapCoordinateDefectSeries68]
        rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC0, hBF0]
        linear_combination hT0L
      have hHH15 : HH.coeff 15 = 0 := by
        dsimp only [HH, rhoOneCapCoordinateDefectSeries68]
        rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC1, hBF1]
        linear_combination hT1L
      have hHH16 : HH.coeff 16 = 0 := by
        dsimp only [HH, rhoOneCapCoordinateDefectSeries68]
        rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC2, hBF2]
        linear_combination hT2L
      have hHH17 : HH.coeff 17 = 0 := by
        dsimp only [HH, rhoOneCapCoordinateDefectSeries68]
        rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC3, hBF3]
        linear_combination hT3L
      have hHH18 : HH.coeff 18 = 0 := by
        dsimp only [HH, rhoOneCapCoordinateDefectSeries68]
        rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC4, hBF4]
        linear_combination hT4L
      have hHH19 : HH.coeff 19 = 0 := by
        dsimp only [HH, rhoOneCapCoordinateDefectSeries68]
        rw [pow_two, HahnSeries.coeff_sub, htwo, hscale, hCC5, hBF5]
        linear_combination hT5L
      have hHHorder := rhoOneCap_coordinate_defect_order_twenty_of_coeff_rows68
        BL CT FL hBL hCT hFL (by simpa only [HH] using hHH14)
        (by simpa only [HH] using hHH15) (by simpa only [HH] using hHH16)
        (by simpa only [HH] using hHH17) (by simpa only [HH] using hHH18)
        (by simpa only [HH] using hHH19)
      have hR3core := rhoOneCap_reduced_i3_coeff_twelve_core68
        T.source.epsilon CT FL Gser hCT hFL hGL
      have hR312 : (rhoOneCapReducedI3Series68 T.source.epsilon CT FL Gser).coeff 12 =
          (4 / 3 : k) * AL.coeff (-2) * BL.coeff 11 * FL.coeff 3 := by
        linear_combination hR3core + hI3L
      have hR4core := rhoOneCap_reduced_i4_coeff_sixteen_core68
        T.source.epsilon BL CT FL Gser hBL hCT hFL hGL
      have hR416 : (rhoOneCapReducedI4Series68 T.source.epsilon BL CT FL Gser).coeff 16 = 0 := by
        linear_combination hR4core + hI4L
      have hR313 := rhoOneCap_reduced_i3_coeff_thirteen_of_source_factor68
        T.source.gamma T.source.epsilon i3 AL BL CL CT FL Gser
        hAL hBL hCL hCT hFL hGL (by rfl) hi3L
      have hR417 := rhoOneCap_reduced_i4_coeff_seventeen_of_source_factor68
        T.source.gamma T.source.epsilon BL CL CT FL Gser hBL (by rfl) hi4L
      have hT7L := rhoOneCap_post_restoration_transport_seven68
        (AL.coeff (-2)) (AL.coeff (-1)) T.source.epsilon BL CT FL Gser
        hBL hCT hFL (by rw [hFcoeff 3]; exact hf3ne)
        hR3 hR4 hHHorder hR312 hR313 hR416 hR417 hT6Series
      have hR314 := rhoOneCap_reduced_i3_coeff_fourteen_of_source_factor68
        T.source.gamma T.source.epsilon i3 AL BL CL CT FL Gser
        hAL hBL hCL hCT hFL hGL (by rfl) hi3L
      have hR418 := rhoOneCap_reduced_i4_coeff_eighteen_of_source_factor68
        T.source.gamma T.source.epsilon BL CL CT FL Gser hBL (by rfl) hi4L
      have hT8L := rhoOneCap_post_restoration_transport_eight68
        (AL.coeff (-2)) (AL.coeff (-1)) (AL.coeff 0)
        T.source.epsilon BL CT FL Gser hBL hCT hFL
        (by rw [hFcoeff 3]; exact hf3ne) hR3 hR4 hHHorder
        hR312 hR313 hR314 hR416 hR417 hR418 hT6Series hT7L
      have hR315 := rhoOneCap_reduced_i3_coeff_fifteen_of_source_factor68
        T.source.gamma T.source.epsilon i3 AL BL CL CT FL Gser
        hAL hBL hCL hCT hFL hGL (by rfl) hi3L
      have hR419 := rhoOneCap_reduced_i4_coeff_nineteen_of_source_factor68
        T.source.gamma T.source.epsilon BL CL CT FL Gser hBL (by rfl) hi4L
      have hT9L := rhoOneCap_post_restoration_transport_nine68
        (AL.coeff (-2)) (AL.coeff (-1)) (AL.coeff 0) (AL.coeff 1)
        T.source.epsilon BL CT FL Gser hBL hCT hFL
        (by rw [hFcoeff 3]; exact hf3ne) hR3 hR4 hHHorder
        hR312 hR313 hR314 hR315 hR416 hR417 hR418 hR419
        hT6Series hT7L hT8L
      refine ⟨i3, sold, cs, hseven, ?_⟩
      exact hT9L
    · exact (hrays.1 hcoord.1).elim
  · exact Or.inr htail

end AlignedSquareTerminalGBoundaryCapPostRestorationNineBackwire68

end Max11DegreeRoutes
