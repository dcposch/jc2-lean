import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapEndpointRowsScratch

/-! # Source backwire of I₃[11], I₄[15], and endpoint T₅ -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapEndpointSourceBackwire68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapEndpointSourceHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

def RhoOneDoubleZeroTerminalGBoundaryCapEndpointFiveResidual68
    (root j gamma epsilon : k) (A0 : k[X])
    (h0R AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapFourthTransportResidual68
      root j gamma epsilon A0 h0R AR BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧ 2 * C.coeff 0 + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      ∃ i3 sold cs : k,
        RhoOneDoubleZeroTerminalGBoundaryCapEndpointFivePacket68
          gamma epsilon i3 sold cs (A0.derivative.eval root)
            (A0.derivative.derivative.eval root)
            (A0.derivative.derivative.derivative.eval root)
            A B C F G (ratFuncAtHahn46 root (Differential.deriv AR)))

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapEndpointFiveResidual
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
    RhoOneDoubleZeroTerminalGBoundaryCapEndpointFiveResidual68
        T.root j T.source.gamma T.source.epsilon (localClearedA68RhoOne g u)
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapEndpointFiveResidual68]
  have hprevRaw :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapFourthTransportResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprevRaw with hprev | htail
  · left
    refine ⟨hprev, ?_⟩
    intro hcoord hc1 hc2
    obtain ⟨i3, sold, cs, hpacket⟩ := hprev.2 hcoord hc1 hc2
    have hI3ten := hpacket.1.1
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
    have hci3 := hnext.1
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryCI3CapPacket68] at hci3
    rcases hci3 with
      ⟨hi3H, hc3, hc4, hc5, hc6, hb7, hb8, hb9, hb10,
        hS7, hB11, hcap3, hc7ne, hcap4, hb11ne, hBexact⟩
    have hterminalTwoResidual := hprev.1.1.1.1.1.1
    have hi4res := hterminalTwoResidual.1.1
    have hfinite := hi4res.1.1.1.1.1.1.1.1
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68] at hfinite
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
      have hrow11raw := rhoOneI3CapFactored_cap_coeff_eleven68
        T.root T.source.gamma T.source.epsilon i3 AR BR CR FR GR
        hAH (by simpa only [BR] using hB11)
        (by rw [hCRmap]; exact hC) (by rw [hFRmap]; exact hF3)
        (by rw [hGRmap]; exact hG) (by rw [hCRmap]; exact hS7) hi3R
      have hrow15raw := rhoOneI4ZeroFactored_cap_coeff_fifteen68
        T.root T.source.gamma T.source.epsilon BR CR FR GR
        (by simpa only [BR] using hB11) (by rw [hFRmap]; exact hF3)
        (by rw [hGRmap]; exact hG) (by rw [hCRmap]; exact hS7) hfact
      rw [hCRmap, hFRmap, hGRmap] at hrow11raw hrow15raw
      have hrow11 : 4 * rhoOneI3CapElevenCore68
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D))
            (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0))
              (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.E))) +
          3 * T.source.epsilon *
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 11 = 0 := by
        simpa only [rhoOneI3CapElevenCore68] using hrow11raw
      have hrow15 : 4 * rhoOneI4CapFifteenCore68
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
                (ratFuncAtHahn46 T.root T.source.E))) +
          3 * T.source.epsilon *
            (ratFuncAtHahn46 T.root T.source.B).coeff 15 = 0 := by
        dsimp only [BR] at hrow15raw
        dsimp only [rhoOneI4CapFifteenCore68]
        linear_combination hrow15raw
      let AL := ratFuncAtLaurent46 T.root AR
      let BL := ratFuncAtLaurent46 T.root BR
      let CL := ratFuncAtLaurent46 T.root CR
      let FL := ratFuncAtLaurent46 T.root FR
      let Gser : LaurentSeries k := ratFuncAtLaurent46 T.root GR
      let SR : RatFunc k := 2 * CR + RatFunc.C (3 * T.source.gamma)
      let SL : LaurentSeries k := 2 * CL + HahnSeries.C (3 * T.source.gamma)
      let CT : LaurentSeries k :=
        CL + HahnSeries.C ((3 / 2 : k) * T.source.gamma)
      have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root AR (-2) hAH
      have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root BR 11
        (by
          dsimp only [BR]
          norm_num at hB11 ⊢
          exact hB11)
      have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root CR 0
        (by rw [hCRmap]; exact hC)
      have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root FR 3
        (by rw [hFRmap]; exact hF3)
      have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root GR (-1)
        (by rw [hGRmap]; exact hG)
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
        have hhalf : HahnSeries.C (1 / 2 : k) =
            (1 / 2 : LaurentSeries k) := by
          rw [map_div₀, map_one, map_ofNat]
        have hthreehalf : HahnSeries.C ((3 / 2 : k) * T.source.gamma) =
            (3 / 2 : LaurentSeries k) * HahnSeries.C T.source.gamma := by
          rw [map_mul]
          have h32 : HahnSeries.C (3 / 2 : k) =
              (3 / 2 : LaurentSeries k) := by
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
      have hfne :
          (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).coeff 3 ≠ 0 := by
        exact hf3ne
      have hgne :
          (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) ≠ 0 := by
        intro hg0
        rw [hg0, mul_zero, zero_add] at hcap4
        exact (mul_ne_zero hc7ne hfne) hcap4
      have hT0 : 2 *
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff 7 ^ 2 -
          (ratFuncAtHahn46 T.root T.source.B).coeff 11 *
            (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 3 = 0 := by
        linear_combination -hnext.2.1
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
        have hgT1 :
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
              (ratFuncAtHahn46 T.root T.source.D)).coeff 3 * hnext.2.2.2.2 -
            (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).coeff 4 * hcap4
        exact (mul_eq_zero.mp hgT1).resolve_left hgne
      have hBcoeff (n : ℤ) : BL.coeff n =
          (ratFuncAtHahn46 T.root T.source.B).coeff (n : ℚ) := by
        have h := ratFuncAtHahn46_coeff_int68 T.root BR n
        dsimp only [BL, BR]
        exact h.symm
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
        exact hI4twelve.2.2.1
      have hT3L : 4 * CT.coeff 7 * CT.coeff 10 + 4 * CT.coeff 8 * CT.coeff 9 -
          BL.coeff 14 * FL.coeff 3 - BL.coeff 13 * FL.coeff 4 -
          BL.coeff 12 * FL.coeff 5 - BL.coeff 11 * FL.coeff 6 = 0 := by
        rw [hCcoeff 7 (by norm_num), hCcoeff 10 (by norm_num),
          hCcoeff 8 (by norm_num), hCcoeff 9 (by norm_num),
          hBcoeff 14, hFcoeff 3, hBcoeff 13, hFcoeff 4,
          hBcoeff 12, hFcoeff 5, hBcoeff 11, hFcoeff 6]
        exact hdet.2.2.2.2
      have hT4L : 4 * CT.coeff 7 * CT.coeff 11 + 4 * CT.coeff 8 * CT.coeff 10 +
          2 * CT.coeff 9 ^ 2 - BL.coeff 15 * FL.coeff 3 -
          BL.coeff 14 * FL.coeff 4 - BL.coeff 13 * FL.coeff 5 -
          BL.coeff 12 * FL.coeff 6 - BL.coeff 11 * FL.coeff 7 = 0 := by
        rw [hCcoeff 7 (by norm_num), hCcoeff 11 (by norm_num),
          hCcoeff 8 (by norm_num), hCcoeff 10 (by norm_num),
          hCcoeff 9 (by norm_num), hBcoeff 15, hFcoeff 3,
          hBcoeff 14, hFcoeff 4, hBcoeff 13, hFcoeff 5,
          hBcoeff 12, hFcoeff 6, hBcoeff 11, hFcoeff 7]
        exact hpacket.2
      have hf3L : FL.coeff 3 ≠ 0 := by
        rw [hFcoeff 3]
        exact hfne
      have hT5L := rhoOneCap_coordinate_defect_t5_of_rows68
        T.source.epsilon BL CT FL Gser hBL hCT hFL hf3L hR3 hR4
        hT0L hT1L hT2L hT3L hT4L
      have hc7n := hCcoeff 7 (by norm_num)
      have hc8n := hCcoeff 8 (by norm_num)
      have hc9n := hCcoeff 9 (by norm_num)
      have hc10n := hCcoeff 10 (by norm_num)
      have hc11n := hCcoeff 11 (by norm_num)
      have hc12n := hCcoeff 12 (by norm_num)
      have hb11n := hBcoeff 11
      have hb12n := hBcoeff 12
      have hb13n := hBcoeff 13
      have hb14n := hBcoeff 14
      have hb15n := hBcoeff 15
      have hb16n := hBcoeff 16
      have hf3n := hFcoeff 3
      have hf4n := hFcoeff 4
      have hf5n := hFcoeff 5
      have hf6n := hFcoeff 6
      have hf7n := hFcoeff 7
      have hf8n := hFcoeff 8
      norm_num at hc7n hc8n hc9n hc10n hc11n hc12n hb11n hb12n hb13n hb14n hb15n hb16n hf3n hf4n hf5n hf6n hf7n hf8n
      have hT5 : rhoOneCapCoordinateDefectT5Core68
          (ratFuncAtHahn46 T.root T.source.B)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)) = 0 := by
        dsimp only [rhoOneCapCoordinateDefectT5Core68]
        rw [← hc7n, ← hc12n, ← hc8n, ← hc11n, ← hc9n, ← hc10n,
          ← hb16n, ← hf3n, ← hb15n, ← hf4n, ← hb14n, ← hf5n,
          ← hb13n, ← hf6n, ← hb12n, ← hf7n, ← hb11n, ← hf8n]
        exact hT5L
      refine ⟨i3, sold, cs, ?_⟩
      dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapEndpointFivePacket68,
        RhoOneDoubleZeroTerminalGBoundaryCapI4FifteenPacket68,
        RhoOneDoubleZeroTerminalGBoundaryCapI3ElevenPacket68]
      exact ⟨⟨⟨hpacket, hrow11⟩, hrow15⟩, hT5⟩
    · exact (hrays.1 hcoord.1).elim
  · exact Or.inr htail

end AlignedSquareTerminalGBoundaryCapEndpointSourceBackwire68

end Max11DegreeRoutes
