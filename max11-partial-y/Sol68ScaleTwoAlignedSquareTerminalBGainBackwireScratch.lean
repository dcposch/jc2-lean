import Sol68ScaleTwoAlignedSquareTerminalBGainSourceScratch

/-! # Closing the independent B-gain child in the refined-G-zero selector -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalBGainBackwire68

variable {k : Type*} [Field k] [CharZero k]

def RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
    (gamma : k) (B C F : HahnSeries ℚ k) : Prop :=
  ((↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧ B.coeff (1 : ℚ) = 0) ∧
    ((F.coeff (0 : ℚ) = 0 ∧
        (↑(1 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
        RhoOneDoubleZeroTerminalCollapsedOne68 gamma B C F) ∨
      2 * C.coeff (0 : ℚ) + 3 * gamma = 0)

def RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
    (gamma : k) (B C F : HahnSeries ℚ k) : Prop :=
  ((↑(1 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧ F.coeff (0 : ℚ) = 0) ∧
    RhoOneDoubleZeroTerminalCollapsedOne68 gamma B C F

def RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68
    (gamma : k) (B C F G : HahnSeries ℚ k) : Prop :=
  G.coeff (-1 : ℚ) ≠ 0 ∨
    (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
      (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 gamma B C F ∨
       RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 gamma B C F))

/-- The independent `B≥2, F≥0` child is no longer open: its terminal
face either lands on the affine scalar wall or raises `F` and feeds the
already-collapsed gain tower. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalBGainResidual
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB :
      (↑(1 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC :
      (0 : WithTop ℚ) ≤
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF :
      (0 : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG :
      (↑(-1 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A) B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A) C
      (rhoOneEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68
      T.source.gamma B C F G := by
  dsimp only [RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68,
    RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68,
    RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hg | ⟨hg, hG0, htail⟩
  · exact Or.inl hg
  · right
    refine ⟨hg, hG0, ?_⟩
    rcases htail with hBgain | hFgain
    · left
      refine ⟨hBgain, ?_⟩
      have hterminal := T.rhoOne_exceptional_doubleZero_bGain_terminal_split
        hp hH hp6 hp5 hp4 P hBgain.1 hC hF hG0 hbeta hdelta hzeta
      dsimp only at hterminal
      rcases hterminal with hf0 | hscalar
      · left
        let AR : RatFunc k := T.source.A
        let BR : RatFunc k := T.source.B
        let DR : RatFunc k := T.source.D
        let FR : RatFunc k := DR - RatFunc.C (1 / 3 : k) * AR * BR
        have hFRmap : ratFuncAtHahn46 T.root FR =
            rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D) := by
          dsimp only [FR, DR, AR, BR, rhoOneTangentDDefectHahn68]
          simp only [map_sub, map_mul, ratFuncAtHahn46_C]
        have hFR0 : (0 : WithTop ℚ) ≤
            (ratFuncAtHahn46 T.root FR).orderTop := by
          rw [hFRmap]
          exact hF
        have hf0raw : (ratFuncAtHahn46 T.root FR).coeff ((0 : ℤ) : ℚ) = 0 := by
          norm_num
          rw [hFRmap]
          exact hf0
        have hF1raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
          T.root FR 0 hFR0 hf0raw
        norm_num at hF1raw
        have hF1 : (↑(1 : ℚ) : WithTop ℚ) ≤
            (rhoOneTangentDDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.B)
              (ratFuncAtHahn46 T.root T.source.D)).orderTop := by
          rw [← hFRmap]
          exact hF1raw
        exact ⟨hf0, hF1,
          T.rhoOne_exceptional_doubleZero_gainTower_fourBoxResidual
            hp hH hp6 hp5 hp4 P hB hC hF1 hG0 hbeta hdelta hzeta⟩
      · exact Or.inr hscalar
    · right
      exact ⟨hFgain,
        T.rhoOne_exceptional_doubleZero_gainTower_fourBoxResidual
          hp hH hp6 hp5 hp4 P hB hC hFgain.1 hG0 hbeta hdelta hzeta⟩

end AlignedSquareTerminalBGainBackwire68

end Max11DegreeRoutes
