import Sol68ScaleTwoAlignedSquareTerminalFourBoxScratch

/-! # Back-wiring the fourth-box terminal deletion -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalFourBoxBackwire68

variable {k : Type*} [Field k] [CharZero k]

def RhoOneDoubleZeroTerminalCollapsedThree68
    (gamma : k) (B C : HahnSeries ℚ k) : Prop :=
  B.coeff (3 : ℚ) ≠ 0 ∨
    (B.coeff (3 : ℚ) = 0 ∧
      (↑(4 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
      2 * C.coeff (0 : ℚ) + 3 * gamma = 0)

def RhoOneDoubleZeroTerminalCollapsedTwo68
    (gamma : k) (B C F : HahnSeries ℚ k) : Prop :=
  B.coeff (2 : ℚ) ≠ 0 ∨
    (B.coeff (2 : ℚ) = 0 ∧
      (↑(3 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
      ((((↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
          F.coeff (2 : ℚ) = 0) ∧
        RhoOneDoubleZeroTerminalCollapsedThree68 gamma B C) ∨
       2 * C.coeff (0 : ℚ) + 3 * gamma = 0))

def RhoOneDoubleZeroTerminalCollapsedOne68
    (gamma : k) (B C F : HahnSeries ℚ k) : Prop :=
  B.coeff (1 : ℚ) ≠ 0 ∨
    (B.coeff (1 : ℚ) = 0 ∧
      (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
      ((((↑(2 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
          F.coeff (1 : ℚ) = 0) ∧
        RhoOneDoubleZeroTerminalCollapsedTwo68 gamma B C F) ∨
       2 * C.coeff (0 : ℚ) + 3 * gamma = 0))

/-- After the fourth box is deleted, the third selector has only its nonzero
`B[3]` face and affine sibling. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_tripleGain_fourBoxResidual
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB :
      (↑(3 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC :
      (0 : WithTop ℚ) ≤
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF :
      (↑(3 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG :
      (0 : WithTop ℚ) ≤
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
    RhoOneDoubleZeroTerminalCollapsedThree68 T.source.gamma B C := by
  dsimp only
  have hnext := T.rhoOne_exceptional_doubleZero_tripleGain_next
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hb3 | ⟨hb3, hB4, htail⟩
  · exact Or.inl hb3
  · right
    refine ⟨hb3, hB4, ?_⟩
    rcases htail with hF4 | hscalar
    · exact (T.rhoOne_exceptional_doubleZero_fourBox_impossible
        hp hH hp6 hp5 hp4 P hB4 hC hF4.1 hG hbeta hdelta hzeta).elim
    · exact hscalar

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_doubleGain_fourBoxResidual
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB :
      (↑(2 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC :
      (0 : WithTop ℚ) ≤
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF :
      (↑(2 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG :
      (0 : WithTop ℚ) ≤
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
    RhoOneDoubleZeroTerminalCollapsedTwo68 T.source.gamma B C F := by
  dsimp only
  have hnext := T.rhoOne_exceptional_doubleZero_doubleGain_next
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hb2 | ⟨hb2, hB3, htail⟩
  · exact Or.inl hb2
  · right
    refine ⟨hb2, hB3, ?_⟩
    rcases htail with hF3 | hscalar
    · left
      exact ⟨hF3, T.rhoOne_exceptional_doubleZero_tripleGain_fourBoxResidual
        hp hH hp6 hp5 hp4 P hB3 hC hF3.1 hG hbeta hdelta hzeta⟩
    · exact Or.inr hscalar

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_gainTower_fourBoxResidual
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
      (↑(1 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG :
      (0 : WithTop ℚ) ≤
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
    RhoOneDoubleZeroTerminalCollapsedOne68 T.source.gamma B C F := by
  dsimp only
  have hnext := T.rhoOne_exceptional_doubleZero_gZero_fNext
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hb1 | ⟨hb1, hB2, htail⟩
  · exact Or.inl hb1
  · right
    refine ⟨hb1, hB2, ?_⟩
    rcases htail with hF2 | hscalar
    · left
      exact ⟨hF2, T.rhoOne_exceptional_doubleZero_doubleGain_fourBoxResidual
        hp hH hp6 hp5 hp4 P hB2 hC hF2.1 hG hbeta hdelta hzeta⟩
    · exact Or.inr hscalar

def RhoOneDoubleZeroRefinedGZeroTerminalResidual68
    (gamma : k) (B C F G : HahnSeries ℚ k) : Prop :=
  G.coeff (-1 : ℚ) ≠ 0 ∨
    (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
      (((↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
          B.coeff (1 : ℚ) = 0) ∨
       (((↑(1 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
          F.coeff (0 : ℚ) = 0) ∧
        RhoOneDoubleZeroTerminalCollapsedOne68 gamma B C F)))

/-- Backward audit through the preceding `G[-1]=0` selector.  Its `F`-gain
child now carries the collapsed terminal residual; its independent `B`-gain
child and the nonzero `G[-1]` face remain explicit. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalResidual
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
    RhoOneDoubleZeroRefinedGZeroTerminalResidual68
      T.source.gamma B C F G := by
  dsimp only
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hg | ⟨hg, hG0, htail⟩
  · exact Or.inl hg
  · right
    refine ⟨hg, hG0, ?_⟩
    rcases htail with hBgain | hFgain
    · exact Or.inl hBgain
    · right
      exact ⟨hFgain, T.rhoOne_exceptional_doubleZero_gainTower_fourBoxResidual
        hp hH hp6 hp5 hp4 P hB hC hFgain.1 hG0 hbeta hdelta hzeta⟩

end AlignedSquareTerminalFourBoxBackwire68

end Max11DegreeRoutes
