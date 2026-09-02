import Sol68ScaleTwoAlignedSquareQuintupleTerminalScratch

/-! # Wiring the terminal obstruction through the aligned-square gain tower -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGainTower68

variable {k : Type*} [Field k] [CharZero k]

/-! These four predicates record every sibling left by the successive sparse
`I₄` faces.  The only branch omitted at level four is the `B,F` fifth-gain
box, which the terminal Keller row makes impossible. -/

def RhoOneDoubleZeroTerminalResidualFour68
    (gamma : k) (B C : HahnSeries ℚ k) : Prop :=
  B.coeff (4 : ℚ) ≠ 0 ∨
    (B.coeff (4 : ℚ) = 0 ∧
      2 * C.coeff (0 : ℚ) + 3 * gamma = 0)

def RhoOneDoubleZeroTerminalResidualThree68
    (gamma : k) (B C F : HahnSeries ℚ k) : Prop :=
  B.coeff (3 : ℚ) ≠ 0 ∨
    (B.coeff (3 : ℚ) = 0 ∧
      (↑(4 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
      ((((↑(4 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
          F.coeff (3 : ℚ) = 0) ∧
        RhoOneDoubleZeroTerminalResidualFour68 gamma B C) ∨
       2 * C.coeff (0 : ℚ) + 3 * gamma = 0))

def RhoOneDoubleZeroTerminalResidualTwo68
    (gamma : k) (B C F : HahnSeries ℚ k) : Prop :=
  B.coeff (2 : ℚ) ≠ 0 ∨
    (B.coeff (2 : ℚ) = 0 ∧
      (↑(3 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
      ((((↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
          F.coeff (2 : ℚ) = 0) ∧
        RhoOneDoubleZeroTerminalResidualThree68 gamma B C F) ∨
       2 * C.coeff (0 : ℚ) + 3 * gamma = 0))

def RhoOneDoubleZeroTerminalResidualOne68
    (gamma : k) (B C F : HahnSeries ℚ k) : Prop :=
  B.coeff (1 : ℚ) ≠ 0 ∨
    (B.coeff (1 : ℚ) = 0 ∧
      (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
      ((((↑(2 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
          F.coeff (1 : ℚ) = 0) ∧
        RhoOneDoubleZeroTerminalResidualTwo68 gamma B C F) ∨
       2 * C.coeff (0 : ℚ) + 3 * gamma = 0))

/-- At the fourth gain, the `F`-gain sibling is impossible by the terminal
row.  The exact residual consists of the nonzero `B[4]` face and the affine
scalar wall. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_quadrupleGain_terminalResidual
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB :
      (↑(4 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC :
      (0 : WithTop ℚ) ≤
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF :
      (↑(4 : ℚ) : WithTop ℚ) ≤
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
    RhoOneDoubleZeroTerminalResidualFour68 T.source.gamma B C := by
  dsimp only
  have hnext := T.rhoOne_exceptional_doubleZero_quadrupleGain_next
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hb4 | ⟨hb4, hB5, htail⟩
  · exact Or.inl hb4
  · right
    refine ⟨hb4, ?_⟩
    rcases htail with hF5 | hscalar
    · exact (T.rhoOne_exceptional_doubleZero_quintupleBox_impossible
        hp hH hp6 hp5 hp4 P hB5 hC hF5.1 hG hbeta hdelta hzeta).elim
    · exact hscalar

/-- The third-gain selector with its deep fourth/fifth-gain child replaced by
the exact terminal residual. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_tripleGain_terminalResidual
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
    let F := rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A) B
      (ratFuncAtHahn46 T.root T.source.D)
    RhoOneDoubleZeroTerminalResidualThree68 T.source.gamma B C F := by
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
    · left
      exact ⟨hF4, T.rhoOne_exceptional_doubleZero_quadrupleGain_terminalResidual
        hp hH hp6 hp5 hp4 P hB4 hC hF4.1 hG hbeta hdelta hzeta⟩
    · exact Or.inr hscalar

/-- The second-gain selector with the complete later gain tower audited. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_doubleGain_terminalResidual
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
    RhoOneDoubleZeroTerminalResidualTwo68 T.source.gamma B C F := by
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
      exact ⟨hF3, T.rhoOne_exceptional_doubleZero_tripleGain_terminalResidual
        hp hH hp6 hp5 hp4 P hB3 hC hF3.1 hG hbeta hdelta hzeta⟩
    · exact Or.inr hscalar

/-- Strongest source-facing audit of the present gain tower.  Starting at
the first `B,F` gain box, the only residuals are a nonzero `B[n]` face for
`n=1,2,3,4`, or the same affine scalar wall at one of the four stages. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_gainTower_terminalResidual
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
    RhoOneDoubleZeroTerminalResidualOne68 T.source.gamma B C F := by
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
      exact ⟨hF2, T.rhoOne_exceptional_doubleZero_doubleGain_terminalResidual
        hp hH hp6 hp5 hp4 P hB2 hC hF2.1 hG hbeta hdelta hzeta⟩
    · exact Or.inr hscalar

end AlignedSquareTerminalGainTower68

end Max11DegreeRoutes
