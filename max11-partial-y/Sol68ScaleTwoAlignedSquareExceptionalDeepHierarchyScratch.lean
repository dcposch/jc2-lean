import Sol68ScaleTwoAlignedSquareSourceSelectorHierarchyScratch
import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalHomogeneousSource
import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDoubleZeroBNext
import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDoubleZeroCNext

/-! # Deep source hierarchy under the aligned-square exceptional main entry -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareExceptionalDeepHierarchy68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The exact singular double-zero header immediately before the three
`B[0], C[-1], G[-3]` product forks. -/
def RhoOneAlignedSquareExceptionalSingularBase68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C (rhoOneEDefectHahn68 A E)
  rhoOneZeroLCubicExceptionalDiscriminant68
      (A.coeff (-2 : ℚ)) (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0 ∧
  T.source.delta = 0 ∧
  rhoOneZeroLCubicExceptionalSecondDiscriminant68
      (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ)) (C.coeff (-2 : ℚ)) = 0 ∧
  B.coeff (-1 : ℚ) = 0 ∧ C.coeff (-2 : ℚ) = 0

/-- Every source-compatible sibling before the singular double-zero header.
The `delta != 0` child is strengthened by its existing consumer to a
nonzero second discriminant; the homogeneous child records its exact reduced
polynomial. -/
def RhoOneAlignedSquareExceptionalPreDoubleZeroSibling68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C (rhoOneEDefectHahn68 A E)
  let disc0 := rhoOneZeroLCubicExceptionalDiscriminant68
    (A.coeff (-2 : ℚ)) (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ))
  let disc1 := rhoOneZeroLCubicExceptionalSecondDiscriminant68
    (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ)) (C.coeff (-2 : ℚ))
  disc0 ≠ 0 ∨
  (disc0 = 0 ∧ T.source.delta ≠ 0 ∧ disc1 ≠ 0) ∨
  (disc0 = 0 ∧ T.source.delta = 0 ∧ disc1 ≠ 0) ∨
  (disc0 = 0 ∧ T.source.delta = 0 ∧ disc1 = 0 ∧
    C.coeff (-2 : ℚ) ≠ 0 ∧
    rhoOneZeroLCubicExceptionalHomogeneousReduced68
      (A.coeff (-2 : ℚ)) (A.coeff (-1 : ℚ))
      (B.coeff (-1 : ℚ)) (B.coeff (0 : ℚ))
      (C.coeff (-2 : ℚ)) (C.coeff (-1 : ℚ))
      (F.coeff (-2 : ℚ)) = 0)

/-- Exact nonzero forks after the singular header and before `gBox_next`.
Each later zero branch is selected by an actual source product returned by
`doubleZero_next`, `bBox_next`, or `cBox_next`. -/
def RhoOneAlignedSquareExceptionalGBoxBoundarySibling68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C (rhoOneEDefectHahn68 A E)
  RhoOneAlignedSquareExceptionalSingularBase68 T ∧
  ((F.coeff (-2 : ℚ) ≠ 0 ∧
      3 * B.coeff (0 : ℚ) * F.coeff (-2 : ℚ) =
        2 * A.coeff (-2 : ℚ) * B.coeff (0 : ℚ) ^ 2 +
          6 * C.coeff (-1 : ℚ) ^ 2) ∨
   (F.coeff (-2 : ℚ) = 0 ∧ B.coeff (0 : ℚ) ≠ 0 ∧
      G.coeff (-3 : ℚ) = 0) ∨
   (F.coeff (-2 : ℚ) = 0 ∧ B.coeff (0 : ℚ) = 0 ∧
      C.coeff (-1 : ℚ) ≠ 0 ∧ G.coeff (-3 : ℚ) = 0) ∨
   (F.coeff (-2 : ℚ) = 0 ∧ B.coeff (0 : ℚ) = 0 ∧
      C.coeff (-1 : ℚ) = 0 ∧ G.coeff (-3 : ℚ) ≠ 0 ∧
      2 * C.coeff (0 : ℚ) + 3 * T.source.gamma = 0))

/-- Conditional exhaustive deep hierarchy.  Only the literal all-zero
product limb is passed to the previously verified final-order backwire. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptionalMain_deepHierarchy
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (E0 : RhoOneAlignedSquareExceptionalMainEntry68 T g u) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C (rhoOneEDefectHahn68 A E)
    RhoOneAlignedSquareExceptionalPreDoubleZeroSibling68 T ∨
    RhoOneAlignedSquareExceptionalGBoxBoundarySibling68 T ∨
    F.coeff (-1 : ℚ) ≠ 0 ∨ G.coeff (-2 : ℚ) ≠ 0 ∨
    (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0) := by
  dsimp only [RhoOneAlignedSquareExceptionalMainEntry68] at E0
  rcases E0 with ⟨P, hmain, hb, hc, hbeta⟩
  dsimp only at hmain hb hc ⊢
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C (rhoOneEDefectHahn68 A E)
  let disc0 := rhoOneZeroLCubicExceptionalDiscriminant68
    (A.coeff (-2 : ℚ)) (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ))
  let disc1 := rhoOneZeroLCubicExceptionalSecondDiscriminant68
    (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ)) (C.coeff (-2 : ℚ))
  by_cases hdisc0 : disc0 = 0
  · have hfg := T.rhoOne_mainTangent_exceptional_discriminant_zero
      hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc0
    have hdeg := T.rhoOne_mainTangent_exceptional_discriminant_next
      hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc0
    dsimp only at hfg hdeg
    by_cases hdelta : T.source.delta = 0
    · by_cases hdisc1 : disc1 = 0
      · have hcompat :=
          T.rhoOne_mainTangent_exceptional_homogeneous_compatibility
            hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc0 hdelta hdisc1
        dsimp only at hcompat
        have ha : A.coeff (-2 : ℚ) ≠ 0 := by
          simpa only [A] using P.2.2.1
        have hhom := rhoOneZeroLCubicExceptional_homogeneous_singular_reduction68
          (A.coeff (-2 : ℚ)) (A.coeff (-1 : ℚ))
          (B.coeff (-1 : ℚ)) (B.coeff (0 : ℚ))
          (C.coeff (-2 : ℚ)) (C.coeff (-1 : ℚ))
          (F.coeff (-2 : ℚ)) (G.coeff (-3 : ℚ))
          ha (by simpa only [hdelta, A, B, C, F, G] using hdeg.1)
            hdisc1 hcompat
        rcases hhom with ⟨hb1, hc1⟩ | hhomSibling
        · have hnext := T.rhoOne_mainTangent_exceptional_doubleZero_next
            hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc0 hdelta hb1 hc1
          dsimp only at hnext
          by_cases hf1 : F.coeff (-2 : ℚ) = 0
          · have hprodBG : B.coeff (0 : ℚ) * G.coeff (-3 : ℚ) = 0 := by
              have hnext1 : B.coeff (0 : ℚ) * G.coeff (-3 : ℚ) +
                  C.coeff (-1 : ℚ) * F.coeff (-2 : ℚ) = 0 := by
                simpa only [A, B, C0, D, E, C, F, G] using hnext.1
              simpa only [hf1, mul_zero, add_zero] using hnext1
            by_cases hb2 : B.coeff (0 : ℚ) = 0
            · have hbBox := T.rhoOne_exceptional_doubleZero_bBox_next
                hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc0 hdelta
                  hb1 hc1 hf1 hb2
              dsimp only at hbBox
              by_cases hc2 : C.coeff (-1 : ℚ) = 0
              · have hcBox := T.rhoOne_exceptional_doubleZero_cBox_next
                  hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc0 hdelta
                    hb1 hc1 hf1 hb2 hc2
                dsimp only at hcBox
                by_cases hg1 : G.coeff (-3 : ℚ) = 0
                · have hfinal := T.rhoOne_finalOrderBox_from_gBox_selectors
                    hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc0 hdelta
                      hb1 hc1 hf1 hb2 hc2 hg1
                  dsimp only at hfinal
                  rcases hfinal with hFne | hGne | hbox
                  · exact Or.inr (Or.inr (Or.inl hFne))
                  · exact Or.inr (Or.inr (Or.inr (Or.inl hGne)))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr hbox)))
                · have hS : 2 * C.coeff (0 : ℚ) + 3 * T.source.gamma = 0 :=
                    (mul_eq_zero.mp hcBox.2.2.2.1).resolve_left hg1
                  right
                  left
                  dsimp only [RhoOneAlignedSquareExceptionalGBoxBoundarySibling68,
                    RhoOneAlignedSquareExceptionalSingularBase68]
                  exact ⟨⟨hdisc0, hdelta, hdisc1, hb1, hc1⟩,
                    Or.inr (Or.inr (Or.inr ⟨hf1, hb2, hc2, hg1, hS⟩))⟩
              · have hg1 : G.coeff (-3 : ℚ) = 0 :=
                  (mul_eq_zero.mp hbBox.1).resolve_left hc2
                right
                left
                dsimp only [RhoOneAlignedSquareExceptionalGBoxBoundarySibling68,
                  RhoOneAlignedSquareExceptionalSingularBase68]
                exact ⟨⟨hdisc0, hdelta, hdisc1, hb1, hc1⟩,
                  Or.inr (Or.inr (Or.inl ⟨hf1, hb2, hc2, hg1⟩))⟩
            · have hg1 : G.coeff (-3 : ℚ) = 0 :=
                (mul_eq_zero.mp hprodBG).resolve_left hb2
              right
              left
              dsimp only [RhoOneAlignedSquareExceptionalGBoxBoundarySibling68,
                RhoOneAlignedSquareExceptionalSingularBase68]
              exact ⟨⟨hdisc0, hdelta, hdisc1, hb1, hc1⟩,
                Or.inr (Or.inl ⟨hf1, hb2, hg1⟩)⟩
          · have hnonlinear := hnext.2.resolve_left hf1
            right
            left
            dsimp only [RhoOneAlignedSquareExceptionalGBoxBoundarySibling68,
              RhoOneAlignedSquareExceptionalSingularBase68]
            exact ⟨⟨hdisc0, hdelta, hdisc1, hb1, hc1⟩,
              Or.inl ⟨hf1, hnonlinear⟩⟩
        · left
          dsimp only [RhoOneAlignedSquareExceptionalPreDoubleZeroSibling68]
          exact Or.inr (Or.inr (Or.inr
            ⟨hdisc0, hdelta, hdisc1, hhomSibling.1, hhomSibling.2⟩))
      · left
        dsimp only [RhoOneAlignedSquareExceptionalPreDoubleZeroSibling68]
        exact Or.inr (Or.inr (Or.inl ⟨hdisc0, hdelta, hdisc1⟩))
    · have hdisc1 : disc1 ≠ 0 := by
        simpa only [disc1, A, B, C] using
          T.rhoOne_mainTangent_exceptional_secondDiscriminant_ne_zero
            hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc0 hdelta
      left
      dsimp only [RhoOneAlignedSquareExceptionalPreDoubleZeroSibling68]
      exact Or.inr (Or.inl ⟨hdisc0, hdelta, hdisc1⟩)
  · left
    dsimp only [RhoOneAlignedSquareExceptionalPreDoubleZeroSibling68]
    exact Or.inl hdisc0

end AlignedSquareExceptionalDeepHierarchy68

end Max11DegreeRoutes
