import Sol68ScaleTwoAlignedSquareExceptionalDeepHierarchyScratch

/-! # Normalized aligned-square source final inventory -/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareNormalizedFinalInventory68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Under the exceptional main entry, all compatible source consumers are
already represented by the two named deep sibling packets.  The only
unconsumed last boundaries are `F[-1] != 0` and `G[-2] != 0`; the all-zero
limb reaches the assembled local final residual. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptionalMain_finalInventory
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
    RhoOneAlignedSquareLocalFinalResidual68 T g u := by
  have Ecopy := E0
  dsimp only [RhoOneAlignedSquareExceptionalMainEntry68] at Ecopy
  rcases Ecopy with ⟨P, hmain, hb, hc, hbeta⟩
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
  by_cases hdelta : T.source.delta = 0
  · have hdeep := T.rhoOne_exceptionalMain_deepHierarchy
      hp hH hp6 hp5 hp4 E0
    dsimp only at hdeep
    rcases hdeep with hpre | hgbox | hFne | hGne | ⟨horder, hzeta⟩
    · exact Or.inl hpre
    · exact Or.inr (Or.inl hgbox)
    · exact Or.inr (Or.inr (Or.inl hFne))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hGne)))
    · right
      right
      right
      right
      dsimp only [RhoOneAlignedSquareFinalOrderBox68] at horder
      rcases horder with ⟨hB, hC, hF, hG⟩
      dsimp only [RhoOneAlignedSquareLocalFinalResidual68]
      exact T.rhoOne_exceptional_doubleZero_alignedSquareFinalResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  · left
    dsimp only [RhoOneAlignedSquareExceptionalPreDoubleZeroSibling68]
    by_cases hdisc0 : disc0 = 0
    · have hdisc1 : disc1 ≠ 0 := by
        simpa only [disc1, A, B, C] using
          T.rhoOne_mainTangent_exceptional_secondDiscriminant_ne_zero
            hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc0 hdelta
      exact Or.inr (Or.inl ⟨hdisc0, hdelta, hdisc1⟩)
    · exact Or.inl hdisc0

/-- The minimal local inventory emitted by an aligned square normalized
source.  Every unresolved selector is provenance-preserving and the final
leaf is the already assembled residual algebra. -/
def RhoOneAlignedSquareNormalizedLocalFinalInventory68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C (rhoOneEDefectHahn68 A E)
  (h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
  RhoOneZeroLNoncubicSourcePacket68 T g u ∨
  RhoOneAlignedSquareEarlyCubicSibling68 T g u ∨
  RhoOneAlignedSquareExceptionalPreDoubleZeroSibling68 T ∨
  RhoOneAlignedSquareExceptionalGBoxBoundarySibling68 T ∨
  F.coeff (-1 : ℚ) ≠ 0 ∨ G.coeff (-2 : ℚ) ≠ 0 ∨
  RhoOneAlignedSquareLocalFinalResidual68 T g u

/-- Source-facing assembly of the early and deep selector hierarchies. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_normalizedLocalFinalInventory
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    ∃ g u : k[X],
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      RhoOneAlignedSquareNormalizedLocalFinalInventory68 T g u := by
  obtain ⟨g, u, hp5, hp4, hearly⟩ :=
    T.rhoOne_alignedSquare_sourceSelectorHierarchy hp hH hp6
  refine ⟨g, u, hp5, hp4, ?_⟩
  dsimp only [RhoOneAlignedSquareNormalizedLocalFinalInventory68]
  rcases hearly with hdesc | hnoncubic | hearlySibling | hentry
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl hnoncubic)
  · exact Or.inr (Or.inr (Or.inl hearlySibling))
  · have hfinal := T.rhoOne_exceptionalMain_finalInventory
      hp hH hp6 hp5 hp4 hentry
    dsimp only at hfinal
    rcases hfinal with hpre | hgbox | hFne | hGne | hresidual
    · exact Or.inr (Or.inr (Or.inr (Or.inl hpre)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgbox))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hFne)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl hGne))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr hresidual))))))

/-- Normalized aligned-square wrapper. -/
theorem normalized68ScaleTwo_alignedSquare_finalInventory
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ∃ (j : k) (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
        (g u : k[X]),
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      RhoOneAlignedSquareNormalizedLocalFinalInventory68 T g u := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hsource.2.2.1
  have hp6 : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hsource.2.2.2.2.1
  obtain ⟨j, ⟨T⟩⟩ :=
    normalized68ScaleTwo_alignedSquareBranch_localRootData
      hsource hh0 hH haligned
  obtain ⟨g, u, hp5, hp4, hinventory⟩ :=
    T.rhoOne_alignedSquare_normalizedLocalFinalInventory hp hH hp6
  exact ⟨j, T, g, u, hp5, hp4, hinventory⟩

end AlignedSquareNormalizedFinalInventory68

end Max11DegreeRoutes
