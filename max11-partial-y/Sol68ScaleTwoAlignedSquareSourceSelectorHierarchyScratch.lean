import Sol68ScaleTwoAlignedSquareFinalOrderBoxBackwireScratch
import LowScale68ScaleTwoAlignedSquareRhoOneCubicRowOneSource
import LowScale68ScaleTwoAlignedSquareRhoOneCubicMainTangentOrderBridge

/-! # Exhaustive source hierarchy before the exceptional double-zero box -/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareSourceSelectorHierarchy68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The exceptional main-tangent child which is the only early component
capable of reaching the later `gBox` selector chain. -/
def RhoOneAlignedSquareExceptionalMainEntry68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    (A.coeff (-2 : ℚ) * B.coeff (-2 : ℚ) = 3 * D.coeff (-4 : ℚ) ∧
      3 * ER.coeff (-5 : ℚ) = A.coeff (-2 : ℚ) * C.coeff (-3 : ℚ)) ∧
    B.coeff (-2 : ℚ) = 0 ∧ C.coeff (-3 : ℚ) = 0 ∧
    T.source.beta = 0

/-- Literal inventory of every sibling exposed before the exceptional
`b=c=beta=0` main-tangent child.  None is converted to a nonzero-septic
packet: the local datum here has septic coefficient exactly zero. -/
def RhoOneAlignedSquareEarlyCubicSibling68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C ER
  let a := A.coeff (-2 : ℚ)
  let b := B.coeff (-2 : ℚ)
  let c := C.coeff (-3 : ℚ)
  let d := D.coeff (-4 : ℚ)
  let e := ER.coeff (-5 : ℚ)
  RhoOneZeroLCubicSecondNextComponent68 T g u ∨
  (RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0) ∨
  (RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    (a * b = 3 * d ∧ 3 * e = a * c) ∧
    ((c = 0 ∧ b ≠ 0 ∧ F.coeff (-3 : ℚ) = 0 ∧
        -64 * b ^ 3 + 15 * T.source.beta * a ^ 3 +
          576 * b * G.coeff (-4 : ℚ) = 0) ∨
      (c ≠ 0 ∧ b ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
        rhoOneZeroLCubicMainTangentFour68 T.source.beta a b c
          (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0 ∧
        rhoOneZeroLCubicMainTangentThree68 a b c
          (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0)))

/-- Exhaustive source trichotomy on `ZeroLCubicNext`: second component,
the row-one exceptional/nonzero main-tangent siblings, or the unique
`b=c=beta=0` main-tangent entry. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_cubic_earlySelector_trichotomy
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u) :
    RhoOneAlignedSquareEarlyCubicSibling68 T g u ∨
      RhoOneAlignedSquareExceptionalMainEntry68 T g u := by
  rcases P.component_split with Pfirst | Psecond
  · have Prefined := Pfirst.refine_with_I3
    have Prow := Prefined.refine_with_rowOne hp hH hp6 hp5 hp4
    dsimp only [RhoOneZeroLCubicFirstRowOneComponent68] at Prow
    rcases Prow with ⟨P0, hmain | hrowExceptional⟩
    · have hres := T.rhoOne_mainTangent_residual
        hp hH hp6 hp5 hp4 P0 hmain
      dsimp only [RhoOneZeroLCubicMainTangentInvariantResidual68] at hres
      rcases hres with ⟨hc, hbzero | hbnonzero⟩ | hcnonzero
      · right
        dsimp only [RhoOneAlignedSquareExceptionalMainEntry68]
        exact ⟨P0, hmain, hbzero.1, hc, hbzero.2⟩
      · left
        dsimp only [RhoOneAlignedSquareEarlyCubicSibling68]
        exact Or.inr (Or.inr ⟨P0, hmain, Or.inl ⟨hc, hbnonzero⟩⟩)
      · left
        dsimp only [RhoOneAlignedSquareEarlyCubicSibling68]
        exact Or.inr (Or.inr ⟨P0, hmain, Or.inr hcnonzero⟩)
    · left
      dsimp only [RhoOneAlignedSquareEarlyCubicSibling68]
      exact Or.inr (Or.inl ⟨P0, hrowExceptional⟩)
  · left
    dsimp only [RhoOneAlignedSquareEarlyCubicSibling68]
    exact Or.inl Psecond

/-- Full aligned square-source inventory through the first source-valid
main-tangent hierarchy.  The higher-divisibility and explicit noncubic
zero-septic siblings are retained literally. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_sourceSelectorHierarchy
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    ∃ g u : k[X],
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      ((h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
       RhoOneZeroLNoncubicSourcePacket68 T g u ∨
       RhoOneAlignedSquareEarlyCubicSibling68 T g u ∨
       RhoOneAlignedSquareExceptionalMainEntry68 T g u) := by
  obtain ⟨g, hp5⟩ := T.source_scale_fourth_dvd_p5 hp hH hp6
  obtain ⟨u, hp4⟩ := T.source_scale_sq_dvd_p4_afterRhoTwo hp hH hp6
  refine ⟨g, u, hp5, hp4, ?_⟩
  rcases T.rhoOne_component_split_with_cubic_next hp hH hp6 hp5 hp4 with
      hdesc | Pcubic | Pnoncubic
  · exact Or.inl hdesc
  · rcases T.rhoOne_cubic_earlySelector_trichotomy
      hp hH hp6 hp5 hp4 Pcubic with hsibling | hentry
    · exact Or.inr (Or.inr (Or.inl hsibling))
    · exact Or.inr (Or.inr (Or.inr hentry))
  · exact Or.inr (Or.inl Pnoncubic)

/-- Normalized aligned-square source wrapper for the selector hierarchy. -/
theorem normalized68ScaleTwo_alignedSquare_sourceSelectorHierarchy
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
      ((h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
       RhoOneZeroLNoncubicSourcePacket68 T g u ∨
       RhoOneAlignedSquareEarlyCubicSibling68 T g u ∨
       RhoOneAlignedSquareExceptionalMainEntry68 T g u) := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hsource.2.2.1
  have hp6 : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hsource.2.2.2.2.1
  obtain ⟨j, ⟨T⟩⟩ :=
    normalized68ScaleTwo_alignedSquareBranch_localRootData
      hsource hh0 hH haligned
  obtain ⟨g, u, hp5, hp4, hroutes⟩ :=
    T.rhoOne_alignedSquare_sourceSelectorHierarchy hp hH hp6
  exact ⟨j, T, g, u, hp5, hp4, hroutes⟩

end AlignedSquareSourceSelectorHierarchy68

end Max11DegreeRoutes
