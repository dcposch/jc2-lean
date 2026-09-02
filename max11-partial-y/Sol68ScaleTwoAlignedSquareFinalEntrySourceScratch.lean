import Sol68ScaleTwoAlignedSquareSourceFinalResidualScratch

/-! # Exact normalized-source routing into the aligned-square final box -/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareFinalEntrySource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The genuinely later exceptional-box choice in the final entry API.
The initial rho-one cubic packet and the two source divisibilities are not
included: those are supplied separately by the exhaustive source split. -/
def RhoOneAlignedSquareFinalHahnLoadBox68
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
  (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
  (0 : WithTop ℚ) ≤ C.orderTop ∧
  (0 : WithTop ℚ) ≤ F.orderTop ∧
  (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop ∧
  T.source.beta = 0 ∧ T.source.delta = 0 ∧ T.source.zeta = 0

/-- After separating the universally obtained source divisibilities and
the cubic component, the old final-entry predicate is exactly one later
Hahn/load-box conjunct. -/
theorem rhoOneAlignedSquareFinalEntry_iff_hahnLoadBox68
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    {T : SquareZeroLIntegratedLocalRootData68 p q j h0} :
    RhoOneAlignedSquareFinalEntry68 (H := H) T ↔
      ∃ g u : k[X],
        p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
        RhoOneZeroLCubicNextSourcePacket68 T g u ∧
        RhoOneAlignedSquareFinalHahnLoadBox68 T := by
  rfl

/-- The honest local source route.  Square alignment gives both `g,u`
factorizations unconditionally.  The rho-one equations then give exactly
three children: higher source divisibility, the explicit noncubic child, or
the cubic child.  Only on the cubic child is the later Hahn/load box the
single missing conjunct of `RhoOneAlignedSquareFinalEntry68`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_finalEntry_sourceRoutes
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    ∃ g u : k[X],
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      ((h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
       RhoOneZeroLNoncubicSourcePacket68 T g u ∨
       (RhoOneZeroLCubicNextSourcePacket68 T g u ∧
         (¬ RhoOneAlignedSquareFinalHahnLoadBox68 T ∨
          RhoOneAlignedSquareFinalEntry68 (H := H) T))) := by
  obtain ⟨g, hp5⟩ := T.source_scale_fourth_dvd_p5 hp hH hp6
  obtain ⟨u, hp4⟩ := T.source_scale_sq_dvd_p4_afterRhoTwo hp hH hp6
  refine ⟨g, u, hp5, hp4, ?_⟩
  rcases T.rhoOne_component_split_with_cubic_next hp hH hp6 hp5 hp4 with
      hdesc | Pcubic | Pnoncubic
  · exact Or.inl hdesc
  · right
    right
    refine ⟨Pcubic, ?_⟩
    by_cases hbox : RhoOneAlignedSquareFinalHahnLoadBox68 T
    · right
      exact (rhoOneAlignedSquareFinalEntry_iff_hahnLoadBox68).2
        ⟨g, u, hp5, hp4, Pcubic, hbox⟩
    · exact Or.inl hbox
  · exact Or.inr (Or.inl Pnoncubic)

/-- Narrow normalized-source wrapper for an already selected aligned-square
branch.  It constructs the local root datum and returns the exact local
source routing theorem above; no component or exceptional child is dropped. -/
theorem normalized68ScaleTwo_alignedSquare_finalEntry_sourceRoutes
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
       (RhoOneZeroLCubicNextSourcePacket68 T g u ∧
         (¬ RhoOneAlignedSquareFinalHahnLoadBox68 T ∨
          RhoOneAlignedSquareFinalEntry68 (H := H) T))) := by
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
    T.rhoOne_alignedSquare_finalEntry_sourceRoutes hp hH hp6
  exact ⟨j, T, g, u, hp5, hp4, hroutes⟩

end AlignedSquareFinalEntrySource68

end Max11DegreeRoutes
