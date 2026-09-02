import Sol68ScaleTwoAlignedSquareFinalEntrySourceScratch

/-! # Source reduction of the final aligned-square Hahn/load box -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareFinalHahnLoadBoxSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The four order gains in the final box, separated from the three scalar
load vanishings. -/
def RhoOneAlignedSquareFinalOrderBox68
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
  (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop

/-- Literal audit of the seven final-box conjuncts: the four order gains and
the three source loads are independent fields of the existing API. -/
theorem rhoOneAlignedSquareFinalHahnLoadBox_iff_orderBox_loads68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    {T : SquareZeroLIntegratedLocalRootData68 p q j h0} :
    RhoOneAlignedSquareFinalHahnLoadBox68 T ↔
      RhoOneAlignedSquareFinalOrderBox68 T ∧
      T.source.beta = 0 ∧ T.source.delta = 0 ∧ T.source.zeta = 0 := by
  dsimp only [RhoOneAlignedSquareFinalHahnLoadBox68,
    RhoOneAlignedSquareFinalOrderBox68]
  constructor
  · rintro ⟨hB, hC, hF, hG, hbeta, hdelta, hzeta⟩
    exact ⟨⟨hB, hC, hF, hG⟩, hbeta, hdelta, hzeta⟩
  · rintro ⟨⟨hB, hC, hF, hG⟩, hbeta, hdelta, hzeta⟩
    exact ⟨hB, hC, hF, hG, hbeta, hdelta, hzeta⟩

/-- On the exceptional cubic child, once the three already selected source
loads vanish, the exact residual of the final Hahn/load box is only the
four-order packet. -/
theorem RhoOneZeroLCubicNextSourcePacket68.finalHahnLoadBox_reduction
    {p q : k[X][X]} {j : k} {h0 : k[X]} {g u : k[X]}
    {T : SquareZeroLIntegratedLocalRootData68 p q j h0}
    (_P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    ¬ RhoOneAlignedSquareFinalOrderBox68 T ∨
      RhoOneAlignedSquareFinalHahnLoadBox68 T := by
  by_cases horder : RhoOneAlignedSquareFinalOrderBox68 T
  · exact Or.inr
      (rhoOneAlignedSquareFinalHahnLoadBox_iff_orderBox_loads68.mpr
        ⟨horder, hbeta, hdelta, hzeta⟩)
  · exact Or.inl horder

/-- What the initial cubic source packet itself forces toward the final
orders.  It supplies only the old `B >= -2`, `C >= -3` base box.  Thus the
jumps to `B >= 1`, `C >= 0`, and the final `F,G` bounds cannot be projected
from `P`; they are precisely the later exceptional coefficient selectors. -/
theorem RhoOneZeroLCubicNextSourcePacket68.finalOrder_baseBounds
    {p q : k[X][X]} {j : k} {h0 : k[X]} {g u : k[X]}
    {T : SquareZeroLIntegratedLocalRootData68 p q j h0}
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let C := rhoOneCDefectHahn68 A C0
    (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
      (↑(-3 : ℚ) : WithTop ℚ) ≤ C.orderTop := by
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  exact ⟨hbounds.2.1, hbounds.2.2.2.1⟩

/-- Source routing with the three load vanishings discharged.  The two
unconsumed rho-one siblings remain literal.  On the exceptional cubic child
the only remaining conjunct is the four-order packet above. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_finalEntry_sourceRoutes_of_loads
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    ∃ g u : k[X],
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      ((h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
       RhoOneZeroLNoncubicSourcePacket68 T g u ∨
       (RhoOneZeroLCubicNextSourcePacket68 T g u ∧
         (¬ RhoOneAlignedSquareFinalOrderBox68 T ∨
          RhoOneAlignedSquareFinalEntry68 (H := H) T))) := by
  obtain ⟨g, u, hp5, hp4, hroutes⟩ :=
    T.rhoOne_alignedSquare_finalEntry_sourceRoutes hp hH hp6
  refine ⟨g, u, hp5, hp4, ?_⟩
  rcases hroutes with hdesc | hnoncubic | ⟨Pcubic, _hentryRoute⟩
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl hnoncubic)
  · right
    right
    refine ⟨Pcubic, ?_⟩
    by_cases horder : RhoOneAlignedSquareFinalOrderBox68 T
    · right
      exact (rhoOneAlignedSquareFinalEntry_iff_hahnLoadBox68).2
        ⟨g, u, hp5, hp4, Pcubic,
          rhoOneAlignedSquareFinalHahnLoadBox_iff_orderBox_loads68.mpr
            ⟨horder, hbeta, hdelta, hzeta⟩⟩
    · exact Or.inl horder

end AlignedSquareFinalHahnLoadBoxSource68

end Max11DegreeRoutes
