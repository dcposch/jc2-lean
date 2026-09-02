import Sol68ScaleTwoAlignedSquareFinalResidualAssemblyScratch

/-! # Normalized-source handoff to the final aligned-square residual -/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareSourceFinalResidual68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The final residual specialized to one constructed square local-root
datum and its two rho-one cleared source coordinates. -/
def RhoOneAlignedSquareLocalFinalResidual68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
  let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
  let GR : RatFunc k :=
    (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
      RatFunc.C (1 / 3 : k) * AR * CR
  let A0 := localClearedA68RhoOne g u
  let B0 := localClearedB68RhoOne g u (p.coeff 3)
  let C00 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
  let D0 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1)
  let C2 := gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2)
  let F2 := gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1)
  let G2 := gZeroGlobalTangentG68 h0 g u (p.coeff 3) (p.coeff 2)
    (p.coeff 1) (p.coeff 0)
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A
    (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareFinalResidual68
    T.root j T.source.gamma T.source.epsilon
    h0 A0 B0 C00 D0 A0 B0 C2 F2 G2
    (algebraMap k[X] (RatFunc k) h0)
    AR BR T.source.C0 T.source.D T.source.E CR FR GR A B C F G

/-- Exact missing local API: entry into the rho-one exceptional double-zero
box used by the final assembly.  All hypotheses consumed by that assembly,
and no upstream square/nonsquare assumption, occur here. -/
def RhoOneAlignedSquareFinalEntry68
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
  ∃ g u : k[X],
    p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
    RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop ∧
    (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop ∧
    (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop ∧
    (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).orderTop ∧
    T.source.beta = 0 ∧ T.source.delta = 0 ∧ T.source.zeta = 0

/-- Once the exact missing entry packet is supplied, the local square datum
is wired to the final residual without any additional assumptions. -/
theorem SquareZeroLIntegratedLocalRootData68.alignedSquareFinalResidual_of_entry
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hentry : RhoOneAlignedSquareFinalEntry68 (H := H) T) :
    ∃ g u : k[X],
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      RhoOneAlignedSquareLocalFinalResidual68 T g u := by
  rcases hentry with ⟨g, u, hp5, hp4, P, hB, hC, hF, hG,
    hbeta, hdelta, hzeta⟩
  refine ⟨g, u, hp5, hp4, ?_⟩
  dsimp only [RhoOneAlignedSquareLocalFinalResidual68]
  exact T.rhoOne_exceptional_doubleZero_alignedSquareFinalResidual
    hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta

/-- Normalized-source inventory.  The first two leaves are explicit
nonaligned and aligned-nonsquare handoffs.  The square leaf contains the
constructed local datum and either the exact missing entry link, or the
fully assembled residual. -/
def Normalized68ScaleTwoAlignedSquareSourceFinalResidual
    (P Q : MvPolynomial (Fin 2) k) (H : k[X]) : Prop :=
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  let N := (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7
  N ≠ 0 ∨
    (N = 0 ∧ ∀ h0 : k[X], H ≠ h0 ^ 2) ∨
    ∃ (h0 : k[X]) (j : k)
        (T : SquareZeroLIntegratedLocalRootData68 p q j h0),
      H = h0 ^ 2 ∧
      ((¬ RhoOneAlignedSquareFinalEntry68 (H := H) T) ∨
        ∃ g u : k[X],
          p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
          RhoOneAlignedSquareLocalFinalResidual68 T g u)

/-- Every normalized `(6,8)`, scale-two source reaches the final square
inventory.  No nonalignment, squareness, or exceptional-box hypothesis is
assumed: each unresolved routing choice is returned as a literal handoff. -/
theorem normalized68ScaleTwo_alignedSquare_sourceFinalResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2) :
    Normalized68ScaleTwoAlignedSquareSourceFinalResidual P Q H := by
  dsimp only [Normalized68ScaleTwoAlignedSquareSourceFinalResidual]
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  let N := (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7
  have hs := hsource
  rcases hs with ⟨hHne, _hHdegree, hPdegree, _hQdegree, hp6, _hq8,
    _hKeller⟩
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  by_cases haligned : N = 0
  · by_cases hsquare : ∃ h0 : k[X], H = h0 ^ 2
    · rcases hsquare with ⟨h0, hH⟩
      have hh0 : h0 ≠ 0 := by
        intro hh0
        apply hHne
        simp [hH, hh0]
      have haligned' :
          (4 : k[X]) *
              ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 * H -
            (3 : k[X]) *
              ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7 = 0 := by
        simpa only [N, p, q] using haligned
      obtain ⟨j, ⟨T⟩⟩ :=
        normalized68ScaleTwo_alignedSquareBranch_localRootData
          hsource hh0 hH haligned'
      right
      right
      refine ⟨h0, j, T, hH, ?_⟩
      by_cases hentry : RhoOneAlignedSquareFinalEntry68 (H := H) T
      · right
        exact T.alignedSquareFinalResidual_of_entry hp hH hp6' hentry
      · exact Or.inl hentry
    · right
      left
      refine ⟨by simpa only [N, p, q] using haligned, ?_⟩
      intro h0 hH0
      exact hsquare ⟨h0, hH0⟩
  · left
    simpa only [N, p, q] using haligned

end AlignedSquareSourceFinalResidual68

end Max11DegreeRoutes
