import Sol68ScaleTwoAlignedSquareBoundaryFiniteChildI3ReductionScratch
import Fable68ScaleTwoAlignedSquareGZeroChildGlobalReductionScratch

/-! # Final provenance-preserving residual for the aligned-square branch -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareFinalResidualAssembly68

variable {k : Type*} [Field k] [CharZero k]

/-- The literal final inventory of the aligned-square route.  The first
conjunct is the ray-deleted nonzero-`G[-1]` selector, with its deep source
`K` cap and finite `I₃[0]` child.  The second and third conjuncts are the
verified global cleared packet and eighth-stage selector of the independent
`G[-1]=0` reduction.  Keeping the two selectors conjunctively preserves
their proof provenance; no historical residual is silently identified with
a later selector whose nonzero hypothesis was not retained in its type. -/
def RhoOneAlignedSquareFinalResidual68
    (root j gamma epsilon : k)
    (h A0 B0 C00 D0 A1 B1 C2 F2 G2 : k[X])
    (hR A0R B0R C00R D0R E0R CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroBoundaryFiniteChildI3ReductionResidual68
      root j gamma epsilon h A0 B0 C00 D0
      hR A0R B0R CR FR GR A B C F G ∧
    (∃ i4 i3 : k,
      RhoOneGZeroChildGlobalCleared68 gamma epsilon i4 i3
        h A1 B1 C2 F2 G2) ∧
    (RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextResidual68
        root j gamma epsilon A0 hR A0R B0R CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneGZeroChildBGainRefinedEighth68 gamma epsilon
            A0R B0R C00R D0R E0R A B C F G ∨
         RhoOneGZeroChildFGainRefinedEighth68 gamma epsilon
            A0R B0R C00R D0R E0R A B C F G)))

/-- Source-facing assembly of the final aligned-square inventory. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_alignedSquareFinalResidual
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
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
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
      AR BR T.source.C0 T.source.D T.source.E CR FR GR A B C F G := by
  dsimp only [RhoOneAlignedSquareFinalResidual68]
  refine ⟨?_, ?_⟩
  · exact
      T.rhoOne_exceptional_doubleZero_refinedGZero_boundaryFiniteChildI3ReductionResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  · exact
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenGlobalReductionResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta

end AlignedSquareFinalResidualAssembly68

end Max11DegreeRoutes
