import Sol68ScaleTwoAlignedSquareTerminalGRaysEliminationScratch
import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapI4NextScratch

/-! # Finite-child reduction on the nonzero-`G[-1]` boundary cap -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryFiniteChildReduction68

variable {k : Type*} [Field k] [CharZero k]

/-- The cap Keller scalar and the last sparse `I₄` transport give two
quadratic scalar walls on the finite `C[1] ≠ 0`, `B[5] ≠ 0` child. -/
theorem rhoOneDoubleZero_boundaryFiniteChild_quadraticWalls68
    (a b c f g q : k)
    (hscalar : (8 / 9 : k) * a * f * g = q)
    (htransport : b * g + c * f = 0) :
    (8 / 9 : k) * a * b * g ^ 2 + q * c = 0 ∧
      (8 / 9 : k) * a * c * f ^ 2 + q * b = 0 := by
  constructor
  · linear_combination
      (8 / 9 : k) * a * g * htransport - c * hscalar
  · linear_combination
      (8 / 9 : k) * a * f * htransport - b * hscalar

/-- The literal finite child after the ray deletion.  Besides the exact
order-five alternatives, it records the first unused `I₄` row and the two
quadratic scalar consequences of the Keller normalization. -/
def RhoOneDoubleZeroBoundaryFiniteChildPacket68
    (root j epsilon : k) (h0R : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  ∃ c : k, c ≠ 0 ∧
    ratFuncAtHahn46 root h0R = HahnSeries.single (1 : ℚ) c ∧
    G.coeff (-1 : ℚ) ≠ 0 ∧ F.coeff (3 : ℚ) ≠ 0 ∧
    C.coeff (1 : ℚ) ≠ 0 ∧ B.coeff (5 : ℚ) ≠ 0 ∧
    B.orderTop = (↑(5 : ℚ) : WithTop ℚ) ∧
    (8 / 9 : k) * A.coeff (-2 : ℚ) * F.coeff (3 : ℚ) *
        G.coeff (-1 : ℚ) = j * c⁻¹ ∧
    B.coeff (5 : ℚ) * G.coeff (-1 : ℚ) +
        C.coeff (1 : ℚ) * F.coeff (3 : ℚ) = 0 ∧
    (8 / 9 : k) * A.coeff (-2 : ℚ) * B.coeff (5 : ℚ) *
        G.coeff (-1 : ℚ) ^ 2 +
          (j * c⁻¹) * C.coeff (1 : ℚ) = 0 ∧
    (8 / 9 : k) * A.coeff (-2 : ℚ) * C.coeff (1 : ℚ) *
        F.coeff (3 : ℚ) ^ 2 +
          (j * c⁻¹) * B.coeff (5 : ℚ) = 0 ∧
    4 * (B.coeff (5 : ℚ) * G.coeff (0 : ℚ) +
          B.coeff (6 : ℚ) * G.coeff (-1 : ℚ)) +
      4 * (C.coeff (1 : ℚ) * F.coeff (4 : ℚ) +
          C.coeff (2 : ℚ) * F.coeff (3 : ℚ)) +
      3 * epsilon * B.coeff (5 : ℚ) = 0

/-- Source-facing selector after deleting both signed rays.  The boundary
is now either the already-frozen deep cap `C[1]=B[5]=0`, or the explicit
finite quadratic packet above; the independently active `G[-1]=0` child is
retained verbatim. -/
def RhoOneDoubleZeroBoundaryFiniteChildReductionResidual68
    (root j gamma epsilon : k)
    (h A0 B0 C00 D0 : k[X])
    (hR AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  (RhoOneDoubleZeroTerminalGBoundaryCapKSourceOrderResidual68
        root j gamma epsilon h A0 B0 C00 D0
        hR AR BR CR FR GR A B C F G ∧
    RhoOneDoubleZeroTerminalGBoundaryCapI4NextResidual68
        root j gamma epsilon hR BR CR FR GR A B C F G ∧
    B.coeff (1 : ℚ) = 0 ∧
    2 * C.coeff (0 : ℚ) + 3 * gamma = 0 ∧
    G.coeff (-1 : ℚ) ≠ 0 ∧
    ((C.coeff (1 : ℚ) = 0 ∧ B.coeff (5 : ℚ) = 0 ∧
        (↑(6 : ℚ) : WithTop ℚ) ≤ B.orderTop) ∨
      RhoOneDoubleZeroBoundaryFiniteChildPacket68
        root j epsilon hR A B C F G)) ∨
  (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
    (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 gamma B C F ∨
     RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 gamma B C F))

/-- Literal source backwire of the boundary finite-child reduction. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_boundaryFiniteChildReductionResidual
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
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A
      (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroBoundaryFiniteChildReductionResidual68
      T.root j T.source.gamma T.source.epsilon h0 A0 B0 C00 D0
      (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G := by
  dsimp only [RhoOneDoubleZeroBoundaryFiniteChildReductionResidual68]
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A
    (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  have hselector := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hselector
  rcases hselector with ⟨_, _, _, _, _, _, hGne | hzero⟩
  · have hrays :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGRaysEliminatedResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    rcases hrays with ⟨hK, hb1, hS0, _hi4zero⟩ | hbad
    · have hnext :=
        T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapI4NextResidual
          hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
      rcases hnext with hi4 | hbad'
      · left
        refine ⟨hK, hi4, hb1, hS0, hGne, ?_⟩
        have htarget := hi4.1.2 ⟨hb1, hS0⟩
        rcases htarget with ⟨c, hc, hsingle, hscalar, hsplit⟩
        rcases hsplit with hdeep | hfinite
        · exact Or.inl hdeep
        · right
          have hshape := hi4.1.1
          dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68]
            at hshape
          rcases hshape with ⟨_hfactor, hboundary | hray⟩
          · rcases hboundary with ⟨hcurrent, _hf2, _hF3, _hb4, _hB5,
                hi4three, hf3ne⟩
            have hrow5 := (hi4.2 ⟨hb1, hS0⟩).1
            have hquadratic :=
              rhoOneDoubleZero_boundaryFiniteChild_quadraticWalls68
                (A.coeff (-2 : ℚ)) (B.coeff (5 : ℚ))
                (C.coeff (1 : ℚ)) (F.coeff (3 : ℚ))
                (G.coeff (-1 : ℚ)) (j * c⁻¹) hscalar hi4three
            exact ⟨c, hc, hsingle, hGne, hf3ne, hfinite.1,
              hfinite.2.1, hfinite.2.2, hscalar, hi4three,
              hquadratic.1, hquadratic.2, hrow5⟩
          · exact (hray.1 hb1).elim
      · exact (hGne hbad'.1).elim
    · exact (hGne hbad.1).elim
  · right
    rcases hzero with ⟨hGzero, hG0, _⟩
    have hres :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalBGainResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only [RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68] at hres
    rcases hres with hbad | ⟨_, _, htail⟩
    · exact (hbad hGzero).elim
    · exact ⟨hGzero, hG0, htail⟩

end AlignedSquareBoundaryFiniteChildReduction68

end Max11DegreeRoutes
