import Sol68ScaleTwoAlignedSquareFinalHahnLoadBoxSourceScratch
import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDoubleZeroGNext

/-! # Backwiring the last aligned-square order box -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareFinalOrderBoxBackwire68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The strongest existing source backwire into the final order box.  Its
inputs are exactly the selectors already consumed by `gBox_next`; no new
coefficient identity is assumed.  The existing refined faces then show
that the only two remaining boundary siblings are the nonzero `F[-1]` and
nonzero `G[-2]` faces. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_finalOrderBox_from_gBox_selectors
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hmain :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      A.coeff (-2 : ℚ) * B.coeff (-2 : ℚ) = 3 * D.coeff (-4 : ℚ) ∧
      3 * ER.coeff (-5 : ℚ) = A.coeff (-2 : ℚ) * C.coeff (-3 : ℚ))
    (hb :
      let B := ratFuncAtHahn46 T.root T.source.B
      B.coeff (-2 : ℚ) = 0)
    (hc :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ) = 0)
    (hbeta : T.source.beta = 0)
    (hdisc :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      let F := rhoOneTangentDDefectHahn68 A B D
      let G := rhoOneTangentEDefectHahn68 A C ER
      rhoOneZeroLCubicExceptionalDiscriminant68
        (A.coeff (-2 : ℚ)) (F.coeff (-3 : ℚ))
        (G.coeff (-4 : ℚ)) = 0)
    (hdelta : T.source.delta = 0)
    (hb1 :
      let B := ratFuncAtHahn46 T.root T.source.B
      B.coeff (-1 : ℚ) = 0)
    (hc1 :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      (rhoOneCDefectHahn68 A C0).coeff (-2 : ℚ) = 0)
    (hf1 :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let D := ratFuncAtHahn46 T.root T.source.D
      (rhoOneTangentDDefectHahn68 A B D).coeff (-2 : ℚ) = 0)
    (hb2 :
      let B := ratFuncAtHahn46 T.root T.source.B
      B.coeff (0 : ℚ) = 0)
    (hc2 :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      (rhoOneCDefectHahn68 A C0).coeff (-1 : ℚ) = 0)
    (hg1 :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      (rhoOneTangentEDefectHahn68 A C ER).coeff (-3 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C (rhoOneEDefectHahn68 A E)
    F.coeff (-1 : ℚ) ≠ 0 ∨ G.coeff (-2 : ℚ) ≠ 0 ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0) := by
  have hgbox := T.rhoOne_exceptional_doubleZero_gBox_next
    hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc hdelta hb1 hc1 hf1 hb2 hc2 hg1
  dsimp only at hgbox ⊢
  rcases hgbox with ⟨hB, hC, hF, hG, _hzetaFace, hzeta⟩
  have hfaces := T.rhoOne_exceptional_doubleZero_refined_faces
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hfaces
  rcases hfaces with ⟨_hB, _hC, _hF, _hG, h4, h3, _hcompat⟩
  by_cases hf :
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff (-1 : ℚ) = 0
  · have hsplit := T.rhoOne_exceptional_doubleZero_refined_fZero
      P hB hC hF hG hbeta hdelta hzeta h4 h3 hf
    dsimp only at hsplit
    rcases hsplit with ⟨hB', hC', hF', hG', hGgain | hGboundary⟩
    · right
      right
      refine ⟨?_, hzeta⟩
      dsimp only [RhoOneAlignedSquareFinalOrderBox68]
      exact ⟨hB', hC', hF', hGgain.1⟩
    · exact Or.inr (Or.inl hGboundary.1)
  · exact Or.inl hf

end AlignedSquareFinalOrderBoxBackwire68

end Max11DegreeRoutes
