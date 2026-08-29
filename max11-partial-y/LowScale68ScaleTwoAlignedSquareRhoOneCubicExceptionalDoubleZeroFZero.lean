import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDoubleZero

/-! # The `f₁ = 0` descent on the exceptional double-zero component -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicExceptionalDoubleZeroFZero68

variable {k : Type*} [Field k] [CharZero k]

/-- Vanishing of the boundary coefficient of the actual rational-function
`F` defect raises its integral Hahn order by one. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_fZero_order
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hF :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let D := ratFuncAtHahn46 T.root T.source.D
      let F := rhoOneTangentDDefectHahn68 A B D
      (↑(-2 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hf :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let D := ratFuncAtHahn46 T.root T.source.D
      let F := rhoOneTangentDDefectHahn68 A B D
      F.coeff (-2 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let D := ratFuncAtHahn46 T.root T.source.D
    let F := rhoOneTangentDDefectHahn68 A B D
    (↑(-1 : ℚ) : WithTop ℚ) ≤ F.orderTop := by
  dsimp only at hF hf ⊢
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let DR : RatFunc k := T.source.D
  let FR : RatFunc k := DR - RatFunc.C (1 / 3 : k) * AR * BR
  let AH := ratFuncAtHahn46 T.root AR
  let BH := ratFuncAtHahn46 T.root BR
  let DH := ratFuncAtHahn46 T.root DR
  let FRH := ratFuncAtHahn46 T.root FR
  have hFRmap : FRH = rhoOneTangentDDefectHahn68 AH BH DH := by
    dsimp only [FRH, FR, AH, BH, DH, AR, BR, DR,
      rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hbase : (↑(-2 : ℚ) : WithTop ℚ) ≤ FRH.orderTop := by
    rw [hFRmap]
    simpa only [AH, BH, DH, AR, BR, DR] using hF
  have hzero : FRH.coeff (-2 : ℚ) = 0 := by
    rw [hFRmap]
    simpa only [AH, BH, DH, AR, BR, DR] using hf
  have hi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root FR (-2) hbase hzero
  norm_num at hi
  change (↑(-1 : ℚ) : WithTop ℚ) ≤ FRH.orderTop at hi
  rw [hFRmap] at hi
  simpa only [AH, BH, DH, AR, BR, DR] using hi

/-- The analogous one-step gain for the actual `B` coordinate. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_bZero_order
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hB :
      let B := ratFuncAtHahn46 T.root T.source.B
      (0 : WithTop ℚ) ≤ B.orderTop)
    (hb :
      let B := ratFuncAtHahn46 T.root T.source.B
      B.coeff (0 : ℚ) = 0) :
    let B := ratFuncAtHahn46 T.root T.source.B
    (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop := by
  dsimp only at hB hb ⊢
  have hi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root T.source.B 0 hB hb
  norm_num at hi
  exact hi

/-- Vanishing of the next coefficient of the actual `G` defect raises its
integral Hahn order from `-3` to `-2`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_gZero_order
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hG :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      let G := rhoOneTangentEDefectHahn68 A C ER
      (↑(-3 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hg :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      let G := rhoOneTangentEDefectHahn68 A C ER
      G.coeff (-3 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let G := rhoOneTangentEDefectHahn68 A C ER
    (↑(-2 : ℚ) : WithTop ℚ) ≤ G.orderTop := by
  dsimp only at hG hg ⊢
  let AR : RatFunc k := T.source.A
  let C0R : RatFunc k := T.source.C0
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let GR : RatFunc k := ER - RatFunc.C (1 / 3 : k) * AR * CR
  let AH := ratFuncAtHahn46 T.root AR
  let C0H := ratFuncAtHahn46 T.root C0R
  let E0H := ratFuncAtHahn46 T.root E0R
  let CRH := ratFuncAtHahn46 T.root CR
  let ERH := ratFuncAtHahn46 T.root ER
  let GRH := ratFuncAtHahn46 T.root GR
  have hCRmap : CRH = rhoOneCDefectHahn68 AH C0H := by
    dsimp only [CRH, CR, AH, C0H, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ERH = rhoOneEDefectHahn68 AH E0H := by
    dsimp only [ERH, ER, AH, E0H, AR, E0R, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGRmap : GRH = rhoOneTangentEDefectHahn68 AH CRH ERH := by
    dsimp only [GRH, GR, ERH, AH, CRH, AR,
      rhoOneTangentEDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hGRmap' : GRH = rhoOneTangentEDefectHahn68 AH
      (rhoOneCDefectHahn68 AH C0H) (rhoOneEDefectHahn68 AH E0H) := by
    rw [hGRmap, hCRmap, hERmap]
  have hbase : (↑(-3 : ℚ) : WithTop ℚ) ≤ GRH.orderTop := by
    rw [hGRmap']
    simpa only [AH, C0H, E0H, AR, C0R, E0R] using hG
  have hzero : GRH.coeff (-3 : ℚ) = 0 := by
    rw [hGRmap']
    simpa only [AH, C0H, E0H, AR, C0R, E0R] using hg
  have hi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root GR (-3) hbase hzero
  norm_num at hi
  change (↑(-2 : ℚ) : WithTop ℚ) ≤ GRH.orderTop at hi
  rw [hGRmap'] at hi
  simpa only [AH, C0H, E0H, AR, C0R, E0R] using hi

/-- The first available invariant after `f₁ = 0` is the already source-valid
`I₄(-3)` face.  It becomes `b₂ g₁ = 0`, hence gives a discrete order-gain
fork for the two actual source defects. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_fZero_descent
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hnext :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      let F := rhoOneTangentDDefectHahn68 A B D
      let G := rhoOneTangentEDefectHahn68 A C ER
      B.coeff (0 : ℚ) * G.coeff (-3 : ℚ) +
          C.coeff (-1 : ℚ) * F.coeff (-2 : ℚ) = 0)
    (hF :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let D := ratFuncAtHahn46 T.root T.source.D
      let F := rhoOneTangentDDefectHahn68 A B D
      (↑(-2 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hB :
      let B := ratFuncAtHahn46 T.root T.source.B
      (0 : WithTop ℚ) ≤ B.orderTop)
    (hG :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      let G := rhoOneTangentEDefectHahn68 A C ER
      (↑(-3 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hf :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let D := ratFuncAtHahn46 T.root T.source.D
      let F := rhoOneTangentDDefectHahn68 A B D
      F.coeff (-2 : ℚ) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    (↑(-1 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
      (((↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧ B.coeff (0 : ℚ) = 0) ∨
       ((↑(-2 : ℚ) : WithTop ℚ) ≤ G.orderTop ∧ G.coeff (-3 : ℚ) = 0)) := by
  dsimp only at hnext hF hB hG hf ⊢
  have hFgain := T.rhoOne_exceptional_fZero_order hF hf
  dsimp only at hFgain
  have hprod :
      (ratFuncAtHahn46 T.root T.source.B).coeff (0 : ℚ) *
        (rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-3 : ℚ) = 0 := by
    simpa only [hf, mul_zero, add_zero] using hnext
  constructor
  · exact hFgain
  · rcases mul_eq_zero.mp hprod with hb0 | hg3
    · left
      exact ⟨T.rhoOne_exceptional_bZero_order hB hb0, hb0⟩
    · right
      exact ⟨T.rhoOne_exceptional_gZero_order hG hg3, hg3⟩

end AlignedSquareRhoOneCubicExceptionalDoubleZeroFZero68

end Max11DegreeRoutes
