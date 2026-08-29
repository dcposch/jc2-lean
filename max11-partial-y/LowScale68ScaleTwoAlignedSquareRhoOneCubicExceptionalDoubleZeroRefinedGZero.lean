import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDoubleZeroRefinedFZero

/-! # The next faces after the `g = 0` order gain -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicExceptionalDoubleZeroRefinedGZero68

variable {k : Type*} [Field k] [CharZero k]

local instance exceptionalDoubleZeroRefinedGZeroHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def rhoOneZeroLCubicDoubleZeroGZeroFour68
    (gamma b c f g : k) : k :=
  2 * b * g + f * (2 * c + 3 * gamma)

def rhoOneZeroLCubicDoubleZeroGZeroThree68
    (gamma a b c f g : k) : k :=
  -2 * a * b * f + 3 * g * (2 * c + 3 * gamma)

/-- Exact next faces in the box `ord(B) ≥ 1`, `ord(C) ≥ 0`,
`ord(F) ≥ 0`, `ord(G) ≥ -1`.  The `I₃(-1)` face is load-free, while
`I₄(0)` records the ground-field first-integral load. -/
theorem firstIntegral_mainTangent_doubleZero_gZero_faces68
    (gamma epsilon : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (0 : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop) :
    (firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C (0 : k))
      (HahnSeries.C epsilon) (HahnSeries.C (0 : k))).coeff (0 : ℚ) =
        (4 / 3 : k) * rhoOneZeroLCubicDoubleZeroGZeroFour68 gamma
          (B.coeff (1 : ℚ)) (C.coeff (0 : ℚ))
          (F.coeff (0 : ℚ)) (G.coeff (-1 : ℚ)) ∧
    (firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C (0 : k))
      (HahnSeries.C epsilon) (HahnSeries.C (0 : k))).coeff (-1 : ℚ) =
        (4 / 9 : k) * rhoOneZeroLCubicDoubleZeroGZeroThree68 gamma
          (A.coeff (-2 : ℚ)) (B.coeff (1 : ℚ)) (C.coeff (0 : ℚ))
          (F.coeff (0 : ℚ)) (G.coeff (-1 : ℚ)) := by
  have hz (r : ℚ) (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : r < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5 n1 n2 n3 n4 n5).coeff r = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 r h1 h2 h3 h4 h5 hlt
  have lead (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop) :=
    weightedMonomial68_coeff_at_general_lower_next s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
  have h4dec := firstIntegralFour_mainTangent_decomposition68
    (k := HahnSeries ℚ k) (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
      (HahnSeries.C (0 : k)) (HahnSeries.C epsilon) (HahnSeries.C (0 : k))
      A B C F G
  have h3dec := firstIntegralThree_mainTangent_decomposition68
    (k := HahnSeries ℚ k) (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
      (HahnSeries.C (0 : k)) (HahnSeries.C epsilon) (HahnSeries.C (0 : k))
      A B C F G
  have h4decH :
      firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
          (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
          (HahnSeries.C gamma) (HahnSeries.C (0 : k))
          (HahnSeries.C epsilon) (HahnSeries.C (0 : k)) =
        firstIntegralFourMainTangentTopHahn68 0 A B C F G +
          firstIntegralFourMainTangentLowerHahn68 0 gamma 0 epsilon 0
            A B C F G := by
    rw [h4dec]
    simp only [firstIntegralFourMainTangentTop68,
      firstIntegralFourMainTangentLower68,
      firstIntegralFourMainTangentTopHahn68,
      firstIntegralFourMainTangentLowerHahn68, weightedMonomial68,
      map_mul, map_neg, map_div₀, map_ofNat, map_one]
    ring
  have h3decH :
      firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
          (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
          (HahnSeries.C gamma) (HahnSeries.C (0 : k))
          (HahnSeries.C epsilon) (HahnSeries.C (0 : k)) =
        firstIntegralThreeMainTangentTopHahn68 A B C F G +
          firstIntegralThreeMainTangentLowerHahn68 0 gamma 0 epsilon 0
            A B C F G := by
    rw [h3dec]
    simp only [firstIntegralThreeMainTangentTop68,
      firstIntegralThreeMainTangentLower68,
      firstIntegralThreeMainTangentTopHahn68,
      firstIntegralThreeMainTangentLowerHahn68, weightedMonomial68,
      map_mul, map_neg, map_div₀, map_ofNat, map_one]
    ring
  have h4t1 := hz 0 (-8 / 27 : k) B A C F G 3 0 0 0 0
    1 (-2) 0 0 (-1) hB hA hC hF hG (by norm_num)
  have h4t3 := lead (8 / 3 : k) B G A C F 1 1 0 0 0
    1 (-1) (-2) 0 0 hB hG hA hC hF
  have h4t4 := lead (8 / 3 : k) C F A B G 1 1 0 0 0
    0 0 (-2) 1 (-1) hC hF hA hB hG
  have h4l6 := lead (4 * gamma) F A B C G 1 0 0 0 0
    0 (-2) 1 0 (-1) hF hA hB hC hG
  have h4l8 := hz 0 (2 * epsilon) B A C F G 1 0 0 0 0
    1 (-2) 0 0 (-1) hB hA hC hF hG (by norm_num)
  have h3t1 := lead (-8 / 9 : k) A B F C G 1 1 1 0 0
    (-2) 1 0 0 (-1) hA hB hF hC hG
  have h3t2 := hz (-1) (-8 / 9 : k) B C A F G 2 1 0 0 0
    1 0 (-2) 0 (-1) hB hC hA hF hG (by norm_num)
  have h3t3 := lead (8 / 3 : k) C G A B F 1 1 0 0 0
    0 (-1) (-2) 1 0 hC hG hA hB hF
  have h3l2 := hz (-1) (4 / 3 : k) F A B C G 2 0 0 0 0
    0 (-2) 1 0 (-1) hF hA hB hC hG (by norm_num)
  have h3l6 := hz (-1) (-(2 / 3 : k) * gamma) B A C F G 2 0 0 0 0
    1 (-2) 0 0 (-1) hB hA hC hF hG (by norm_num)
  have h3l7 := lead (4 * gamma) G A B C F 1 0 0 0 0
    (-1) (-2) 1 0 0 hG hA hB hC hF
  have h3l8 := hz (-1) (2 * epsilon) C A B F G 1 0 0 0 0
    0 (-2) 1 0 (-1) hC hA hB hF hG (by norm_num)
  norm_num at h4t3 h4t4 h4l6 h3t1 h3t3 h3l7
  have h3t1' :
      (weightedMonomial68 (-8 / 9 : k) A B F C G 1 1 1 0 0).coeff
          (-1 : ℚ) =
        (-8 / 9 : k) * A.coeff (-2 : ℚ) * B.coeff (1 : ℚ) *
          F.coeff (0 : ℚ) := by
    convert h3t1 using 1 <;> ring
  have hCzero : (HahnSeries.C (0 : k) : HahnSeries ℚ k) = 0 :=
    HahnSeries.C_zero
  constructor
  · rw [h4decH]
    simp only [HahnSeries.coeff_add, firstIntegralFourMainTangentTopHahn68,
      firstIntegralFourMainTangentLowerHahn68]
    rw [h4t1, h4t3, h4t4, h4l6, h4l8]
    simp only [weightedMonomial68, mul_zero, zero_mul, neg_zero,
      HahnSeries.coeff_zero]
    rw [hCzero]
    simp only [zero_mul, HahnSeries.coeff_zero, add_zero,
      rhoOneZeroLCubicDoubleZeroGZeroFour68]
    ring
  · rw [h3decH]
    simp only [HahnSeries.coeff_add, firstIntegralThreeMainTangentTopHahn68,
      firstIntegralThreeMainTangentLowerHahn68]
    rw [h3t1', h3t2, h3t3, h3l2, h3l6, h3l7, h3l8]
    simp only [weightedMonomial68, mul_zero, zero_mul, neg_zero,
      HahnSeries.coeff_zero]
    rw [hCzero]
    simp only [zero_mul, HahnSeries.coeff_zero, add_zero,
      rhoOneZeroLCubicDoubleZeroGZeroThree68]
    ring

/-- Rational-function transport, retaining the `I₄` load explicitly. -/
theorem ratFunc_doubleZero_gZero_faces68
    (root : k) (A B C F G : RatFunc k)
    (gamma epsilon i4 i3 : k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hi4 : firstIntegralFour68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      (RatFunc.C (0 : k)) (RatFunc.C gamma) (RatFunc.C (0 : k))
      (RatFunc.C epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4)
    (hi3 : firstIntegralThree68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      (RatFunc.C (0 : k)) (RatFunc.C gamma) (RatFunc.C (0 : k))
      (RatFunc.C epsilon) (RatFunc.C (0 : k)) = RatFunc.C i3) :
    i4 = (4 / 3 : k) * rhoOneZeroLCubicDoubleZeroGZeroFour68 gamma
      ((ratFuncAtHahn46 root B).coeff (1 : ℚ))
      ((ratFuncAtHahn46 root C).coeff (0 : ℚ))
      ((ratFuncAtHahn46 root F).coeff (0 : ℚ))
      ((ratFuncAtHahn46 root G).coeff (-1 : ℚ)) ∧
    rhoOneZeroLCubicDoubleZeroGZeroThree68 gamma
      ((ratFuncAtHahn46 root A).coeff (-2 : ℚ))
      ((ratFuncAtHahn46 root B).coeff (1 : ℚ))
      ((ratFuncAtHahn46 root C).coeff (0 : ℚ))
      ((ratFuncAtHahn46 root F).coeff (0 : ℚ))
      ((ratFuncAtHahn46 root G).coeff (-1 : ℚ)) = 0 := by
  have hi4H := congrArg (ratFuncAtHahn46 root) hi4
  have hi3H := congrArg (ratFuncAtHahn46 root) hi3
  have hi4H' :
      firstIntegralFour68 0 (ratFuncAtHahn46 root A)
          (ratFuncAtHahn46 root B)
          ((ratFuncAtHahn46 root A) ^ 2 / 3 + ratFuncAtHahn46 root C)
          ((ratFuncAtHahn46 root A) * (ratFuncAtHahn46 root B) / 3 +
            ratFuncAtHahn46 root F)
          ((ratFuncAtHahn46 root A) ^ 3 / 27 +
            (ratFuncAtHahn46 root A) * (ratFuncAtHahn46 root C) / 3 +
              ratFuncAtHahn46 root G)
          (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
          (HahnSeries.C (0 : k)) (HahnSeries.C epsilon)
          (HahnSeries.C (0 : k)) = HahnSeries.C i4 := by
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtHahn46_C] using hi4H
  have hi3H' :
      firstIntegralThree68 0 (ratFuncAtHahn46 root A)
          (ratFuncAtHahn46 root B)
          ((ratFuncAtHahn46 root A) ^ 2 / 3 + ratFuncAtHahn46 root C)
          ((ratFuncAtHahn46 root A) * (ratFuncAtHahn46 root B) / 3 +
            ratFuncAtHahn46 root F)
          ((ratFuncAtHahn46 root A) ^ 3 / 27 +
            (ratFuncAtHahn46 root A) * (ratFuncAtHahn46 root C) / 3 +
              ratFuncAtHahn46 root G)
          (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
          (HahnSeries.C (0 : k)) (HahnSeries.C epsilon)
          (HahnSeries.C (0 : k)) = HahnSeries.C i3 := by
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtHahn46_C] using hi3H
  have hface := firstIntegral_mainTangent_doubleZero_gZero_faces68
    gamma epsilon (ratFuncAtHahn46 root A) (ratFuncAtHahn46 root B)
      (ratFuncAtHahn46 root C) (ratFuncAtHahn46 root F)
      (ratFuncAtHahn46 root G) hA hB hC hF hG
  have h4coeff := congrArg
    (fun X : HahnSeries ℚ k => X.coeff (0 : ℚ)) hi4H'
  have h3coeff := congrArg
    (fun X : HahnSeries ℚ k => X.coeff (-1 : ℚ)) hi3H'
  have h4const : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (0 : ℚ) = i4 := by
    simp [HahnSeries.C_apply]
  have h3const : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-1 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hface.1, h4const] at h4coeff
  rw [hface.2, h3const] at h3coeff
  constructor
  · exact h4coeff.symm
  · linear_combination (9 / 4 : k) * h3coeff

/-- Algebraic sharpening when the new `G` boundary also vanishes. -/
theorem rhoOneZeroLCubicDoubleZero_gZero_next_split68
    (gamma a b c f g : k) (ha : a ≠ 0)
    (h3 : rhoOneZeroLCubicDoubleZeroGZeroThree68 gamma a b c f g = 0)
    (hg : g = 0) : b = 0 ∨ f = 0 := by
  simp only [rhoOneZeroLCubicDoubleZeroGZeroThree68] at h3
  subst g
  have habf : a * b * f = 0 := by
    linear_combination (-1 / 2 : k) * h3
  rcases mul_eq_zero.mp habf with hab | hf
  · rcases mul_eq_zero.mp hab with ha0 | hb
    · exact (ha ha0).elim
    · exact Or.inl hb
  · exact Or.inr hf

/-- Source-facing next packet on the `g = 0` order-gain branch. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refined_gZero
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB :
      let B := ratFuncAtHahn46 T.root T.source.B
      (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      (0 : WithTop ℚ) ≤ (rhoOneCDefectHahn68 A C0).orderTop)
    (hF :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let D := ratFuncAtHahn46 T.root T.source.D
      (0 : WithTop ℚ) ≤ (rhoOneTangentDDefectHahn68 A B D).orderTop)
    (hG :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      (↑(-1 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentEDefectHahn68 A C ER).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
    (0 : WithTop ℚ) ≤ C.orderTop ∧
    (0 : WithTop ℚ) ≤ F.orderTop ∧
    (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop ∧
    (∃ i4 : k,
      firstIntegralFour68 0 T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 ∧
      i4 = (4 / 3 : k) * rhoOneZeroLCubicDoubleZeroGZeroFour68
        T.source.gamma (B.coeff (1 : ℚ)) (C.coeff (0 : ℚ))
        (F.coeff (0 : ℚ)) (G.coeff (-1 : ℚ))) ∧
    rhoOneZeroLCubicDoubleZeroGZeroThree68 T.source.gamma
      (A.coeff (-2 : ℚ)) (B.coeff (1 : ℚ)) (C.coeff (0 : ℚ))
      (F.coeff (0 : ℚ)) (G.coeff (-1 : ℚ)) = 0 ∧
    (G.coeff (-1 : ℚ) ≠ 0 ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (((↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧ B.coeff (1 : ℚ) = 0) ∨
         ((↑(1 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧ F.coeff (0 : ℚ) = 0)))) := by
  dsimp only at hB hC hF hG ⊢
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let C0R : RatFunc k := T.source.C0
  let DR : RatFunc k := T.source.D
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let FR : RatFunc k := DR - RatFunc.C (1 / 3 : k) * AR * BR
  let GR : RatFunc k := ER - RatFunc.C (1 / 3 : k) * AR * CR
  let AH := ratFuncAtHahn46 T.root AR
  let BH := ratFuncAtHahn46 T.root BR
  let C0H := ratFuncAtHahn46 T.root C0R
  let DH := ratFuncAtHahn46 T.root DR
  let E0H := ratFuncAtHahn46 T.root E0R
  let CRH := ratFuncAtHahn46 T.root CR
  let ERH := ratFuncAtHahn46 T.root ER
  let FRH := ratFuncAtHahn46 T.root FR
  let GRH := ratFuncAtHahn46 T.root GR
  have hCRmap : CRH = rhoOneCDefectHahn68 AH C0H := by
    dsimp only [CRH, CR, AH, C0H, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ERH = rhoOneEDefectHahn68 AH E0H := by
    dsimp only [ERH, ER, AH, E0H, AR, E0R, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFRmap : FRH = rhoOneTangentDDefectHahn68 AH BH DH := by
    dsimp only [FRH, FR, AH, BH, DH, AR, BR, DR,
      rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hGRmap : GRH = rhoOneTangentEDefectHahn68 AH CRH ERH := by
    dsimp only [GRH, GR, ERH, AH, CRH, AR,
      rhoOneTangentEDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hGRmap' : GRH = rhoOneTangentEDefectHahn68 AH
      (rhoOneCDefectHahn68 AH C0H) (rhoOneEDefectHahn68 AH E0H) := by
    rw [hGRmap, hCRmap, hERmap]
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤ AH.orderTop := by
    simpa only [AH, AR] using hbounds.1
  have hBH : (↑(1 : ℚ) : WithTop ℚ) ≤ BH.orderTop := by
    simpa only [BH, BR] using hB
  have hCRH : (0 : WithTop ℚ) ≤ CRH.orderTop := by
    rw [hCRmap]
    simpa only [AH, C0H, AR, C0R] using hC
  have hFRH : (0 : WithTop ℚ) ≤ FRH.orderTop := by
    rw [hFRmap]
    simpa only [AH, BH, DH, AR, BR, DR] using hF
  have hGRH : (↑(-1 : ℚ) : WithTop ℚ) ≤ GRH.orderTop := by
    rw [hGRmap']
    simpa only [AH, C0H, E0H, AR, C0R, E0R] using hG
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  rw [hbeta, hdelta, hzeta] at hi4 hi3
  have hi4source :
      firstIntegralFour68 0 T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 := by
    simpa only [RatFunc.algebraMap_eq_C, map_zero] using hi4
  have hCrec : AR ^ 2 / 3 + CR = C0R := by
    dsimp only [CR, AR, C0R]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hDrec : AR * BR / 3 + FR = DR := by
    dsimp only [FR, AR, BR, DR]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = E0R := by
    dsimp only [GR, ER, CR, AR, C0R, E0R]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hi4T :
      firstIntegralFour68 0 AR BR (AR ^ 2 / 3 + CR) (AR * BR / 3 + FR)
        (AR ^ 3 / 27 + AR * CR / 3 + GR) (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 := by
    rw [hCrec, hDrec, hErec]
    simpa only [AR, BR, C0R, DR, E0R] using hi4source
  have hi3T :
      firstIntegralThree68 0 AR BR (AR ^ 2 / 3 + CR) (AR * BR / 3 + FR)
        (AR ^ 3 / 27 + AR * CR / 3 + GR) (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i3 := by
    rw [hCrec, hDrec, hErec]
    simpa only [AR, BR, C0R, DR, E0R, RatFunc.algebraMap_eq_C,
      map_zero] using hi3
  have hfaces := ratFunc_doubleZero_gZero_faces68 T.root AR BR CR FR GR
    T.source.gamma T.source.epsilon i4 i3 hAH hBH hCRH hFRH hGRH hi4T hi3T
  have hCRraw : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root C0R) := by
    simpa only [CRH, AH, C0H] using hCRmap
  have hERraw : ratFuncAtHahn46 T.root ER =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root E0R) := by
    simpa only [ERH, AH, E0H] using hERmap
  have hFRraw : ratFuncAtHahn46 T.root FR =
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root DR) := by
    simpa only [FRH, AH, BH, DH] using hFRmap
  have hGRraw : ratFuncAtHahn46 T.root GR =
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root C0R))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root E0R)) := by
    simpa only [GRH, AH, CRH, ERH, hCRraw, hERraw] using hGRmap
  rw [hCRraw, hFRraw, hGRraw] at hfaces
  have hfaces' := hfaces
  simp only [AR, BR, C0R, DR, E0R] at hfaces'
  refine ⟨hB, hC, hF, hG, ⟨i4, hi4source, hfaces'.1⟩, hfaces'.2, ?_⟩
  by_cases hg1 :
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) = 0
  · right
    have hsplit := rhoOneZeroLCubicDoubleZero_gZero_next_split68
      T.source.gamma
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (1 : ℚ))
        ((rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff (0 : ℚ))
        ((rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff (0 : ℚ))
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ))
        P.2.2.1 hfaces'.2 hg1
    have hg1z : GRH.coeff ((-1 : ℤ) : ℚ) = 0 := by
      norm_num
      rw [hGRmap']
      simpa only [AH, C0H, E0H, AR, C0R, E0R] using hg1
    have hG0 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
      T.root GR (-1) hGRH hg1z
    norm_num at hG0
    change (0 : WithTop ℚ) ≤ GRH.orderTop at hG0
    have hGout : (0 : WithTop ℚ) ≤
        (rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).orderTop := by
      rw [← hGRraw]
      exact hG0
    refine ⟨hg1, hGout, ?_⟩
    rcases hsplit with hb1 | hf0
    · left
      have hb1z : BH.coeff ((1 : ℤ) : ℚ) = 0 := by
        norm_num
        simpa only [BH, BR] using hb1
      have hB2 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
        T.root BR 1 hBH hb1z
      norm_num at hB2
      have hB2out : (↑(2 : ℚ) : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root T.source.B).orderTop := by
        change (↑((2 : ℤ) : ℚ) : WithTop ℚ) ≤ BH.orderTop
        exact hB2
      exact ⟨hB2out, hb1⟩
    · right
      have hf0z : FRH.coeff ((0 : ℤ) : ℚ) = 0 := by
        norm_num
        rw [hFRmap]
        simpa only [AH, BH, DH, AR, BR, DR] using hf0
      have hF1 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
        T.root FR 0 hFRH hf0z
      norm_num at hF1
      have hFout : (↑(1 : ℚ) : WithTop ℚ) ≤
          (rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).orderTop := by
        rw [← hFRraw]
        exact hF1
      exact ⟨hFout, hf0⟩
  · exact Or.inl hg1

end AlignedSquareRhoOneCubicExceptionalDoubleZeroRefinedGZero68

end Max11DegreeRoutes
