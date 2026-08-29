import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDoubleZeroRefinedFaces

/-! # The `f = 0` split in the refined double-zero packet -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicExceptionalDoubleZeroRefinedFZero68

variable {k : Type*} [Field k] [CharZero k]

local instance exceptionalDoubleZeroRefinedFZeroHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- On `f = 0`, the two refined faces say either `g = 0`, or both the
`B` boundary and the affine factor vanish. -/
theorem rhoOneZeroLCubicDoubleZero_refined_fZero_split68
    (gamma a b c f g : k)
    (h4 : rhoOneZeroLCubicDoubleZeroRefinedFour68 gamma b c f g = 0)
    (h3 : rhoOneZeroLCubicDoubleZeroRefinedThree68 gamma a b c f g = 0)
    (hf : f = 0) :
    g = 0 ∨ (g ≠ 0 ∧ b = 0 ∧ 2 * c + 3 * gamma = 0) := by
  simp only [rhoOneZeroLCubicDoubleZeroRefinedFour68] at h4
  simp only [rhoOneZeroLCubicDoubleZeroRefinedThree68] at h3
  subst f
  norm_num at h4 h3
  by_cases hg : g = 0
  · exact Or.inl hg
  · right
    exact ⟨hg, h4.resolve_right hg, h3.resolve_left hg⟩

/-- After `f = b = 0` and the affine cancellation, the next `I₄(0)` face
is the single product of the new `B` coefficient and the nonzero old `G`
coefficient. -/
theorem firstIntegral_mainTangent_doubleZero_refined_fZero_four68
    (gamma epsilon : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (0 : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : 2 * C.coeff (0 : ℚ) + 3 * gamma = 0) :
    (firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C (0 : k))
      (HahnSeries.C epsilon) (HahnSeries.C (0 : k))).coeff (0 : ℚ) =
        (8 / 3 : k) * B.coeff (2 : ℚ) * G.coeff (-2 : ℚ) := by
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
  have hdec := firstIntegralFour_mainTangent_decomposition68
    (k := HahnSeries ℚ k) (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
      (HahnSeries.C (0 : k)) (HahnSeries.C epsilon) (HahnSeries.C (0 : k))
      A B C F G
  have hdecH :
      firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
          (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
          (HahnSeries.C gamma) (HahnSeries.C (0 : k))
          (HahnSeries.C epsilon) (HahnSeries.C (0 : k)) =
        firstIntegralFourMainTangentTopHahn68 0 A B C F G +
          firstIntegralFourMainTangentLowerHahn68 0 gamma 0 epsilon 0
            A B C F G := by
    rw [hdec]
    simp only [firstIntegralFourMainTangentTop68,
      firstIntegralFourMainTangentLower68,
      firstIntegralFourMainTangentTopHahn68,
      firstIntegralFourMainTangentLowerHahn68, weightedMonomial68,
      map_mul, map_neg, map_div₀, map_ofNat, map_one]
    ring
  have ht1 := hz 0 (-8 / 27 : k) B A C F G 3 0 0 0 0
    2 (-2) 0 0 (-2) hB hA hC hF hG (by norm_num)
  have ht3 := lead (8 / 3 : k) B G A C F 1 1 0 0 0
    2 (-2) (-2) 0 0 hB hG hA hC hF
  have ht4 := lead (8 / 3 : k) C F A B G 1 1 0 0 0
    0 0 (-2) 2 (-2) hC hF hA hB hG
  have hl6 := lead (4 * gamma) F A B C G 1 0 0 0 0
    0 (-2) 2 0 (-2) hF hA hB hC hG
  have hl8 := hz 0 (2 * epsilon) B A C F G 1 0 0 0 0
    2 (-2) 0 0 (-2) hB hA hC hF hG (by norm_num)
  norm_num at ht3 ht4 hl6
  have hCzero : (HahnSeries.C (0 : k) : HahnSeries ℚ k) = 0 :=
    HahnSeries.C_zero
  rw [hdecH]
  simp only [HahnSeries.coeff_add, firstIntegralFourMainTangentTopHahn68,
    firstIntegralFourMainTangentLowerHahn68]
  rw [ht1, ht3, ht4, hl6, hl8]
  simp only [weightedMonomial68, mul_zero, zero_mul, neg_zero,
    HahnSeries.coeff_zero]
  rw [hCzero]
  simp only [zero_mul, HahnSeries.coeff_zero, add_zero]
  linear_combination (4 / 3 : k) * F.coeff 0 * hS

/-- Rational-function transport of the next single-product face. -/
theorem ratFunc_doubleZero_refined_fZero_four_face68
    (root : k) (A B C F G : RatFunc k)
    (gamma epsilon i4 : k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS : 2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma = 0)
    (hi4 : firstIntegralFour68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      (RatFunc.C (0 : k)) (RatFunc.C gamma) (RatFunc.C (0 : k))
      (RatFunc.C epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4) :
    i4 = (8 / 3 : k) * (ratFuncAtHahn46 root B).coeff (2 : ℚ) *
      (ratFuncAtHahn46 root G).coeff (-2 : ℚ) := by
  have hi4H := congrArg (ratFuncAtHahn46 root) hi4
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
  have hface := firstIntegral_mainTangent_doubleZero_refined_fZero_four68
    gamma epsilon (ratFuncAtHahn46 root A) (ratFuncAtHahn46 root B)
      (ratFuncAtHahn46 root C) (ratFuncAtHahn46 root F)
      (ratFuncAtHahn46 root G) hA hB hC hF hG hS
  have hcoeff := congrArg
    (fun X : HahnSeries ℚ k => X.coeff (0 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (0 : ℚ) = i4 := by
    simp [HahnSeries.C_apply]
  rw [hface, hconst] at hcoeff
  exact hcoeff.symm

/-- Source-facing split of the `f = 0` component.  The `g = 0` branch gains
one order in `G`.  On `g ≠ 0`, the old faces raise `B` to order two and the
next `I₄(0)` coefficient records the exact surviving first-integral load. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refined_fZero
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
      (↑(-1 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68 A B D).orderTop)
    (hG :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      (↑(-2 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentEDefectHahn68 A C ER).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0)
    (h4 :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      let F := rhoOneTangentDDefectHahn68 A B D
      let G := rhoOneTangentEDefectHahn68 A C ER
      rhoOneZeroLCubicDoubleZeroRefinedFour68 T.source.gamma
        (B.coeff (1 : ℚ)) (C.coeff (0 : ℚ))
        (F.coeff (-1 : ℚ)) (G.coeff (-2 : ℚ)) = 0)
    (h3 :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      let F := rhoOneTangentDDefectHahn68 A B D
      let G := rhoOneTangentEDefectHahn68 A C ER
      rhoOneZeroLCubicDoubleZeroRefinedThree68 T.source.gamma
        (A.coeff (-2 : ℚ)) (B.coeff (1 : ℚ)) (C.coeff (0 : ℚ))
        (F.coeff (-1 : ℚ)) (G.coeff (-2 : ℚ)) = 0)
    (hf :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let D := ratFuncAtHahn46 T.root T.source.D
      (rhoOneTangentDDefectHahn68 A B D).coeff (-1 : ℚ) = 0) :
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
    (↑(-2 : ℚ) : WithTop ℚ) ≤ G.orderTop ∧
    (((↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop ∧ G.coeff (-2 : ℚ) = 0) ∨
      (G.coeff (-2 : ℚ) ≠ 0 ∧
       (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧ B.coeff (1 : ℚ) = 0 ∧
       2 * C.coeff (0 : ℚ) + 3 * T.source.gamma = 0 ∧
       ∃ i4 : k,
         firstIntegralFour68 0 T.source.A T.source.B T.source.C0
           T.source.D T.source.E (RatFunc.C (0 : k))
           (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
           (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 ∧
         i4 = (8 / 3 : k) * B.coeff (2 : ℚ) * G.coeff (-2 : ℚ))) := by
  dsimp only at hB hC hF hG h4 h3 hf ⊢
  have hsplit := rhoOneZeroLCubicDoubleZero_refined_fZero_split68
    T.source.gamma
      ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
      ((ratFuncAtHahn46 T.root T.source.B).coeff (1 : ℚ))
      ((rhoOneCDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff (0 : ℚ))
      ((rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).coeff (-1 : ℚ))
      ((rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-2 : ℚ)) h4 h3 hf
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
  have hFRH0 : (↑(-1 : ℚ) : WithTop ℚ) ≤ FRH.orderTop := by
    rw [hFRmap]
    simpa only [AH, BH, DH, AR, BR, DR] using hF
  have hGRH : (↑(-2 : ℚ) : WithTop ℚ) ≤ GRH.orderTop := by
    rw [hGRmap']
    simpa only [AH, C0H, E0H, AR, C0R, E0R] using hG
  have hfz : FRH.coeff ((-1 : ℤ) : ℚ) = 0 := by
    norm_num
    rw [hFRmap]
    simpa only [AH, BH, DH, AR, BR, DR] using hf
  have hFRH := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root FR (-1) hFRH0 hfz
  norm_num at hFRH
  change (0 : WithTop ℚ) ≤ FRH.orderTop at hFRH
  have hFRout : (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop := by
    rw [← hFRmap]
    exact hFRH
  refine ⟨hB, hC, hFRout, hG, ?_⟩
  rcases hsplit with hg0 | hnon
  · left
    have hgz : GRH.coeff ((-2 : ℤ) : ℚ) = 0 := by
      norm_num
      rw [hGRmap']
      simpa only [AH, C0H, E0H, AR, C0R, E0R] using hg0
    have hGi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
      T.root GR (-2) hGRH hgz
    norm_num at hGi
    change (↑(-1 : ℚ) : WithTop ℚ) ≤ GRH.orderTop at hGi
    have hGout : (↑(-1 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).orderTop := by
      rw [← hGRmap']
      exact hGi
    exact ⟨hGout, hg0⟩
  · right
    rcases hnon with ⟨hg_ne, hb1, hS⟩
    have hb1z : BH.coeff ((1 : ℤ) : ℚ) = 0 := by
      norm_num
      simpa only [BH, BR] using hb1
    have hBH2 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
      T.root BR 1 hBH hb1z
    norm_num at hBH2
    change (↑(2 : ℚ) : WithTop ℚ) ≤ BH.orderTop at hBH2
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
          (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) =
            RatFunc.C i4 := by
      rw [hCrec, hDrec, hErec]
      simpa only [AR, BR, C0R, DR, E0R] using hi4source
    have hS' : 2 * CRH.coeff (0 : ℚ) + 3 * T.source.gamma = 0 := by
      rw [hCRmap]
      simpa only [AH, C0H, AR, C0R] using hS
    have hload := ratFunc_doubleZero_refined_fZero_four_face68
      T.root AR BR CR FR GR T.source.gamma T.source.epsilon i4
        hAH hBH2 hCRH hFRH hGRH hS' hi4T
    have hBHout : (↑(2 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.B).orderTop := by
      simpa only [BH, BR] using hBH2
    have hload' : i4 = (8 / 3 : k) *
        (ratFuncAtHahn46 T.root T.source.B).coeff (2 : ℚ) *
        (rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (-2 : ℚ) := by
      have hGRraw : ratFuncAtHahn46 T.root GR =
          rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E)) := by
        simpa only [GRH, AH, C0H, E0H, AR, C0R, E0R] using hGRmap'
      rw [← hGRraw]
      simpa only [BR] using hload
    exact ⟨hg_ne, hBHout, hb1, hS, ⟨i4, hi4source, hload'⟩⟩

end AlignedSquareRhoOneCubicExceptionalDoubleZeroRefinedFZero68

end Max11DegreeRoutes
