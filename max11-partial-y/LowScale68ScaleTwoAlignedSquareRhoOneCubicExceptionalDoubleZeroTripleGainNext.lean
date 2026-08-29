import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDoubleZeroDoubleGainNext

/-! # One more face in the `B,F` gain tower -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicExceptionalDoubleZeroTripleGainNext68

variable {k : Type*} [Field k] [CharZero k]

local instance exceptionalDoubleZeroTripleGainNextHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- At the next level of the gain tower, the coefficient at exponent three is
again the sparse `I₄` face. -/
theorem firstIntegral_mainTangent_doubleZero_tripleGain_four68
    (gamma epsilon : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(3 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (0 : WithTop ℚ) ≤ G.orderTop) :
    (firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C (0 : k))
      (HahnSeries.C epsilon) (HahnSeries.C (0 : k))).coeff (3 : ℚ) =
        (2 / 3 : k) * rhoOneZeroLCubicDoubleZeroDoubleGainFour68
          gamma epsilon (B.coeff (3 : ℚ)) (C.coeff (0 : ℚ))
          (F.coeff (3 : ℚ)) (G.coeff (0 : ℚ)) := by
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
  have h3t1 := hz 3 (-8 / 27 : k) B A C F G 3 0 0 0 0
    3 (-2) 0 3 0 hB hA hC hF hG (by norm_num)
  have h3t3 := lead (8 / 3 : k) B G A C F 1 1 0 0 0
    3 0 (-2) 0 3 hB hG hA hC hF
  have h3t4 := lead (8 / 3 : k) C F A B G 1 1 0 0 0
    0 3 (-2) 3 0 hC hF hA hB hG
  have h3l6 := lead (4 * gamma) F A B C G 1 0 0 0 0
    3 (-2) 3 0 0 hF hA hB hC hG
  have h3l8 := lead (2 * epsilon) B A C F G 1 0 0 0 0
    3 (-2) 0 3 0 hB hA hC hF hG
  norm_num at h3t3 h3t4 h3l6 h3l8
  have hCzero : (HahnSeries.C (0 : k) : HahnSeries ℚ k) = 0 :=
    HahnSeries.C_zero
  rw [hdecH]
  simp only [HahnSeries.coeff_add, firstIntegralFourMainTangentTopHahn68,
    firstIntegralFourMainTangentLowerHahn68]
  rw [h3t1, h3t3, h3t4, h3l6, h3l8]
  simp only [weightedMonomial68, mul_zero, zero_mul, neg_zero,
    HahnSeries.coeff_zero]
  rw [hCzero]
  simp only [zero_mul, HahnSeries.coeff_zero, add_zero,
    rhoOneZeroLCubicDoubleZeroDoubleGainFour68]
  ring

/-- Rational transport of the exponent-three sparse face. -/
theorem ratFunc_doubleZero_tripleGain_four68
    (root : k) (A B C F G : RatFunc k)
    (gamma epsilon : k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hi4 : firstIntegralFour68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      (RatFunc.C (0 : k)) (RatFunc.C gamma) (RatFunc.C (0 : k))
      (RatFunc.C epsilon) (RatFunc.C (0 : k)) = RatFunc.C (0 : k)) :
    rhoOneZeroLCubicDoubleZeroDoubleGainFour68 gamma epsilon
      ((ratFuncAtHahn46 root B).coeff (3 : ℚ))
      ((ratFuncAtHahn46 root C).coeff (0 : ℚ))
      ((ratFuncAtHahn46 root F).coeff (3 : ℚ))
      ((ratFuncAtHahn46 root G).coeff (0 : ℚ)) = 0 := by
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
          (HahnSeries.C (0 : k)) = HahnSeries.C (0 : k) := by
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtHahn46_C] using hi4H
  have hface := firstIntegral_mainTangent_doubleZero_tripleGain_four68
    gamma epsilon (ratFuncAtHahn46 root A) (ratFuncAtHahn46 root B)
      (ratFuncAtHahn46 root C) (ratFuncAtHahn46 root F)
      (ratFuncAtHahn46 root G) hA hB hC hF hG
  have h3coeff := congrArg
    (fun X : HahnSeries ℚ k => X.coeff (3 : ℚ)) hi4H'
  have h3const : (HahnSeries.C (0 : k) : HahnSeries ℚ k).coeff (3 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hface, h3const] at h3coeff
  linear_combination (3 / 2 : k) * h3coeff

/-- The source-facing third gain. The two old siblings are not folded into this
branch: the theorem assumes the stronger `B,F` orders explicitly. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_tripleGain_next
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB :
      let B := ratFuncAtHahn46 T.root T.source.B
      (↑(3 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      (0 : WithTop ℚ) ≤ (rhoOneCDefectHahn68 A C0).orderTop)
    (hF :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let D := ratFuncAtHahn46 T.root T.source.D
      (↑(3 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68 A B D).orderTop)
    (hG :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      (0 : WithTop ℚ) ≤ (rhoOneTangentEDefectHahn68 A C ER).orderTop)
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
    (↑(3 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
    (0 : WithTop ℚ) ≤ C.orderTop ∧
    (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
    (0 : WithTop ℚ) ≤ G.orderTop ∧
    firstIntegralFour68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C (0 : k) ∧
    rhoOneZeroLCubicDoubleZeroDoubleGainFour68 T.source.gamma
      T.source.epsilon (B.coeff (3 : ℚ)) (C.coeff (0 : ℚ))
      (F.coeff (3 : ℚ)) (G.coeff (0 : ℚ)) = 0 ∧
    (B.coeff (3 : ℚ) ≠ 0 ∨
      (B.coeff (3 : ℚ) = 0 ∧
       (↑(4 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
       (((↑(4 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧ F.coeff (3 : ℚ) = 0) ∨
        2 * C.coeff (0 : ℚ) + 3 * T.source.gamma = 0))) := by
  dsimp only at hB hC hF hG ⊢
  have hB2 : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop :=
    le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hB
  have hF2 : (↑(2 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop :=
    le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hF
  have hprev := T.rhoOne_exceptional_doubleZero_doubleGain_next
    P hB2 hC hF2 hG hbeta hdelta hzeta
  dsimp only at hprev
  have hi4zero := hprev.2.2.2.2.1
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
  have hBH : (↑(3 : ℚ) : WithTop ℚ) ≤ BH.orderTop := by
    simpa only [BH, BR] using hB
  have hCRH : (0 : WithTop ℚ) ≤ CRH.orderTop := by
    rw [hCRmap]
    simpa only [AH, C0H, AR, C0R] using hC
  have hFRH : (↑(3 : ℚ) : WithTop ℚ) ≤ FRH.orderTop := by
    rw [hFRmap]
    simpa only [AH, BH, DH, AR, BR, DR] using hF
  have hGRH : (0 : WithTop ℚ) ≤ GRH.orderTop := by
    rw [hGRmap']
    simpa only [AH, C0H, E0H, AR, C0R, E0R] using hG
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
        (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C (0 : k) := by
    rw [hCrec, hDrec, hErec]
    simpa only [AR, BR, C0R, DR, E0R] using hi4zero
  have hface := ratFunc_doubleZero_tripleGain_four68 T.root AR BR CR FR GR
    T.source.gamma T.source.epsilon hAH hBH hCRH hFRH hGRH hi4T
  have hCRraw : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root C0R) := by
    simpa only [CRH, AH, C0H] using hCRmap
  have hFRraw : ratFuncAtHahn46 T.root FR =
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root DR) := by
    simpa only [FRH, AH, BH, DH] using hFRmap
  have hERraw : ratFuncAtHahn46 T.root ER =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root E0R) := by
    simpa only [ERH, AH, E0H] using hERmap
  have hGRraw : ratFuncAtHahn46 T.root GR =
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root C0R))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root E0R)) := by
    simpa only [GRH, AH, CRH, ERH, hCRraw, hERraw] using hGRmap
  rw [hCRraw, hFRraw, hGRraw] at hface
  simp only [AR, BR, C0R, DR, E0R] at hface
  refine ⟨hB, hC, hF, hG, hi4zero, hface, ?_⟩
  by_cases hb3 : (ratFuncAtHahn46 T.root T.source.B).coeff (3 : ℚ) = 0
  · right
    have hb3z : BH.coeff ((3 : ℤ) : ℚ) = 0 := by
      norm_num
      simpa only [BH, BR] using hb3
    have hB4 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
      T.root BR 3 hBH hb3z
    norm_num at hB4
    have hB4out : (↑(4 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.B).orderTop := by
      change (↑((4 : ℤ) : ℚ) : WithTop ℚ) ≤ BH.orderTop
      exact hB4
    refine ⟨hb3, hB4out, ?_⟩
    have hsplit := rhoOneZeroLCubicDoubleZero_doubleGain_split68
      T.source.gamma T.source.epsilon
        ((ratFuncAtHahn46 T.root T.source.B).coeff (3 : ℚ))
        ((rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).coeff (0 : ℚ))
        ((rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).coeff (3 : ℚ))
        ((rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).coeff (0 : ℚ))
        hface hb3
    rcases hsplit with hf3 | hS
    · left
      have hf3z : FRH.coeff ((3 : ℤ) : ℚ) = 0 := by
        norm_num
        rw [hFRmap]
        simpa only [AH, BH, DH, AR, BR, DR] using hf3
      have hF4 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
        T.root FR 3 hFRH hf3z
      norm_num at hF4
      have hF4out : (↑(4 : ℚ) : WithTop ℚ) ≤
          (rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D)).orderTop := by
        rw [← hFRraw]
        exact hF4
      exact ⟨hF4out, hf3⟩
    · exact Or.inr hS
  · exact Or.inl hb3

end AlignedSquareRhoOneCubicExceptionalDoubleZeroTripleGainNext68

end Max11DegreeRoutes
