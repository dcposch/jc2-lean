import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDoubleZero

/-! # Next invariant face in the improved `C` box -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicExceptionalDoubleZeroCNext68

variable {k : Type*} [Field k] [CharZero k]

local instance exceptionalDoubleZeroCNextHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- With `B` and the cubic defect both improved, the next `I₃` coefficient
is the sparse product of the old `G` boundary coefficient and one affine
new `C` coefficient. -/
theorem firstIntegral_mainTangent_doubleZero_cBox_three68
    (gamma epsilon zeta : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(-1 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-3 : ℚ) : WithTop ℚ) ≤ G.orderTop) :
    (firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C (0 : k))
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-3 : ℚ) =
        (4 / 3 : k) * G.coeff (-3 : ℚ) *
          (2 * C.coeff (0 : ℚ) + 3 * gamma) := by
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
  have hdec := firstIntegralThree_mainTangent_decomposition68
    (k := HahnSeries ℚ k) (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
      (HahnSeries.C (0 : k)) (HahnSeries.C epsilon) (HahnSeries.C zeta)
      A B C F G
  have hdecH :
      firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
          (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
          (HahnSeries.C gamma) (HahnSeries.C (0 : k))
          (HahnSeries.C epsilon) (HahnSeries.C zeta) =
        firstIntegralThreeMainTangentTopHahn68 A B C F G +
          firstIntegralThreeMainTangentLowerHahn68 0 gamma 0 epsilon zeta
            A B C F G := by
    rw [hdec]
    simp only [firstIntegralThreeMainTangentTop68,
      firstIntegralThreeMainTangentLower68,
      firstIntegralThreeMainTangentTopHahn68,
      firstIntegralThreeMainTangentLowerHahn68, weightedMonomial68,
      map_mul, map_neg, map_div₀, map_ofNat, map_one]
    ring
  have ht1 := hz (-3) (-8 / 9 : k) A B F C G 1 1 1 0 0
    (-2) 1 (-1) 0 (-3) hA hB hF hC hG (by norm_num)
  have ht2 := hz (-3) (-8 / 9 : k) B C A F G 2 1 0 0 0
    1 0 (-2) (-1) (-3) hB hC hA hF hG (by norm_num)
  have ht3 := lead (8 / 3 : k) C G A B F 1 1 0 0 0
    0 (-3) (-2) 1 (-1) hC hG hA hB hF
  have hl2 := hz (-3) (4 / 3 : k) F A B C G 2 0 0 0 0
    (-1) (-2) 1 0 (-3) hF hA hB hC hG (by norm_num)
  have hl6 := hz (-3) (-(2 / 3 : k) * gamma) B A C F G 2 0 0 0 0
    1 (-2) 0 (-1) (-3) hB hA hC hF hG (by norm_num)
  have hl7 := lead (4 * gamma) G A B C F 1 0 0 0 0
    (-3) (-2) 1 0 (-1) hG hA hB hC hF
  have hl8 := hz (-3) (2 * epsilon) C A B F G 1 0 0 0 0
    0 (-2) 1 (-1) (-3) hC hA hB hF hG (by norm_num)
  have hl10 := hz (-3) zeta B A C F G 1 0 0 0 0
    1 (-2) 0 (-1) (-3) hB hA hC hF hG (by norm_num)
  norm_num at ht3 hl7
  have hCzero : (HahnSeries.C (0 : k) : HahnSeries ℚ k) = 0 :=
    HahnSeries.C_zero
  rw [hdecH]
  simp only [HahnSeries.coeff_add, firstIntegralThreeMainTangentTopHahn68,
    firstIntegralThreeMainTangentLowerHahn68]
  rw [ht1, ht2, ht3, hl2, hl6, hl7, hl8, hl10]
  simp only [weightedMonomial68, mul_zero, zero_mul, neg_zero,
    HahnSeries.coeff_zero]
  rw [hCzero]
  simp only [zero_mul, HahnSeries.coeff_zero, add_zero]
  ring

/-- Rational-function transport of the sparse `I₃(-3)` face. -/
theorem ratFunc_doubleZero_cBox_three_face68
    (root : k) (A B C F G : RatFunc k)
    (gamma epsilon zeta i3 : k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hi3 : firstIntegralThree68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      (RatFunc.C (0 : k)) (RatFunc.C gamma) (RatFunc.C (0 : k))
      (RatFunc.C epsilon) (RatFunc.C zeta) = RatFunc.C i3) :
    (ratFuncAtHahn46 root G).coeff (-3 : ℚ) *
      (2 * (ratFuncAtHahn46 root C).coeff (0 : ℚ) + 3 * gamma) = 0 := by
  have hi3H := congrArg (ratFuncAtHahn46 root) hi3
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
          (HahnSeries.C zeta) = HahnSeries.C i3 := by
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtHahn46_C] using hi3H
  have hface := firstIntegral_mainTangent_doubleZero_cBox_three68
    gamma epsilon zeta (ratFuncAtHahn46 root A) (ratFuncAtHahn46 root B)
      (ratFuncAtHahn46 root C) (ratFuncAtHahn46 root F)
      (ratFuncAtHahn46 root G) hA hB hC hF hG
  have hcoeff := congrArg
    (fun X : HahnSeries ℚ k => X.coeff (-3 : ℚ)) hi3H'
  have hconst : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-3 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hface, hconst] at hcoeff
  linear_combination (3 / 4 : k) * hcoeff

/-- Source-facing refinement of the improved `B,C,F` box.  The next
invariant either raises `G` by one integral order, or leaves the explicit
affine residual `2 C[0] + 3 gamma = 0`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_cBox_next
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
      (rhoOneCDefectHahn68 A C0).coeff (-1 : ℚ) = 0) :
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
    (↑(-1 : ℚ) : WithTop ℚ) ≤ F.orderTop ∧
    G.coeff (-3 : ℚ) * (2 * C.coeff (0 : ℚ) + 3 * T.source.gamma) = 0 ∧
      (((↑(-2 : ℚ) : WithTop ℚ) ≤ G.orderTop ∧
          G.coeff (-3 : ℚ) = 0) ∨
        2 * C.coeff (0 : ℚ) + 3 * T.source.gamma = 0) := by
  have hBC0 := T.rhoOne_mainTangent_exceptional_doubleZero_orders
    hp hH hp6 hp5 hp4 P hb hc hb1 hc1
  have hFG0 := T.rhoOne_mainTangent_exceptional_discriminant_orders
    hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc
  dsimp only at hb hc hb1 hc1 hf1 hb2 hc2 hBC0 hFG0 ⊢
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
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤ AH.orderTop := by
    simpa only [AH, AR] using hbounds.1
  have hBH0 : (0 : WithTop ℚ) ≤ BH.orderTop := by
    simpa only [BH, BR] using hBC0.1
  have hCRH0 : (↑(-1 : ℚ) : WithTop ℚ) ≤ CRH.orderTop := by
    rw [hCRmap]
    exact hBC0.2
  have hFRH0 : (↑(-2 : ℚ) : WithTop ℚ) ≤ FRH.orderTop := by
    rw [hFRmap]
    exact hFG0.1
  have hGRH : (↑(-3 : ℚ) : WithTop ℚ) ≤ GRH.orderTop := by
    rw [hGRmap, hCRmap, hERmap]
    exact hFG0.2
  have hb2z : BH.coeff ((0 : ℤ) : ℚ) = 0 := by
    norm_num
    simpa only [BH, BR] using hb2
  have hBH := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root BR 0 hBH0 hb2z
  have hCRH := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root CR (-1) hCRH0 (by
      change CRH.coeff (-1 : ℚ) = 0
      rw [hCRmap]
      simpa only [AH, C0H, AR, C0R] using hc2)
  have hFRH := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root FR (-2) hFRH0 (by
      change FRH.coeff (-2 : ℚ) = 0
      rw [hFRmap]
      simpa only [AH, BH, DH, AR, BR, DR] using hf1)
  norm_num at hBH hCRH hFRH
  change (↑(1 : ℚ) : WithTop ℚ) ≤ BH.orderTop at hBH
  change (0 : WithTop ℚ) ≤ CRH.orderTop at hCRH
  change (↑(-1 : ℚ) : WithTop ℚ) ≤ FRH.orderTop at hFRH
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  rw [hbeta, hdelta] at hi4 hi3
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
  have hi3T :
      firstIntegralThree68 0 AR BR (AR ^ 2 / 3 + CR) (AR * BR / 3 + FR)
        (AR ^ 3 / 27 + AR * CR / 3 + GR) (RatFunc.C (0 : k))
        (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
        (RatFunc.C T.source.epsilon) (RatFunc.C T.source.zeta) =
          RatFunc.C i3 := by
    rw [hCrec, hDrec, hErec]
    simpa only [AR, BR, C0R, DR, E0R, RatFunc.algebraMap_eq_C,
      map_zero] using hi3
  have hface := ratFunc_doubleZero_cBox_three_face68 T.root AR BR CR FR GR
    T.source.gamma T.source.epsilon T.source.zeta i3 hAH hBH hCRH hFRH
      hGRH hi3T
  have hCRmap' : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root C0R) := by
    simpa only [CRH, AH, C0H] using hCRmap
  have hERmap' : ratFuncAtHahn46 T.root ER =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root E0R) := by
    simpa only [ERH, AH, E0H] using hERmap
  have hFRmap' : ratFuncAtHahn46 T.root FR =
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root DR) := by
    simpa only [FRH, AH, BH, DH] using hFRmap
  have hGRmap' : ratFuncAtHahn46 T.root GR =
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root AR)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root C0R))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (ratFuncAtHahn46 T.root E0R)) := by
    simpa only [GRH, AH, CRH, ERH, hCRmap', hERmap'] using hGRmap
  rw [hCRmap', hGRmap'] at hface
  have hface' :
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).coeff (-3 : ℚ) *
      (2 * (rhoOneCDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).coeff (0 : ℚ) +
          3 * T.source.gamma) = 0 := by
    simpa only [AR, C0R, E0R] using hface
  have hBH' : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop := by
    simpa only [BH, BR] using hBH
  have hCRH' : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop := by
    rw [← hCRmap']
    exact hCRH
  have hFRH' : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop := by
    rw [← hFRmap']
    exact hFRH
  refine ⟨hBH', hCRH', hFRH', hface', ?_⟩
  rcases mul_eq_zero.mp hface' with hg3 | haff
  · left
    have hg3z : (ratFuncAtHahn46 T.root GR).coeff ((-3 : ℤ) : ℚ) = 0 := by
      rw [hGRmap']
      norm_num
      simpa only [AR, C0R, E0R] using hg3
    have hGi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
      T.root GR (-3) hGRH hg3z
    norm_num at hGi
    change (↑(-2 : ℚ) : WithTop ℚ) ≤ GRH.orderTop at hGi
    have hGiMap : (↑(-2 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root AR)
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root AR)
            (ratFuncAtHahn46 T.root C0R))
          (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root AR)
            (ratFuncAtHahn46 T.root E0R))).orderTop := by
      rw [← hGRmap']
      exact hGi
    exact ⟨by simpa only [AR, C0R, E0R] using hGiMap, hg3⟩
  · exact Or.inr haff

end AlignedSquareRhoOneCubicExceptionalDoubleZeroCNext68

end Max11DegreeRoutes
