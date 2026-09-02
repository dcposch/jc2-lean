import Sol68ScaleTwoAlignedSquareTerminalGQuadraticWallScratch

/-! # The next `I₄` coefficient on the nonzero-`G[-1]` quadratic wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGI4Next68

variable {k : Type*} [Field k] [CharZero k]

/-- The zero-load fourth first integral in factored depressed coordinates. -/
def rhoOneI4ZeroFactored68 (gamma epsilon B C F G : k) : k :=
  (-8 / 27 : k) * B ^ 3 + (8 / 3 : k) * B * G +
    (4 / 3 : k) * (2 * C + 3 * gamma) * F + 2 * epsilon * B

theorem firstIntegralFour_mainTangent_zero_factor68
    (gamma epsilon A B C F G : k)
    (hzero : firstIntegralFour68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      0 gamma 0 epsilon 0 = 0) :
    rhoOneI4ZeroFactored68 gamma epsilon B C F G = 0 := by
  rw [firstIntegralFour_mainTangent_decomposition68] at hzero
  simp only [firstIntegralFourMainTangentTop68,
    firstIntegralFourMainTangentLower68, rhoOneI4ZeroFactored68] at hzero ⊢
  linear_combination hzero

/-- Once the boundary cancellations raise `B` and `2C+3γ`, the first
positive coefficient of the global zero-`I₄` factor is sparse. -/
theorem rhoOneI4ZeroFactored_boundary_coeff_one68
    (gamma epsilon : k) (B C F G : HahnSeries ℚ k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hF : (0 : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑(1 : ℚ) : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hfactor : rhoOneI4ZeroFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) B C F G = 0) :
    B.coeff (2 : ℚ) * G.coeff (-1 : ℚ) +
      C.coeff (1 : ℚ) * F.coeff (0 : ℚ) = 0 := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hS' : (↑(1 : ℚ) : WithTop ℚ) ≤ S.orderTop := by
    simpa only [S] using hS
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (1 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (1 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 1 h1 h2 h3 h4 h5 hlt
  have lead (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop) :=
    weightedMonomial68_coeff_at_general_lower_next s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
  have hB3 := hz (-8 / 27) B B B B B 3 0 0 0 0
    2 2 2 2 2 hB hB hB hB hB (by norm_num)
  have hBG := lead (8 / 3) B G B F S 1 1 0 0 0
    2 (-1) 2 0 1 hB hG hB hF hS'
  have hSF := lead (4 / 3) S F B S G 1 1 0 0 0
    1 0 2 1 (-1) hS' hF hB hS' hG
  have heB := hz (2 * epsilon) B B B B B 1 0 0 0 0
    2 2 2 2 2 hB hB hB hB hB (by norm_num)
  norm_num at hBG hSF
  have hfactor' :
      weightedMonomial68 (-8 / 27 : k) B B B B B 3 0 0 0 0 +
        weightedMonomial68 (8 / 3 : k) B G B F S 1 1 0 0 0 +
        weightedMonomial68 (4 / 3 : k) S F B S G 1 1 0 0 0 +
        weightedMonomial68 (2 * epsilon) B B B B B 1 0 0 0 0 = 0 := by
    simpa only [rhoOneI4ZeroFactored68, S, weightedMonomial68,
      pow_zero, pow_one, mul_one, map_add, map_mul, map_div₀, map_neg,
      map_ofNat, map_one] using hfactor
  have hc := congrArg (fun X : HahnSeries ℚ k => X.coeff (1 : ℚ)) hfactor'
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at hc
  rw [hB3, hBG, hSF, heB] at hc
  have hSco : S.coeff (1 : ℚ) = 2 * C.coeff (1 : ℚ) := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * C).coeff (1 : ℚ) = 2 * C.coeff (1 : ℚ) := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp [HahnSeries.C_apply]
  rw [hSco] at hc
  linear_combination (3 / 8 : k) * hc

/-- Root-parametric source-facing form of the exact next packet. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGI4NextResidual
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
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A
      (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    ((rhoOneI4ZeroFactored68 (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.epsilon) T.source.B
          (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2)
          (T.source.D - RatFunc.C (1 / 3 : k) * T.source.A * T.source.B)
          ((T.source.E - RatFunc.C (1 / 27 : k) * T.source.A ^ 3) -
            RatFunc.C (1 / 3 : k) * T.source.A *
              (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2)) = 0 ∧
       (((B.coeff (1 : ℚ) = 0 ∧ 2 * C.coeff (0 : ℚ) +
              3 * T.source.gamma = 0) ∧
          (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
          (↑(1 : ℚ) : WithTop ℚ) ≤
            (2 * C + HahnSeries.C (3 * T.source.gamma)).orderTop ∧
          B.coeff (2 : ℚ) * G.coeff (-1 : ℚ) +
            C.coeff (1 : ℚ) * F.coeff (0 : ℚ) = 0) ∨
        (B.coeff (1 : ℚ) ≠ 0 ∧
          2 * C.coeff (0 : ℚ) + 3 * T.source.gamma ≠ 0 ∧
          ∃ r : k, r ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2 : ℚ) ∧
            (3 * (2 * C.coeff (0 : ℚ) + 3 * T.source.gamma) =
                2 * r * B.coeff (1 : ℚ) ∨
             3 * (2 * C.coeff (0 : ℚ) + 3 * T.source.gamma) =
                -(2 * r * B.coeff (1 : ℚ)))))) ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F))) := by
  dsimp only
  have hprev :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGFactoredResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hprev
  rcases hprev with hnonzero | hzero
  · left
    rcases hnonzero with ⟨i4, hi4source, hi4zero, hshape⟩
    let AR : RatFunc k := T.source.A
    let BR : RatFunc k := T.source.B
    let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
    let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
    let GR : RatFunc k :=
      (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
        RatFunc.C (1 / 3 : k) * AR * CR
    have hCrec : AR ^ 2 / 3 + CR = T.source.C0 := by
      dsimp only [CR, AR]
      simp only [map_div₀, map_one, map_ofNat]
      ring
    have hDrec : AR * BR / 3 + FR = T.source.D := by
      dsimp only [FR, AR, BR]
      simp only [map_div₀, map_one, map_ofNat]
      ring
    have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = T.source.E := by
      dsimp only [GR, CR, AR]
      simp only [map_div₀, map_one, map_ofNat]
      ring
    have hi40 : firstIntegralFour68 0 AR BR (AR ^ 2 / 3 + CR)
        (AR * BR / 3 + FR) (AR ^ 3 / 27 + AR * CR / 3 + GR)
        (RatFunc.C (0 : k)) (RatFunc.C T.source.gamma)
        (RatFunc.C (0 : k)) (RatFunc.C T.source.epsilon)
        (RatFunc.C (0 : k)) = 0 := by
      rw [hCrec, hDrec, hErec]
      rw [hi4source, hi4zero]
      simp
    have hfactR := firstIntegralFour_mainTangent_zero_factor68
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      AR BR CR FR GR (by simpa only [map_zero] using hi40)
    refine ⟨by simpa only [AR, BR, CR, FR, GR] using hfactR, ?_⟩
    rcases hshape with hboundary | hrays
    · left
      rcases hboundary with ⟨hb1, hS0⟩
      let SR : RatFunc k := RatFunc.C 2 * CR + RatFunc.C (3 * T.source.gamma)
      have hCRmap : ratFuncAtHahn46 T.root CR =
          rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0) := by
        dsimp only [CR, AR, rhoOneCDefectHahn68]
        simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
      have hFRmap : ratFuncAtHahn46 T.root FR =
          rhoOneTangentDDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.B)
            (ratFuncAtHahn46 T.root T.source.D) := by
        dsimp only [FR, AR, BR, rhoOneTangentDDefectHahn68]
        simp only [map_sub, map_mul, ratFuncAtHahn46_C]
      have hGRmap : ratFuncAtHahn46 T.root GR =
          rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E)) := by
        dsimp only [GR, CR, AR, rhoOneTangentEDefectHahn68,
          rhoOneCDefectHahn68, rhoOneEDefectHahn68]
        simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
      have hB2 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
        T.root BR (1 : ℤ) (by
          dsimp only [BR]
          convert hB using 1 <;> norm_num) (by
          norm_num
          simpa only [BR] using hb1)
      norm_num at hB2
      have hSRmap : ratFuncAtHahn46 T.root SR =
          2 * ratFuncAtHahn46 T.root CR +
            HahnSeries.C (3 * T.source.gamma) := by
        dsimp only [SR]
        simp only [map_add, map_mul, ratFuncAtHahn46_C, map_ofNat]
      have hSR0 : (0 : WithTop ℚ) ≤
          (ratFuncAtHahn46 T.root SR).orderTop := by
        rw [hSRmap]
        apply hahnOrderTop_add_nonneg46
        · exact hahnOrderTop_mul_nonneg46 2 (ratFuncAtHahn46 T.root CR)
            (by simpa only [map_ofNat] using
              hahnOrderTop_C_nonneg46 (k := k) (2 : k))
            (by rw [hCRmap]; exact hC)
        · exact hahnOrderTop_C_nonneg46 _
      have hSRco : (ratFuncAtHahn46 T.root SR).coeff (0 : ℚ) = 0 := by
        rw [hSRmap, hCRmap]
        rw [HahnSeries.coeff_add]
        have htwo :
            (2 * rhoOneCDefectHahn68
              (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0)).coeff (0 : ℚ) =
              2 * (rhoOneCDefectHahn68
                (ratFuncAtHahn46 T.root T.source.A)
                (ratFuncAtHahn46 T.root T.source.C0)).coeff (0 : ℚ) := by
          rw [two_mul, HahnSeries.coeff_add]
          ring
        rw [htwo]
        simpa [HahnSeries.C_apply] using hS0
      have hSR1 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
        T.root SR 0 hSR0 (by norm_num; exact hSRco)
      norm_num at hSR1
      have hfactH := congrArg (ratFuncAtHahn46 T.root) hfactR
      have hfactH' : rhoOneI4ZeroFactored68
          (HahnSeries.C T.source.gamma) (HahnSeries.C T.source.epsilon)
          (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root CR)
          (ratFuncAtHahn46 T.root FR) (ratFuncAtHahn46 T.root GR) = 0 := by
        simpa only [rhoOneI4ZeroFactored68, map_add, map_mul, map_pow,
          map_neg, map_div₀, map_ofNat, map_zero, map_one,
          ratFuncAtHahn46_C] using hfactH
      have hnextface := rhoOneI4ZeroFactored_boundary_coeff_one68
        T.source.gamma T.source.epsilon
        (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root CR)
        (ratFuncAtHahn46 T.root FR) (ratFuncAtHahn46 T.root GR)
        hB2 (by rw [hFRmap]; exact hF) (by rw [hGRmap]; exact hG)
        (by rw [← hSRmap]; exact hSR1) hfactH'
      refine ⟨⟨hb1, hS0⟩, ?_, ?_, ?_⟩
      · dsimp only [BR] at hB2
        convert hB2 using 1 <;> norm_num
      · rw [← hCRmap, ← hSRmap]
        exact hSR1
      · rw [hCRmap, hFRmap, hGRmap] at hnextface
        simpa only [BR] using hnextface
    · right
      exact hrays
  · exact Or.inr hzero

end AlignedSquareTerminalGI4Next68

end Max11DegreeRoutes
