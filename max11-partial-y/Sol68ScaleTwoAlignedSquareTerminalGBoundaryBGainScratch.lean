import Sol68ScaleTwoAlignedSquareTerminalGBoundaryNextScratch

/-! # The next `B` gain on the zero-boundary nonzero-`G[-1]` packet -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryBGain68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryBGainHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- In the gained box, coefficient two of the global zero-`I₄` factor is
the next sparse `BG+SF` face. -/
theorem rhoOneI4ZeroFactored_boundary_coeff_two68
    (gamma epsilon : k) (B C F G : HahnSeries ℚ k)
    (hB : (↑(3 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hF : (↑(1 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑(1 : ℚ) : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hfactor : rhoOneI4ZeroFactored68
      (HahnSeries.C gamma) (HahnSeries.C epsilon) B C F G = 0) :
    B.coeff (3 : ℚ) * G.coeff (-1 : ℚ) +
      C.coeff (1 : ℚ) * F.coeff (1 : ℚ) = 0 := by
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
      (hlt : (2 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (2 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 2 h1 h2 h3 h4 h5 hlt
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
    3 3 3 3 3 hB hB hB hB hB (by norm_num)
  have hBG := lead (8 / 3) B G B F S 1 1 0 0 0
    3 (-1) 3 1 1 hB hG hB hF hS'
  have hSF := lead (4 / 3) S F B S G 1 1 0 0 0
    1 1 3 1 (-1) hS' hF hB hS' hG
  have heB := hz (2 * epsilon) B B B B B 1 0 0 0 0
    3 3 3 3 3 hB hB hB hB hB (by norm_num)
  norm_num at hBG hSF
  have hfactor' :
      weightedMonomial68 (-8 / 27 : k) B B B B B 3 0 0 0 0 +
        weightedMonomial68 (8 / 3 : k) B G B F S 1 1 0 0 0 +
        weightedMonomial68 (4 / 3 : k) S F B S G 1 1 0 0 0 +
        weightedMonomial68 (2 * epsilon) B B B B B 1 0 0 0 0 = 0 := by
    simpa only [rhoOneI4ZeroFactored68, S, weightedMonomial68,
      pow_zero, pow_one, mul_one, map_add, map_mul, map_div₀, map_neg,
      map_ofNat, map_one] using hfactor
  have hc := congrArg (fun X : HahnSeries ℚ k => X.coeff (2 : ℚ)) hfactor'
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

def RhoOneDoubleZeroTerminalGBoundaryBGainResidual68
    (gamma epsilon : k) (BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  rhoOneI4ZeroFactored68 (RatFunc.C gamma) (RatFunc.C epsilon)
      BR CR FR GR = 0 ∧
    (((((B.coeff (1 : ℚ) = 0 ∧ 2 * C.coeff (0 : ℚ) + 3 * gamma = 0) ∧
          (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
          (↑(1 : ℚ) : WithTop ℚ) ≤
            (2 * C + HahnSeries.C (3 * gamma)).orderTop ∧
          B.coeff (2 : ℚ) * G.coeff (-1 : ℚ) +
            C.coeff (1 : ℚ) * F.coeff (0 : ℚ) = 0) ∧
          F.coeff (0 : ℚ) = 0 ∧
          (↑(1 : ℚ) : WithTop ℚ) ≤ F.orderTop) ∧
        B.coeff (2 : ℚ) = 0 ∧
        (↑(3 : ℚ) : WithTop ℚ) ≤ B.orderTop ∧
        B.coeff (3 : ℚ) * G.coeff (-1 : ℚ) +
          C.coeff (1 : ℚ) * F.coeff (1 : ℚ) = 0) ∨
      (B.coeff (1 : ℚ) ≠ 0 ∧
        2 * C.coeff (0 : ℚ) + 3 * gamma ≠ 0 ∧
        ∃ r : k, r ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2 : ℚ) ∧
          (3 * (2 * C.coeff (0 : ℚ) + 3 * gamma) =
              2 * r * B.coeff (1 : ℚ) ∨
           3 * (2 * C.coeff (0 : ℚ) + 3 * gamma) =
              -(2 * r * B.coeff (1 : ℚ)))))

/-- Backwired next `B` gain and coefficient-two `I₄` face. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryBGainResidual
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
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A
      (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroTerminalGBoundaryBGainResidual68
        T.source.gamma T.source.epsilon BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryBGainResidual68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hGne | ⟨hGzero, hG0, htail⟩
  · have hprev :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryNextResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryNextResidual68] at hprev
    rcases hprev with ⟨hfact, hshape⟩ | hbad
    · left
      refine ⟨hfact, ?_⟩
      rcases hshape with hboundary | hrays
      · left
        rcases hboundary with ⟨hbase, hf0, hF1⟩
        rcases hbase with ⟨hcoord, hB2, hS1, hi4old⟩
        have hb2 : (ratFuncAtHahn46 T.root T.source.B).coeff (2 : ℚ) = 0 := by
          rw [hf0] at hi4old
          norm_num at hi4old
          rcases hi4old with hb | hg
          · exact hb
          · exact (hGne hg).elim
        have hB3 := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
          T.root T.source.B 2 hB2 (by norm_num; exact hb2)
        norm_num at hB3
        let AR : RatFunc k := T.source.A
        let BR : RatFunc k := T.source.B
        let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
        let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
        let GR : RatFunc k :=
          (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
            RatFunc.C (1 / 3 : k) * AR * CR
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
        change rhoOneI4ZeroFactored68
          (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
          BR CR FR GR = 0 at hfact
        have hfactH := congrArg (ratFuncAtHahn46 T.root) hfact
        have hfactH' : rhoOneI4ZeroFactored68
            (HahnSeries.C T.source.gamma) (HahnSeries.C T.source.epsilon)
            (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root CR)
            (ratFuncAtHahn46 T.root FR) (ratFuncAtHahn46 T.root GR) = 0 := by
          simpa only [rhoOneI4ZeroFactored68, map_add, map_mul, map_pow,
            map_neg, map_div₀, map_ofNat, map_zero, map_one,
            ratFuncAtHahn46_C] using hfactH
        have hi4next := rhoOneI4ZeroFactored_boundary_coeff_two68
          T.source.gamma T.source.epsilon
          (ratFuncAtHahn46 T.root BR) (ratFuncAtHahn46 T.root CR)
          (ratFuncAtHahn46 T.root FR) (ratFuncAtHahn46 T.root GR)
          (by
            dsimp only [BR]
            convert hB3 using 1 <;> norm_num)
          (by rw [hFRmap]; exact hF1)
          (by rw [hGRmap]; exact hG) (by rw [hCRmap]; exact hS1) hfactH'
        rw [hCRmap, hFRmap, hGRmap] at hi4next
        exact ⟨⟨⟨hcoord, hB2, hS1, hi4old⟩, hf0, hF1⟩, hb2,
          (by convert hB3 using 1 <;> norm_num),
          by simpa only [BR] using hi4next⟩
      · right
        exact hrays
    · exact (hGne hbad.1).elim
  · right
    refine ⟨hGzero, hG0, ?_⟩
    have hres :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalBGainResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only [RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68] at hres
    rcases hres with hbad | ⟨_, _, htail'⟩
    · exact (hbad hGzero).elim
    · exact htail'

end AlignedSquareTerminalGBoundaryBGain68

end Max11DegreeRoutes
