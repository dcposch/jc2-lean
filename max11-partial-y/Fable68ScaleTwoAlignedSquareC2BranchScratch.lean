import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapI4NextScratch

/-! # The first `I₃` row on the preserved `C[2]≠0` face of the cap

On the `G[-1]≠0` coordinate child of the finite terminal cap, the
coefficient-five `I₄` row split its `C[1]=0` branch into a `C[2]=0`
order-gain grandchild and a preserved finite-order face
`C[2]≠0 ∧ B[6]≠0 ∧ ord B = 6` tied by `B[6]G[-1]+C[2]F[3]=0`.  The third
first integral has not yet been consumed anywhere on this face: its
lowest exact row is the coefficient-one row, whose unique surviving term
is `(4/3)·(2C+3γ)[2]·G[-1] = (8/3)·C[2]·G[-1]`.  With `G[-1]≠0` this
forces `C[2]=0`, so the preserved finite-order face is impossible and the
`C[1]=0` child collapses onto its `C[2]=0` grandchild.  The `C[1]≠0`
branch, the nonzero quadratic rays, and the `G[-1]=0` sibling are
untouched. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapC2Branch68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareTerminalGBoundaryCapC2BranchHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The third first integral in the double-zero main-tangent coordinates,
restated for the preserved `C[2]≠0` face. -/
def rhoOneI3C2BranchFactored68 (gamma epsilon A B C F G : k) : k :=
  (-8 / 9 : k) * A * B * F - (8 / 9 : k) * B ^ 2 * C +
    (4 / 3 : k) * (2 * C + 3 * gamma) * G +
    (4 / 3 : k) * F ^ 2 - (2 / 3 : k) * gamma * B ^ 2 +
    2 * epsilon * C

theorem firstIntegralThree_c2Branch_factor68
    (gamma epsilon A B C F G i3 : k)
    (hi3 : firstIntegralThree68 0 A B (A ^ 2 / 3 + C)
      (A * B / 3 + F) (A ^ 3 / 27 + A * C / 3 + G)
      0 gamma 0 epsilon 0 = i3) :
    rhoOneI3C2BranchFactored68 gamma epsilon A B C F G = i3 := by
  rw [firstIntegralThree_mainTangent_decomposition68] at hi3
  simp only [firstIntegralThreeMainTangentTop68,
    firstIntegralThreeMainTangentLower68,
    rhoOneI3C2BranchFactored68] at hi3 ⊢
  linear_combination hi3

/-- On the order-six `B` face with `C[1]=0`, the coefficient-one `I₃` row
is the single product `(2C+3γ)[2]·G[-1]`. -/
theorem rhoOneI3C2BranchFactored_coeff_one68
    (gamma epsilon i3 : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(6 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑(2 : ℚ) : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hC1 : C.coeff (1 : ℚ) = 0)
    (hi3 : rhoOneI3C2BranchFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    C.coeff (2 : ℚ) * G.coeff (-1 : ℚ) = 0 := by
  let S : HahnSeries ℚ k := 2 * C + HahnSeries.C (3 * gamma)
  have hS' : (↑(2 : ℚ) : WithTop ℚ) ≤ S.orderTop := by
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
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 1
      h1 h2 h3 h4 h5 hlt
  have lead (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop) :=
    weightedMonomial68_coeff_at_general_lower_next s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
  have hABF := hz (-8 / 9) A B F C G 1 1 1 0 0
    (-2) 6 3 0 (-1) hA hB hF hC hG (by norm_num)
  have hB2C := hz (-8 / 9) B C A F G 2 1 0 0 0
    6 0 (-2) 3 (-1) hB hC hA hF hG (by norm_num)
  have hSGraw := lead (4 / 3) S G A B F 1 1 0 0 0
    2 (-1) (-2) 6 3 hS' hG hA hB hF
  have hSG :
      (weightedMonomial68 (4 / 3 : k) S G A B F 1 1 0 0 0).coeff 1 =
        (4 / 3 : k) * S.coeff 2 * G.coeff (-1 : ℚ) := by
    convert hSGraw using 1 <;> norm_num
  have hF2 := hz (4 / 3) F A B C G 2 0 0 0 0
    3 (-2) 6 0 (-1) hF hA hB hC hG (by norm_num)
  have hgammaB2 := hz (-(2 / 3) * gamma) B A C F G 2 0 0 0 0
    6 (-2) 0 3 (-1) hB hA hC hF hG (by norm_num)
  have hepsC :
      (weightedMonomial68 (2 * epsilon) C A B F G 1 0 0 0 0).coeff 1 = 0 := by
    simp only [weightedMonomial68, pow_one, pow_zero, mul_one,
      HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hC1,
      mul_zero]
  have hright : (HahnSeries.C i3 : HahnSeries ℚ k).coeff 1 = 0 := by
    simp [HahnSeries.C_apply]
  have hrewrite : rhoOneI3C2BranchFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G =
      weightedMonomial68 (-8 / 9 : k) A B F C G 1 1 1 0 0 +
      weightedMonomial68 (-8 / 9 : k) B C A F G 2 1 0 0 0 +
      weightedMonomial68 (4 / 3 : k) S G A B F 1 1 0 0 0 +
      weightedMonomial68 (4 / 3 : k) F A B C G 2 0 0 0 0 +
      weightedMonomial68 (-(2 / 3 : k) * gamma) B A C F G 2 0 0 0 0 +
      weightedMonomial68 (2 * epsilon) C A B F G 1 0 0 0 0 := by
    simp only [rhoOneI3C2BranchFactored68, S, weightedMonomial68, pow_zero,
      pow_one, mul_one, map_mul, map_div₀, map_neg, map_ofNat]
    ring
  have hc := congrArg (fun X : HahnSeries ℚ k => X.coeff 1) hi3
  rw [hrewrite] at hc
  simp only [HahnSeries.coeff_add] at hc
  rw [hABF, hB2C, hSG, hF2, hgammaB2, hepsC, hright] at hc
  have hSco : S.coeff 2 = 2 * C.coeff 2 := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    have htwo : (2 * C).coeff 2 = 2 * C.coeff 2 := by
      rw [two_mul, HahnSeries.coeff_add]
      ring
    rw [htwo]
    simp [HahnSeries.C_apply]
  rw [hSco] at hc
  linear_combination (3 / 8 : k) * hc

/-- The previous cap residual, sharpened on its `C[1]=0` coordinate
child: the preserved `C[2]≠0` finite-order face is impossible, so that
child always carries the `C[2]=0` order gain.  The `C[1]≠0` branch and
both nonzero quadratic rays remain verbatim in the first conjunct. -/
def RhoOneDoubleZeroTerminalGBoundaryCapC2BranchResidual68
    (root j gamma epsilon : k) (h0R BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapI4NextResidual68
      root j gamma epsilon h0R BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧
        2 * C.coeff (0 : ℚ) + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 →
      C.coeff (2 : ℚ) = 0 ∧ B.coeff (6 : ℚ) = 0 ∧
        (↑(7 : ℚ) : WithTop ℚ) ≤ B.orderTop)

/-- Literal source backwire of the coefficient-one `I₃` row: the
preserved `C[2]≠0` face of the cap is eliminated. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapC2BranchResidual
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
    RhoOneDoubleZeroTerminalGBoundaryCapC2BranchResidual68
        T.root j T.source.gamma T.source.epsilon
        (algebraMap k[X] (RatFunc k) h0) BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F)) := by
  dsimp only [RhoOneDoubleZeroTerminalGBoundaryCapC2BranchResidual68]
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, _, _, hsplit⟩
  rcases hsplit with hGne | ⟨hGzero, hG0, htail⟩
  · have hprev :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapI4NextResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    rcases hprev with hcapNext | hbad
    · left
      refine ⟨hcapNext, ?_⟩
      intro hcoord hc1
      have htarget := hcapNext.2 hcoord
      rcases htarget with ⟨hrow5, hCsplit⟩
      rcases hCsplit with hCzero | hCne
      · rcases hCzero with ⟨⟨hc1', hb5, hB6⟩, hC2split⟩
        rcases hC2split with hC2zero | hC2ne
        · exact hC2zero
        · exfalso
          rcases hC2ne with ⟨hc2ne, hb6ne, hBexact⟩
          have hfinite := hcapNext.1.1
          dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68]
            at hfinite
          rcases hfinite with ⟨hfact, hboundary | hrays⟩
          · rcases hboundary with ⟨hcurrent, hf2, hF3, hb4, hB5,
              hi4three, hf3ne⟩
            rcases hcurrent with ⟨hprev4, hb3, hB4, hi4two⟩
            rcases hprev4 with ⟨hprev3, hf1, hF2⟩
            rcases hprev3 with ⟨hprev2, hb2, hB3, hi4one⟩
            rcases hprev2 with ⟨hprev1, hf0, hF1⟩
            rcases hprev1 with ⟨hcoord', hB2, hS1, hi4zero⟩
            let AR : RatFunc k := T.source.A
            let BR : RatFunc k := T.source.B
            let CR : RatFunc k :=
              T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
            let FR : RatFunc k :=
              T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
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
            let SR : RatFunc k := 2 * CR + RatFunc.C (3 * T.source.gamma)
            have hSRmap : ratFuncAtHahn46 T.root SR =
                2 * ratFuncAtHahn46 T.root CR +
                  HahnSeries.C (3 * T.source.gamma) := by
              dsimp only [SR]
              simp only [map_add, map_mul, map_ofNat, ratFuncAtHahn46_C]
            have hscoeff (n : ℤ) (hn : n ≠ 0)
                (hcn : (ratFuncAtHahn46 T.root CR).coeff (n : ℚ) = 0) :
                (ratFuncAtHahn46 T.root SR).coeff (n : ℚ) = 0 := by
              rw [hSRmap, HahnSeries.coeff_add]
              have htwo :
                  (2 * ratFuncAtHahn46 T.root CR).coeff (n : ℚ) =
                    2 * (ratFuncAtHahn46 T.root CR).coeff (n : ℚ) := by
                rw [two_mul, HahnSeries.coeff_add]
                ring
              rw [htwo, hcn]
              simp only [HahnSeries.C_apply]
              rw [HahnSeries.coeff_single_of_ne]
              · ring
              · exact_mod_cast hn
            have hS1R : (↑(1 : ℚ) : WithTop ℚ) ≤
                (ratFuncAtHahn46 T.root SR).orderTop := by
              rw [hSRmap, hCRmap]
              exact hS1
            have hS2raw := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
              T.root SR 1 hS1R (hscoeff 1 (by norm_num) (by
                rw [hCRmap]
                exact hc1))
            norm_num at hS2raw
            have hbounds := P.2.1
            dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
            have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
                (ratFuncAtHahn46 T.root AR).orderTop := by
              simpa only [AR] using hbounds.1
            obtain ⟨i4, i3, hi4raw, hi3raw⟩ :=
              integratedFirstIntegrals_exist_ground68
                T.source.A T.source.B T.source.C0 T.source.D T.source.E
                (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
                0 T.source.alpha T.source.beta T.source.gamma T.source.delta
                T.source.epsilon T.source.zeta T.source.eta (by
                  simpa only [RatFunc.algebraMap_eq_C] using
                    T.source.bracket_eq)
            rw [hbeta, hdelta, hzeta] at hi3raw
            have hCrec : AR ^ 2 / 3 + CR = T.source.C0 := by
              dsimp only [CR, AR]
              simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one,
                map_ofNat]
              ring
            have hDrec : AR * BR / 3 + FR = T.source.D := by
              dsimp only [FR, AR, BR]
              simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one,
                map_ofNat]
              ring
            have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = T.source.E := by
              dsimp only [GR, CR, AR]
              simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one,
                map_ofNat]
              ring
            have hi3T :
                firstIntegralThree68 0 AR BR (AR ^ 2 / 3 + CR)
                  (AR * BR / 3 + FR) (AR ^ 3 / 27 + AR * CR / 3 + GR)
                  0 (RatFunc.C T.source.gamma) 0
                  (RatFunc.C T.source.epsilon) 0 = RatFunc.C i3 := by
              rw [hCrec, hDrec, hErec]
              simpa only [AR, BR, RatFunc.algebraMap_eq_C, map_zero]
                using hi3raw
            have hi3R := firstIntegralThree_c2Branch_factor68
              (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
              AR BR CR FR GR (RatFunc.C i3) hi3T
            have hi3Hraw := congrArg (ratFuncAtHahn46 T.root) hi3R
            have hi3H : rhoOneI3C2BranchFactored68
                (HahnSeries.C T.source.gamma)
                (HahnSeries.C T.source.epsilon)
                (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
                (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
                (ratFuncAtHahn46 T.root GR) = HahnSeries.C i3 := by
              simpa only [rhoOneI3C2BranchFactored68, map_add, map_sub,
                map_mul, map_pow, map_neg, map_div₀, map_ofNat, map_zero,
                map_one, RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C]
                using hi3Hraw
            have hface := rhoOneI3C2BranchFactored_coeff_one68
              T.source.gamma T.source.epsilon i3
              (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
              (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
              (ratFuncAtHahn46 T.root GR)
              hAH (by simpa only [BR] using hB6)
              (by rw [hCRmap]; exact hC) (by rw [hFRmap]; exact hF3)
              (by rw [hGRmap]; exact hG)
              (by rw [hSRmap] at hS2raw; exact hS2raw)
              (by rw [hCRmap]; exact hc1) hi3H
            rw [hCRmap, hGRmap] at hface
            rcases mul_eq_zero.mp hface with hc2zero | hgzero
            · exact hc2ne hc2zero
            · exact hGne hgzero
          · exact hrays.1 hcoord.1
      · exact (hCne.1 hc1).elim
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

#print axioms firstIntegralThree_c2Branch_factor68
#print axioms rhoOneI3C2BranchFactored_coeff_one68
#print axioms SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapC2BranchResidual

end AlignedSquareTerminalGBoundaryCapC2Branch68

end Max11DegreeRoutes
