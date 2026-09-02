import Sol68ScaleTwoAlignedSquareBoundaryFiniteChildReductionScratch

/-! # The independent `I₃[0]` row on the finite boundary child -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryFiniteChildI3Reduction68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareBoundaryFiniteChildI3HahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- At the finite boundary orders, coefficient zero of the global third
first integral has only the `S[1]G[-1]`, `epsilon*C[0]`, and ground-constant
faces. -/
theorem rhoOneI3CapFactored_boundary_coeff_zero68
    (gamma epsilon i3 : k) (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(5 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hS : (↑(1 : ℚ) : WithTop ℚ) ≤
      (2 * C + HahnSeries.C (3 * gamma)).orderTop)
    (hi3 : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G = HahnSeries.C i3) :
    i3 = (8 / 3 : k) * C.coeff (1 : ℚ) * G.coeff (-1 : ℚ) +
      2 * epsilon * C.coeff (0 : ℚ) := by
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
      (hlt : 0 < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (0 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 0 h1 h2 h3 h4 h5 hlt
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
    (-2) 5 3 0 (-1) hA hB hF hC hG (by norm_num)
  have hB2C := hz (-8 / 9) B C A F G 2 1 0 0 0
    5 0 (-2) 3 (-1) hB hC hA hF hG (by norm_num)
  have hSGraw := lead (4 / 3) S G A B F 1 1 0 0 0
    1 (-1) (-2) 5 3 hS' hG hA hB hF
  have hSG :
      (weightedMonomial68 (4 / 3 : k) S G A B F 1 1 0 0 0).coeff 0 =
        (4 / 3 : k) * S.coeff 1 * G.coeff (-1 : ℚ) := by
    convert hSGraw using 1 <;> ring
  have hF2 := hz (4 / 3) F A B C G 2 0 0 0 0
    3 (-2) 5 0 (-1) hF hA hB hC hG (by norm_num)
  have hgammaB2 := hz (-(2 / 3) * gamma) B A C F G 2 0 0 0 0
    5 (-2) 0 3 (-1) hB hA hC hF hG (by norm_num)
  have hepsC :
      (weightedMonomial68 (2 * epsilon) C A B F G 1 0 0 0 0).coeff 0 =
        2 * epsilon * C.coeff 0 := by
    simp only [weightedMonomial68, pow_one, pow_zero, mul_one,
      HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hright : (HahnSeries.C i3 : HahnSeries ℚ k).coeff 0 = i3 := by
    simp [HahnSeries.C_apply]
  have hrewrite : rhoOneI3CapFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G =
      weightedMonomial68 (-8 / 9 : k) A B F C G 1 1 1 0 0 +
      weightedMonomial68 (-8 / 9 : k) B C A F G 2 1 0 0 0 +
      weightedMonomial68 (4 / 3 : k) S G A B F 1 1 0 0 0 +
      weightedMonomial68 (4 / 3 : k) F A B C G 2 0 0 0 0 +
      weightedMonomial68 (-(2 / 3 : k) * gamma) B A C F G 2 0 0 0 0 +
      weightedMonomial68 (2 * epsilon) C A B F G 1 0 0 0 0 := by
    simp only [rhoOneI3CapFactored68, S, weightedMonomial68, pow_zero,
      pow_one, mul_one, map_mul, map_div₀, map_neg, map_ofNat]
    ring
  have hc := congrArg (fun X : HahnSeries ℚ k => X.coeff (0 : ℚ)) hi3
  rw [hrewrite] at hc
  simp only [HahnSeries.coeff_add] at hc
  rw [hABF, hB2C, hSG, hF2, hgammaB2, hepsC, hright] at hc
  have hSone : S.coeff (1 : ℚ) = 2 * C.coeff (1 : ℚ) := by
    dsimp only [S]
    simp [HahnSeries.C_apply, two_mul]
  rw [hSone] at hc
  linear_combination -hc

/-- Testing the new `I₃[0]` scalar against the first finite quadratic wall
produces a cubic scalar residual, not a contradiction. -/
theorem rhoOneDoubleZero_boundaryFiniteChild_i3CubicWall68
    (a b c0 c1 g q i3 epsilon : k)
    (hi3 : i3 = (8 / 3 : k) * c1 * g + 2 * epsilon * c0)
    (hquadratic : (8 / 9 : k) * a * b * g ^ 2 + q * c1 = 0) :
    q * (i3 - 2 * epsilon * c0) +
      (64 / 27 : k) * a * b * g ^ 3 = 0 := by
  linear_combination
    q * hi3 + (8 / 3 : k) * g * hquadratic

/-- The finite child augmented by the first genuinely independent `I₃`
coefficient and its exact cubic consequence. -/
def RhoOneDoubleZeroBoundaryFiniteChildI3Packet68
    (root j epsilon : k) (h0R : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroBoundaryFiniteChildPacket68
      root j epsilon h0R A B C F G ∧
    ∃ i3 c : k, c ≠ 0 ∧
      ratFuncAtHahn46 root h0R = HahnSeries.single (1 : ℚ) c ∧
      i3 = (8 / 3 : k) * C.coeff (1 : ℚ) * G.coeff (-1 : ℚ) +
        2 * epsilon * C.coeff (0 : ℚ) ∧
      (j * c⁻¹) * (i3 - 2 * epsilon * C.coeff (0 : ℚ)) +
        (64 / 27 : k) * A.coeff (-2 : ℚ) * B.coeff (5 : ℚ) *
          G.coeff (-1 : ℚ) ^ 3 = 0

def RhoOneDoubleZeroBoundaryFiniteChildI3ReductionResidual68
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
      RhoOneDoubleZeroBoundaryFiniteChildI3Packet68
        root j epsilon hR A B C F G)) ∨
  (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
    (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 gamma B C F ∨
     RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 gamma B C F))

/-- Source transport of the independent finite-child `I₃[0]` scalar. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_boundaryFiniteChild_i3ZeroScalar
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(5 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (↑(3 : ℚ) : WithTop ℚ) ≤
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
    (hS : (↑(1 : ℚ) : WithTop ℚ) ≤
      (2 * rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0) +
        HahnSeries.C (3 * T.source.gamma)).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    ∃ i3 : k, i3 =
      (8 / 3 : k) *
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (1 : ℚ) *
          (rhoOneTangentEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.C0))
            (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
              (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ) +
        2 * T.source.epsilon *
          (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0)).coeff (0 : ℚ) := by
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
  obtain ⟨_i4, i3, _hi4, hi3raw⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  rw [hbeta, hdelta, hzeta] at hi3raw
  have hCrec : AR ^ 2 / 3 + CR = T.source.C0 := by
    dsimp only [CR, AR]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hDrec : AR * BR / 3 + FR = T.source.D := by
    dsimp only [FR, AR, BR]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = T.source.E := by
    dsimp only [GR, CR, AR]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hi3T :
      firstIntegralThree68 0 AR BR (AR ^ 2 / 3 + CR)
        (AR * BR / 3 + FR) (AR ^ 3 / 27 + AR * CR / 3 + GR)
        0 (RatFunc.C T.source.gamma) 0 (RatFunc.C T.source.epsilon) 0 =
          RatFunc.C i3 := by
    rw [hCrec, hDrec, hErec]
    simpa only [AR, BR, RatFunc.algebraMap_eq_C, map_zero] using hi3raw
  have hi3R := firstIntegralThree_cap_factor68
    (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      AR BR CR FR GR (RatFunc.C i3) hi3T
  have hi3Hraw := congrArg (ratFuncAtHahn46 T.root) hi3R
  have hi3H : rhoOneI3CapFactored68
      (HahnSeries.C T.source.gamma) (HahnSeries.C T.source.epsilon)
      (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
      (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
      (ratFuncAtHahn46 T.root GR) = HahnSeries.C i3 := by
    simpa only [rhoOneI3CapFactored68, map_add, map_sub, map_mul,
      map_pow, map_neg, map_div₀, map_ofNat, map_zero, map_one,
      RatFunc.algebraMap_eq_C, ratFuncAtHahn46_C] using hi3Hraw
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  have hscalar := rhoOneI3CapFactored_boundary_coeff_zero68
    T.source.gamma T.source.epsilon i3
      (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
      (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
      (ratFuncAtHahn46 T.root GR)
      (by simpa only [AR] using hbounds.1)
      (by simpa only [BR] using hB)
      (by rw [hCRmap]; exact hC)
      (by rw [hFRmap]; exact hF)
      (by rw [hGRmap]; exact hG)
      (by rw [hCRmap]; exact hS) hi3H
  refine ⟨i3, ?_⟩
  rw [hCRmap, hGRmap] at hscalar
  simpa only [AR, BR] using hscalar

/-- Source-facing top selector with the finite child reduced by `I₃[0]`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_boundaryFiniteChildI3ReductionResidual
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
    RhoOneDoubleZeroBoundaryFiniteChildI3ReductionResidual68
      T.root j T.source.gamma T.source.epsilon h0 A0 B0 C00 D0
      (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G := by
  dsimp only [RhoOneDoubleZeroBoundaryFiniteChildI3ReductionResidual68]
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A
    (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  have hprev :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_boundaryFiniteChildReductionResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprev with
      ⟨hK, hi4, hb1, hS0, hGne, hdeep | hfinite⟩ | hzero
  · exact Or.inl ⟨hK, hi4, hb1, hS0, hGne, Or.inl hdeep⟩
  · left
    refine ⟨hK, hi4, hb1, hS0, hGne, Or.inr ?_⟩
    have hshape := hi4.1.1
    dsimp only [RhoOneDoubleZeroTerminalGBoundaryFiniteResidual68] at hshape
    rcases hshape with ⟨_hfactor, hboundary | hray⟩
    · rcases hboundary with ⟨hcurrent, _hf2, hF3, _hb4, hB5,
          _hi4three, _hf3ne⟩
      rcases hcurrent with ⟨hprev4, _hb3, _hB4, _hi4two⟩
      rcases hprev4 with ⟨hprev3, _hf1, _hF2⟩
      rcases hprev3 with ⟨hprev2, _hb2, _hB3, _hi4one⟩
      rcases hprev2 with ⟨hprev1, _hf0, _hF1⟩
      rcases hprev1 with ⟨_hcoord, _hB2, hS1, _hi4zero⟩
      have hfiniteOld := hfinite
      rcases hfinite with ⟨c, hc, hsingle, hGne', hf3ne', hc1ne,
        hb5ne, hBexact, hscalar, htransport, hquadratic, hquadratic', hrow5⟩
      rcases T.rhoOne_exceptional_doubleZero_boundaryFiniteChild_i3ZeroScalar
          P hB5 hC hF3 hG hS1 hbeta hdelta hzeta with ⟨i3, hi3scalar⟩
      have hcubic := rhoOneDoubleZero_boundaryFiniteChild_i3CubicWall68
        (A.coeff (-2 : ℚ)) (B.coeff (5 : ℚ)) (C.coeff (0 : ℚ))
        (C.coeff (1 : ℚ)) (G.coeff (-1 : ℚ)) (j * c⁻¹) i3
        T.source.epsilon hi3scalar hquadratic
      exact ⟨hfiniteOld, i3, c, hc, hsingle, hi3scalar, hcubic⟩
    · exact (hray.1 hb1).elim
  · exact Or.inr hzero

end AlignedSquareBoundaryFiniteChildI3Reduction68

end Max11DegreeRoutes
