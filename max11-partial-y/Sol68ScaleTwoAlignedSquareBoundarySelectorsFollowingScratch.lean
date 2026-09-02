import Sol68ScaleTwoAlignedSquareBoundarySelectorsNextScratch

/-! # Coupled boundary-selector reductions after the next invariant faces -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundarySelectorsFollowing68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance boundarySelectorsFollowingLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

omit [IsAlgClosed k] in
/-- Cancellation of the two nonzero leading coordinates turns the `I3(-1)`
face into a scalar next-jet relation. -/
theorem rhoOne_boundaryF_coupled_scalar68
    (a b am bm fm f0 : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrel : 3 * fm = 2 * a * b)
    (hrow : a * b * f0 = fm * (am * b + a * bm)) :
    3 * f0 = 2 * (am * b + a * bm) := by
  have hp : a * b * (3 * f0 - 2 * (am * b + a * bm)) = 0 := by
    linear_combination 3 * hrow + (am * b + a * bm) * hrel
  rcases mul_eq_zero.mp hp with hab | hs
  · rcases mul_eq_zero.mp hab with ha0 | hb0
    · exact (ha ha0).elim
    · exact (hb hb0).elim
  · linear_combination hs

omit [IsAlgClosed k] in
/-- The sparse arbitrary-ground `I4(1)` face on the `G[-2]` boundary. -/
theorem rhoOne_boundaryG_i4one_laurent68
    (gamma epsilon i4 : k) (B C F G : LaurentSeries k)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G = HahnSeries.C i4) :
    B.coeff 2 * G.coeff (-1) + B.coeff 3 * G.coeff (-2) +
      C.coeff 1 * F.coeff 0 = 0 := by
  let S : LaurentSeries k := 2 * C + HahnSeries.C (3 * gamma)
  have hSbase : (0 : WithTop ℤ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · rw [two_mul]
      exact (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
    · by_cases hx : 3 * gamma = 0
      · rw [hx, HahnSeries.C_zero]
        simp
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hx]
        simp
  have hSco0 : S.coeff 0 = 0 := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single_same]
    linear_combination hS0
  have hS := laurent_orderTop_ge_succ_of_coeff_zero68 S 0 hSbase hSco0
  have hSco1 : S.coeff 1 = 2 * C.coeff 1 := by
    dsimp only [S]
    simp [two_mul, HahnSeries.C_apply, HahnSeries.coeff_single]
  have hBG := laurent_coeff_mul_lower_succ68 B G 2 (-2) hB hG
  have hSF := laurent_coeff_mul_lower68 S F 1 0 hS hF
  norm_num at hBG hSF
  have hBB : (↑(4 : ℤ) : WithTop ℤ) ≤ (B * B).orderTop := by
    apply le_trans _ HahnSeries.orderTop_add_le_mul
    have ht := add_le_add hB hB
    norm_num at ht ⊢
    exact ht
  have hB3ord : (↑(6 : ℤ) : WithTop ℤ) ≤ (B ^ 3).orderTop := by
    rw [pow_succ, pow_two]
    apply le_trans _ HahnSeries.orderTop_add_le_mul
    have ht := add_le_add hBB hB
    norm_num at ht ⊢
    exact ht
  have hB3z : (B ^ 3).coeff 1 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB3ord)
  have hBz : B.coeff 1 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hB)
  have hi4rhs : (HahnSeries.C i4 : LaurentSeries k).coeff 1 = 0 := by
    simp [HahnSeries.C_apply]
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hi4rewrite : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) B C F G =
      HahnSeries.C (-(8 / 27 : k)) * (B ^ 3) +
        HahnSeries.C (8 / 3 : k) * (B * G) +
        HahnSeries.C (4 / 3 : k) * (S * F) +
        HahnSeries.C (2 * epsilon) * B := by
    simp only [rhoOneI4ZeroFactored68, S, HahnSeries.C_eq_algebraMap,
      map_mul, map_add, map_neg, map_div₀, map_ofNat, map_one]
    ring
  have hi4c := congrArg (fun X : LaurentSeries k => X.coeff 1) hi4
  rw [hi4rewrite] at hi4c
  simp only [HahnSeries.coeff_add, hscale] at hi4c
  rw [hB3z, hBG, hSF, hBz, hSco1, hi4rhs] at hi4c
  linear_combination (3 / 8 : k) * hi4c

omit [IsAlgClosed k] in
/-- Rational transport of the sparse `I4(1)` face. -/
theorem ratFunc_boundaryG_i4one68
    (root gamma epsilon i4 : k) (B C F G : RatFunc k)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hS0 : 2 * (ratFuncAtHahn46 root C).coeff 0 + 3 * gamma = 0)
    (hi4 : rhoOneI4ZeroFactored68 (RatFunc.C gamma)
      (RatFunc.C epsilon) B C F G = RatFunc.C i4) :
    (ratFuncAtHahn46 root B).coeff 2 * (ratFuncAtHahn46 root G).coeff (-1) +
      (ratFuncAtHahn46 root B).coeff 3 * (ratFuncAtHahn46 root G).coeff (-2) +
      (ratFuncAtHahn46 root C).coeff 1 * (ratFuncAtHahn46 root F).coeff 0 = 0 := by
  let BL := ratFuncAtLaurent46 root B
  let CL := ratFuncAtLaurent46 root C
  let FL := ratFuncAtLaurent46 root F
  let GLa := ratFuncAtLaurent46 root G
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B 2 hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C 0 hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F 0 hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-2) hG
  have hi4L := congrArg (ratFuncAtLaurent46 root) hi4
  have hi4L' : rhoOneI4ZeroFactored68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) BL CL FL GLa = HahnSeries.C i4 := by
    simpa only [BL, CL, FL, GLa, rhoOneI4ZeroFactored68,
      map_add, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
      ratFuncAtLaurent46_C68] using hi4L
  have hcs (R : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 root R n
  have hS0L : 2 * CL.coeff 0 + 3 * gamma = 0 := by
    rw [← hcs C 0]
    exact hS0
  have hf := rhoOne_boundaryG_i4one_laurent68 gamma epsilon i4
    BL CL FL GLa hBL hCL hFL hGL hS0L hi4L'
  have hf' := hf
  simp only [BL, CL, FL, GLa, ← hcs B 2, ← hcs B 3,
    ← hcs C 1, ← hcs F 0, ← hcs G (-1), ← hcs G (-2)] at hf'
  convert hf' using 1 <;> norm_num

omit [IsAlgClosed k] in
/-- Crossing `I4(1)` with terminal coefficient `-4` removes the two shared
next-jet terms. -/
theorem rhoOne_boundaryG_i4_terminal_cross68
    (am a b bm fm f0 f1 gm g0 c1 : k)
    (hi4 : b * gm + bm * g0 + c1 * f0 = 0)
    (hterm : g0 * (3 * f1 + am * b + a * bm) + a * f0 * c1 = 0) :
    g0 * (3 * f1 + am * b) = a * b * gm := by
  linear_combination hterm - a * hi4

def RhoOneAlignedSquareFNegOneBoundaryFollowing68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  RhoOneAlignedSquareFNegOneBoundaryNext68 T g u ∧
  3 * F.coeff 0 =
    2 * (A.coeff (-1) * B.coeff 1 + A.coeff (-2) * B.coeff 2)

def RhoOneAlignedSquareGNegTwoBoundaryFollowing68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  RhoOneAlignedSquareGNegTwoBoundaryNext68 T g u ∧
  ∃ i4 : k,
    firstIntegralFour68 0 T.source.A T.source.B T.source.C0
      T.source.D T.source.E (RatFunc.C (0 : k))
      (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
      (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 ∧
    B.coeff 2 * G.coeff (-1) + B.coeff 3 * G.coeff (-2) +
      C.coeff 1 * F.coeff 0 = 0 ∧
    G.coeff (-2) * (3 * F.coeff 1 + A.coeff (-1) * B.coeff 2) =
      A.coeff (-2) * B.coeff 2 * G.coeff (-1)

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryF_following
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareFNegOneBoundaryNext68 T g u) :
    RhoOneAlignedSquareFNegOneBoundaryFollowing68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryNext68] at Rc
  rcases Rc with ⟨R0, i4, hi4src, hi4face, hrow⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryResidual68] at R0c
  rcases R0c with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hS, hb, hrel⟩
  have ha : (ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ) ≠ 0 :=
    P.2.2.1
  have hs := rhoOne_boundaryF_coupled_scalar68
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff (1 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff (2 : ℚ))
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (-1 : ℚ))
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (0 : ℚ))
    ha hb hrel hrow
  dsimp only [RhoOneAlignedSquareFNegOneBoundaryFollowing68]
  exact ⟨R, hs⟩

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_following
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoBoundaryNext68 T g u) :
    RhoOneAlignedSquareGNegTwoBoundaryFollowing68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rc
  rcases Rc with ⟨R0, hi3packet, hterminal⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at R0c
  rcases R0c with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hb1, hS, hscalar, hi4old⟩
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  have hCmap : ratFuncAtHahn46 T.root C =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, A, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : ratFuncAtHahn46 T.root F =
      rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, A, B, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hEmap : ratFuncAtHahn46 T.root E =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [E, A, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGmap : ratFuncAtHahn46 T.root G =
      rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, hCmap]
    rw [map_mul, ratFuncAtHahn46_C]
  obtain ⟨i4, i3, hi4f, hi3f, hi4src, hi3src⟩ :=
    T.rhoOne_boundary_integral_factors P hbeta hdelta hzeta
  have hi4face := ratFunc_boundaryG_i4one68 T.root T.source.gamma
    T.source.epsilon i4 B C F G
      (by simpa only [B] using hB) (by rw [hCmap]; exact hC)
      (by rw [hFmap]; exact hF) (by rw [hGmap]; exact hG)
      (by rw [hCmap]; exact hS) hi4f
  have hi4faceC := hi4face
  rw [hGmap, hCmap, hFmap] at hi4faceC
  have hcross := rhoOne_boundaryG_i4_terminal_cross68
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff (2 : ℚ))
    ((ratFuncAtHahn46 T.root T.source.B).coeff (3 : ℚ))
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (-1 : ℚ))
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (0 : ℚ))
    ((rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (1 : ℚ))
    ((rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ))
    ((rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-2 : ℚ))
    ((rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff (1 : ℚ))
    hi4faceC hterminal
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68]
  refine ⟨R, i4, hi4src, ?_, hcross⟩
  simpa only [A, B] using hi4faceC

/-- Both finite boundary limbs are strictly refined; the final order box is
preserved literally. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundarySelectors_following
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareFNegOneBoundaryNext68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryNext68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0)) :
    RhoOneAlignedSquareFNegOneBoundaryFollowing68 T g u ∨
      RhoOneAlignedSquareGNegTwoBoundaryFollowing68 T g u ∨
      (RhoOneAlignedSquareFinalOrderBox68 T ∧ T.source.zeta = 0) := by
  rcases R with hF | hG | hbox
  · exact Or.inl (T.rhoOne_boundaryF_following hF)
  · exact Or.inr (Or.inl (T.rhoOne_boundaryG_following hG))
  · exact Or.inr (Or.inr hbox)

end AlignedSquareBoundarySelectorsFollowing68

end Max11DegreeRoutes
