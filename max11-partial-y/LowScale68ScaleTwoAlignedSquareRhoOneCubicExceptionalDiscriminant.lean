import LowScale68ScaleTwoAlignedSquareRhoOneCubicMainTangentNextCoefficient

/-! # The exceptional discriminant and its next invariant face -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicExceptionalDiscriminant68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneCubicExceptionalDiscriminantHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Rational functions embedded at a finite place have integral Hahn
exponents.  Hence killing the coefficient at an integral lower bound improves
that bound by one. -/
theorem ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    (a : k) (R : RatFunc k) (n : ℤ)
    (hord : (↑(n : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 a R).orderTop)
    (hcoeff : (ratFuncAtHahn46 a R).coeff (n : ℚ) = 0) :
    (↑((n + 1 : ℤ) : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 a R).orderTop := by
  let y : LaurentSeries k := ratFuncAtLaurent46 a R
  let e : ℤ ↪o ℚ :=
    ⟨⟨Int.castAddHom ℚ, intCastAddHom46_injective⟩,
      intCastAddHom46_le _ _⟩
  have hX : ratFuncAtHahn46 a R =
      HahnSeries.embDomain e y := by
    dsimp only [e, y, ratFuncAtHahn46, laurentToRationalHahn46]
    rfl
  rw [hX, HahnSeries.orderTop_embDomain] at hord ⊢
  rw [hX] at hcoeff
  cases hm : y.orderTop with
  | top => simp [hm]
  | coe m =>
      simp only [hm, WithTop.map_coe, WithTop.coe_le_coe] at hord ⊢
      dsimp only [e, Int.castAddHom] at hord ⊢
      change (n : ℚ) ≤ (m : ℚ) at hord
      change ((n + 1 : ℤ) : ℚ) ≤ (m : ℚ)
      have hneQ : (n : ℚ) ≠ (m : ℚ) := by
        intro hnm
        have horder :
            (HahnSeries.embDomain e y).orderTop =
              ((n : ℚ) : WithTop ℚ) := by
          rw [HahnSeries.orderTop_embDomain, hm, WithTop.map_coe]
          change ((m : ℚ) : WithTop ℚ) = ((n : ℚ) : WithTop ℚ)
          exact congrArg (fun q : ℚ => (q : WithTop ℚ)) hnm.symm
        exact (HahnSeries.orderTop_ne_of_coeff_eq_zero hcoeff) horder
      have hleZ : n ≤ m := by exact_mod_cast hord
      have hneZ : n ≠ m := by exact_mod_cast hneQ
      have hs : n + 1 ≤ m := by omega
      exact_mod_cast hs

def rhoOneZeroLCubicExceptionalDiscriminant68 (a f g : k) : k :=
  2 * a * f ^ 2 + 6 * g ^ 2

/-- The singular determinant component of the first exceptional packet
already forces both transverse leading coefficients to vanish. -/
theorem rhoOneZeroLCubicExceptional_discriminant_zero68
    (a b1 c1 f g : k)
    (h4 : rhoOneZeroLCubicExceptionalFour68 b1 c1 f g = 0)
    (h3 : rhoOneZeroLCubicExceptionalThree68 a b1 c1 f g = 0)
    (hdisc : rhoOneZeroLCubicExceptionalDiscriminant68 a f g = 0) :
    f = 0 ∧ g = 0 := by
  have helim := rhoOneZeroLCubicExceptional_next_elimination68
    a b1 c1 f g h4 h3
  simp only [rhoOneZeroLCubicExceptionalDiscriminant68] at hdisc
  have hf3 : f ^ 3 = 0 := by
    rw [hdisc] at helim
    simp only [mul_zero] at helim
    linear_combination (-1 / 3 : k) * helim.1
  have hf : f = 0 := eq_zero_of_pow_eq_zero hf3
  refine ⟨hf, ?_⟩
  have hg2 : g ^ 2 = 0 := by
    simp only [hf, zero_pow, OfNat.ofNat_ne_zero, mul_zero, zero_add] at hdisc
    linear_combination (1 / 6 : k) * hdisc
  exact eq_zero_of_pow_eq_zero hg2

def rhoOneZeroLCubicExceptionalDegenerateFour68
    (delta a b1 c1 f1 g1 : k) : k :=
  (8 / 3 : k) * (b1 * g1 + c1 * f1) + (1 / 4 : k) * delta * a ^ 2

def rhoOneZeroLCubicExceptionalDegenerateThree68
    (a b1 c1 f1 g1 : k) : k :=
  (-8 / 9 : k) * a * b1 * f1 + (8 / 3 : k) * c1 * g1

def rhoOneZeroLCubicExceptionalSecondDiscriminant68
    (a b1 c1 : k) : k :=
  a * b1 ^ 2 + 3 * c1 ^ 2

theorem rhoOneZeroLCubicExceptional_degenerate_elimination68
    (delta a b1 c1 f1 g1 : k)
    (h4 : rhoOneZeroLCubicExceptionalDegenerateFour68
      delta a b1 c1 f1 g1 = 0)
    (h3 : rhoOneZeroLCubicExceptionalDegenerateThree68
      a b1 c1 f1 g1 = 0) :
    32 * rhoOneZeroLCubicExceptionalSecondDiscriminant68 a b1 c1 * f1 +
        9 * delta * a ^ 2 * c1 = 0 ∧
      32 * rhoOneZeroLCubicExceptionalSecondDiscriminant68 a b1 c1 * g1 +
        3 * delta * a ^ 3 * b1 = 0 := by
  simp only [rhoOneZeroLCubicExceptionalDegenerateFour68] at h4
  simp only [rhoOneZeroLCubicExceptionalDegenerateThree68] at h3
  simp only [rhoOneZeroLCubicExceptionalSecondDiscriminant68]
  constructor
  · linear_combination 36 * c1 * h4 - 36 * b1 * h3
  · linear_combination 12 * a * b1 * h4 + 36 * c1 * h3

/-- Away from `delta = 0`, the second linear system is nonsingular. -/
theorem rhoOneZeroLCubicExceptional_secondDiscriminant_ne_zero68
    (delta a b1 c1 f1 g1 : k) (ha : a ≠ 0) (hdelta : delta ≠ 0)
    (h4 : rhoOneZeroLCubicExceptionalDegenerateFour68
      delta a b1 c1 f1 g1 = 0)
    (h3 : rhoOneZeroLCubicExceptionalDegenerateThree68
      a b1 c1 f1 g1 = 0) :
    rhoOneZeroLCubicExceptionalSecondDiscriminant68 a b1 c1 ≠ 0 := by
  intro hdisc
  have helim := rhoOneZeroLCubicExceptional_degenerate_elimination68
    delta a b1 c1 f1 g1 h4 h3
  rw [hdisc] at helim
  norm_num at helim
  have hc1 : c1 = 0 := by
    rcases helim.1 with (hd | ha0) | hc1
    · exact (hdelta hd).elim
    · exact (ha ha0).elim
    · exact hc1
  have hb1 : b1 = 0 := by
    rcases helim.2 with (hd | ha0) | hb1
    · exact (hdelta hd).elim
    · exact (ha ha0).elim
    · exact hb1
  simp only [rhoOneZeroLCubicExceptionalDegenerateFour68, hb1, hc1,
    zero_mul, zero_add] at h4
  have hda : delta * a ^ 2 = 0 := by
    linear_combination 4 * h4
  exact (mul_ne_zero hdelta (pow_ne_zero 2 ha)) hda

/-- The next I4/I3 coefficients after the discriminant-zero descent
`f = g = 0`. -/
theorem firstIntegral_mainTangent_exceptional_degenerate_coeff68
    (gamma delta epsilon zeta : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-2 : ℚ) : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(-2 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-3 : ℚ) : WithTop ℚ) ≤ G.orderTop) :
    (firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
      (HahnSeries.C zeta)).coeff (-4 : ℚ) =
        rhoOneZeroLCubicExceptionalDegenerateFour68 delta
          (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
          (C.coeff (-2 : ℚ)) (F.coeff (-2 : ℚ))
          (G.coeff (-3 : ℚ)) ∧
    (firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
      (HahnSeries.C zeta)).coeff (-5 : ℚ) =
        rhoOneZeroLCubicExceptionalDegenerateThree68
          (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
          (C.coeff (-2 : ℚ)) (F.coeff (-2 : ℚ))
          (G.coeff (-3 : ℚ)) := by
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
      (HahnSeries.C delta) (HahnSeries.C epsilon) (HahnSeries.C zeta)
      A B C F G
  have h3dec := firstIntegralThree_mainTangent_decomposition68
    (k := HahnSeries ℚ k) (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C epsilon) (HahnSeries.C zeta)
      A B C F G
  have h4decH :
      firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
          (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
          (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
          (HahnSeries.C zeta) =
        firstIntegralFourMainTangentTopHahn68 0 A B C F G +
          firstIntegralFourMainTangentLowerHahn68 0 gamma delta epsilon zeta
            A B C F G := by
    rw [h4dec]
    simp only [firstIntegralFourMainTangentTop68,
      firstIntegralFourMainTangentLower68, firstIntegralFourMainTangentTopHahn68,
      firstIntegralFourMainTangentLowerHahn68, weightedMonomial68, map_mul,
      map_neg, map_div₀, map_ofNat, map_one]
    ring
  have h3decH :
      firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
          (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
          (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
          (HahnSeries.C zeta) =
        firstIntegralThreeMainTangentTopHahn68 A B C F G +
          firstIntegralThreeMainTangentLowerHahn68 0 gamma delta epsilon zeta
            A B C F G := by
    rw [h3dec]
    simp only [firstIntegralThreeMainTangentTop68,
      firstIntegralThreeMainTangentLower68, firstIntegralThreeMainTangentTopHahn68,
      firstIntegralThreeMainTangentLowerHahn68, weightedMonomial68, map_mul,
      map_neg, map_div₀, map_ofNat, map_one]
    ring
  have h4t1 := hz (-4) (-8 / 27 : k) B A C F G 3 0 0 0 0
    (-1) (-2) (-2) (-2) (-3) hB hA hC hF hG (by norm_num)
  have h4t3 := lead (8 / 3 : k) B G A C F 1 1 0 0 0
    (-1) (-3) (-2) (-2) (-2) hB hG hA hC hF
  have h4t4 := lead (8 / 3 : k) C F A B G 1 1 0 0 0
    (-2) (-2) (-2) (-1) (-3) hC hF hA hB hG
  have h4l3 := lead ((1 / 4 : k) * delta) A B C F G 2 0 0 0 0
    (-2) (-1) (-2) (-2) (-3) hA hB hC hF hG
  have h4l5 := hz (-4) (3 * delta) C A B F G 1 0 0 0 0
    (-2) (-2) (-1) (-2) (-3) hC hA hB hF hG (by norm_num)
  have h4l6 := hz (-4) (4 * gamma) F A B C G 1 0 0 0 0
    (-2) (-2) (-1) (-2) (-3) hF hA hB hC hG (by norm_num)
  have h4l7 := hz (-4) zeta A B C F G 1 0 0 0 0
    (-2) (-1) (-2) (-2) (-3) hA hB hC hF hG (by norm_num)
  have h4l8 := hz (-4) (2 * epsilon) B A C F G 1 0 0 0 0
    (-1) (-2) (-2) (-2) (-3) hB hA hC hF hG (by norm_num)
  have h3t1 := lead (-8 / 9 : k) A B F C G 1 1 1 0 0
    (-2) (-1) (-2) (-2) (-3) hA hB hF hC hG
  have h3t2 := hz (-5) (-8 / 9 : k) B C A F G 2 1 0 0 0
    (-1) (-2) (-2) (-2) (-3) hB hC hA hF hG (by norm_num)
  have h3t3 := lead (8 / 3 : k) C G A B F 1 1 0 0 0
    (-2) (-3) (-2) (-1) (-2) hC hG hA hB hF
  have h3l2 := hz (-5) (4 / 3 : k) F A B C G 2 0 0 0 0
    (-2) (-2) (-1) (-2) (-3) hF hA hB hC hG (by norm_num)
  have h3l5 := hz (-5) (-(1 / 2 : k) * delta) A B C F G 1 1 0 0 0
    (-2) (-1) (-2) (-2) (-3) hA hB hC hF hG (by norm_num)
  have h3l6 := hz (-5) (-(2 / 3 : k) * gamma) B A C F G 2 0 0 0 0
    (-1) (-2) (-2) (-2) (-3) hB hA hC hF hG (by norm_num)
  have h3l7 := hz (-5) (4 * gamma) G A B C F 1 0 0 0 0
    (-3) (-2) (-1) (-2) (-2) hG hA hB hC hF (by norm_num)
  have h3l8 := hz (-5) (2 * epsilon) C A B F G 1 0 0 0 0
    (-2) (-2) (-1) (-2) (-3) hC hA hB hF hG (by norm_num)
  have h3l9 := hz (-5) (3 * delta) F A B C G 1 0 0 0 0
    (-2) (-2) (-1) (-2) (-3) hF hA hB hC hG (by norm_num)
  have h3l10 := hz (-5) zeta B A C F G 1 0 0 0 0
    (-1) (-2) (-2) (-2) (-3) hB hA hC hF hG (by norm_num)
  norm_num at h4t3 h4t4 h4l3 h3t1 h3t3
  have h3t1' :
      (weightedMonomial68 (-8 / 9 : k) A B F C G 1 1 1 0 0).coeff
          (-5 : ℚ) =
        (-8 / 9 : k) * A.coeff (-2 : ℚ) * B.coeff (-1 : ℚ) *
          F.coeff (-2 : ℚ) := by
    convert h3t1 using 1 <;> ring
  have hCzero : (HahnSeries.C (0 : k) : HahnSeries ℚ k) = 0 :=
    HahnSeries.C_zero
  constructor
  · rw [h4decH]
    simp only [HahnSeries.coeff_add, firstIntegralFourMainTangentTopHahn68,
      firstIntegralFourMainTangentLowerHahn68]
    rw [h4t1, h4t3, h4t4, h4l3, h4l5, h4l6, h4l7, h4l8]
    simp only [weightedMonomial68, mul_zero, zero_mul, neg_zero]
    rw [hCzero]
    simp only [zero_mul, HahnSeries.coeff_zero,
      rhoOneZeroLCubicExceptionalDegenerateFour68]
    ring
  · rw [h3decH]
    simp only [HahnSeries.coeff_add, firstIntegralThreeMainTangentTopHahn68,
      firstIntegralThreeMainTangentLowerHahn68]
    rw [h3t1', h3t2, h3t3, h3l2, h3l5, h3l6, h3l7, h3l8, h3l9,
      h3l10]
    simp only [weightedMonomial68, mul_zero, zero_mul, neg_zero]
    rw [hCzero]
    simp only [zero_mul, HahnSeries.coeff_zero,
      rhoOneZeroLCubicExceptionalDegenerateThree68]
    ring

/-- Source-facing singular-discriminant split. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_exceptional_discriminant_zero
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
        (G.coeff (-4 : ℚ)) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    F.coeff (-3 : ℚ) = 0 ∧ G.coeff (-4 : ℚ) = 0 := by
  have hnext := T.rhoOne_mainTangent_exceptional_next
    hp hH hp6 hp5 hp4 P hmain hb hc hbeta
  dsimp only at hdisc hnext ⊢
  exact rhoOneZeroLCubicExceptional_discriminant_zero68 _ _ _ _ _
    hnext.1 hnext.2 hdisc

/-- On the singular discriminant, integral support promotes the two vanished
transverse coefficients to improved Hahn orders. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_exceptional_discriminant_orders
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
        (G.coeff (-4 : ℚ)) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    ((↑(-2 : ℚ) : WithTop ℚ) ≤ F.orderTop) ∧
      ((↑(-3 : ℚ) : WithTop ℚ) ≤ G.orderTop) := by
  have hbase := T.rhoOne_mainTangent_defect_orders
    hp hH hp6 hp5 hp4 P hmain
  have hzero := T.rhoOne_mainTangent_exceptional_discriminant_zero
    hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc
  dsimp only at hbase hzero ⊢
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
  let CH := ratFuncAtHahn46 T.root C0R
  let DH := ratFuncAtHahn46 T.root DR
  let EH := ratFuncAtHahn46 T.root E0R
  let CRH := ratFuncAtHahn46 T.root CR
  let ERH := ratFuncAtHahn46 T.root ER
  let FRH := ratFuncAtHahn46 T.root FR
  let GRH := ratFuncAtHahn46 T.root GR
  have hCRmap : CRH = rhoOneCDefectHahn68 AH CH := by
    dsimp only [CRH, CR, AH, CH, AR, C0R, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ERH = rhoOneEDefectHahn68 AH EH := by
    dsimp only [ERH, ER, AH, EH, AR, E0R, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFRmap : FRH = rhoOneTangentDDefectHahn68 AH BH DH := by
    dsimp only [FRH, FR, AH, BH, DH, AR, BR, DR,
      rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hGRmap : GRH = rhoOneTangentEDefectHahn68 AH CRH ERH := by
    dsimp only [GRH, GR, ERH, AH, CRH, AR,
      rhoOneTangentEDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hFbase : (↑(-3 : ℚ) : WithTop ℚ) ≤ FRH.orderTop := by
    rw [hFRmap]
    exact hbase.1
  have hGbase : (↑(-4 : ℚ) : WithTop ℚ) ≤ GRH.orderTop := by
    rw [hGRmap, hCRmap, hERmap]
    exact hbase.2
  have hFzero : FRH.coeff (-3 : ℚ) = 0 := by
    rw [hFRmap]
    exact hzero.1
  have hGzero : GRH.coeff (-4 : ℚ) = 0 := by
    rw [hGRmap, hCRmap, hERmap]
    exact hzero.2
  have hFi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root FR (-3) hFbase hFzero
  have hGi := ratFuncAtHahn46_orderTop_ge_int_succ_of_coeff_zero
    T.root GR (-4) hGbase hGzero
  norm_num at hFi hGi
  constructor
  · rw [← hFRmap]
    exact hFi
  · rw [← hCRmap, ← hERmap, ← hGRmap]
    exact hGi

/-- Exact source transport of the first invariant packet after the singular
discriminant has forced `f = g = 0`. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_exceptional_discriminant_next
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
        (G.coeff (-4 : ℚ)) = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    rhoOneZeroLCubicExceptionalDegenerateFour68 T.source.delta
      (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
      (C.coeff (-2 : ℚ)) (F.coeff (-2 : ℚ))
      (G.coeff (-3 : ℚ)) = 0 ∧
    rhoOneZeroLCubicExceptionalDegenerateThree68
      (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
      (C.coeff (-2 : ℚ)) (F.coeff (-2 : ℚ))
      (G.coeff (-3 : ℚ)) = 0 := by
  have hBC := T.rhoOne_mainTangent_exceptional_orders
    hp hH hp6 hp5 hp4 P hb hc
  have hFG := T.rhoOne_mainTangent_exceptional_discriminant_orders
    hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc
  dsimp only at hb hc hBC hFG ⊢
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C ER
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  have hA := hbounds.1
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi4H := congrArg (ratFuncAtHahn46 T.root) hi4
  have hi4H' :
      firstIntegralFour68 0 A B C0 D E
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i4 := by
    dsimp only [A, B, C0, D, E]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi4H
  have hi3H := congrArg (ratFuncAtHahn46 T.root) hi3
  have hi3H' :
      firstIntegralThree68 0 A B C0 D E
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i3 := by
    dsimp only [A, B, C0, D, E]
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi3H
  rw [hbeta] at hi4H' hi3H'
  have hthird : HahnSeries.C (1 / 3 : k) =
      (1 / 3 : HahnSeries ℚ k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_one]
    simp only [map_ofNat]
  have hCrec : A ^ 2 / 3 + C = C0 := by
    dsimp only [C, rhoOneCDefectHahn68]
    rw [hthird]
    ring
  have hDrec : A * B / 3 + F = D := by
    dsimp only [F, rhoOneTangentDDefectHahn68]
    simp only [map_mul, map_div₀, map_ofNat, map_one]
    ring
  have hErec : A ^ 3 / 27 + A * C / 3 + G = E := by
    dsimp only [G, ER, rhoOneTangentEDefectHahn68,
      rhoOneEDefectHahn68]
    simp only [map_mul, map_div₀, map_ofNat, map_one]
    ring
  have hformula := firstIntegral_mainTangent_exceptional_degenerate_coeff68
    T.source.gamma T.source.delta T.source.epsilon T.source.zeta
      A B C F G hA hBC.1 hBC.2 hFG.1 hFG.2
  have h4coeff := congrArg (fun X : HahnSeries ℚ k => X.coeff (-4 : ℚ))
    hi4H'
  have h3coeff := congrArg (fun X : HahnSeries ℚ k => X.coeff (-5 : ℚ))
    hi3H'
  have h4const : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-4 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  have h3const : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-5 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [← hCrec, ← hDrec, ← hErec, hformula.1, h4const] at h4coeff
  rw [← hCrec, ← hDrec, ← hErec, hformula.2, h3const] at h3coeff
  exact ⟨h4coeff, h3coeff⟩

/-- Exact source-facing component split: if `delta ≠ 0`, the second
discriminant cannot vanish. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_exceptional_secondDiscriminant_ne_zero
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
    (hdelta : T.source.delta ≠ 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let C := rhoOneCDefectHahn68 A C0
    rhoOneZeroLCubicExceptionalSecondDiscriminant68
      (A.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
      (C.coeff (-2 : ℚ)) ≠ 0 := by
  have hnext := T.rhoOne_mainTangent_exceptional_discriminant_next
    hp hH hp6 hp5 hp4 P hmain hb hc hbeta hdisc
  have ha :
      let A := ratFuncAtHahn46 T.root T.source.A
      A.coeff (-2 : ℚ) ≠ 0 := by
    exact P.2.2.1
  dsimp only at hnext ha ⊢
  exact rhoOneZeroLCubicExceptional_secondDiscriminant_ne_zero68
    T.source.delta _ _ _ _ _ ha hdelta hnext.1 hnext.2

end AlignedSquareRhoOneCubicExceptionalDiscriminant68

end Max11DegreeRoutes
