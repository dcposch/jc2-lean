import LowScale68ScaleTwoAlignedSquareRhoOneCubicMainTangent

/-! # The next I4/I3 invariants on the zero-septic main tangent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicMainTangentInvariants68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneCubicMainTangentInvariantsHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def rhoOneZeroLCubicMainTangentFour68 (beta a b c f g : k) : k :=
  -64 * b ^ 3 + 15 * beta * a ^ 3 + 576 * b * g + 576 * c * f

def rhoOneZeroLCubicMainTangentThree68 (a b c f g : k) : k :=
  -a * b * f - b ^ 2 * c + 3 * c * g

def firstIntegralFourMainTangentTop68
    (beta A B C F G : k) : k :=
  (-8 / 27 : k) * B ^ 3 + (5 / 72 : k) * beta * A ^ 3 +
    (8 / 3 : k) * B * G + (8 / 3 : k) * C * F

def firstIntegralFourMainTangentLower68
    (beta gamma delta epsilon zeta A B C F G : k) : k :=
  (5 / 6 : k) * beta * A * C - (5 / 12 : k) * beta * B ^ 2 +
  (1 / 4 : k) * delta * A ^ 2 + 5 * beta * G + 3 * delta * C +
  4 * gamma * F + A * zeta + 2 * B * epsilon

def firstIntegralThreeMainTangentTop68 (A B C F G : k) : k :=
  (-8 / 9 : k) * A * B * F - (8 / 9 : k) * B ^ 2 * C +
    (8 / 3 : k) * C * G

def firstIntegralThreeMainTangentLower68
    (beta gamma delta epsilon zeta A B C F G : k) : k :=
  (-5 / 72 : k) * beta * A ^ 2 * B + (4 / 3 : k) * F ^ 2 -
  (5 / 6 : k) * beta * A * F - (5 / 6 : k) * beta * B * C -
  (1 / 2 : k) * delta * A * B - (2 / 3 : k) * gamma * B ^ 2 +
  4 * gamma * G + 2 * epsilon * C + 3 * delta * F + B * zeta

theorem firstIntegralFour_mainTangent_decomposition68
    (beta gamma delta epsilon zeta A B C F G : k) :
    firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
        (A ^ 3 / 27 + A * C / 3 + G) beta gamma delta epsilon zeta =
      firstIntegralFourMainTangentTop68 beta A B C F G +
        firstIntegralFourMainTangentLower68 beta gamma delta epsilon zeta
          A B C F G := by
  simp only [firstIntegralFour68, firstIntegralFourMainTangentTop68,
    firstIntegralFourMainTangentLower68]
  ring

theorem firstIntegralThree_mainTangent_decomposition68
    (beta gamma delta epsilon zeta A B C F G : k) :
    firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
        (A ^ 3 / 27 + A * C / 3 + G) beta gamma delta epsilon zeta =
      firstIntegralThreeMainTangentTop68 A B C F G +
        firstIntegralThreeMainTangentLower68 beta gamma delta epsilon zeta
          A B C F G := by
  simp only [firstIntegralThree68, firstIntegralThreeMainTangentTop68,
    firstIntegralThreeMainTangentLower68]
  ring

def firstIntegralFourMainTangentTopHahn68
    (beta : k) (A B C F G : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 (-8 / 27 : k) B A C F G 3 0 0 0 0 +
  weightedMonomial68 ((5 / 72 : k) * beta) A B C F G 3 0 0 0 0 +
  weightedMonomial68 (8 / 3 : k) B G A C F 1 1 0 0 0 +
  weightedMonomial68 (8 / 3 : k) C F A B G 1 1 0 0 0

def firstIntegralThreeMainTangentTopHahn68
    (A B C F G : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 (-8 / 9 : k) A B F C G 1 1 1 0 0 +
  weightedMonomial68 (-8 / 9 : k) B C A F G 2 1 0 0 0 +
  weightedMonomial68 (8 / 3 : k) C G A B F 1 1 0 0 0

def firstIntegralFourMainTangentLowerHahn68
    (beta gamma delta epsilon zeta : k)
    (A B C F G : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 ((5 / 6 : k) * beta) A C B F G 1 1 0 0 0 +
  weightedMonomial68 (-(5 / 12 : k) * beta) B A C F G 2 0 0 0 0 +
  weightedMonomial68 ((1 / 4 : k) * delta) A B C F G 2 0 0 0 0 +
  weightedMonomial68 (5 * beta) G A B C F 1 0 0 0 0 +
  weightedMonomial68 (3 * delta) C A B F G 1 0 0 0 0 +
  weightedMonomial68 (4 * gamma) F A B C G 1 0 0 0 0 +
  weightedMonomial68 zeta A B C F G 1 0 0 0 0 +
  weightedMonomial68 (2 * epsilon) B A C F G 1 0 0 0 0

def firstIntegralThreeMainTangentLowerHahn68
    (beta gamma delta epsilon zeta : k)
    (A B C F G : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 (-(5 / 72 : k) * beta) A B C F G 2 1 0 0 0 +
  weightedMonomial68 (4 / 3 : k) F A B C G 2 0 0 0 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) A F B C G 1 1 0 0 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) B C A F G 1 1 0 0 0 +
  weightedMonomial68 (-(1 / 2 : k) * delta) A B C F G 1 1 0 0 0 +
  weightedMonomial68 (-(2 / 3 : k) * gamma) B A C F G 2 0 0 0 0 +
  weightedMonomial68 (4 * gamma) G A B C F 1 0 0 0 0 +
  weightedMonomial68 (2 * epsilon) C A B F G 1 0 0 0 0 +
  weightedMonomial68 (3 * delta) F A B C G 1 0 0 0 0 +
  weightedMonomial68 zeta B A C F G 1 0 0 0 0

theorem firstIntegralMainTangentLower_coeff_zero68
    (beta gamma delta epsilon zeta : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-3 : ℚ) : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(-3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-4 : ℚ) : WithTop ℚ) ≤ G.orderTop) :
    (firstIntegralFourMainTangentLowerHahn68 beta gamma delta epsilon zeta
      A B C F G).coeff (-6 : ℚ) = 0 ∧
    (firstIntegralThreeMainTangentLowerHahn68 beta gamma delta epsilon zeta
      A B C F G).coeff (-7 : ℚ) = 0 := by
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
  constructor
  · have h1 := hz (-6) ((5 / 6 : k) * beta) A C B F G 1 1 0 0 0
      (-2) (-3) (-2) (-3) (-4) hA hC hB hF hG (by norm_num)
    have h2 := hz (-6) (-(5 / 12 : k) * beta) B A C F G 2 0 0 0 0
      (-2) (-2) (-3) (-3) (-4) hB hA hC hF hG (by norm_num)
    have h3 := hz (-6) ((1 / 4 : k) * delta) A B C F G 2 0 0 0 0
      (-2) (-2) (-3) (-3) (-4) hA hB hC hF hG (by norm_num)
    have h4 := hz (-6) (5 * beta) G A B C F 1 0 0 0 0
      (-4) (-2) (-2) (-3) (-3) hG hA hB hC hF (by norm_num)
    have h5 := hz (-6) (3 * delta) C A B F G 1 0 0 0 0
      (-3) (-2) (-2) (-3) (-4) hC hA hB hF hG (by norm_num)
    have h6 := hz (-6) (4 * gamma) F A B C G 1 0 0 0 0
      (-3) (-2) (-2) (-3) (-4) hF hA hB hC hG (by norm_num)
    have h7 := hz (-6) zeta A B C F G 1 0 0 0 0
      (-2) (-2) (-3) (-3) (-4) hA hB hC hF hG (by norm_num)
    have h8 := hz (-6) (2 * epsilon) B A C F G 1 0 0 0 0
      (-2) (-2) (-3) (-3) (-4) hB hA hC hF hG (by norm_num)
    simp only [firstIntegralFourMainTangentLowerHahn68, HahnSeries.coeff_add]
    rw [h1, h2, h3, h4, h5, h6, h7, h8]
    ring
  · have h1 := hz (-7) (-(5 / 72 : k) * beta) A B C F G 2 1 0 0 0
      (-2) (-2) (-3) (-3) (-4) hA hB hC hF hG (by norm_num)
    have h2 := hz (-7) (4 / 3 : k) F A B C G 2 0 0 0 0
      (-3) (-2) (-2) (-3) (-4) hF hA hB hC hG (by norm_num)
    have h3 := hz (-7) (-(5 / 6 : k) * beta) A F B C G 1 1 0 0 0
      (-2) (-3) (-2) (-3) (-4) hA hF hB hC hG (by norm_num)
    have h4 := hz (-7) (-(5 / 6 : k) * beta) B C A F G 1 1 0 0 0
      (-2) (-3) (-2) (-3) (-4) hB hC hA hF hG (by norm_num)
    have h5 := hz (-7) (-(1 / 2 : k) * delta) A B C F G 1 1 0 0 0
      (-2) (-2) (-3) (-3) (-4) hA hB hC hF hG (by norm_num)
    have h6 := hz (-7) (-(2 / 3 : k) * gamma) B A C F G 2 0 0 0 0
      (-2) (-2) (-3) (-3) (-4) hB hA hC hF hG (by norm_num)
    have h7 := hz (-7) (4 * gamma) G A B C F 1 0 0 0 0
      (-4) (-2) (-2) (-3) (-3) hG hA hB hC hF (by norm_num)
    have h8 := hz (-7) (2 * epsilon) C A B F G 1 0 0 0 0
      (-3) (-2) (-2) (-3) (-4) hC hA hB hF hG (by norm_num)
    have h9 := hz (-7) (3 * delta) F A B C G 1 0 0 0 0
      (-3) (-2) (-2) (-3) (-4) hF hA hB hC hG (by norm_num)
    have h10 := hz (-7) zeta B A C F G 1 0 0 0 0
      (-2) (-2) (-3) (-3) (-4) hB hA hC hF hG (by norm_num)
    simp only [firstIntegralThreeMainTangentLowerHahn68, HahnSeries.coeff_add]
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    ring

theorem firstIntegralMainTangentTop_coeff68
    (beta : k) (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-3 : ℚ) : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(-3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-4 : ℚ) : WithTop ℚ) ≤ G.orderTop) :
    (firstIntegralFourMainTangentTopHahn68 beta A B C F G).coeff (-6 : ℚ) =
      (1 / 216 : k) * rhoOneZeroLCubicMainTangentFour68 beta
        (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ))
        (C.coeff (-3 : ℚ)) (F.coeff (-3 : ℚ))
        (G.coeff (-4 : ℚ)) ∧
    (firstIntegralThreeMainTangentTopHahn68 A B C F G).coeff (-7 : ℚ) =
      (8 / 9 : k) * rhoOneZeroLCubicMainTangentThree68
        (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ))
        (C.coeff (-3 : ℚ)) (F.coeff (-3 : ℚ))
        (G.coeff (-4 : ℚ)) := by
  have lead (r : ℚ) (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hw : (n1 : ℚ) * r1 + (n2 : ℚ) * r2 + (n3 : ℚ) * r3 +
        (n4 : ℚ) * r4 + (n5 : ℚ) * r5 = r) :=
    weightedMonomial68_coeff_at_general_lower_next s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 h1 h2 h3 h4 h5
  constructor
  · have h1 := lead (-6) (-8 / 27 : k) B A C F G 3 0 0 0 0
      (-2) (-2) (-3) (-3) (-4) hB hA hC hF hG (by norm_num)
    have h2 := lead (-6) ((5 / 72 : k) * beta) A B C F G 3 0 0 0 0
      (-2) (-2) (-3) (-3) (-4) hA hB hC hF hG (by norm_num)
    have h3 := lead (-6) (8 / 3 : k) B G A C F 1 1 0 0 0
      (-2) (-4) (-2) (-3) (-3) hB hG hA hC hF (by norm_num)
    have h4 := lead (-6) (8 / 3 : k) C F A B G 1 1 0 0 0
      (-3) (-3) (-2) (-2) (-4) hC hF hA hB hG (by norm_num)
    norm_num at h1 h2 h3 h4
    have h1' : (weightedMonomial68 (-8 / 27 : k) B A C F G 3 0 0 0 0).coeff
        (-6 : ℚ) = (-8 / 27 : k) * (B.coeff (-2 : ℚ)) ^ 3 := by
      convert h1 using 1 <;> ring
    simp only [firstIntegralFourMainTangentTopHahn68, HahnSeries.coeff_add]
    rw [h1', h2, h3, h4]
    simp only [rhoOneZeroLCubicMainTangentFour68]
    ring
  · have h1 := lead (-7) (-8 / 9 : k) A B F C G 1 1 1 0 0
      (-2) (-2) (-3) (-3) (-4) hA hB hF hC hG (by norm_num)
    have h2 := lead (-7) (-8 / 9 : k) B C A F G 2 1 0 0 0
      (-2) (-3) (-2) (-3) (-4) hB hC hA hF hG (by norm_num)
    have h3 := lead (-7) (8 / 3 : k) C G A B F 1 1 0 0 0
      (-3) (-4) (-2) (-2) (-3) hC hG hA hB hF (by norm_num)
    norm_num at h1 h2 h3
    have h1' : (weightedMonomial68 (-8 / 9 : k) A B F C G 1 1 1 0 0).coeff
        (-7 : ℚ) = (-8 / 9 : k) * A.coeff (-2 : ℚ) *
          B.coeff (-2 : ℚ) * F.coeff (-3 : ℚ) := by
      convert h1 using 1 <;> ring
    have h2' : (weightedMonomial68 (-8 / 9 : k) B C A F G 2 1 0 0 0).coeff
        (-7 : ℚ) = (-8 / 9 : k) * (B.coeff (-2 : ℚ)) ^ 2 *
          C.coeff (-3 : ℚ) := by
      convert h2 using 1 <;> ring
    simp only [firstIntegralThreeMainTangentTopHahn68, HahnSeries.coeff_add]
    rw [h1', h2', h3]
    simp only [rhoOneZeroLCubicMainTangentThree68]
    ring

theorem firstIntegral_mainTangent_coeff68
    (beta gamma delta epsilon zeta : k)
    (A B C F G : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-3 : ℚ) : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(-3 : ℚ) : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-4 : ℚ) : WithTop ℚ) ≤ G.orderTop) :
    (firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C beta)
      (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
      (HahnSeries.C zeta)).coeff (-6 : ℚ) =
        (1 / 216 : k) * rhoOneZeroLCubicMainTangentFour68 beta
          (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ))
          (C.coeff (-3 : ℚ)) (F.coeff (-3 : ℚ))
          (G.coeff (-4 : ℚ)) ∧
    (firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C beta)
      (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
      (HahnSeries.C zeta)).coeff (-7 : ℚ) =
        (8 / 9 : k) * rhoOneZeroLCubicMainTangentThree68
          (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ))
          (C.coeff (-3 : ℚ)) (F.coeff (-3 : ℚ))
          (G.coeff (-4 : ℚ)) := by
  have h4dec := firstIntegralFour_mainTangent_decomposition68
    (k := HahnSeries ℚ k) (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C epsilon) (HahnSeries.C zeta)
      A B C F G
  have h3dec := firstIntegralThree_mainTangent_decomposition68
    (k := HahnSeries ℚ k) (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C epsilon) (HahnSeries.C zeta)
      A B C F G
  have hlower := firstIntegralMainTangentLower_coeff_zero68
    beta gamma delta epsilon zeta A B C F G hA hB hC hF hG
  have htop := firstIntegralMainTangentTop_coeff68 beta A B C F G
    hA hB hC hF hG
  have h4decH :
      firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
          (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C beta)
          (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
          (HahnSeries.C zeta) =
        firstIntegralFourMainTangentTopHahn68 beta A B C F G +
          firstIntegralFourMainTangentLowerHahn68 beta gamma delta epsilon zeta
            A B C F G := by
    rw [h4dec]
    simp only [firstIntegralFourMainTangentTop68,
      firstIntegralFourMainTangentLower68, firstIntegralFourMainTangentTopHahn68,
      firstIntegralFourMainTangentLowerHahn68, weightedMonomial68, map_mul,
      map_neg, map_div₀, map_ofNat, map_one]
    ring
  have h3decH :
      firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
          (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C beta)
          (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
          (HahnSeries.C zeta) =
        firstIntegralThreeMainTangentTopHahn68 A B C F G +
          firstIntegralThreeMainTangentLowerHahn68 beta gamma delta epsilon zeta
            A B C F G := by
    rw [h3dec]
    simp only [firstIntegralThreeMainTangentTop68,
      firstIntegralThreeMainTangentLower68, firstIntegralThreeMainTangentTopHahn68,
      firstIntegralThreeMainTangentLowerHahn68, weightedMonomial68, map_mul,
      map_neg, map_div₀, map_ofNat, map_one]
    ring
  constructor
  · rw [h4decH, HahnSeries.coeff_add, hlower.1, add_zero]
    exact htop.1
  · rw [h3decH, HahnSeries.coeff_add, hlower.2, add_zero]
    exact htop.2

theorem rhoOneZeroLCubicMainTangent_rows_force_c68
    (beta a b c f g : k)
    (h1 : rhoOneZeroLCubicMainTangentOne68 a b c f g = 0)
    (h3 : rhoOneZeroLCubicMainTangentThree68 a b c f g = 0) :
    c = 0 ∨ c ^ 2 = a * b ^ 2 := by
  have hfac : c * (c ^ 2 - a * b ^ 2) = 0 := by
    simp only [rhoOneZeroLCubicMainTangentOne68] at h1
    simp only [rhoOneZeroLCubicMainTangentThree68] at h3
    linear_combination (1 / 9 : k) * (h1 + 7 * a * h3)
  rcases mul_eq_zero.mp hfac with hc | hc
  · exact Or.inl hc
  · right
    linear_combination hc

/-- Exact finite split cut out by the old row-one face and the two new
first-integral faces.  In particular, the `c = 0` component separates into
the exceptional `b = 0, beta = 0` locus and the `b ≠ 0, f = 0` locus. -/
theorem rhoOneZeroLCubicMainTangent_exact_split68
    (beta a b c f g : k) (ha : a ≠ 0)
    (h1 : rhoOneZeroLCubicMainTangentOne68 a b c f g = 0)
    (h4 : rhoOneZeroLCubicMainTangentFour68 beta a b c f g = 0)
    (h3 : rhoOneZeroLCubicMainTangentThree68 a b c f g = 0) :
    (c = 0 ∧
      ((b = 0 ∧ beta = 0) ∨
       (b ≠ 0 ∧ f = 0 ∧
        -64 * b ^ 3 + 15 * beta * a ^ 3 + 576 * b * g = 0))) ∨
    (c ≠ 0 ∧ b ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
      rhoOneZeroLCubicMainTangentFour68 beta a b c f g = 0 ∧
      rhoOneZeroLCubicMainTangentThree68 a b c f g = 0) := by
  have hcsplit :=
    rhoOneZeroLCubicMainTangent_rows_force_c68 beta a b c f g h1 h3
  by_cases hc0 : c = 0
  · left
    refine ⟨hc0, ?_⟩
    by_cases hb : b = 0
    · left
      refine ⟨hb, ?_⟩
      simp only [rhoOneZeroLCubicMainTangentFour68, hc0, hb] at h4
      norm_num at h4
      exact h4.resolve_right ha
    · right
      have habf : a * b * f = 0 := by
        simp only [rhoOneZeroLCubicMainTangentThree68, hc0, mul_zero,
          zero_mul, sub_zero, add_zero] at h3
        linear_combination -h3
      have hf : f = 0 :=
        (mul_eq_zero.mp habf).resolve_left (mul_ne_zero ha hb)
      refine ⟨hb, hf, ?_⟩
      simpa only [rhoOneZeroLCubicMainTangentFour68, hc0, hf, mul_zero,
        add_zero] using h4
  · right
    have hc : c ^ 2 = a * b ^ 2 := hcsplit.resolve_left hc0
    have hb : b ≠ 0 := by
      intro hb
      have hc2 : c * c = 0 := by
        simpa only [hb, pow_two, mul_zero] using hc
      exact hc0 (mul_self_eq_zero.mp hc2)
    exact ⟨hc0, hb, hc, h4, h3⟩

/-- Conditional source transport of the two new invariant rows.  The only
explicit hypotheses beyond the canonical source packet are the two improved
tangent-defect orders; the previous source construction proves these orders
internally, but does not export them as an API. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_invariants_of_orders
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hF :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let D := ratFuncAtHahn46 T.root T.source.D
      (↑(-3 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68 A B D).orderTop)
    (hG :
      let A := ratFuncAtHahn46 T.root T.source.A
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      (↑(-4 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentEDefectHahn68 A C ER).orderTop) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    rhoOneZeroLCubicMainTangentFour68 T.source.beta
      (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ)) (C.coeff (-3 : ℚ))
      (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0 ∧
    rhoOneZeroLCubicMainTangentThree68
      (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ)) (C.coeff (-3 : ℚ))
      (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0 := by
  dsimp only at hF hG ⊢
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C ER
  dsimp only [RhoOneZeroLCubicNextSourcePacket68,
    RhoOneZeroLCubicImprovedHahnBounds68] at P
  rcases P with ⟨P0, ⟨hA, hB, hC0, hC, hD, hE, hER⟩, hAne,
    htaut, h4old, h3old, hsplit⟩
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
  have hformula := firstIntegral_mainTangent_coeff68
    T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta A B C F G hA hB hC hF hG
  have h4coeff := congrArg (fun X : HahnSeries ℚ k => X.coeff (-6 : ℚ)) hi4H'
  have h3coeff := congrArg (fun X : HahnSeries ℚ k => X.coeff (-7 : ℚ)) hi3H'
  have h4const : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-6 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  have h3const : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-7 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [← hCrec, ← hDrec, ← hErec, hformula.1, h4const] at h4coeff
  rw [← hCrec, ← hDrec, ← hErec, hformula.2, h3const] at h3coeff
  constructor
  · exact (mul_eq_zero.mp h4coeff).resolve_left (by norm_num)
  · exact (mul_eq_zero.mp h3coeff).resolve_left (by norm_num)

end AlignedSquareRhoOneCubicMainTangentInvariants68

end Max11DegreeRoutes
