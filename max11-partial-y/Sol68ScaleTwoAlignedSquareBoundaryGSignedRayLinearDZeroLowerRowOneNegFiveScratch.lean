import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayLinearDZeroTerminalPlusOneB8TransportScratch

/-! # The unused lower-row-one face closes the signed `G[-2]` branch

The coefficient `-5` of lower row one is structural: on the retained order
box it contains no fresh positive jet.  After the old wall
`2 C[0] + 3 gamma = 0`, it is a nonzero multiple of `G[-2]^2`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayLinearDZeroLowerRowOneNegFive68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance alignedSquareBoundaryLowerRowOneNegFiveHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Exact leading derivative coefficient at a simple local root.  The
argument only uses the inclusive order bound `-2 ≤ ord f`; equality is
allowed. -/
theorem ratFuncAtHahn68_deriv_coeff_negThree_of_ge_negTwo
    (a : k) (h0 : k[X]) (f : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hscale :
      (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0)).orderTop =
        (↑(1 : ℚ) : WithTop ℚ))
    (hf : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 a f).orderTop) :
    (ratFuncAtHahn46 a (Differential.deriv f)).coeff (-3 : ℚ) =
      (-2 : k) * (ratFuncAtHahn46 a f).coeff (-2 : ℚ) := by
  let H : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let HH : HahnSeries ℚ k := ratFuncAtHahn46 a H
  let FH : HahnSeries ℚ k := ratFuncAtHahn46 a f
  let dHH : HahnSeries ℚ k := ratFuncAtHahn46 a (Differential.deriv H)
  let dFH : HahnSeries ℚ k := ratFuncAtHahn46 a (Differential.deriv f)
  obtain ⟨c, hc, hsingle, hderiv⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv h0 a hdegree hroot
  have hHH : HH.orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
    simpa only [HH, H] using hscale
  have hFH : (↑(-2 : ℚ) : WithTop ℚ) ≤ FH.orderTop := by
    simpa only [FH] using hf
  have hdFH : (↑(-3 : ℚ) : WithTop ℚ) ≤ dFH.orderTop := by
    simpa only [dFH] using
      ratFuncAtHahn68_deriv_orderTop_ge_negThree_of_ge_negTwo
        a h0 f hscale hf
  have hprod : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 a (H ^ 2 * f)).orderTop := by
    have hHsq : (↑(2 : ℚ) : WithTop ℚ) ≤ (HH * HH).orderTop := by
      rw [HahnSeries.orderTop_mul, hHH]
      norm_num
    have hm := hahnOrderTop_mul_lower46 (HH * HH) FH 2 (-2) hHsq hFH
    norm_num at hm
    simpa only [map_mul, map_pow, pow_two, HH, FH, H,
      HahnSeries.orderTop_mul] using hm
  have hdprod : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 a (Differential.deriv (H ^ 2 * f))).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg a (H ^ 2 * f) hprod
  have hdprodco :
      (ratFuncAtHahn46 a (Differential.deriv (H ^ 2 * f))).coeff
        (-1 : ℚ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hdprod)
  have hcross :
      ((HH * dHH + HH * dHH) * FH).coeff (-1 : ℚ) =
        (2 : k) * c ^ 2 * FH.coeff (-2 : ℚ) := by
    have hdHH : (0 : WithTop ℚ) ≤ dHH.orderTop := by
      rw [show dHH = HahnSeries.C c by simpa only [dHH, H] using hderiv]
      by_cases hc0 : c = 0
      · exact (hc hc0).elim
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hc0]
        simp
    have hlead := weightedMonomial68_coeff_at_general_lower_next
      (2 : k) HH dHH FH HH FH 1 1 1 0 0
      1 0 (-2) 1 (-2) hHH.ge hdHH hFH hHH.ge hFH
    norm_num at hlead
    have hre : (HH * dHH + HH * dHH) * FH =
        weightedMonomial68 (2 : k) HH dHH FH HH FH 1 1 1 0 0 := by
      simp only [weightedMonomial68, pow_one, pow_zero, mul_one, map_ofNat]
      ring
    rw [hre, hlead]
    rw [show HH = HahnSeries.single (1 : ℚ) c by
      simpa only [HH, H] using hsingle]
    rw [show dHH = HahnSeries.C c by simpa only [dHH, H] using hderiv]
    simp only [HahnSeries.coeff_single_same, HahnSeries.C_apply,
      HahnSeries.coeff_single_same]
    ring
  have hmain : ((HH * HH) * dFH).coeff (-1 : ℚ) =
      c ^ 2 * dFH.coeff (-3 : ℚ) := by
    have hlead := weightedMonomial68_coeff_at_general_lower_next
      (1 : k) HH HH dFH HH FH 1 1 1 0 0
      1 1 (-3) 1 (-2) hHH.ge hHH.ge hdFH hHH.ge hFH
    norm_num at hlead
    have hre : (HH * HH) * dFH =
        weightedMonomial68 (1 : k) HH HH dFH HH FH 1 1 1 0 0 := by
      simp only [weightedMonomial68, pow_one, pow_zero, mul_one, map_one,
        one_mul]
    rw [hre, hlead]
    rw [show HH = HahnSeries.single (1 : ℚ) c by
      simpa only [HH, H] using hsingle]
    simp only [HahnSeries.coeff_single_same]
    ring
  have hleibniz :
      ratFuncAtHahn46 a (Differential.deriv (H ^ 2 * f)) =
        (HH * dHH + HH * dHH) * FH + (HH * HH) * dFH := by
    dsimp only [HH, FH, dHH, dFH]
    simp only [pow_two, Derivation.leibniz, map_add, map_mul, smul_eq_mul]
    ring
  have hcoeff := congrArg
    (fun X : HahnSeries ℚ k => X.coeff (-1 : ℚ)) hleibniz
  rw [hdprodco, HahnSeries.coeff_add, hcross, hmain] at hcoeff
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hfac : c ^ 2 *
      (dFH.coeff (-3 : ℚ) + 2 * FH.coeff (-2 : ℚ)) = 0 := by
    linear_combination -hcoeff
  have hsum := (mul_eq_zero.mp hfac).resolve_left hc2
  have heq : dFH.coeff (-3 : ℚ) = (-2 : k) * FH.coeff (-2 : ℚ) := by
    linear_combination hsum
  simpa only [dFH, FH] using heq

/-- At order `-5`, lower row one contains exactly `A*C*dG`,
`gamma*A*dG`, and `G*dG`. -/
theorem lowerRowOneMainTangent_coeff_negFive_boundary68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (0 : WithTop ℚ) ≤ F.orderTop)
    (hG : (↑(-2 : ℚ) : WithTop ℚ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (↑(-3 : ℚ) : WithTop ℚ) ≤ dG.orderTop) :
    (lowerRowOneMainTangentWeightTenHahn68 A B C F G
        dA dB dC dF dG +
      lowerRowOneMainTangentLowerHahn68 0 gamma 0 epsilon 0
        A B C F G dA dB dC dF dG).coeff (-5 : ℚ) =
      (8 / 9 : k) * A.coeff (-2 : ℚ) * C.coeff 0 * dG.coeff (-3 : ℚ) +
      (4 / 3 : k) * gamma * A.coeff (-2 : ℚ) * dG.coeff (-3 : ℚ) +
      (8 / 3 : k) * G.coeff (-2 : ℚ) * dG.coeff (-3 : ℚ) := by
  have hz (s : k) (X1 X2 X3 X4 X5 : HahnSeries ℚ k)
      (n1 n2 n3 n4 n5 : ℕ) (r1 r2 r3 r4 r5 : ℚ)
      (h1 : (↑r1 : WithTop ℚ) ≤ X1.orderTop)
      (h2 : (↑r2 : WithTop ℚ) ≤ X2.orderTop)
      (h3 : (↑r3 : WithTop ℚ) ≤ X3.orderTop)
      (h4 : (↑r4 : WithTop ℚ) ≤ X4.orderTop)
      (h5 : (↑r5 : WithTop ℚ) ≤ X5.orderTop)
      (hlt : (-5 : ℚ) < (n1 : ℚ) * r1 + (n2 : ℚ) * r2 +
        (n3 : ℚ) * r3 + (n4 : ℚ) * r4 + (n5 : ℚ) * r5) :
      (weightedMonomial68 s X1 X2 X3 X4 X5
        n1 n2 n3 n4 n5).coeff (-5 : ℚ) = 0 :=
    weightedMonomial68_coeff_zero_of_general_lower s X1 X2 X3 X4 X5
      n1 n2 n3 n4 n5 r1 r2 r3 r4 r5 (-5)
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
  have h1 := hz (-8 / 27 : k) A B F dA G 1 1 1 1 0
    (-2) 2 0 (-3) (-2) hA hB hF hdA hG (by norm_num)
  have h2 := hz (-8 / 27 : k) A B dF C G 2 1 1 0 0
    (-2) 2 0 0 (-2) hA hB hdF hC hG (by norm_num)
  have h3 := hz (-8 / 27 : k) A F dB C G 2 1 1 0 0
    (-2) 0 0 0 (-2) hA hF hdB hC hG (by norm_num)
  have h4 := hz (-8 / 9 : k) C dC A B G 2 1 0 0 0
    0 0 (-2) 2 (-2) hC hdC hA hB hG (by norm_num)
  have h5 := hz (8 / 27 : k) B C dA A G 2 1 1 0 0
    2 0 (-3) (-2) (-2) hB hC hdA hA hG (by norm_num)
  have h6 := lead (8 / 9 : k) A C dG B G 1 1 1 0 0
    (-2) 0 (-3) 2 (-2) hA hC hdG hB hG
  have h7 := hz (8 / 9 : k) A G dC B F 1 1 1 0 0
    (-2) (-2) 0 2 0 hA hG hdC hB hF (by norm_num)
  have h8 := hz (2 * epsilon) dG A B C F 1 0 0 0 0
    (-3) (-2) 2 0 0 hdG hA hB hC hF (by norm_num)
  have h9 := hz (-(2 / 3 : k) * gamma) F dB A B C 1 1 0 0 0
    0 0 (-2) 2 0 hF hdB hA hB hC (by norm_num)
  have h10 := hz ((2 / 3 : k) * epsilon) A dC B C F 1 1 0 0 0
    (-2) 0 2 0 0 hA hdC hB hC hF (by norm_num)
  have h11 := hz ((2 / 3 : k) * gamma) B dF A C F 1 1 0 0 0
    2 0 (-2) 0 0 hB hdF hA hC hF (by norm_num)
  have h12 := hz (-(4 / 3 : k) * gamma) C dC A B F 1 1 0 0 0
    0 0 (-2) 2 0 hC hdC hA hB hF (by norm_num)
  have h13 := hz ((2 / 9 : k) * gamma) B dA A C F 2 1 0 0 0
    2 (-3) (-2) 0 0 hB hdA hA hC hF (by norm_num)
  have h14 := lead ((4 / 3 : k) * gamma) A dG B C F 1 1 0 0 0
    (-2) (-3) 2 0 0 hA hdG hB hC hF
  have h15 := hz (-4 / 3 : k) C F dB A B 1 1 1 0 0
    0 0 0 (-2) 2 hC hF hdB hA hB (by norm_num)
  have h16 := hz (-4 / 9 : k) B C dF A F 1 1 1 0 0
    2 0 0 (-2) 0 hB hC hdF hA hF (by norm_num)
  have h17 := hz (-4 / 9 : k) B F dC A C 1 1 1 0 0
    2 0 0 (-2) 0 hB hF hdC hA hC (by norm_num)
  have h18 := hz (-4 / 9 : k) F dA A B C 2 1 0 0 0
    0 (-3) (-2) 2 0 hF hdA hA hB hC (by norm_num)
  have h19 := hz (4 / 9 : k) B dG A C F 2 1 0 0 0
    2 (-3) (-2) 0 0 hB hdG hA hC hF (by norm_num)
  have h20 := lead (8 / 3 : k) G dG A B C 1 1 0 0 0
    (-2) (-3) (-2) 2 0 hG hdG hA hB hC
  norm_num at h6 h14 h20
  simp only [lowerRowOneMainTangentWeightTenHahn68,
    lowerRowOneMainTangentLowerHahn68, HahnSeries.coeff_add]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20]
  have hCzero : (HahnSeries.C (0 : k) : HahnSeries ℚ k) = 0 :=
    HahnSeries.C_zero
  simp only [weightedMonomial68, mul_zero, zero_mul, neg_zero, add_zero,
    hCzero, HahnSeries.coeff_zero]
  ring

/-- Opaque names keep the source-to-Hahn algebra transport factored. -/
def rhoOne_boundaryG_lowerA68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : RatFunc k :=
  T.source.A

def rhoOne_boundaryG_lowerB68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : RatFunc k :=
  T.source.B

def rhoOne_boundaryG_lowerC68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : RatFunc k :=
  T.source.C0 - RatFunc.C (1 / 3 : k) * rhoOne_boundaryG_lowerA68 T ^ 2

def rhoOne_boundaryG_lowerF68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : RatFunc k :=
  T.source.D - RatFunc.C (1 / 3 : k) *
    rhoOne_boundaryG_lowerA68 T * rhoOne_boundaryG_lowerB68 T

def rhoOne_boundaryG_lowerE68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : RatFunc k :=
  T.source.E - RatFunc.C (1 / 27 : k) * rhoOne_boundaryG_lowerA68 T ^ 3

def rhoOne_boundaryG_lowerG68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : RatFunc k :=
  rhoOne_boundaryG_lowerE68 T - RatFunc.C (1 / 3 : k) *
    rhoOne_boundaryG_lowerA68 T * rhoOne_boundaryG_lowerC68 T

set_option maxHeartbeats 800000 in
/-- The lower-row-one equation, transported from the original integrated
source to depressed main-tangent coordinates. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_lowerRowOne_mainTangent_source_zero68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    lowerRowOneMainTangentWeightTenHahn68
        (ratFuncAtHahn46 T.root (rhoOne_boundaryG_lowerA68 T))
        (ratFuncAtHahn46 T.root (rhoOne_boundaryG_lowerB68 T))
        (ratFuncAtHahn46 T.root (rhoOne_boundaryG_lowerC68 T))
        (ratFuncAtHahn46 T.root (rhoOne_boundaryG_lowerF68 T))
        (ratFuncAtHahn46 T.root (rhoOne_boundaryG_lowerG68 T))
        (ratFuncAtHahn46 T.root (Differential.deriv (rhoOne_boundaryG_lowerA68 T)))
        (ratFuncAtHahn46 T.root (Differential.deriv (rhoOne_boundaryG_lowerB68 T)))
        (ratFuncAtHahn46 T.root (Differential.deriv (rhoOne_boundaryG_lowerC68 T)))
        (ratFuncAtHahn46 T.root (Differential.deriv (rhoOne_boundaryG_lowerF68 T)))
        (ratFuncAtHahn46 T.root (Differential.deriv (rhoOne_boundaryG_lowerG68 T))) +
      lowerRowOneMainTangentLowerHahn68 0 T.source.gamma
        0 T.source.epsilon 0
        (ratFuncAtHahn46 T.root (rhoOne_boundaryG_lowerA68 T))
        (ratFuncAtHahn46 T.root (rhoOne_boundaryG_lowerB68 T))
        (ratFuncAtHahn46 T.root (rhoOne_boundaryG_lowerC68 T))
        (ratFuncAtHahn46 T.root (rhoOne_boundaryG_lowerF68 T))
        (ratFuncAtHahn46 T.root (rhoOne_boundaryG_lowerG68 T))
        (ratFuncAtHahn46 T.root (Differential.deriv (rhoOne_boundaryG_lowerA68 T)))
        (ratFuncAtHahn46 T.root (Differential.deriv (rhoOne_boundaryG_lowerB68 T)))
        (ratFuncAtHahn46 T.root (Differential.deriv (rhoOne_boundaryG_lowerC68 T)))
        (ratFuncAtHahn46 T.root (Differential.deriv (rhoOne_boundaryG_lowerF68 T)))
        (ratFuncAtHahn46 T.root (Differential.deriv (rhoOne_boundaryG_lowerG68 T))) = 0 := by
  let A : RatFunc k := rhoOne_boundaryG_lowerA68 T
  let B : RatFunc k := rhoOne_boundaryG_lowerB68 T
  let C : RatFunc k := rhoOne_boundaryG_lowerC68 T
  let F : RatFunc k := rhoOne_boundaryG_lowerF68 T
  let E : RatFunc k := rhoOne_boundaryG_lowerE68 T
  let G : RatFunc k := rhoOne_boundaryG_lowerG68 T
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (Polynomial.C x)
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C 0) T.source.A T.source.B
      T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.zeta) (RatFunc.C T.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst 0) (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta)
      (hconst T.source.eta) T.source.bracket_eq
  have hrowR := hlow.2.2.2.1
  have hdecR := lowerRowOneMainTangent_decomposition68 (k := k)
    ratFuncDerivation68 A B C F G
      (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.delta)
      (RatFunc.C T.source.epsilon) (RatFunc.C T.source.zeta)
      (RatFunc.C T.source.eta)
      (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta)
      (hconst T.source.eta)
  dsimp only at hdecR
  have hCrec : A ^ 2 / 3 + C = T.source.C0 := by
    dsimp only [C, A, rhoOne_boundaryG_lowerC68,
      rhoOne_boundaryG_lowerA68]
    simp only [div_eq_mul_inv]
    rw [show (3 : RatFunc k) = RatFunc.C (3 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 3).symm]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]
    norm_num
    ring
  have hDrec : A * B / 3 + F = T.source.D := by
    dsimp only [F, A, B, rhoOne_boundaryG_lowerF68,
      rhoOne_boundaryG_lowerA68, rhoOne_boundaryG_lowerB68]
    simp only [div_eq_mul_inv]
    rw [show (3 : RatFunc k) = RatFunc.C (3 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 3).symm]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]
    norm_num
    ring
  have hErec : A ^ 3 / 27 + A * C / 3 + G = T.source.E := by
    dsimp only [G, E, C, A, rhoOne_boundaryG_lowerG68,
      rhoOne_boundaryG_lowerE68, rhoOne_boundaryG_lowerC68,
      rhoOne_boundaryG_lowerA68]
    simp only [div_eq_mul_inv]
    rw [show (3 : RatFunc k) = RatFunc.C (3 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 3).symm]
    rw [show (27 : RatFunc k) = RatFunc.C (27 : k) by
      simpa using (map_ofNat (RatFunc.C : k →+* RatFunc k) 27).symm]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]
    rw [← map_inv₀ (RatFunc.C : k →+* RatFunc k)]
    norm_num
    ring
  rw [hCrec, hDrec, hErec] at hdecR
  simp only [ratFuncDerivation46_apply] at hdecR
  have hmainR :
      lowerRowOneMainTangentWeightTenAlg68 A B C F G
          (Differential.deriv A) (Differential.deriv B)
          (Differential.deriv C) (Differential.deriv F)
          (Differential.deriv G) +
        lowerRowOneMainTangentLowerAlg68
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
          (RatFunc.C T.source.zeta) A B C F G
          (Differential.deriv A) (Differential.deriv B)
          (Differential.deriv C) (Differential.deriv F)
          (Differential.deriv G) = 0 := by
    rw [← hdecR]
    have hCzeroR : RatFunc.C (0 : k) = 0 := map_zero (RatFunc.C : k →+* RatFunc k)
    rw [hCzeroR] at hrowR
    simp only [ratFuncDerivation46_apply] at hrowR
    simpa only [A, B, rhoOne_boundaryG_lowerA68,
      rhoOne_boundaryG_lowerB68] using hrowR
  rw [hbeta, hdelta, hzeta] at hmainR
  have hmainH := congrArg (ratFuncAtHahn46 T.root) hmainR
  simp only [map_add, map_zero] at hmainH
  rw [← hmainH]
  simp only [lowerRowOneMainTangentWeightTenAlg68,
    lowerRowOneMainTangentLowerAlg68,
    lowerRowOneMainTangentWeightTenHahn68,
    lowerRowOneMainTangentLowerHahn68, weightedMonomial68,
    map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_ofNat,
    map_zero, map_one, ratFuncAtHahn46_C]
  ring

/-- The unused structural row contradicts the nonzero `G[-2]` selector;
it closes both old affine cells at once. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_lowerRowOne_impossible68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (R : RhoOneAlignedSquareGNegTwoSignedRayLinearDZeroTerminalPlusOneB8Transport68 T) :
    False := by
  have Qc := Q
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68] at Qc
  rcases Qc with ⟨Rm, hquadratic⟩
  have Rmc := Rm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68] at Rmc
  rcases Rmc with ⟨Rtf, hminor⟩
  have Rtfc := Rtf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rtfc
  rcases Rtfc with ⟨Rt, i3two, i4three, hi3twoSrc, hi4threeSrc, hdet⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hcross⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨Rbase, hi3zero, htermFour⟩
  have Rbasec := Rbase
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at Rbasec
  rcases Rbasec with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hfneg, hgneg, hb1, hS0, hscalar, hi4base⟩
  let A : RatFunc k := rhoOne_boundaryG_lowerA68 T
  let B : RatFunc k := rhoOne_boundaryG_lowerB68 T
  let C : RatFunc k := rhoOne_boundaryG_lowerC68 T
  let F : RatFunc k := rhoOne_boundaryG_lowerF68 T
  let E : RatFunc k := rhoOne_boundaryG_lowerE68 T
  let G : RatFunc k := rhoOne_boundaryG_lowerG68 T
  have hCmap : ratFuncAtHahn46 T.root C =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, A, rhoOne_boundaryG_lowerC68,
      rhoOne_boundaryG_lowerA68, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : ratFuncAtHahn46 T.root F =
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, A, B, rhoOne_boundaryG_lowerF68,
      rhoOne_boundaryG_lowerA68, rhoOne_boundaryG_lowerB68,
      rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hEmap : ratFuncAtHahn46 T.root E =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [E, A, rhoOne_boundaryG_lowerE68,
      rhoOne_boundaryG_lowerA68, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGmap : ratFuncAtHahn46 T.root G =
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOne_boundaryG_lowerG68,
      rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, map_mul, ratFuncAtHahn46_C, hCmap]
    simp only [rhoOne_boundaryG_lowerA68, A]
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root A).orderTop := by
    simpa only [A, rhoOne_boundaryG_lowerA68] using P.2.1.1
  have hBH : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root B).orderTop := by
    simpa only [B, rhoOne_boundaryG_lowerB68] using hB
  have hCH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root C).orderTop := by
    rw [hCmap]
    exact hC
  have hFH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root F).orderTop := by
    rw [hFmap]
    exact hF
  have hGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by
    rw [hGmap]
    exact hG
  have hdAH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv A)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negThree_of_ge_negTwo
      T.root h0 A T.scale_order hAH
  have hdBH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv B)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root B
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBH)
  have hdCH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv C)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root C hCH
  have hdFH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv F)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root F hFH
  have hdGH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv G)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negThree_of_ge_negTwo
      T.root h0 G T.scale_order hGH
  have hrow := T.rhoOne_lowerRowOne_mainTangent_source_zero68
    hbeta hdelta hzeta
  have hface := lowerRowOneMainTangent_coeff_negFive_boundary68
    T.source.gamma T.source.epsilon
    (ratFuncAtHahn46 T.root A) (ratFuncAtHahn46 T.root B)
    (ratFuncAtHahn46 T.root C) (ratFuncAtHahn46 T.root F)
    (ratFuncAtHahn46 T.root G)
    (ratFuncAtHahn46 T.root (Differential.deriv A))
    (ratFuncAtHahn46 T.root (Differential.deriv B))
    (ratFuncAtHahn46 T.root (Differential.deriv C))
    (ratFuncAtHahn46 T.root (Differential.deriv F))
    (ratFuncAtHahn46 T.root (Differential.deriv G))
    hAH hBH hCH hFH hGH hdAH hdBH hdCH hdFH hdGH
  have hcoeff := congrArg
    (fun X : HahnSeries ℚ k => X.coeff (-5 : ℚ)) hrow
  rw [hface, HahnSeries.coeff_zero] at hcoeff
  have hdGco := ratFuncAtHahn68_deriv_coeff_negThree_of_ge_negTwo
    T.root h0 G T.scale_degree T.root_eq T.scale_order hGH
  have hS0' :
      2 * (ratFuncAtHahn46 T.root C).coeff 0 + 3 * T.source.gamma = 0 := by
    rw [hCmap]
    exact hS0
  have hTransport := R.1.1.1.1.1.1
  rcases hTransport.2 with ⟨sigmaCell, rCell, sigma, r, hrCell0, hrCell,
    hsigma, hr0, hb, hgm2, hray, hcells⟩
  have hgm2' : (ratFuncAtHahn46 T.root G).coeff (-2 : ℚ) ≠ 0 := by
    rw [hGmap]
    exact hgm2
  have hAC :
      (8 / 9 : k) * (ratFuncAtHahn46 T.root A).coeff (-2 : ℚ) *
          (ratFuncAtHahn46 T.root C).coeff 0 *
          (ratFuncAtHahn46 T.root (Differential.deriv G)).coeff (-3 : ℚ) +
        (4 / 3 : k) * T.source.gamma *
          (ratFuncAtHahn46 T.root A).coeff (-2 : ℚ) *
          (ratFuncAtHahn46 T.root (Differential.deriv G)).coeff (-3 : ℚ) = 0 := by
    linear_combination
      (4 / 9 : k) * (ratFuncAtHahn46 T.root A).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 T.root (Differential.deriv G)).coeff (-3 : ℚ) * hS0'
  have hprod :
      (ratFuncAtHahn46 T.root G).coeff (-2 : ℚ) *
        (ratFuncAtHahn46 T.root (Differential.deriv G)).coeff (-3 : ℚ) = 0 := by
    linear_combination (3 / 8 : k) * (hcoeff - hAC)
  rw [hdGco] at hprod
  have hsq : (ratFuncAtHahn46 T.root G).coeff (-2 : ℚ) ^ 2 = 0 := by
    linear_combination (-1 / 2 : k) * hprod
  exact (pow_ne_zero 2 hgm2') hsq

end AlignedSquareBoundaryGSignedRayLinearDZeroLowerRowOneNegFive68

end Max11DegreeRoutes
