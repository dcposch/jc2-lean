import LowScale68ScaleTwoAfterRhoOneNextBox

/-! # The next exact branch row after the `(1,1,2,2,2)` box

The coefficient at exponent `-4` of the fourth exact first integral is
already determined by the five initial coordinates.  On the two surviving
pole-five branches it becomes a linear equation: the `3x=a²` branch fixes
the initial `B`, while the `9x=2a²` branch fixes the initial `D`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AfterRhoOneBranchRows68

variable {k : Type*} [Field k] [CharZero k]

local instance afterRhoOneBranchRowsHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

def afterRhoOneNextFourFace68 (L a b x d : k) : k :=
  (-8 / 9 : k) * a ^ 2 * d + (8 / 3 : k) * x * d +
    (40 / 81 : k) * a ^ 3 * b - (16 / 9 : k) * a * b * x +
    (7 / 12 : k) * x ^ 2 * L + (385 / 5184 : k) * a ^ 4 * L -
    (35 / 72 : k) * a ^ 2 * x * L

theorem firstIntegralFour68_coeff_neg4_afterRhoOneNext
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-1 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-2 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-2 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-2 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralFour68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-4 : ℚ) =
      afterRhoOneNextFourFace68 L (A.coeff (-1 : ℚ))
        (B.coeff (-1 : ℚ)) (C0.coeff (-2 : ℚ))
        (D.coeff (-2 : ℚ)) := by
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hlt : (-4 : ℚ) < (aA : ℚ) * (-1) + (aB : ℚ) * (-1) +
        (aC : ℚ) * (-2) + (aD : ℚ) * (-2) + (aE : ℚ) * (-2)) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-4 : ℚ) = 0 := by
    exact weightedMonomial68_coeff_zero_of_general_lower c A B C0 D E
      aA aB aC aD aE (-1) (-1) (-2) (-2) (-2) (-4)
      hA hB hC hD hE hlt
  have hlead (c : k) (aA aB aC aD aE : ℕ)
      (hw : (aA : ℚ) * (-1) + (aB : ℚ) * (-1) +
          (aC : ℚ) * (-2) + (aD : ℚ) * (-2) + (aE : ℚ) * (-2) = -4) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff (-4 : ℚ) =
        c * (A.coeff (-1 : ℚ)) ^ aA * (B.coeff (-1 : ℚ)) ^ aB *
          (C0.coeff (-2 : ℚ)) ^ aC * (D.coeff (-2 : ℚ)) ^ aD *
          (E.coeff (-2 : ℚ)) ^ aE := by
    rw [← hw]
    exact weightedMonomial68_coeff_at_general_lower_next c A B C0 D E
      aA aB aC aD aE (-1) (-1) (-2) (-2) (-2) hA hB hC hD hE
  have ht1 := hzero (-8 / 27 : k) 0 3 0 0 0 (by norm_num)
  have ht2 := hlead (-8 / 9 : k) 2 0 0 1 0 (by norm_num)
  have ht3 := hzero (8 / 3 : k) 0 1 0 0 1 (by norm_num)
  have ht4 := hlead (8 / 3 : k) 0 0 1 1 0 (by norm_num)
  have ht5 := hlead (40 / 81 : k) 3 1 0 0 0 (by norm_num)
  have ht6 := hlead (-16 / 9 : k) 1 1 1 0 0 (by norm_num)
  have hh1 := hzero zeta 1 0 0 0 0 (by norm_num)
  have hh2 := hzero (2 * epsilon) 0 1 0 0 0 (by norm_num)
  have hh3 := hzero (3 * delta) 0 0 1 0 0 (by norm_num)
  have hh4 := hzero (4 * gamma) 0 0 0 1 0 (by norm_num)
  have hh5 := hzero (5 * beta) 0 0 0 0 1 (by norm_num)
  have hh6 := hzero (-(5 / 12 : k) * beta) 0 2 0 0 0 (by norm_num)
  have hh7 := hzero (-(3 / 4 : k) * delta) 2 0 0 0 0 (by norm_num)
  have hh8 := hlead ((7 / 12 : k) * L) 0 0 2 0 0 (by norm_num)
  have hh9 := hzero ((35 / 216 : k) * beta) 3 0 0 0 0 (by norm_num)
  have hh10 := hlead ((385 / 5184 : k) * L) 4 0 0 0 0 (by norm_num)
  have hh11 := hzero (-(35 / 72 : k) * L) 1 2 0 0 0 (by norm_num)
  have hh12 := hlead (-(35 / 72 : k) * L) 2 0 1 0 0 (by norm_num)
  have hh13 := hzero (-(5 / 6 : k) * beta) 1 0 1 0 0 (by norm_num)
  have hh14 := hzero (-(4 / 3 : k) * gamma) 1 1 0 0 0 (by norm_num)
  have hh15 := hzero ((7 / 6 : k) * L) 1 0 0 0 1 (by norm_num)
  have hh16 := hzero ((7 / 6 : k) * L) 0 1 0 1 0 (by norm_num)
  rw [firstIntegralFour68_eq_localFaces]
  simp only [firstIntegralFourTopFaceHahn68,
    firstIntegralFourHigherHahn68, HahnSeries.coeff_add]
  rw [ht1, ht2, ht3, ht4, ht5, ht6, hh1, hh2, hh3, hh4, hh5, hh6,
    hh7, hh8, hh9, hh10, hh11, hh12, hh13, hh14, hh15, hh16]
  simp only [afterRhoOneNextFourFace68]
  norm_num
  ring

theorem SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_fourFace
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    let a := (ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ)
    let b := (ratFuncAtHahn46 T.root T.source.B).coeff (-1 : ℚ)
    let x := (ratFuncAtHahn46 T.root T.source.C0).coeff (-2 : ℚ)
    let d := (ratFuncAtHahn46 T.root T.source.D).coeff (-2 : ℚ)
    afterRhoOneNextFourFace68 l a b x d = 0 := by
  dsimp only
  let AH := ratFuncAtHahn46 T.root T.source.A
  let BH := ratFuncAtHahn46 T.root T.source.B
  let CH := ratFuncAtHahn46 T.root T.source.C0
  let DH := ratFuncAtHahn46 T.root T.source.D
  let EH := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBoundsAfterRhoOneNext hp hH hp6 hp5 hp4 hp3
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      l T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi4H := congrArg (ratFuncAtHahn46 T.root) hi4
  have hi4H' :
      firstIntegralFour68 (HahnSeries.C l) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i4 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi4H
  have hcoeff := congrArg
    (fun z : HahnSeries ℚ k => z.coeff (-4 : ℚ)) hi4H'
  have hconst : (HahnSeries.C i4 : HahnSeries ℚ k).coeff (-4 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralFour68_coeff_neg4_afterRhoOneNext
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH
      (by simpa only [AH] using hA) (by simpa only [BH] using hB)
      (by simpa only [CH] using hC) (by simpa only [DH] using hD)
      (by simpa only [EH] using hE)
  rw [hface] at hcoeff
  exact hcoeff

theorem afterRhoOneNextFourFace_firstBranch
    (L a b x d : k) (ha : a ≠ 0) (hx : 3 * x - a ^ 2 = 0)
    (hface : afterRhoOneNextFourFace68 L a b x d = 0) :
    512 * b + 119 * L * a = 0 := by
  have hx' : x = a ^ 2 / 3 := by linear_combination (1 / 3 : k) * hx
  rw [hx'] at hface
  have hfac : a ^ 3 *
      ((-8 / 81 : k) * b - (119 / 5184 : k) * L * a) = 0 := by
    rw [afterRhoOneNextFourFace68] at hface
    linear_combination hface
  have hinner := (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 3 ha)
  linear_combination (-5184 : k) * hinner

theorem afterRhoOneNextFourFace_secondBranch
    (L a b x d : k) (ha : a ≠ 0) (hx : 9 * x - 2 * a ^ 2 = 0)
    (hface : afterRhoOneNextFourFace68 L a b x d = 0) :
    4608 * d - 1536 * a * b + 77 * L * a ^ 2 = 0 := by
  have hx' : x = 2 * a ^ 2 / 9 := by linear_combination (1 / 9 : k) * hx
  rw [hx'] at hface
  have hfac : a ^ 2 *
      ((-8 / 27 : k) * d + (8 / 81 : k) * a * b -
        (77 / 15552 : k) * L * a ^ 2) = 0 := by
    rw [afterRhoOneNextFourFace68] at hface
    linear_combination hface
  have hinner := (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 ha)
  linear_combination (-15552 : k) * hinner

def AfterRhoOneBranchRowsResidual68
    {p q : k[X][X]} {j l : k} {h0 : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (g u v : k[X]) : Prop :=
  ∃ c : k, c ≠ 0 ∧
    let a := c⁻¹ * u.eval T.root
    let b := c⁻¹ *
      (v.eval T.root - (2 / 3 : k) * u.eval T.root * g.eval T.root)
    let x := (c ^ 2)⁻¹ * (p.coeff 2).eval T.root
    let d := (c ^ 2)⁻¹ *
      (-(1 / 3 : k) * (p.coeff 2).eval T.root * g.eval T.root)
    a ≠ 0 ∧
      ((3 * x - a ^ 2 = 0 ∧ 512 * b + 119 * l * a = 0) ∨
       (9 * x - 2 * a ^ 2 = 0 ∧
        4608 * d - 1536 * a * b + 77 * l * a ^ 2 = 0))

theorem SquareConstantLIntegratedLocalRootData68.afterRhoOneBranchRows_split
    {p q : k[X][X]} {j l : k} {h0 H g u v : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 5 * g)
    (hp4 : p.coeff 4 = h0 ^ 3 * u) (hp3 : p.coeff 3 = h0 ^ 2 * v) :
    h0 ^ 4 ∣ p.coeff 4 ∨ AfterRhoOneBranchRowsResidual68 T g u v := by
  have hthree := T.afterRhoOneNext_face hp hH hp6 hp5 hp4 hp3
  have hfour := T.afterRhoOneNext_fourFace hp hH hp6 hp5 hp4 hp3
  obtain ⟨c, hc, hAco, hBco, hCco, hDco, hEco⟩ :=
    T.coordinateInitialPacketAfterRhoOneNext hp hH hp6 hp5 hp4 hp3
  let a : k := c⁻¹ * u.eval T.root
  let b : k := c⁻¹ *
    (v.eval T.root - (2 / 3 : k) * u.eval T.root * g.eval T.root)
  let x : k := (c ^ 2)⁻¹ * (p.coeff 2).eval T.root
  let d : k := (c ^ 2)⁻¹ *
    (-(1 / 3 : k) * (p.coeff 2).eval T.root * g.eval T.root)
  dsimp only at hthree hfour
  rw [hAco, hCco] at hthree
  rw [hAco, hBco, hCco, hDco] at hfour
  change a * (3 * x - a ^ 2) * (9 * x - 2 * a ^ 2) = 0 at hthree
  change afterRhoOneNextFourFace68 l a b x d = 0 at hfour
  by_cases ha : a = 0
  · left
    have ha' : c⁻¹ * u.eval T.root = 0 := by simpa only [a] using ha
    have huroot : u.eval T.root = 0 :=
      (mul_eq_zero.mp ha').resolve_left (inv_ne_zero hc)
    obtain ⟨w, huw⟩ := linearPolynomial_dvd_of_eval_eq_zero
      h0 u T.root T.scale_degree T.root_eq huroot
    refine ⟨w, ?_⟩
    rw [hp4, huw]
    ring
  · right
    have hprod : (3 * x - a ^ 2) * (9 * x - 2 * a ^ 2) = 0 := by
      have hthree' : a * ((3 * x - a ^ 2) * (9 * x - 2 * a ^ 2)) = 0 := by
        simpa only [mul_assoc] using hthree
      exact (mul_eq_zero.mp hthree').resolve_left ha
    refine ⟨c, hc, ?_⟩
    change a ≠ 0 ∧
      ((3 * x - a ^ 2 = 0 ∧ 512 * b + 119 * l * a = 0) ∨
       (9 * x - 2 * a ^ 2 = 0 ∧
        4608 * d - 1536 * a * b + 77 * l * a ^ 2 = 0))
    refine ⟨ha, ?_⟩
    rcases mul_eq_zero.mp hprod with hx | hx
    · exact Or.inl ⟨hx,
        afterRhoOneNextFourFace_firstBranch l a b x d ha hx hfour⟩
    · exact Or.inr ⟨hx,
        afterRhoOneNextFourFace_secondBranch l a b x d ha hx hfour⟩

/-- Original-data wrapper for the narrowed two-branch packet. -/
theorem SquareConstantLIntegratedLocalRootData68.afterRhoOneBranchRows_globalSplit
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    h0 ^ 4 ∣ p.coeff 4 ∨ ∃ g u v : k[X],
      p.coeff 5 = h0 ^ 5 * g ∧ p.coeff 4 = h0 ^ 3 * u ∧
      p.coeff 3 = h0 ^ 2 * v ∧ AfterRhoOneBranchRowsResidual68 T g u v := by
  rcases T.afterRhoOne_next_divisibilities hp hH hp6 with
    ⟨⟨g, hp5⟩, ⟨u, hp4⟩, ⟨v, hp3⟩⟩
  rcases T.afterRhoOneBranchRows_split hp hH hp6 hp5 hp4 hp3 with hdiv | hres
  · exact Or.inl hdiv
  · exact Or.inr ⟨g, u, v, hp5, hp4, hp3, hres⟩

end AfterRhoOneBranchRows68

#print axioms firstIntegralFour68_coeff_neg4_afterRhoOneNext
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOneNext_fourFace
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOneBranchRows_split
#print axioms SquareConstantLIntegratedLocalRootData68.afterRhoOneBranchRows_globalSplit

end Max11DegreeRoutes
