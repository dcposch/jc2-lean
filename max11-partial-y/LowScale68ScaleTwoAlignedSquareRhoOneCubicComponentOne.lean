import LowScale68ScaleTwoAlignedSquareRhoOneCubicRemainder

/-! # The first refined zero-septic cubic component -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicComponentOne68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareRhoOneCubicComponentOneHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The first potentially informative cubic-defect face of lower row one. -/
def rhoOneZeroLCubicNextOne68 (a b c d e : k) : k :=
  -135 * e ^ 2 - 7 * a ^ 3 * b ^ 2 + 9 * a ^ 2 * c ^ 2 +
    18 * a ^ 2 * b * d + 18 * a * c * e + 9 * a * d ^ 2

/-- Exact improved-weight-eleven portion of lower row one. -/
def lowerRowOneCubicWeightElevenHahn68
    (A B C D E dA dB dC dD dE : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 (8 / 3 : k) E dE A B C 1 1 0 0 0 +
  weightedMonomial68 (4 / 27 : k) A B dA C D 2 2 1 0 0 +
  weightedMonomial68 (-8 / 27 : k) A C dC B D 2 1 1 0 0 +
  weightedMonomial68 (-8 / 27 : k) A D dB B C 2 1 1 0 0 +
  weightedMonomial68 (-8 / 27 : k) A B dD C D 2 1 1 0 0 +
  weightedMonomial68 (16 / 81 : k) A B dB C D 3 1 1 0 0 +
  weightedMonomial68 (-8 / 9 : k) C E dA B D 1 1 1 0 0 +
  weightedMonomial68 (-4 / 9 : k) D dA A B C 2 1 0 0 0

theorem lowerRowOneCubicWeightElevenHahn68_coeff_neg11
    (A B C D E dA dB dC dD dE : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-2 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-3 : ℚ) : WithTop ℚ) ≤ C.orderTop)
    (hD : (↑(-4 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-5 : ℚ) : WithTop ℚ) ≤ E.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (↑(-3 : ℚ) : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (↑(-4 : ℚ) : WithTop ℚ) ≤ dC.orderTop)
    (hdD : (↑(-5 : ℚ) : WithTop ℚ) ≤ dD.orderTop)
    (hdE : (↑(-6 : ℚ) : WithTop ℚ) ≤ dE.orderTop)
    (hdAco : dA.coeff (-3 : ℚ) = (-2 : k) * A.coeff (-2 : ℚ))
    (hdBco : dB.coeff (-3 : ℚ) = (-2 : k) * B.coeff (-2 : ℚ))
    (hdCco : dC.coeff (-4 : ℚ) = (-3 : k) * C.coeff (-3 : ℚ))
    (hdDco : dD.coeff (-5 : ℚ) = (-4 : k) * D.coeff (-4 : ℚ))
    (hdEco : dE.coeff (-6 : ℚ) = (-5 : k) * E.coeff (-5 : ℚ)) :
    (lowerRowOneCubicWeightElevenHahn68 A B C D E dA dB dC dD dE).coeff
        (-11 : ℚ) =
      (8 / 81 : k) * rhoOneZeroLCubicNextOne68
        (A.coeff (-2 : ℚ)) (B.coeff (-2 : ℚ))
        (C.coeff (-3 : ℚ)) (D.coeff (-4 : ℚ))
        (E.coeff (-5 : ℚ)) := by
  have h1 := weightedMonomial68_coeff_at_general_lower_next
    (8 / 3 : k) E dE A B C 1 1 0 0 0
      (-5) (-6) (-2) (-2) (-3) hE hdE hA hB hC
  have h2 := weightedMonomial68_coeff_at_general_lower_next
    (4 / 27 : k) A B dA C D 2 2 1 0 0
      (-2) (-2) (-3) (-3) (-4) hA hB hdA hC hD
  have h3 := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 27 : k) A C dC B D 2 1 1 0 0
      (-2) (-3) (-4) (-2) (-4) hA hC hdC hB hD
  have h4 := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 27 : k) A D dB B C 2 1 1 0 0
      (-2) (-4) (-3) (-2) (-3) hA hD hdB hB hC
  have h5 := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 27 : k) A B dD C D 2 1 1 0 0
      (-2) (-2) (-5) (-3) (-4) hA hB hdD hC hD
  have h6 := weightedMonomial68_coeff_at_general_lower_next
    (16 / 81 : k) A B dB C D 3 1 1 0 0
      (-2) (-2) (-3) (-3) (-4) hA hB hdB hC hD
  have h7 := weightedMonomial68_coeff_at_general_lower_next
    (-8 / 9 : k) C E dA B D 1 1 1 0 0
      (-3) (-5) (-3) (-2) (-4) hC hE hdA hB hD
  have h8 := weightedMonomial68_coeff_at_general_lower_next
    (-4 / 9 : k) D dA A B C 2 1 0 0 0
      (-4) (-3) (-2) (-2) (-3) hD hdA hA hB hC
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8
  simp only [lowerRowOneCubicWeightElevenHahn68, HahnSeries.coeff_add]
  norm_num only
  rw [h1, h2, h3, h4, h5, h6, h7, h8, hdAco, hdBco, hdCco, hdDco,
    hdEco]
  simp only [rhoOneZeroLCubicNextOne68]
  ring

/-- I3 already sharpens component one: away from the main tangent family,
both `b` and the cubic `C`-defect vanish. -/
theorem rhoOneZeroLCubic_firstComponent_I3_split68
    (a b c d e : k)
    (h3 : rhoOneZeroLCubicNextThree68 a b c d e = 0)
    (hd : a * b = 3 * d)
    (hfirst : b = 0 ∨ 3 * e = a * c) :
    (a * b = 3 * d ∧ 3 * e = a * c) ∨
      (b = 0 ∧ c = 0 ∧ d = 0) := by
  rcases hfirst with hb | he
  · have hd0 : d = 0 := by rw [hb] at hd; norm_num at hd; exact hd
    have hcprod : c * (3 * e - a * c) = 0 := by
      simp only [rhoOneZeroLCubicNextThree68] at h3
      rw [hb, hd0] at h3
      linear_combination (9 / 8 : k) * h3
    rcases mul_eq_zero.mp hcprod with hc | he'
    · exact Or.inr ⟨hb, hc, hd0⟩
    · left
      refine ⟨hd, ?_⟩
      linear_combination he'
  · exact Or.inl ⟨hd, he⟩

/-- On the exceptional I3 locus, the new row-one face is exactly
`-135 e²`; hence its vanishing kills the final defect. -/
theorem rhoOneZeroLCubic_firstComponent_exceptional_rowOne68
    (a b c d e : k)
    (hb : b = 0) (hc : c = 0) (hd : d = 0)
    (h1 : rhoOneZeroLCubicNextOne68 a b c d e = 0) : e = 0 := by
  rw [hb, hc, hd, rhoOneZeroLCubicNextOne68] at h1
  have he2 : e ^ 2 = 0 := by linear_combination (-1 / 135 : k) * h1
  exact eq_zero_of_pow_eq_zero he2

/-- The main tangent component itself makes the row-one face vanish
identically; a still lower coefficient is genuinely required there. -/
theorem rhoOneZeroLCubic_firstComponent_main_rowOne_tautology68
    (a b c d e : k) (hd : a * b = 3 * d) (he : 3 * e = a * c) :
    rhoOneZeroLCubicNextOne68 a b c d e = 0 := by
  have hd' : d = a * b / 3 := by linear_combination (-1 / 3 : k) * hd
  have he' : e = a * c / 3 := by linear_combination (1 / 3 : k) * he
  rw [hd', he', rhoOneZeroLCubicNextOne68]
  ring

/-- Source-valid lower row one has zero coefficient at exponent `-11`. -/
theorem SquareZeroLIntegratedLocalRootData68.lowerRowOne_actual_coeff_neg11_zero
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T0 : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    let C0 := ratFuncAtHahn46 T0.root T0.source.C0
    let D := ratFuncAtHahn46 T0.root T0.source.D
    let TT := ratFuncAtHahn46 T0.root
      (integratedT68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.epsilon))
    let U := ratFuncAtHahn46 T0.root
      (integratedU68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.zeta))
    let V := ratFuncAtHahn46 T0.root
      (integratedV68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
        (RatFunc.C T0.source.eta))
    let dD := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.D)
    let dE := ratFuncAtHahn46 T0.root (Differential.deriv T0.source.E)
    let dU := ratFuncAtHahn46 T0.root (Differential.deriv
      (integratedU68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.zeta)))
    let dV := ratFuncAtHahn46 T0.root (Differential.deriv
      (integratedV68 (RatFunc.C 0) T0.source.A T0.source.B T0.source.C0
        T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
        (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
        (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
        (RatFunc.C T0.source.eta)))
    (U * dD + 2 * TT * dE - 2 * C0 * dV - D * dU).coeff (-11 : ℚ) = 0 := by
  dsimp only
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (C x : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C 0) T0.source.A T0.source.B
      T0.source.C0 T0.source.D T0.source.E (RatFunc.C T0.source.alpha)
      (RatFunc.C T0.source.beta) (RatFunc.C T0.source.gamma)
      (RatFunc.C T0.source.delta) (RatFunc.C T0.source.epsilon)
      (RatFunc.C T0.source.zeta) (RatFunc.C T0.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst 0) (hconst T0.source.alpha) (hconst T0.source.beta)
      (hconst T0.source.gamma) (hconst T0.source.delta)
      (hconst T0.source.epsilon) (hconst T0.source.zeta)
      (hconst T0.source.eta) T0.source.bracket_eq
  have hrowH := congrArg (ratFuncAtHahn46 T0.root) hlow.2.2.2.1
  have hcoeff := congrArg (fun x : HahnSeries ℚ k => x.coeff (-11 : ℚ)) hrowH
  simpa only [ratFuncDerivation46_apply, map_add, map_sub, map_mul,
    map_ofNat, map_zero, HahnSeries.coeff_zero] using hcoeff

/-- Source component one sharpened by its already-available I3 equation. -/
def RhoOneZeroLCubicFirstI3RefinedComponent68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let a := A.coeff (-2 : ℚ)
  let b := B.coeff (-2 : ℚ)
  let c := (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ)
  let d := D.coeff (-4 : ℚ)
  let e := (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)
  RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    ((a * b = 3 * d ∧ 3 * e = a * c) ∨
      (b = 0 ∧ c = 0 ∧ d = 0))

theorem RhoOneZeroLCubicFirstNextComponent68.refine_with_I3
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    {T : SquareZeroLIntegratedLocalRootData68 p q j h0}
    {g u : k[X]} (P : RhoOneZeroLCubicFirstNextComponent68 T g u) :
    RhoOneZeroLCubicFirstI3RefinedComponent68 T g u := by
  dsimp only [RhoOneZeroLCubicFirstNextComponent68,
    RhoOneZeroLCubicFirstI3RefinedComponent68] at P ⊢
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let a := A.coeff (-2 : ℚ)
  let b := B.coeff (-2 : ℚ)
  let c := (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ)
  let d := D.coeff (-4 : ℚ)
  let e := (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)
  rcases P with ⟨P0, hd⟩
  have h3 : rhoOneZeroLCubicNextThree68 a b c d e = 0 := by
    simpa only [A, B, C0, D, E, a, b, c, d, e] using P0.2.2.2.2.2.1
  have h4 : rhoOneZeroLCubicNextFour68 a b c d e = 0 := by
    simpa only [A, B, C0, D, E, a, b, c, d, e] using P0.2.2.2.2.1
  have hfirst := rhoOneZeroLCubic_firstComponent_split68 a b c d e h4 hd
  exact ⟨P0, rhoOneZeroLCubic_firstComponent_I3_split68
    a b c d e h3 hd hfirst⟩

end AlignedSquareRhoOneCubicComponentOne68

end Max11DegreeRoutes
