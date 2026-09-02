import Sol68ScaleTwoAlignedSquareTerminalGBoundaryCapT16SplitBackwireScratch

/-! # Source valuation behind the corrected-cap order dichotomy -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGBoundaryCapKSourceOrder68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareCapKSourceOrderHahnCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

/-- The polynomial numerator of the corrected cap defect after the common
`h^8` denominator is cleared. -/
def rhoOneCapCorrectedClearedNumerator68
    (h A0 B0 C00 D0 : k[X]) (gamma : k) : k[X] :=
  let C0 := C00 - C (1 / 3 : k) * A0 ^ 2
  let CT0 := C0 + C ((3 / 2 : k) * gamma) * h ^ 4
  let F0 := D0 - C (1 / 3 : k) * A0 * B0
  2 * CT0 ^ 2 - B0 * F0 + C (2 / 3 : k) * (A0 * B0 ^ 2)

/-- Rational-function form of the same corrected defect. -/
def rhoOneCapCorrectedRatFunc68
    (gamma : k) (A B C0 D : RatFunc k) : RatFunc k :=
  let C1 := C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let CT := C1 + RatFunc.C ((3 / 2 : k) * gamma)
  let F := D - RatFunc.C (1 / 3 : k) * A * B
  2 * CT ^ 2 - B * F + RatFunc.C (2 / 3 : k) * (A * B ^ 2)

/-- The five ordinary rho-one clearings put the corrected defect over the
single denominator `h^8`. -/
theorem rhoOneCap_corrected_clearing68
    (h A0 B0 C00 D0 : k[X]) (gamma : k)
    (A B C0 D : RatFunc k)
    (hA : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h) ^ 2 * A)
    (hB : algebraMap k[X] (RatFunc k) B0 =
      (algebraMap k[X] (RatFunc k) h) ^ 3 * B)
    (hC : algebraMap k[X] (RatFunc k) C00 =
      (algebraMap k[X] (RatFunc k) h) ^ 4 * C0)
    (hD : algebraMap k[X] (RatFunc k) D0 =
      (algebraMap k[X] (RatFunc k) h) ^ 5 * D) :
    algebraMap k[X] (RatFunc k)
        (rhoOneCapCorrectedClearedNumerator68 h A0 B0 C00 D0 gamma) =
      (algebraMap k[X] (RatFunc k) h) ^ 8 *
        rhoOneCapCorrectedRatFunc68 gamma A B C0 D := by
  simp only [rhoOneCapCorrectedClearedNumerator68,
    rhoOneCapCorrectedRatFunc68, map_add, map_sub, map_mul, map_pow,
    map_ofNat, map_div₀, map_one, Polynomial.map_C, RatFunc.algebraMap_C]
  rw [hA, hB, hC, hD]
  ring

/-- Exact action of the finite-place Laurent embedding on a coefficient
polynomial. -/
theorem ratFuncAtLaurent46_algebraMap68 (a : k) (p : k[X]) :
    ratFuncAtLaurent46 a (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (LaurentSeries k) (p.comp (X + C a)) := by
  simp only [ratFuncAtLaurent46, RatFunc.liftRingHom_algebraMap,
    polynomialAtLaurent46, RingHom.comp_apply, polynomialTranslate46,
    Polynomial.coe_compRingHom_apply]

/-- A degree-one local scale has exact Laurent order one at its root. -/
theorem ratFuncAtLaurent68_linearRoot_orderTop_eq_one
    (h : k[X]) (a : k) (hdegree : h.natDegree = 1)
    (hroot : h.eval a = 0) :
    (ratFuncAtLaurent46 a
      (algebraMap k[X] (RatFunc k) h)).orderTop =
        (↑(1 : ℤ) : WithTop ℤ) := by
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by
    simpa [← hlinear] using hroot
  have hcomp : h.comp (X + C a) = C c * X := by
    apply Polynomial.funext
    intro x
    rw [← hlinear]
    simp only [Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    linear_combination hca
  rw [ratFuncAtLaurent46_algebraMap68, hcomp, map_mul]
  simp [Polynomial.algebraMap_hahnSeries_apply, HahnSeries.C_apply,
    HahnSeries.orderTop_single hc]

/-- Exact finite Laurent order of an embedded polynomial is bounded by its
ordinary degree. -/
theorem natDegree_ge_of_ratFuncAtLaurent_orderTop_eq68
    (a : k) (p : k[X]) (n : ℕ)
    (horder : (ratFuncAtLaurent46 a
      (algebraMap k[X] (RatFunc k) p)).orderTop =
        (↑(n : ℤ) : WithTop ℤ)) :
    n ≤ p.natDegree := by
  have hcoeff :
      (ratFuncAtLaurent46 a
        (algebraMap k[X] (RatFunc k) p)).coeff (n : ℤ) ≠ 0 :=
    HahnSeries.coeff_orderTop_ne horder
  rw [ratFuncAtLaurent46_algebraMap68,
    Polynomial.algebraMap_hahnSeries_apply] at hcoeff
  rw [HahnSeries.ofPowerSeries_apply_coeff, Polynomial.coeff_coe] at hcoeff
  change (p.comp (X + C a)).coeff n ≠ 0 at hcoeff
  have hdegComp : n ≤ (p.comp (X + C a)).natDegree := by
    by_contra hnot
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hnot)
    exact hcoeff hz
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C,
    Nat.mul_one] at hdegComp
  exact hdegComp

/-- Clearing by `h^8` adds exactly eight to a finite local order, hence an
order-`n` corrected defect forces degree at least `n+8` in its explicit
polynomial numerator. -/
theorem rhoOneCap_corrected_cleared_natDegree_lower_bound68
    (a : k) (h K0 : k[X]) (KR : RatFunc k) (n : ℕ)
    (hscale : (ratFuncAtLaurent46 a
      (algebraMap k[X] (RatFunc k) h)).orderTop =
        (↑(1 : ℤ) : WithTop ℤ))
    (hclear : algebraMap k[X] (RatFunc k) K0 =
      (algebraMap k[X] (RatFunc k) h) ^ 8 * KR)
    (horder : (ratFuncAtLaurent46 a KR).orderTop =
      (↑(n : ℤ) : WithTop ℤ)) :
    n + 8 ≤ K0.natDegree := by
  let hL := ratFuncAtLaurent46 a (algebraMap k[X] (RatFunc k) h)
  let KL := ratFuncAtLaurent46 a KR
  have hpowAll : ∀ m : ℕ,
      (hL ^ m).orderTop = (↑((m : ℕ) : ℤ) : WithTop ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, HahnSeries.orderTop_mul, ih]
        dsimp only [hL]
        rw [hscale, ← WithTop.coe_add]
        norm_num
  have hpow : (hL ^ 8).orderTop = (↑(8 : ℤ) : WithTop ℤ) := by
    simpa using hpowAll 8
  have hmapped := congrArg (ratFuncAtLaurent46 a) hclear
  simp only [map_mul, map_pow] at hmapped
  have hK0order :
      (ratFuncAtLaurent46 a
        (algebraMap k[X] (RatFunc k) K0)).orderTop =
          (↑((n + 8 : ℕ) : ℤ) : WithTop ℤ) := by
    rw [hmapped, HahnSeries.orderTop_mul, hpow]
    rw [horder, ← WithTop.coe_add]
    norm_num [add_comm]
  exact natDegree_ge_of_ratFuncAtLaurent_orderTop_eq68 a K0 (n + 8)
    hK0order

/-- Exact source residual: the two cap orders are respectively a degree-45
and degree-38 condition on one explicit polynomial numerator. -/
def RhoOneCapKSourceOrderPacket68
    (gamma : k) (h A0 B0 C00 D0 : k[X]) : Prop :=
  let K0 := rhoOneCapCorrectedClearedNumerator68 h A0 B0 C00 D0 gamma
  (gamma = 0 ∧ 45 ≤ K0.natDegree) ∨
    (gamma ≠ 0 ∧ 38 ≤ K0.natDegree)

/-- Source-facing residual retaining the full predecessor and recording the
exact polynomial consequence on its cap-coordinate child. -/
def RhoOneDoubleZeroTerminalGBoundaryCapKSourceOrderResidual68
    (root j gamma epsilon : k)
    (h A0 B0 C00 D0 : k[X])
    (hR AR BR CR FR GR : RatFunc k)
    (A B C F G : HahnSeries ℚ k) : Prop :=
  RhoOneDoubleZeroTerminalGBoundaryCapT16SplitResidual68
      root j gamma epsilon A0 hR AR BR CR FR GR A B C F G ∧
    ((B.coeff (1 : ℚ) = 0 ∧ 2 * C.coeff 0 + 3 * gamma = 0) →
      C.coeff (1 : ℚ) = 0 → C.coeff (2 : ℚ) = 0 →
      RhoOneCapKSourceOrderPacket68 gamma h A0 B0 C00 D0)

/-- The exact T16 dichotomy, transported all the way back to the literal
rho-one cleared coordinate polynomials.  No upper bound on the `X`-degree
of this numerator is part of the normalized source interface. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapKSourceOrderResidual
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
      (rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
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
    let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    RhoOneDoubleZeroTerminalGBoundaryCapKSourceOrderResidual68
        T.root j T.source.gamma T.source.epsilon h0 A0 B0 C00 D0
        (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68 T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68 T.source.gamma B C F)) := by
  dsimp only
  have hprev :=
    T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapT16SplitResidual
      hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
  rcases hprev with hprev | htail
  · left
    refine ⟨hprev, ?_⟩
    intro hcoord hc1 hc2
    have hsplit := hprev.2 hcoord hc1 hc2
    let A0 := localClearedA68RhoOne g u
    let B0 := localClearedB68RhoOne g u (p.coeff 3)
    let C00 := localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
    let D0 := localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
      (p.coeff 1)
    let KR := rhoOneCapCorrectedRatFunc68 T.source.gamma T.source.A
      T.source.B T.source.C0 T.source.D
    obtain ⟨hA, hB0, hC0, hD0, _hE0⟩ :=
      T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero hH hp6 hp5 hp4
    have hclear : algebraMap k[X] (RatFunc k)
        (rhoOneCapCorrectedClearedNumerator68 h0 A0 B0 C00 D0
          T.source.gamma) =
      (algebraMap k[X] (RatFunc k) h0) ^ 8 * KR := by
      exact rhoOneCap_corrected_clearing68 h0 A0 B0 C00 D0
        T.source.gamma T.source.A T.source.B T.source.C0 T.source.D
        (by simpa only [A0] using hA) (by simpa only [B0] using hB0)
        (by simpa only [C00] using hC0) (by simpa only [D0] using hD0)
    let AL : LaurentSeries k := ratFuncAtLaurent46 T.root T.source.A
    let BL : LaurentSeries k := ratFuncAtLaurent46 T.root T.source.B
    let CL : LaurentSeries k := ratFuncAtLaurent46 T.root
      (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2)
    let CT : LaurentSeries k :=
      CL + HahnSeries.C ((3 / 2 : k) * T.source.gamma)
    let FL : LaurentSeries k := ratFuncAtLaurent46 T.root
      (T.source.D - RatFunc.C (1 / 3 : k) * T.source.A * T.source.B)
    have hKRmap : ratFuncAtLaurent46 T.root KR =
        rhoOneCapCorrectedDefect68 AL BL CT FL := by
      dsimp only [KR, rhoOneCapCorrectedRatFunc68, AL, BL, CL, CT, FL,
        rhoOneCapCorrectedDefect68, rhoOneCapCoordinateDefectSeries68]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
        ratFuncAtLaurent46_C68]
    have hscaleL := ratFuncAtLaurent68_linearRoot_orderTop_eq_one
      h0 T.root T.scale_degree T.root_eq
    dsimp only [RhoOneCapKSourceOrderPacket68]
    rcases hsplit with hzero | hnonzero
    · left
      refine ⟨hzero.1, ?_⟩
      have horder : (ratFuncAtLaurent46 T.root KR).orderTop =
          (↑(37 : ℤ) : WithTop ℤ) := by
        rw [hKRmap]
        simpa only [AL, BL, CL, CT, FL] using hzero.2.2.1
      exact rhoOneCap_corrected_cleared_natDegree_lower_bound68
        T.root h0
        (rhoOneCapCorrectedClearedNumerator68 h0 A0 B0 C00 D0
          T.source.gamma) KR 37 hscaleL hclear horder
    · right
      refine ⟨hnonzero.1, ?_⟩
      have horder : (ratFuncAtLaurent46 T.root KR).orderTop =
          (↑(30 : ℤ) : WithTop ℤ) := by
        rw [hKRmap]
        simpa only [AL, BL, CL, CT, FL] using hnonzero.2.2.1
      exact rhoOneCap_corrected_cleared_natDegree_lower_bound68
        T.root h0
        (rhoOneCapCorrectedClearedNumerator68 h0 A0 B0 C00 D0
          T.source.gamma) KR 30 hscaleL hclear horder
  · exact Or.inr htail

end AlignedSquareTerminalGBoundaryCapKSourceOrder68

end Max11DegreeRoutes
