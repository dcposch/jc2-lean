import LowScale68ScaleTwoClosureBridge

/-! # The aligned `(6,8)`, scale-two source face

The nonzero septic face is closed.  On the remaining aligned face the
integrated septic coefficient is literally zero, so the existing local
record (which assumes that coefficient is nonzero) cannot be reused.  This
file gives the exact source-to-local handoff for the square-core chamber and
separates it from the genuinely nonsquare quadratic-core chamber.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedScaleTwo68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Local data produced by an aligned square-core source.  It differs from
`SquareConstantLIntegratedLocalRootData68` in exactly one respect: the
septic coefficient is zero, rather than nonzero. -/
structure SquareZeroLIntegratedLocalRootData68
    (p q : k[X][X]) (j : k) (h0 : k[X]) where
  source : SquareConstantLIntegratedSourceData68 p q j h0 0
  root : k
  scale_ne_zero : h0 ≠ 0
  scale_degree : h0.natDegree = 1
  root_eq : h0.eval root = 0
  jacobian_ne_zero : j ≠ 0
  scale_order :
    (ratFuncAtHahn46 root
      (algebraMap k[X] (RatFunc k) h0)).orderTop =
        (↑(1 : ℚ) : WithTop ℚ)
  terminal_order :
    (ratFuncAtHahn46 root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).orderTop =
        (↑(-1 : ℚ) : WithTop ℚ)

/-- Every aligned normalized source whose quadratic core is a square gives
the exact zero-septic integrated local-root package. -/
theorem normalized68ScaleTwo_alignedSquareBranch_localRootData
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ∃ j : k, Nonempty (SquareZeroLIntegratedLocalRootData68 p q j h0) := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  have haligned' : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0 := by
    simpa only [p, q] using haligned
  have hh0degree : h0.natDegree = 1 := by
    have hdeg := congrArg Polynomial.natDegree hH
    rw [hHdegree, natDegree_pow] at hdeg
    omega
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hh0degree
  let a : k := -d / c
  have hroot : h0.eval a = 0 := by
    rw [← hlinear]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    dsimp only [a]
    field_simp [hc]
    ring
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  have hN : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = Polynomial.C 0 * h0 ^ 7 := by
    simpa only [Polynomial.C_0, zero_mul] using haligned'
  obtain ⟨S⟩ := squareConstantLIntegratedSourceData68
    p q H h0 j 0 hp hq hh0 hH hp6' hq8' hN hD
  have hsource0 : SquareConstantLIntegratedSourceData68 p q j h0 0 := by
    simpa using S
  let T : SquareZeroLIntegratedLocalRootData68 p q j h0 := {
    source := hsource0
    root := a
    scale_ne_zero := hh0
    scale_degree := hh0degree
    root_eq := hroot
    jacobian_ne_zero := hj
    scale_order :=
      ratFuncAtHahn68_linearRoot_orderTop_eq_one
        h0 a hh0degree hroot
    terminal_order :=
      ratFuncAtHahn68_kellerTerminal_orderTop_eq_neg_one
        h0 j a hh0 hj hh0degree hroot
  }
  exact ⟨j, ⟨T⟩⟩

/-- The exact remaining square-core local theorem. -/
def PlaneKeller68AlignedSquareLocalRootExclusion : Prop :=
  ∀ (p q : k[X][X]) (j : k) (h0 : k[X]),
    SquareZeroLIntegratedLocalRootData68 p q j h0 → False

/-- The exact remaining nonsquare source theorem.  This chamber requires the
quadratic-field/deck descent, rather than a finite root of a square root. -/
def PlaneKeller68AlignedNonsquareExclusion : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) k) (H : k[X]),
    Normalized68LeadingCoreSource P Q H 2 →
      (∀ h0 : k[X], H ≠ h0 ^ 2) →
      (let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
       let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
       (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) → False

/-- The square-core source chamber is closed by precisely the zero-septic
local-root exclusion above. -/
theorem normalized68ScaleTwo_alignedSquareBranch_impossible_of_localRootExclusion
    (hlocal : PlaneKeller68AlignedSquareLocalRootExclusion (k := k))
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) : False := by
  obtain ⟨j, ⟨T⟩⟩ :=
    normalized68ScaleTwo_alignedSquareBranch_localRootData
      hsource hh0 hH haligned
  exact hlocal _ _ j h0 T

/-- Exhaustive reduction of the aligned face to its square zero-septic local
claim and its nonsquare quadratic-field theorem. -/
theorem planeKeller68AlignedScaleTwoExclusion_of_square_nonsquare
    (hsquare : PlaneKeller68AlignedSquareLocalRootExclusion (k := k))
    (hnonsquare : PlaneKeller68AlignedNonsquareExclusion (k := k)) :
    PlaneKeller68AlignedScaleTwoExclusion (k := k) := by
  intro P Q H hsource haligned
  by_cases hsq : ∃ h0 : k[X], H = h0 ^ 2
  · obtain ⟨h0, hH⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      simp [hH, hzero]
    exact normalized68ScaleTwo_alignedSquareBranch_impossible_of_localRootExclusion
      hsquare hsource hh0 hH haligned
  · have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := by
      intro h0 hH
      exact hsq ⟨h0, hH⟩
    exact hnonsquare P Q H hsource hnsq haligned

end AlignedScaleTwo68

end Max11DegreeRoutes
