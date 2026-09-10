import Sol68ScaleTwoAlignedSquareSourceSelectorHierarchyScratch

/-! # Consuming the second cubic-next component of the aligned-square hierarchy

The second zero-septic cubic-next component carries the single row
`a b² - b d + 2 c² = 0` on top of `RhoOneZeroLCubicNextSourcePacket68`.
Backwiring the packet-honest lower rows one and two through this equation
yields the kernel square `(a b² + 3 c²)²` in the row ideal, hence the exact
pin `a b² + 3 c² = 0`.  The pin splits the component as `b (a b - 3 d) = 0`;
on `b ≠ 0` the main-tangent relations `a b = 3 d` and `3 e = a c` re-emerge
and the already-verified invariant residual clashes with the pin
(`c² = a b²` against `a b² = -3 c²`), eliminating that limb outright.  The
second component therefore collapses onto the exceptional zero sibling
`b = c = d = e = 0`, and the early sibling inventory loses one disjunct. -/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareSecondNextComponentConsumer68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Backwired kernel pin: on the second component, rows two and one place
`c (a b² + 3 c²)²` and `(a b² - 3 c²) (a b² + 3 c²)²` in the row ideal, and
the two cofactors are jointly incompatible with `a b² + 3 c² ≠ 0`. -/
theorem rhoOneZeroLCubicSecondComponent_kernel_pin68
    (a b c d e : k) (ha : a ≠ 0)
    (hS : a * b ^ 2 - b * d + 2 * c ^ 2 = 0)
    (h4 : rhoOneZeroLCubicNextFour68 a b c d e = 0)
    (h2 : rhoOneZeroLCubicNextTwo68 a b c d e = 0)
    (h1 : rhoOneZeroLCubicNextOne68 a b c d e = 0) :
    a * b ^ 2 + 3 * c ^ 2 = 0 := by
  have h4' : -2 * a * b * c + 3 * c * d + 3 * b * e = 0 := by
    simp only [rhoOneZeroLCubicNextFour68] at h4
    linear_combination (9 / 8 : k) * h4
  simp only [rhoOneZeroLCubicNextTwo68] at h2
  simp only [rhoOneZeroLCubicNextOne68] at h1
  have hcK : c * (a * b ^ 2 + 3 * c ^ 2) ^ 2 = 0 := by
    linear_combination (b ^ 3 / 12 : k) * h2 +
      ((27 * a * b ^ 2 * c - 27 * b ^ 2 * e + 54 * c ^ 3) / 12 : k) * hS +
      ((8 * a * b ^ 3 + 18 * b * c ^ 2) / 12 : k) * h4'
  have hbK : (a * b ^ 2 - 3 * c ^ 2) * (a * b ^ 2 + 3 * c ^ 2) ^ 2 = 0 := by
    linear_combination (b ^ 4 / 20 : k) * h1 +
      ((27 * a ^ 2 * b ^ 4 + 9 * a * b ^ 3 * d - 45 * a * b ^ 2 * c ^ 2 +
          135 * b ^ 2 * c * e - 270 * c ^ 4) / 20 : k) * hS +
      ((-21 * a * b ^ 3 * c + 45 * b ^ 3 * e - 90 * b * c ^ 3) / 20 : k) * h4'
  by_contra hK
  have hK2 : (a * b ^ 2 + 3 * c ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hK
  have hc0 : c = 0 := (mul_eq_zero.mp hcK).resolve_right hK2
  have hb2 : a * b ^ 2 - 3 * c ^ 2 = 0 :=
    (mul_eq_zero.mp hbK).resolve_right hK2
  apply hK
  linear_combination hb2 + 6 * c * hc0

/-- Scalar dichotomy on the second component: either the total kill of all
four defect coordinates, or the main-tangent relations together with the
kernel pin. -/
theorem rhoOneZeroLCubicSecondComponent_split68
    (a b c d e : k) (ha : a ≠ 0)
    (hS : a * b ^ 2 - b * d + 2 * c ^ 2 = 0)
    (h4 : rhoOneZeroLCubicNextFour68 a b c d e = 0)
    (h3 : rhoOneZeroLCubicNextThree68 a b c d e = 0)
    (h2 : rhoOneZeroLCubicNextTwo68 a b c d e = 0)
    (h1 : rhoOneZeroLCubicNextOne68 a b c d e = 0) :
    (b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0) ∨
      (b ≠ 0 ∧ a * b = 3 * d ∧ 3 * e = a * c ∧
        a * b ^ 2 + 3 * c ^ 2 = 0) := by
  have hK := rhoOneZeroLCubicSecondComponent_kernel_pin68
    a b c d e ha hS h4 h2 h1
  by_cases hb : b = 0
  · left
    have hc : c = 0 := by
      have hc2 : c ^ 2 = 0 := by
        rw [hb] at hK
        linear_combination (1 / 3 : k) * hK
      exact eq_zero_of_pow_eq_zero hc2
    have hd : d = 0 := by
      have hd2 : d ^ 2 = 0 := by
        simp only [rhoOneZeroLCubicNextThree68] at h3
        rw [hb, hc] at h3
        linear_combination (3 / 4 : k) * h3
      exact eq_zero_of_pow_eq_zero hd2
    have he := rhoOneZeroLCubic_firstComponent_exceptional_rowOne68
      a b c d e hb hc hd h1
    exact ⟨hb, hc, hd, he⟩
  · right
    have hbsplit : b * (a * b - 3 * d) = 0 := by
      linear_combination 3 * hS - 2 * hK
    have habd : a * b = 3 * d := by
      have h := (mul_eq_zero.mp hbsplit).resolve_left hb
      linear_combination h
    have hforce := rhoOneZeroLCubic_nextFour_nextTwo_force68 a b c d e h4 h2
    have hace : a * b * (a * c - 3 * e) = 0 := by
      linear_combination hforce - 3 * e * habd
    have h3e : 3 * e = a * c := by
      have h := (mul_eq_zero.mp hace).resolve_left (mul_ne_zero ha hb)
      linear_combination -h
    exact ⟨hb, habd, h3e, hK⟩

/-- Source-honest collapse of the second cubic-next component.  The
main-tangent limb produced by the kernel pin is eliminated against the
invariant residual: its nonzero leaf demands `c² = a b²` while the pin
gives `a b² = -3 c²`, and its `c = 0` leaf kills `b`.  Only the exact zero
locus in all four defect coordinates survives. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_secondNextComponent_zeroCollapse
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hsecond : RhoOneZeroLCubicSecondNextComponent68 T g u) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    RhoOneZeroLCubicNextSourcePacket68 T g u ∧
      B.coeff (-2 : ℚ) = 0 ∧
      (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ) = 0 ∧
      D.coeff (-4 : ℚ) = 0 ∧
      (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ) = 0 := by
  dsimp only [RhoOneZeroLCubicSecondNextComponent68] at hsecond
  obtain ⟨P, hS⟩ := hsecond
  dsimp only
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
  have ha : a ≠ 0 := P.2.2.1
  have hSc : a * b ^ 2 - b * d + 2 * c ^ 2 = 0 := hS
  have h4 : rhoOneZeroLCubicNextFour68 a b c d e = 0 := P.2.2.2.2.1
  have h3 : rhoOneZeroLCubicNextThree68 a b c d e = 0 := P.2.2.2.2.2.1
  have h2 : rhoOneZeroLCubicNextTwo68 a b c d e = 0 := by
    simpa only [A, B, C0, D, E, a, b, c, d, e] using
      T.rhoOne_cubicBranch_nextTwo_zero hp hH hp6 hp5 hp4 P.1
  have h1 : rhoOneZeroLCubicNextOne68 a b c d e = 0 := by
    simpa only [A, B, C0, D, E, a, b, c, d, e] using
      T.rhoOne_cubicBranch_nextOne_zero hp hH hp6 hp5 hp4 P
  rcases rhoOneZeroLCubicSecondComponent_split68 a b c d e ha hSc h4 h3 h2 h1
    with ⟨hb, hc, hd, he⟩ | ⟨hb, habd, h3e, hK⟩
  · exact ⟨P, hb, hc, hd, he⟩
  · exfalso
    have hres := T.rhoOne_mainTangent_residual hp hH hp6 hp5 hp4 P
      ⟨habd, h3e⟩
    dsimp only [RhoOneZeroLCubicMainTangentInvariantResidual68] at hres
    rcases hres with ⟨hc0, -⟩ | ⟨hcne, -, hcsq, -, -⟩
    · have hc0' : c = 0 := hc0
      have hb2 : a * b ^ 2 = 0 := by
        linear_combination hK - 3 * c * hc0'
      exact hb (eq_zero_of_pow_eq_zero
        ((mul_eq_zero.mp hb2).resolve_left ha))
    · have hcsq' : c ^ 2 = a * b ^ 2 := hcsq
      have hc2 : c ^ 2 = 0 := by
        linear_combination (1 / 4 : k) * hK + (1 / 4 : k) * hcsq'
      exact hcne (eq_zero_of_pow_eq_zero hc2)

/-- The early sibling inventory with the second cubic-next component
consumed: its disjunct merges into the exceptional zero sibling, and the
two row-one main-tangent leaves are retained literally. -/
def RhoOneAlignedSquareReducedCubicSibling68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C ER
  let a := A.coeff (-2 : ℚ)
  let b := B.coeff (-2 : ℚ)
  let c := C.coeff (-3 : ℚ)
  let d := D.coeff (-4 : ℚ)
  let e := ER.coeff (-5 : ℚ)
  (RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0) ∨
  (RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    (a * b = 3 * d ∧ 3 * e = a * c) ∧
    ((c = 0 ∧ b ≠ 0 ∧ F.coeff (-3 : ℚ) = 0 ∧
        -64 * b ^ 3 + 15 * T.source.beta * a ^ 3 +
          576 * b * G.coeff (-4 : ℚ) = 0) ∨
      (c ≠ 0 ∧ b ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
        rhoOneZeroLCubicMainTangentFour68 T.source.beta a b c
          (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0 ∧
        rhoOneZeroLCubicMainTangentThree68 a b c
          (F.coeff (-3 : ℚ)) (G.coeff (-4 : ℚ)) = 0)))

/-- Reduction of the early sibling inventory: the second-component disjunct
collapses into the exceptional zero sibling; every other limb is preserved
verbatim. -/
theorem RhoOneAlignedSquareEarlyCubicSibling68.reduce_secondComponent
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    {T : SquareZeroLIntegratedLocalRootData68 p q j h0}
    (hsib : RhoOneAlignedSquareEarlyCubicSibling68 T g u)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    RhoOneAlignedSquareReducedCubicSibling68 T g u := by
  dsimp only [RhoOneAlignedSquareEarlyCubicSibling68,
    RhoOneAlignedSquareReducedCubicSibling68] at hsib ⊢
  rcases hsib with hsecond | hzero | hmain
  · have hcollapse := T.rhoOne_secondNextComponent_zeroCollapse
      hp hH hp6 hp5 hp4 hsecond
    dsimp only at hcollapse
    exact Or.inl hcollapse
  · exact Or.inl hzero
  · exact Or.inr hmain

/-- Full aligned square-source inventory with the second cubic-next
component consumed.  The descent, noncubic, and exceptional main-tangent
entries are untouched. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_reducedSourceSelectorHierarchy
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    ∃ g u : k[X],
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      ((h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
       RhoOneZeroLNoncubicSourcePacket68 T g u ∨
       RhoOneAlignedSquareReducedCubicSibling68 T g u ∨
       RhoOneAlignedSquareExceptionalMainEntry68 T g u) := by
  obtain ⟨g, u, hp5, hp4, hroutes⟩ :=
    T.rhoOne_alignedSquare_sourceSelectorHierarchy hp hH hp6
  refine ⟨g, u, hp5, hp4, ?_⟩
  rcases hroutes with hdesc | hnon | hsib | hentry
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl hnon)
  · exact Or.inr (Or.inr (Or.inl
      (hsib.reduce_secondComponent hp hH hp6 hp5 hp4)))
  · exact Or.inr (Or.inr (Or.inr hentry))

/-- Normalized aligned-square source wrapper for the reduced selector
hierarchy. -/
theorem normalized68ScaleTwo_alignedSquare_reducedSourceSelectorHierarchy
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ∃ (j : k) (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
        (g u : k[X]),
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      ((h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
       RhoOneZeroLNoncubicSourcePacket68 T g u ∨
       RhoOneAlignedSquareReducedCubicSibling68 T g u ∨
       RhoOneAlignedSquareExceptionalMainEntry68 T g u) := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hsource.2.2.1
  have hp6 : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hsource.2.2.2.2.1
  obtain ⟨j, ⟨T⟩⟩ :=
    normalized68ScaleTwo_alignedSquareBranch_localRootData
      hsource hh0 hH haligned
  obtain ⟨g, u, hp5, hp4, hroutes⟩ :=
    T.rhoOne_alignedSquare_reducedSourceSelectorHierarchy hp hH hp6
  exact ⟨j, T, g, u, hp5, hp4, hroutes⟩

end AlignedSquareSecondNextComponentConsumer68

end Max11DegreeRoutes
