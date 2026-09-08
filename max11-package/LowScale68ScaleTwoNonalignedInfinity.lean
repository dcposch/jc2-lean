import LowScale68ScaleTwoSourceFace
import LowScale46WeightedInfinity

/-! # Nonaligned scale-two source adapter for `(6,8)`

This scratch module turns the nonzero first face

`H = h²`, `4 p₅ H - 3 q₇ = λ h⁷`

into the complete integrated sextic/octic differential normal form over
`k(x)`.  The surviving septic coefficient is the explicit nonzero constant
`l = -λ/3`.  The remaining local-root contradiction is isolated in the
same source-facing shape as the proved `(4,6)` mismatch theorem.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section NonalignedSourceAdapter68

variable {k : Type*} [Field k] [CharZero k]

local instance sourceHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- A degree-one coefficient polynomial has exact local order one at its
root under the finite-place Hahn embedding. -/
theorem ratFuncAtHahn68_linearRoot_orderTop_eq_one
    (h0 : k[X]) (a : k) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) :
    (ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0)).orderTop =
      (↑(1 : ℚ) : WithTop ℚ) := by
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by
    simpa [← hlinear] using hroot
  rw [ratFuncAtHahn46_algebraMap]
  have hcomp : h0.comp (Polynomial.X + Polynomial.C a) =
      Polynomial.C c * Polynomial.X := by
    apply Polynomial.funext
    intro x
    rw [← hlinear]
    simp only [Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    linear_combination hca
  rw [hcomp, map_mul]
  simp [Polynomial.algebraMap_hahnSeries_apply, HahnSeries.C_apply,
    HahnSeries.orderTop_single hc]

/-- At that root the transformed Keller terminal `j / h` has exact local
order `-1`. -/
theorem ratFuncAtHahn68_kellerTerminal_orderTop_eq_neg_one
    (h0 : k[X]) (j a : k) (hh0 : h0 ≠ 0) (hj : j ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0) :
    (ratFuncAtHahn46 a
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).orderTop =
        (↑(-1 : ℚ) : WithTop ℚ) := by
  let hH : HahnSeries ℚ k :=
    ratFuncAtHahn46 a (algebraMap k[X] (RatFunc k) h0)
  have hhH : hH ≠ 0 := by
    dsimp only [hH]
    simpa only [map_zero] using
      (ratFuncAtHahn46_injective a).ne
        (RatFunc.algebraMap_ne_zero hh0)
  have hhOrder : hH.orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
    dsimp only [hH]
    exact ratFuncAtHahn68_linearRoot_orderTop_eq_one
      h0 a hdegree hroot
  have hinvOrder : hH⁻¹.orderTop = (↑(-1 : ℚ) : WithTop ℚ) :=
    hahnOrderTop_inv_eq_neg46 hH 1 hhH hhOrder
  simp only [div_eq_mul_inv, map_mul, ratFuncAtHahn46_C, map_inv₀]
  change (HahnSeries.C j * hH⁻¹).orderTop =
    (↑(-1 : ℚ) : WithTop ℚ)
  rw [HahnSeries.orderTop_mul, HahnSeries.C_apply,
    HahnSeries.orderTop_single hj, hinvOrder]
  norm_num

/-- Exact integrated source data produced by a square-core `(6,8)` source
whose depressed septic coefficient is the selected ground constant `l`.

Unlike a free differential-field package, this retains the literal source
polynomials, the linear square root, its depression center, and the Keller
terminal `j / h`; these are precisely the ingredients a local-root theorem
needs. -/
structure SquareConstantLIntegratedSourceData68
    (p q : k[X][X]) (j : k) (h0 : k[X]) (l : k) where
  r : RatFunc k
  A : RatFunc k
  B : RatFunc k
  C0 : RatFunc k
  D : RatFunc k
  E : RatFunc k
  alpha : k
  beta : k
  gamma : k
  delta : k
  epsilon : k
  zeta : k
  eta : k
  center_eq : r = sexticDepressionR68
    (algebraMap k[X] (RatFunc k) h0)
    (algebraMap k[X] (RatFunc k) (p.coeff 5))
  sextic_eq :
    affineDepress68 (algebraMap k[X] (RatFunc k) h0) r
        (sourceToRatFunc68 p) = depressedSextic68 A B C0 D E
  octic_eq :
    affineDepress68 (algebraMap k[X] (RatFunc k) h0) r
        (sourceToRatFunc68 q) =
      depressedOctic68 (RatFunc.C l)
        (integratedP68 A (RatFunc.C alpha))
        (integratedQ68 (RatFunc.C l) A B (RatFunc.C beta))
        (integratedR68 (RatFunc.C l) A B C0 (RatFunc.C alpha)
          (RatFunc.C gamma))
        (integratedS68 (RatFunc.C l) A B C0 D (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C delta))
        (integratedT68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon))
        (integratedU68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C zeta))
        (integratedV68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C eta))
  bracket_eq :
    differentialJacobian ratFuncDerivation68
        (depressedSextic68 A B C0 D E)
        (depressedOctic68 (RatFunc.C l)
          (integratedP68 A (RatFunc.C alpha))
          (integratedQ68 (RatFunc.C l) A B (RatFunc.C beta))
          (integratedR68 (RatFunc.C l) A B C0 (RatFunc.C alpha)
            (RatFunc.C gamma))
          (integratedS68 (RatFunc.C l) A B C0 D (RatFunc.C alpha)
            (RatFunc.C beta) (RatFunc.C delta))
          (integratedT68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
            (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon))
          (integratedU68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
            (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
            (RatFunc.C zeta))
          (integratedV68 (RatFunc.C l) A B C0 D E (RatFunc.C alpha)
            (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
            (RatFunc.C epsilon) (RatFunc.C eta))) =
      Polynomial.C (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)

/-- The exact local-root package delivered by a nonaligned scale-two source.
It records not only the integrated rational normal form but also the simple
zero of the scale and the resulting order `-1` Keller terminal. -/
structure SquareConstantLIntegratedLocalRootData68
    (p q : k[X][X]) (j : k) (h0 : k[X]) (l : k) where
  source : SquareConstantLIntegratedSourceData68 p q j h0 l
  root : k
  scale_ne_zero : h0 ≠ 0
  scale_degree : h0.natDegree = 1
  root_eq : h0.eval root = 0
  jacobian_ne_zero : j ≠ 0
  septic_ne_zero : l ≠ 0
  scale_order :
    (ratFuncAtHahn46 root
      (algebraMap k[X] (RatFunc k) h0)).orderTop =
        (↑(1 : ℚ) : WithTop ℚ)
  terminal_order :
    (ratFuncAtHahn46 root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).orderTop =
        (↑(-1 : ℚ) : WithTop ℚ)

set_option maxHeartbeats 2000000 in
/-- Literal construction of the complete integrated package.  The
seventh-power source identity determines the septic constant exactly. -/
theorem squareConstantLIntegratedSourceData68
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hN : (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 =
      Polynomial.C lambda * h0 ^ 7)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    Nonempty
      (SquareConstantLIntegratedSourceData68 p q j h0 (-lambda / 3)) := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
  let r : RatFunc k := sexticDepressionR68 h a5
  let A := depressedA68 h r a5 a4
  let B := depressedB68 h r a5 a4 a3
  let C0 := depressedC68 h r a5 a4 a3 a2
  let D := depressedD68 h r a5 a4 a3 a2 a1
  let E := depressedE68 h r a5 a4 a3 a2 a1 a0
  let L := depressedL68 h r b7
  let P0 := depressedP68 h r b7 b6
  let Q0 := depressedQ68 h r b7 b6 b5
  let R0 := depressedR68 h r b7 b6 b5 b4
  let S0 := depressedS68 h r b7 b6 b5 b4 b3
  let T0 := depressedT68 h r b7 b6 b5 b4 b3 b2
  let U0 := depressedU68 h r b7 b6 b5 b4 b3 b2 b1
  let V0 := depressedV68 h r b7 b6 b5 b4 b3 b2 b1 b0
  have hh : h ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = h ^ 6 := by
    simp only [hp6, hH, h, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 8) = h ^ 8 := by
    simp only [hq8, hH, h, map_pow]
    ring
  have hpDep : affineDepress68 h r (sourceToRatFunc68 p) =
      depressedSextic68 A B C0 D E := by
    exact affineDepress_sourceSextic68 p h r hp hh hpTop rfl
  have hqDep : affineDepress68 h r (sourceToRatFunc68 q) =
      depressedOctic68 L P0 Q0 R0 S0 T0 U0 V0 := by
    exact affineDepress_sourceOctic68 q h r hq hh hqTop
  have hnum : 4 * a5 * h ^ 2 - 3 * b7 = RatFunc.C lambda * h ^ 7 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    simpa only [hH, h, a5, b7, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hL : L = RatFunc.C (-lambda / 3) := by
    dsimp only [L, r]
    rw [depressedL68_eq_discriminator h a5 b7 hh, hnum]
    calc
      -(RatFunc.C lambda * h ^ 7) / (3 * h ^ 7) =
          -(RatFunc.C lambda) / 3 := by field_simp [hh]
      _ = RatFunc.C (-lambda / 3) := by
        simp only [map_neg, map_div₀, map_ofNat]
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j h r hh hD
  rw [hpDep, hqDep] at hbracket
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta,
      hl, hP, hQ, hR, hS, hT, hU, hV⟩ :=
    depressedCoefficients_integrate_over_ground68
      L P0 Q0 R0 S0 T0 U0 V0 A B C0 D E (RatFunc.C j / h) hbracket
  have hlvalue : l = -lambda / 3 := by
    apply RatFunc.C_injective
    simpa only [RatFunc.algebraMap_eq_C] using hl.symm.trans hL
  subst l
  have hqIntegrated : affineDepress68 h r (sourceToRatFunc68 q) =
      depressedOctic68 (RatFunc.C (-lambda / 3))
        (integratedP68 A (RatFunc.C alpha))
        (integratedQ68 (RatFunc.C (-lambda / 3)) A B (RatFunc.C beta))
        (integratedR68 (RatFunc.C (-lambda / 3)) A B C0
          (RatFunc.C alpha) (RatFunc.C gamma))
        (integratedS68 (RatFunc.C (-lambda / 3)) A B C0 D
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta))
        (integratedT68 (RatFunc.C (-lambda / 3)) A B C0 D E
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C epsilon))
        (integratedU68 (RatFunc.C (-lambda / 3)) A B C0 D E
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C delta) (RatFunc.C zeta))
        (integratedV68 (RatFunc.C (-lambda / 3)) A B C0 D E
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C eta)) := by
    rw [hqDep, hP, hQ, hR, hS, hT, hU, hV, hL]
    simp only [RatFunc.algebraMap_eq_C]
  have hbracketIntegrated :
      differentialJacobian ratFuncDerivation68
          (depressedSextic68 A B C0 D E)
          (depressedOctic68 (RatFunc.C (-lambda / 3))
            (integratedP68 A (RatFunc.C alpha))
            (integratedQ68 (RatFunc.C (-lambda / 3)) A B (RatFunc.C beta))
            (integratedR68 (RatFunc.C (-lambda / 3)) A B C0
              (RatFunc.C alpha) (RatFunc.C gamma))
            (integratedS68 (RatFunc.C (-lambda / 3)) A B C0 D
              (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta))
            (integratedT68 (RatFunc.C (-lambda / 3)) A B C0 D E
              (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
              (RatFunc.C epsilon))
            (integratedU68 (RatFunc.C (-lambda / 3)) A B C0 D E
              (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
              (RatFunc.C delta) (RatFunc.C zeta))
            (integratedV68 (RatFunc.C (-lambda / 3)) A B C0 D E
              (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
              (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C eta))) =
        Polynomial.C (RatFunc.C j / h) := by
    rw [hP, hQ, hR, hS, hT, hU, hV, hL] at hbracket
    simpa only [RatFunc.algebraMap_eq_C] using hbracket
  exact ⟨{
    r := r
    A := A
    B := B
    C0 := C0
    D := D
    E := E
    alpha := alpha
    beta := beta
    gamma := gamma
    delta := delta
    epsilon := epsilon
    zeta := zeta
    eta := eta
    center_eq := rfl
    sextic_eq := hpDep
    octic_eq := hqIntegrated
    bracket_eq := hbracketIntegrated
  }⟩

/-- The one remaining theorem needed to close the nonaligned scale-two
branch.  It is intentionally a proposition, not an axiom: it asks only for
the local-root exclusion of the exact source package constructed above. -/
def PlaneKeller68NonalignedLocalRootExclusion : Prop :=
  ∀ (p q : k[X][X]) (j : k) (h0 : k[X]) (l : k),
    SquareConstantLIntegratedLocalRootData68 p q j h0 l → False

/-- Every normalized nonzero scale-two face supplies the complete integrated
local-root data, including the exact orders of its scale and terminal. -/
theorem normalized68ScaleTwo_nonzeroFace_localRootData
    [IsAlgClosed k]
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ∃ (j : k) (h0 : k[X]) (l : k),
      Nonempty (SquareConstantLIntegratedLocalRootData68 p q j h0 l) := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized68ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  have hN' : (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 =
      Polynomial.C lambda * h0 ^ 7 := by simpa only [p, q] using hN
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨S⟩ := squareConstantLIntegratedSourceData68
    p q H h0 j lambda hp hq hh0 hH hp6' hq8' hN' hD
  have hl : -lambda / 3 ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hlambda) (by norm_num)
  let T : SquareConstantLIntegratedLocalRootData68
      p q j h0 (-lambda / 3) := {
    source := S
    root := a
    scale_ne_zero := hh0
    scale_degree := hh0degree
    root_eq := hroot
    jacobian_ne_zero := hj
    septic_ne_zero := hl
    scale_order :=
      ratFuncAtHahn68_linearRoot_orderTop_eq_one
        h0 a hh0degree hroot
    terminal_order :=
      ratFuncAtHahn68_kellerTerminal_orderTop_eq_neg_one
        h0 j a hh0 hj hh0degree hroot
  }
  exact ⟨j, h0, -lambda / 3, ⟨T⟩⟩

/-- Conditional closure of the normalized nonzero face using exactly the
local-root interface above. -/
theorem normalized68ScaleTwo_nonzeroFace_impossible_of_localRootExclusion
    [IsAlgClosed k]
    (hlocal : PlaneKeller68NonalignedLocalRootExclusion (k := k))
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 ≠ 0) : False := by
  obtain ⟨j, h0, l, ⟨T⟩⟩ :=
    normalized68ScaleTwo_nonzeroFace_localRootData hsource hnonzero
  exact hlocal _ _ j h0 l T

end NonalignedSourceAdapter68

#print axioms squareConstantLIntegratedSourceData68
#print axioms ratFuncAtHahn68_linearRoot_orderTop_eq_one
#print axioms ratFuncAtHahn68_kellerTerminal_orderTop_eq_neg_one
#print axioms normalized68ScaleTwo_nonzeroFace_localRootData
#print axioms normalized68ScaleTwo_nonzeroFace_impossible_of_localRootExclusion

end Max11DegreeRoutes
