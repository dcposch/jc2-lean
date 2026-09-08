import LowScale68ScaleTwoAfterRhoOneAfterP3Closure
import LowScale68ScaleZeroAssembly

/-! # Source bridge for the closed `(6,8)`, scale-two local package

The local contradiction closes every nonzero discriminator face.  The only
remaining normalized scale-two source chamber is therefore the aligned face
`4 p₅ H - 3 q₇ = 0`.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section ScaleTwoClosureBridge68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The now-closed local package excludes every normalized nonzero
discriminator face, without a conditional local-root interface. -/
theorem normalized68ScaleTwo_nonzeroFace_impossible
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 ≠ 0) : False := by
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
  have hl : -lambda / 3 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hlambda) (by norm_num)
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
      ratFuncAtHahn68_linearRoot_orderTop_eq_one h0 a hh0degree hroot
    terminal_order :=
      ratFuncAtHahn68_kellerTerminal_orderTop_eq_neg_one
        h0 j a hh0 hj hh0degree hroot
  }
  exact T.scaleTwo68_impossible hp hH hp6'

/-- Unconditional consequence of the local closure: every normalized
scale-two `(6,8)` source lies on the aligned discriminator face. -/
theorem normalized68ScaleTwo_discriminator_eq_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0 := by
  dsimp only
  by_contra hnonzero
  exact normalized68ScaleTwo_nonzeroFace_impossible hsource hnonzero

/-- The exact remaining source-level gap after the nonzero closure. -/
def PlaneKeller68AlignedScaleTwoExclusion : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) k) (H : k[X]),
    Normalized68LeadingCoreSource P Q H 2 →
      (let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
       let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
       (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) → False

theorem normalized68ScaleTwo_impossible_of_alignedExclusion
    (haligned : PlaneKeller68AlignedScaleTwoExclusion (k := k))
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2) : False := by
  exact haligned P Q H hsource
    (normalized68ScaleTwo_discriminator_eq_zero hsource)

/-- Conditional route handoff with the sole remaining aligned chamber made
explicit. -/
theorem planeKellerNormalized68ScaleTwoRoute_of_alignedExclusion
    (haligned : PlaneKeller68AlignedScaleTwoExclusion (k := k)) :
    PlaneKellerNormalized68ScaleTwoRoute (k := k) := by
  intro P Q H hsource
  exact (normalized68ScaleTwo_impossible_of_alignedExclusion
    haligned hsource).elim

end ScaleTwoClosureBridge68

end Max11DegreeRoutes
