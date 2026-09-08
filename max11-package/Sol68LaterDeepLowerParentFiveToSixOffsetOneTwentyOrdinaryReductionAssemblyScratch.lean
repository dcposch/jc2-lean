import Fable68LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryNonzeroScratch
import Sol68LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryClosureAssemblyScratch

/-! # Ordinary offset-120/240 parent reduction

The literal offset-`120` selector first deletes its unique `zeta` load.
Its all-nonzero successor is the verified offset-`120` contradiction.  Its
pair-zero successor descends to offset `180`; the zero child there is the
verified offset-`240` ordinary closure.  Thus the only surviving ordinary
packet is the all-nonzero offset-`180` face.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryAssembly68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The exact residual/load row zero has the common one-form expansion
factor.  This is used only to feed the expanded offset-`120` selector. -/
theorem fiveToSix_residualLoadRowZero_expand68
    (m : ℕ) (alpha gamma epsilon zeta eta : k)
    (A B c d e : k[X]) :
    secondaryResidualRowZeroPolynomial68
        (expand k m A) (expand k m B) (expand k m c)
        (expand k m d) (expand k m e) +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        (expand k m A) (expand k m B) (expand k m c)
        ((1 / 3 : k) • (expand k m A * expand k m B) + expand k m d)
        (expand k m e) =
      expand k m
          (secondaryResidualRowZeroPolynomial68 A B c d e +
            cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
              A B c ((1 / 3 : k) • (A * B) + d) e) *
        (m * (X ^ (m - 1) : k[X])) := by
  simp only [secondaryResidualRowZeroPolynomial68,
    cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68, derivative_expand, derivative_add,
    derivative_mul, derivative_pow, derivative_smul, derivative_C,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero, map_smul,
    Polynomial.smul_eq_C_mul, expand_C]
  ring

set_option maxHeartbeats 30000000 in
/-- Source-facing assembly of the ordinary offset selector.  All source
rows remain exact.  The conclusion is precisely the surviving offset-`180`
all-nonzero face; its zero sibling has already descended through and been
closed at offset `240`. -/
theorem fiveToSix_offsetOneTwenty_ordinary_source_reduction68
    (alpha gamma epsilon zeta eta i4 i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 2)
    (he : e.natDegree ≤ 4)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow0 : secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow1 : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow2 : secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    zeta = 0 ∧ d.natDegree ≤ 1 ∧ e.natDegree ≤ 3 ∧
      B.coeff 0 ≠ 0 ∧ c.coeff 2 ≠ 0 ∧
      d.coeff 1 ≠ 0 ∧ e.coeff 3 ≠ 0 ∧
      B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1 = 0 ∧
      A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0 := by
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let ce := expand k 60 c
  let de := expand k 60 d
  let ee := expand k 60 e
  have hAe : Ae.natDegree ≤ 240 := by
    simp only [Ae, natDegree_expand]
    omega
  have hBe : Be.natDegree ≤ 0 := by
    simp only [Be, natDegree_expand]
    omega
  have hce : ce.natDegree ≤ 120 := by
    simp only [ce, natDegree_expand]
    omega
  have hde : de.natDegree ≤ 120 := by
    simp only [de, natDegree_expand]
    omega
  have hee : ee.natDegree ≤ 240 := by
    simp only [ee, natDegree_expand]
    omega
  have haE : Ae.coeff 240 ≠ 0 := by
    simpa [Ae, coeff_expand] using ha
  have hbE : Be.coeff 0 ≠ 0 := by
    simpa [Be, coeff_expand] using hb
  have hi4e : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + de) ee = C i4 := by
    have h := congrArg (expand k 60) hi4
    simpa only [Ae, Be, ce, de, ee, expand_C,
      expand_cubicFirstIntegralFourPolynomial68, map_add, map_mul,
      map_smul] using h
  have hi3e : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + de) ee = C i3 := by
    have h := congrArg (expand k 60) hi3
    simpa only [Ae, Be, ce, de, ee, expand_C,
      expand_cubicFirstIntegralThreePolynomial68, map_add, map_mul,
      map_smul] using h
  have hrow0e : secondaryResidualRowZeroPolynomial68 Ae Be ce de ee +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + de) ee = 0 := by
    dsimp only [Ae, Be, ce, de, ee]
    rw [fiveToSix_residualLoadRowZero_expand68, hrow0, map_zero, zero_mul]
  have hrow719 :
      (secondaryResidualRowZeroPolynomial68 Ae Be ce de ee +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + de) ee).coeff 719 = 0 := by
    rw [hrow0e]
    simp
  have hselect := fiveToSix_offsetOneTwenty_wall_source_zeta_zero68
    alpha gamma epsilon zeta eta i4 i3 Ae Be ce de ee haE hbE hAe hBe
      hce hde hee hi4e hi3e hrow719
  have hzeta : zeta = 0 := hselect.1
  have hi4z := hi4
  have hi3z := hi3
  have hrow0z := hrow0
  have hrow1z := hrow1
  have hrow2z := hrow2
  rw [hzeta] at hi4z hi3z hrow0z hrow1z hrow2z
  rcases hselect.2 with hzeroE | hnzE
  · have hzero : d.coeff 2 = 0 ∧ e.coeff 4 = 0 := by
      simpa [de, ee, coeff_expand] using hzeroE
    have hnext := fiveToSix_offsetOneTwenty_ordinary_pairZero_source_packet68
      gamma epsilon i4 i3 Ae Be ce de ee d e haE hbE hAe hBe hce hde hee
      rfl rfl hzeroE (by simpa only [hzeta] using hi4e)
        (by simpa only [hzeta] using hi3e)
    have hd1 : d.natDegree ≤ 1 := by
      have h := hnext.1
      simp only [de, natDegree_expand] at h
      omega
    have he3 : e.natDegree ≤ 3 := by
      have h := hnext.2.1
      simp only [ee, natDegree_expand] at h
      omega
    rcases hnext.2.2 with hzeroNextE | hnzNextE
    · have hzeroNext : d.coeff 1 = 0 ∧ e.coeff 3 = 0 := by
        simpa [de, ee, coeff_expand] using hzeroNextE
      exact False.elim
        (fiveToSix_offsetTwoForty_ordinary_source_closure68
          alpha gamma epsilon eta i4 i3 A B c d e hA hB hc hd1 he3 ha hb
          hzeroNext hi4z hi3z hrow0z hrow1z hrow2z)
    · have hnzNext : B.coeff 0 ≠ 0 ∧ c.coeff 2 ≠ 0 ∧
          d.coeff 1 ≠ 0 ∧ e.coeff 3 ≠ 0 ∧
          A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0 := by
        simpa [Ae, Be, ce, de, ee, coeff_expand] using hnzNextE
      have hcoeff4 := congrArg (fun p : k[X] => p.coeff 180)
        (by simpa only [hzeta] using hi4e)
      rw [cubicFirstIntegralFourPolynomial68_coeff_oneEighty_ordinaryWall68
        gamma epsilon Ae Be ce de ee hAe hBe hce hnext.1 hnext.2.1]
          at hcoeff4
      norm_num [coeff_C] at hcoeff4
      have hfaceE : Be.coeff 0 * ee.coeff 180 +
          ce.coeff 120 * de.coeff 60 = 0 := hcoeff4
      have hface : B.coeff 0 * e.coeff 3 +
          c.coeff 2 * d.coeff 1 = 0 := by
        simpa [Be, ce, de, ee, coeff_expand] using hfaceE
      exact ⟨hzeta, hd1, he3, hnzNext.1, hnzNext.2.1,
        hnzNext.2.2.1, hnzNext.2.2.2.1, hface,
        hnzNext.2.2.2.2⟩
  · have hnz : B.coeff 0 ≠ 0 ∧ c.coeff 2 ≠ 0 ∧
        d.coeff 2 ≠ 0 ∧ e.coeff 4 ≠ 0 ∧
        A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0 := by
      simpa [Ae, Be, ce, de, ee, coeff_expand] using hnzE
    have hrow9 :
        (secondaryResidualRowZeroPolynomial68 A B c d e +
          cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
            A B c ((1 / 3 : k) • (A * B) + d) e).coeff 9 = 0 := by
      rw [hrow0z]
      simp
    exact False.elim
      (fiveToSix_offsetOneTwenty_ordinary_nonzero_source_false68
        alpha gamma epsilon eta i4 A B c d e hA hB hc hd he ha hb
        hnz.2.1 hnz.2.2.1 hnz.2.2.2.1 hnz.2.2.2.2 hi4z hrow9)

#print axioms fiveToSix_residualLoadRowZero_expand68
#print axioms fiveToSix_offsetOneTwenty_ordinary_source_reduction68

end LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryAssembly68

end Max11DegreeRoutes
