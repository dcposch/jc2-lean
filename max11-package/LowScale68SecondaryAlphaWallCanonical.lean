import LowScale68SecondaryAlphaWall
import LowScale68SecondaryRelaxedCanonical

/-! # Canonical expanded wrapper for the alpha wall `g = n` after `l = 0`

Source input is `IntegratedPolynomialLowerSystem68` on `A,B,C0,D,E`.
After `Ae := expand k 60 A` (and likewise `Be,Ce,De,Ee`), rows two and one
remain zero, but row zero becomes `C terminal * (60 * X^59)`.  Expanded
coordinates therefore must **not** be repackaged as
`IntegratedPolynomialLowerSystem68`.  This wrapper builds the expanded
identities as in `LowScale68SecondaryRelaxedCanonical` and classifies the
wall `g = n`; `alpha` remains free.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlphaWallCanonicalFace68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3000000 in
theorem polynomialSecondaryAlphaWallFace68_of_equations
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3)
    (hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B C0 D)
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) B C0 D E = 0)
    (hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) C0 D E = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) D E).coeff (13 * n - 2 * g - 1) = 0) :
    AlphaWallFace68 (n : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) alpha := by
  have hrel : 2 * g < 3 * n := by omega
  have hinv := polynomialSecondaryInvariantEquations68_of_loadL
    l beta gamma delta epsilon zeta i4 i3 A B C0 c D E e n g
    hn hg hl hrel hA hB hc hD he hC0 hE0 hI4 hI3
  have h2 := hrowTwo
  rw [hC0, hE0] at h2
  have htwo := congrArg
    (fun p : k[X] => p.coeff (11 * n - 2 * g - 1)) h2
  rw [integratedLowerRowTwoPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at htwo
  simp only [coeff_zero] at htwo
  have htwo0 : firstSecondaryTwo68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have htwo0' : firstSecondaryTwo68 (n : k) (n : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
    simpa [hwall] using htwo0
  have h1 := hrowOne
  rw [hC0, hE0] at h1
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 2 * g - 1)) h1
  rw [integratedLowerRowOnePolynomial68_secondaryCoeff_alphaWall
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hwall hA hB hc hD he] at hone
  simp only [coeff_zero] at hone
  have h0 := hrowZero
  rw [hC0, hE0] at h0
  rw [integratedLowerRowZeroPolynomial68_secondaryCoeff_of_loadL
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hl hrel hA hB hc hD he] at h0
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfactor : (8 / 81 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 : firstSecondaryZero68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp h0).resolve_left hfactor
  exact ⟨hinv.1, hinv.2, htwo0', hone, hzero0⟩

theorem polynomialSecondaryAlphaWallClassified68_of_equations
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3)
    (hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B C0 D)
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) B C0 D E = 0)
    (hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) C0 D E = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E) D E).coeff (13 * n - 2 * g - 1) = 0) :
    e.coeff (6 * n - g) = 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) =
        3 * D.coeff (5 * n - g) :=
  alphaWallFace68_classify_of_gap_eq_radius n
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) alpha ha hn
    (polynomialSecondaryAlphaWallFace68_of_equations
      l alpha beta gamma delta epsilon zeta eta i4 i3
      A B C0 c D E e n g hn hg hl hwall hA hB hc hD he ha hC0 hE0
      hI4 hI3 hrowTwo hrowOne hrowZero)

set_option maxHeartbeats 4000000 in
/-- On the canonical expanded system, after `l = 0` on the wall `g = n`,
the first secondary face classifies as `e = 0` and `a*b = 3*d`.  The
parameter `alpha` is unconstrained. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_alphaWallClassified68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl : l = 0)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g = n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change g = n at hwall
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g)
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have hD : De.natDegree ≤ 5 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnlarge : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E hn
  have hrel : 2 * g < 3 * n := by omega
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (13 * n - 2 * g - 1) = 0 :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal _ _ _ _ _ h0e
      (firstSecondaryRowZeroIndex68_gt_fiftyNine n g hnlarge hrel)
  exact polynomialSecondaryAlphaWallClassified68_of_equations
    l alpha beta gamma delta epsilon zeta eta i4 i3
    Ae Be Ce ce De Ee ee n g hn hg hl hwall hA hB hc hD he ha
    hCrec hErec hi4e hi3e h2e h1e h0target

end AlphaWallCanonicalFace68

#print axioms polynomialSecondaryAlphaWallFace68_of_equations
#print axioms polynomialSecondaryAlphaWallClassified68_of_equations
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_alphaWallClassified68

end Max11DegreeRoutes
