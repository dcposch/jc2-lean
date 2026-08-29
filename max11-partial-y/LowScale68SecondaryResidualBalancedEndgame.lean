import LowScale68SecondaryResidualCanonicalBalancedData
import LowScale68SecondaryResidualRowOneFaces
import LowScale68SecondaryResidualRowOneSystem

/-! # The balanced residual row-one contradiction

In the chamber `3g<n`, the canonical residual selector forces `2h=3g`.
The row-two equation then supplies `4*b*c^2-9*d*e=0`, while the next
row-one coefficient is the nonzero scalar
`(-64/9)*(4n-g)*c_top^3`.  The literal row-one load is strictly lower,
so the expanded polynomial lower system is impossible in this chamber.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualBalancedEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

set_option maxHeartbeats 8000000 in
/-- A maximal expanded `(6,8)` polynomial lower system cannot remain in the
residual chamber `3g<n`: row two forces the balanced wall and row one has a
nonzero cubic-face coefficient. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualSmallChamber_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hsmall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * g < n) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let h := secondaryResidualGap68 n d ee
  change 3 * g < n at hsmall
  have hdata := canonicalBalancedResidualData68_of_system
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys (by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change CanonicalBalancedResidualData68 Ae Be ce d ee n g h at hdata
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    calc
      Ee = (1 / 3 : k) • (Ae * Ce) - (2 / 27 : k) • Ae ^ 3 + ee := by
        simpa only [ee] using cubicEDefectPolynomial68_reconstruct Ae Ce Ee
      _ = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
        rw [hCrec]
        apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
        simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
          map_pow, RatFunc.algebraMap_C]
        simp only [map_div₀, map_ofNat, map_one]
        ring
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hrowOne :
      let Crec := (1 / 3 : k) • Ae ^ 2 + ce
      let Drec := (1 / 3 : k) • (Ae * Be) + d
      let Erec := (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee
      lowerRowOnePolynomial68
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Crec Drec
          Erec)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Crec
          Drec Erec)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Crec Drec Erec) Crec Drec Erec = 0 := by
    simp only
    rw [← hCrec, ← hDrec, ← hErec]
    exact h1e
  have hsum := polynomialSecondaryResidualRowOne68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowOne
  have hload := cubicLoadRowOnePolynomial68_degree_lt_cubicFace
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
    hdata.hg hdata.hgh hdata.hsmall hdata.hA hdata.hB hdata.hcdeg
    hdata.hd hdata.he
  exact residualRowOne_add_load_eq_zero_imp_false68
    Ae Be ce d ee
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
    n g h hdata.hg hdata.hgh hdata.hh hdata.hsmall hdata.hbalanced
    hdata.hA hdata.hB hdata.hcdeg hdata.hd hdata.he hdata.hI3 hdata.hc0
    hdata.hdisc hdata.hinc hdata.hrel hload hsum

end SecondaryResidualBalancedEndgame68

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualSmallChamber_impossible68

end Max11DegreeRoutes
