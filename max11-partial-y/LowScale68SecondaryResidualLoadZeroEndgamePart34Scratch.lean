import LowScale68SecondaryResidualLoadZeroEndgamePart33Scratch

/-! # Residual endgame on the `(6,8)` strip `2g<n` after `l=0`

The tracked residual selector/endgame closes `3g<n`.  After `l=0` every
`A^4`/`A^5` Jacobian load vanishes, so the residual walls `8n<9n-3g` and
`10n<11n-3g` hold throughout `g<n`.  This module replays the precise
invariant/load and row-two/row-one degree cutoffs needed by the tracked
middle/selector/descent/row-two/balanced/row-one/endgame chain under the
weaker chamber `l=0` and `2g<n`, then excludes that whole strip.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ResidualLoadZeroEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Shared derivative degree helper -/

/-! ## Load cutoffs after `l=0` -/

/-! ## Homogeneous residual coefficients under `2g<n` -/

/-! ## Double-face extraction and selector under `l=0`, `2g<n` -/

/-! ## Row-two trichotomy, balanced relation, and row-one endgame -/

set_option maxHeartbeats 8000000 in
/-- After `l=0`, the residual chamber `2g<n` is impossible: the selected
gap is balanced and residual row one has a nonzero cubic-face coefficient. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl0 : l = 0)
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
      2 * g < n) :
    False := by
  subst hl0
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
  have hdata := loadZeroBalancedResidualData68_of_system
    alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys (by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change LoadZeroBalancedResidualData68 Ae Be ce d ee n g h at hdata
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
      (integratedTPolynomial68 0 alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
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
        (integratedTPolynomial68 0 alpha beta gamma epsilon Ae Be Crec Drec
          Erec)
        (integratedUPolynomial68 0 alpha beta gamma delta zeta Ae Be Crec
          Drec Erec)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          Ae Be Crec Drec Erec) Crec Drec Erec = 0 := by
    simp only
    rw [← hCrec, ← hDrec, ← hErec]
    exact h1e
  have hsum := polynomialSecondaryResidualRowOne68
    0 alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowOne
  have hload := cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_twoGap
    0 alpha beta gamma delta epsilon zeta eta Ae Be ce d ee n g h
    hdata.hg hdata.hgh hdata.hsmall hdata.hA hdata.hB hdata.hcdeg
    hdata.hd hdata.he
  exact residualRowOne_add_load_eq_zero_imp_false68_of_twoGap
    Ae Be ce d ee
    (cubicLoadRowOnePolynomial68 0 alpha beta gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
    n g h hdata.hg hdata.hgh hdata.hh hdata.hsmall hdata.hbalanced
    hdata.hA hdata.hB hdata.hcdeg hdata.hd hdata.he hdata.hI3 hdata.hc0
    hdata.hdisc hdata.hinc hdata.hrel hload hsum

end ResidualLoadZeroEndgame68
end Max11DegreeRoutes
