import Astra810ScaleZeroQuarticChamberBCDEFG12Part104Scratch

/-! # The BCDEFG12 scale-zero chamber

The chamber is closed by the tracked Open-II six-face certificate.
The auxiliary N7 + (1/4) A C kappa cancels its load-free face at cost 4s,
where s = 3 deg(A) - 2 deg(B). Its remaining terms give strict bands
for l, beta, delta, zeta, theta, including every load wall. These bands
isolate the kappa, mu, xi, pi, N2 and N6 faces throughout the chamber,
including deg(B) = 0. Every compute_degree target has at most six monomials.

Only the git-tracked Tower module is imported. The proof uses full
polynomial identities and coefficient extraction; there are no new axioms
or finite-root shortcuts. No sub-cells remain open.

The supporting definitions and lemmas live in
`Astra810ScaleZeroQuarticChamberBCDEFG12Part01Scratch` …
`…Part27Scratch`, which this module aggregates; they are byte-identical to
the single-module version and are re-exported transitively, so importers of
this module are unaffected.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
/-- The maximal-tie BCDEFG12 residual chamber is impossible. The auxiliary
`N₇ + (1/4)ACκ` supplies strict load bands, and the six resulting scalar
faces satisfy the tracked Open-II certificate. -/
theorem quarticUnownedCell_rBCDEFG12_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) = Polynomial.C (j / t))
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) : False := by
  have hprim := natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticBCDEFG12_loadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hc hprim homi hnu hkap
  have hk := bcdefg12KappaFace_zero810 l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hkap
  have hm := bcdefg12MuFace_zero810 l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hmu
  have hx := bcdefg12XiFace_zero810 l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hxi
  have hp := bcdefg12PiFace_zero810 l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hpi
  have hn2 := bcdefg12N2Face_zero l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hnu hkap
  have hn6 := bcdefg12N6Face_zero l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hprim homi hnu
  have hAne : A ≠ 0 := by intro hz; have ha := hcone.1; simp [hz] at ha
  exact quarticOpenChamberII810_impossible
    A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff
    hk hm hx hp hn2 hn6
    (leadingCoeff_ne_zero.mpr hAne)
    (leadingCoeff_ne_zero.mpr hc.2.1)
    (leadingCoeff_ne_zero.mpr hc.2.2.1)
    (leadingCoeff_ne_zero.mpr hc.2.2.2.1)
    (leadingCoeff_ne_zero.mpr hc.2.2.2.2.1)
    (leadingCoeff_ne_zero.mpr hc.2.2.2.2.2.1)
    (leadingCoeff_ne_zero.mpr hc.2.2.2.2.2.2.1)

end Max11DegreeRoutes

#print axioms Max11DegreeRoutes.quarticUnownedCell_rBCDEFG12_impossible

