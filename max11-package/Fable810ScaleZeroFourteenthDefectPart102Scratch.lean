import Fable810ScaleZeroTwelfthDefectScratch
import Fable810ScaleZeroFourteenthDefectPart101Scratch
import Fable810ScaleZeroFourteenthDefectPart24Scratch

/-! Part 20 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section Depression810FifteenthClearing

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 400000000 in
/-- SPEED (recipe R2, `scripts/coord/LEAN_SPEED_REPORT.md` §7): the weight-`105`
clearing of `ο` carried out on the *atoms* `n_L, …, n_W` rather than on the
expanded source polynomials.  Because `omicronResidual810` is weighted
homogeneous, substituting `X_i = n_i / (d_i h^{e_i})` makes
`2^55 · h^105 · ο` a polynomial in `h, n_L, …, n_W` — 139 monomials. -/
def speedOmicronScaled810 (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    (727947 : F) * h ^ 7 * nL * nA ^ 7
    - (711018 : F) * h ^ 7 * nL * nA ^ 5 * nC
    - (56881440 : F) * h ^ 7 * nL * nA ^ 4 * nB ^ 2
    + (406296 : F) * h ^ 7 * nL * nA ^ 4 * nE
    + (52005888 : F) * h ^ 7 * nL * nA ^ 3 * nB * nD
    + (203148 : F) * h ^ 7 * nL * nA ^ 3 * nC ^ 2
    - (30096 : F) * h ^ 7 * nL * nA ^ 3 * nG
    + (19502208 : F) * h ^ 7 * nL * nA ^ 2 * nB ^ 2 * nC
    - (5778432 : F) * h ^ 7 * nL * nA ^ 2 * nB * nF
    - (180576 : F) * h ^ 7 * nL * nA ^ 2 * nC * nE
    - (11556864 : F) * h ^ 7 * nL * nA ^ 2 * nD ^ 2
    + (104011776 : F) * h ^ 7 * nL * nA * nB ^ 4
    - (5778432 : F) * h ^ 7 * nL * nA * nB ^ 2 * nE
    - (11556864 : F) * h ^ 7 * nL * nA * nB * nC * nD
    - (15048 : F) * h ^ 7 * nL * nA * nC ^ 3
    + (9504 : F) * h ^ 7 * nL * nA * nC * nG
    + (2433024 : F) * h ^ 7 * nL * nA * nD * nF
    + (38016 : F) * h ^ 7 * nL * nA * nE ^ 2
    - (61636608 : F) * h ^ 7 * nL * nB ^ 3 * nD
    - (722304 : F) * h ^ 7 * nL * nB ^ 2 * nC ^ 2
    + (152064 : F) * h ^ 7 * nL * nB ^ 2 * nG
    + (608256 : F) * h ^ 7 * nL * nB * nC * nF
    + (2433024 : F) * h ^ 7 * nL * nB * nD * nE
    + (9504 : F) * h ^ 7 * nL * nC ^ 2 * nE
    + (1216512 : F) * h ^ 7 * nL * nC * nD ^ 2
    - (3456 : F) * h ^ 7 * nL * nE * nG
    - (110592 : F) * h ^ 7 * nL * nF ^ 2
    + (11323620 : F) * nA ^ 6 * nB
    - (737352 : F) * nA ^ 6 * nQ
    - (2528064 : F) * nA ^ 5 * nB * nP
    - (6320160 : F) * nA ^ 5 * nD
    + (90288 : F) * nA ^ 5 * nS
    - (7900200 : F) * nA ^ 4 * nB * nC
    + (1083456 : F) * nA ^ 4 * nB * nR
    + (632016 : F) * nA ^ 4 * nC * nQ
    + (1444608 : F) * nA ^ 4 * nD * nP
    + (902880 : F) * nA ^ 4 * nF
    - (40128 : F) * nA ^ 4 * nU
    - (168537600 : F) * nA ^ 3 * nB ^ 3
    + (40449024 : F) * nA ^ 3 * nB ^ 2 * nQ
    + (1444608 : F) * nA ^ 3 * nB * nC * nP
    + (3611520 : F) * nA ^ 3 * nB * nE
    - (214016 : F) * nA ^ 3 * nB * nT
    + (3611520 : F) * nA ^ 3 * nC * nD
    - (66880 : F) * nA ^ 3 * nC * nS
    - (642048 : F) * nA ^ 3 * nD * nR
    - (374528 : F) * nA ^ 3 * nE * nQ
    - (214016 : F) * nA ^ 3 * nF * nP
    + (1408 : F) * nA ^ 3 * nW
    + (23113728 : F) * nA ^ 2 * nB ^ 3 * nP
    + (173352960 : F) * nA ^ 2 * nB ^ 2 * nD
    - (3210240 : F) * nA ^ 2 * nB ^ 2 * nS
    + (1354320 : F) * nA ^ 2 * nB * nC ^ 2
    - (481536 : F) * nA ^ 2 * nB * nC * nR
    - (35954688 : F) * nA ^ 2 * nB * nD * nQ
    - (642048 : F) * nA ^ 2 * nB * nE * nP
    - (200640 : F) * nA ^ 2 * nB * nG
    + (16896 : F) * nA ^ 2 * nB * nV
    - (140448 : F) * nA ^ 2 * nC ^ 2 * nQ
    - (642048 : F) * nA ^ 2 * nC * nD * nP
    - (401280 : F) * nA ^ 2 * nC * nF
    + (25344 : F) * nA ^ 2 * nC * nU
    - (1605120 : F) * nA ^ 2 * nD * nE
    + (135168 : F) * nA ^ 2 * nD * nT
    + (42240 : F) * nA ^ 2 * nE * nS
    + (101376 : F) * nA ^ 2 * nF * nR
    + (29568 : F) * nA ^ 2 * nG * nQ
    + (28892160 : F) * nA * nB ^ 3 * nC
    - (5136384 : F) * nA * nB ^ 3 * nR
    - (8988672 : F) * nA * nB ^ 2 * nC * nQ
    - (20545536 : F) * nA * nB ^ 2 * nD * nP
    - (12840960 : F) * nA * nB ^ 2 * nF
    + (811008 : F) * nA * nB ^ 2 * nU
    - (160512 : F) * nA * nB * nC ^ 2 * nP
    - (802560 : F) * nA * nB * nC * nE
    + (67584 : F) * nA * nB * nC * nT
    - (51363840 : F) * nA * nB * nD ^ 2
    + (2703360 : F) * nA * nB * nD * nS
    + (202752 : F) * nA * nB * nE * nR
    + (3784704 : F) * nA * nB * nF * nQ
    + (33792 : F) * nA * nB * nG * nP
    - (401280 : F) * nA * nC ^ 2 * nD
    + (10560 : F) * nA * nC ^ 2 * nS
    + (202752 : F) * nA * nC * nD * nR
    + (118272 : F) * nA * nC * nE * nQ
    + (67584 : F) * nA * nC * nF * nP
    - (768 : F) * nA * nC * nW
    + (7569408 : F) * nA * nD ^ 2 * nQ
    + (270336 : F) * nA * nD * nE * nP
    + (84480 : F) * nA * nD * nG
    - (12288 : F) * nA * nD * nV
    + (168960 : F) * nA * nE * nF
    - (18432 : F) * nA * nE * nU
    - (24576 : F) * nA * nF * nT
    - (3840 : F) * nA * nG * nS
    + (46227456 : F) * nB ^ 5
    - (23969792 : F) * nB ^ 4 * nQ
    - (1712128 : F) * nB ^ 3 * nC * nP
    - (4280320 : F) * nB ^ 3 * nE
    + (360448 : F) * nB ^ 3 * nT
    - (12840960 : F) * nB ^ 2 * nC * nD
    + (337920 : F) * nB ^ 2 * nC * nS
    + (3244032 : F) * nB ^ 2 * nD * nR
    + (1892352 : F) * nB ^ 2 * nE * nQ
    + (1081344 : F) * nB ^ 2 * nF * nP
    - (12288 : F) * nB ^ 2 * nW
    - (33440 : F) * nB * nC ^ 3
    + (25344 : F) * nB * nC ^ 2 * nR
    + (3784704 : F) * nB * nC * nD * nQ
    + (67584 : F) * nB * nC * nE * nP
    + (21120 : F) * nB * nC * nG
    - (3072 : F) * nB * nC * nV
    + (4325376 : F) * nB * nD ^ 2 * nP
    + (5406720 : F) * nB * nD * nF
    - (589824 : F) * nB * nD * nU
    + (84480 : F) * nB * nE ^ 2
    - (24576 : F) * nB * nE * nT
    - (245760 : F) * nB * nF * nS
    - (9216 : F) * nB * nG * nR
    + (4928 : F) * nC ^ 3 * nQ
    + (33792 : F) * nC ^ 2 * nD * nP
    + (21120 : F) * nC ^ 2 * nF
    - (2304 : F) * nC ^ 2 * nU
    + (168960 : F) * nC * nD * nE
    - (24576 : F) * nC * nD * nT
    - (7680 : F) * nC * nE * nS
    - (18432 : F) * nC * nF * nR
    - (5376 : F) * nC * nG * nQ
    + (3604480 : F) * nD ^ 3
    - (491520 : F) * nD ^ 2 * nS
    - (73728 : F) * nD * nE * nR
    - (1376256 : F) * nD * nF * nQ
    - (12288 : F) * nD * nG * nP
    - (21504 : F) * nE ^ 2 * nQ
    - (24576 : F) * nE * nF * nP
    + (1024 : F) * nE * nW
    - (7680 : F) * nF * nG
    + (4096 : F) * nF * nV
    + (3072 : F) * nG * nU


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 23 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section DepressedRow810Fifteenth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]


/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`2` Jacobian coefficient is
exactly `3 U G' + 2 V F' + W E'
- F V' - 2 E W' - 3 D X'`. -/
theorem differentialJacobian_coeff_2_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 2 =
      (3 : F) * g.coeff 3 * d (f.coeff 0) +
        (2 : F) * g.coeff 2 * d (f.coeff 1) +
        g.coeff 1 * d (f.coeff 2) -
          f.coeff 1 * d (g.coeff 2) -
          (2 : F) * f.coeff 2 * d (g.coeff 1) -
          (3 : F) * f.coeff 3 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal (2 : ℕ) :
      Finset (ℕ × ℕ)) =
      ({(0, 2), (1, 1),
        (2, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne02_11 : ((0, 2) : ℕ × ℕ) ≠ (1, 1) := by decide
  have hne02_20 : ((0, 2) : ℕ × ℕ) ≠ (2, 0) := by decide
  have hne11_20 : ((1, 1) : ℕ × ℕ) ≠ (2, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 2 =
        (3 : F) * g.coeff 3 * d (f.coeff 0) +
          (2 : F) * g.coeff 2 * d (f.coeff 1) +
          g.coeff 1 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne02_11, hne02_20]),
        Finset.sum_insert (by simp [hne11_20]),
        Finset.sum_singleton]
      ring
    have hder2 : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0 : g.derivative.coeff 0 = g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder2, hder1, hder0]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 2 =
        f.coeff 1 * d (g.coeff 2) +
          (2 : F) * f.coeff 2 * d (g.coeff 1) +
          (3 : F) * f.coeff 3 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne02_11, hne02_20]),
        Finset.sum_insert (by simp [hne11_20]),
        Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; simp
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder2]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring


end DepressedRow810Fifteenth
end Max11DegreeRoutes
end
/-! Part 18 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section Depression810FifteenthClearing

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 16000000 in
def localClearedFifteenthDefectCore810
    {R : Type*} [CommRing R]
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda : R) : R :=
    localClearedFifteenthDefectBlock0_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock1_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock2_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock3_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock4_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock5_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock6_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock7_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock8_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock9_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock10_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock11_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock12_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock13_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    + localClearedFifteenthDefectBlock14_810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda


end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 26 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section ScaleZeroFourteenthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false


/-! ## Degree-`2` source Jacobian row -/

/-- Source-facing degree-`2` Jacobian row of a normalized scale-zero
`(8,10)` pair. -/
theorem normalized810ScaleZero_fifteenthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : k)) -
      ((p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp8, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using
    fableScaleZero_fifteenthCoefficientJacobianRow_raw_810 hp hq hjac


end ScaleZeroFourteenthDefect810
end Max11DegreeRoutes
end
/-! Part 27 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section ScaleZeroFourteenthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false


/-- At scale zero the common core is constant, so the leading octic
coefficient of the degree-`2` row is a differential constant. -/
theorem scaleZero_fifteenthCoefficientJacobianRow_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : k)) -
      ((p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) =
      0 := by
  have hrow :=
    fableScaleZero_fifteenthCoefficientJacobianRow_raw_810 hp hq hjac
  simpa using hrow


end ScaleZeroFourteenthDefect810
end Max11DegreeRoutes
end
/-! Part 29 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section ScaleZeroFourteenthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false


/-! ## Degree-`2` monic Jacobian row -/

/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`2` Jacobian coefficient
is exactly
`3 U G' + 2 V F' + W E'
- F V' - 2 E W' - 3 D X'`.
Here `A = f.coeff 6`, `B = f.coeff 5`, `C = f.coeff 4`, `D = f.coeff 3`,
`E = f.coeff 2`, `F = f.coeff 1`, `G = f.coeff 0`, `L = g.coeff 9`,
`P = g.coeff 8`, `Q = g.coeff 7`, `R = g.coeff 6`, `S = g.coeff 5`,
`T = g.coeff 4`, `U = g.coeff 3`, `V = g.coeff 2`, `W = g.coeff 1`,
and `X = g.coeff 0`. -/
theorem scaleZero_monicOcticDecic_degree2Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 2 =
      (3 : F) * g.coeff 3 * d (f.coeff 0) +
        (2 : F) * g.coeff 2 * d (f.coeff 1) +
        g.coeff 1 * d (f.coeff 2) -
          f.coeff 1 * d (g.coeff 2) -
          (2 : F) * f.coeff 2 * d (g.coeff 1) -
          (3 : F) * f.coeff 3 * d (g.coeff 0) :=
  differentialJacobian_coeff_2_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL


end ScaleZeroFourteenthDefect810
end Max11DegreeRoutes
end
/-! Part 19 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section Depression810FifteenthClearing

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 16000000 in
/-- Polynomial numerator of `36028797018963968 h¹⁰⁵ ο` on the
ninth-power face.  The large literal is blocked above to keep elaboration
linear. -/
def localClearedFifteenthDefect810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X])
    (lambda : F) : F[X] :=
  localClearedFifteenthDefectCore810 h a7 a6 a5 a4 a3 a2 a1 a0
    b8 b7 b6 b5 b4 b3 b2 b1 (Polynomial.C lambda)



end Depression810FifteenthClearing
end Max11DegreeRoutes
end
/-! Part 28 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section ScaleZeroFourteenthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false


/-- Source-facing scale-zero collapse of the degree-`2` row. -/
theorem normalized810ScaleZero_fifteenthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : k)) -
      ((p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using
    scaleZero_fifteenthCoefficientJacobianRow_810 hp hq hjac hHdegree
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)



end ScaleZeroFourteenthDefect810
end Max11DegreeRoutes
end
/-! Part 30 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section ScaleZeroFourteenthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false


/-- The same row integrates: if the degree-`8`, degree-`7`, degree-`6`,
degree-`5`, degree-`4`, and degree-`2` Jacobian rows vanish, `L` is
constant, and the residuals `α, β, γ, δ, ε, ζ, η, θ, ι` are constant,
then the next residual `ο` is a differential constant. -/
theorem scaleZero_omicronResidual_deriv_zero_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0)
    (heta : d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) = 0)
    (htheta : d (thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0) = 0)
    (hiota : d (iotaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0) = 0)
    (hrow8 : (9 : F) * L * d G0 + (8 : F) * P * d F0 +
        (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A -
        F0 * d P - (2 : F) * E0 * d Q -
        (3 : F) * D0 * d R - (4 : F) * C0 * d S0 -
        (5 : F) * B * d T0 - (6 : F) * A * d U0 -
        (8 : F) * d W0 = 0)
    (hrow7 : (8 : F) * P * d G0 + (7 : F) * Q * d F0 +
        (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A -
        F0 * d Q - (2 : F) * E0 * d R -
        (3 : F) * D0 * d S0 - (4 : F) * C0 * d T0 -
        (5 : F) * B * d U0 - (6 : F) * A * d V0 -
        (8 : F) * d X0 = 0)
    (hrow6 : (7 : F) * Q * d G0 + (6 : F) * R * d F0 +
        (5 : F) * S0 * d E0 + (4 : F) * T0 * d D0 +
        (3 : F) * U0 * d C0 + (2 : F) * V0 * d B +
        W0 * d A -
        F0 * d R - (2 : F) * E0 * d S0 -
        (3 : F) * D0 * d T0 - (4 : F) * C0 * d U0 -
        (5 : F) * B * d V0 - (6 : F) * A * d W0 = 0)
    (hrow5 : (6 : F) * R * d G0 + (5 : F) * S0 * d F0 +
        (4 : F) * T0 * d E0 + (3 : F) * U0 * d D0 +
        (2 : F) * V0 * d C0 + W0 * d B -
        F0 * d S0 - (2 : F) * E0 * d T0 -
        (3 : F) * D0 * d U0 - (4 : F) * C0 * d V0 -
        (5 : F) * B * d W0 - (6 : F) * A * d X0 = 0)
    (hrow4 : (5 : F) * S0 * d G0 + (4 : F) * T0 * d F0 +
        (3 : F) * U0 * d E0 + (2 : F) * V0 * d D0 +
        W0 * d C0 -
        F0 * d T0 - (2 : F) * E0 * d U0 -
        (3 : F) * D0 * d V0 - (4 : F) * C0 * d W0 -
        (5 : F) * B * d X0 = 0)
    (hrow : (3 : F) * U0 * d G0 + (2 : F) * V0 * d F0 +
        W0 * d E0 -
        F0 * d V0 - (2 : F) * E0 * d W0 -
        (3 : F) * D0 * d X0 = 0) :
    d (omicronResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 :=
  omicronResidual810_deriv_zero d L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta hiota hrow8
    hrow7 hrow6 hrow5 hrow4 hrow


end ScaleZeroFourteenthDefect810
end Max11DegreeRoutes
end
