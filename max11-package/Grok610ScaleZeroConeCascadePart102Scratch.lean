import Grok610ScaleZeroConeCascadePart101Scratch
import Grok610ScaleZeroConeCascadeSpeedTPart00Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighACone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveHighARest610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : UniqueHighACone610 A B C0 D0 E0) :
    (degreeZeroPrimitiveHighARest610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  have hbase :
      (degreeZeroBaseGroupHighARest610 l A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroBaseGroupHighARest610 l A B C0 D0 E0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have halpha :
      (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have hbeta :
      (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have hdelta :
      (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroDeltaGroupPolynomial610 A B C0 D0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have hepsilon :
      (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroEpsilonGroupPolynomial610 A B C0 D0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have hzeta :
      (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroZetaGroupPolynomial610 A B C0 D0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have heta :
      (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroEtaGroupPolynomial610 A B C0 D0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have htheta :
      (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroThetaGroupPolynomial610 A B C0 E0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  simp only [degreeZeroPrimitiveHighARest610]
  exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
    (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
    (natDegree_smul_lt610 epsilon hepsilon) (natDegree_smul_lt610 zeta hzeta)
    (natDegree_smul_lt610 eta heta) (natDegree_smul_lt610 theta htheta)

end HighACone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighBAndDCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitivePolynomial610_eq_B5_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(36864 / 2239488 : k)) • B ^ 5 +
        degreeZeroPrimitiveHighBRest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighBRest610, degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighBRest610]
  module

end HighBAndDCone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighBAndDCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitivePolynomial610_eq_D3_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      (-(829440 / 2239488 : k)) • D0 ^ 3 +
        degreeZeroPrimitiveHighDRest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610,
    degreeZeroPrimitiveHighDRest610, degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupHighDRest610]
  module

end HighBAndDCone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section SourcePrimitiveDegree610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Source-facing polynomial trajectory: the free core has representatives
in `k[x]`, the integrated primitive is a polynomial in those letters, and
that polynomial has derivative `C (j / t)` hence Newton degree one. -/
theorem normalized610ScaleZero_exists_primitivePolynomial
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      nonzeroLocalClearedFourteenthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C omicron ∧
      let hRF : RatFunc k := RatFunc.C t
      let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)
      let g : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 q)
      algebraMap k[X] (RatFunc k) A = f.coeff 4 ∧
        algebraMap k[X] (RatFunc k) B = f.coeff 3 ∧
        algebraMap k[X] (RatFunc k) C0 = f.coeff 2 ∧
        algebraMap k[X] (RatFunc k) D0 = f.coeff 1 ∧
        algebraMap k[X] (RatFunc k) E0 = f.coeff 0 ∧
        g.coeff 9 = RatFunc.C l ∧
        g.coeff 8 = integratedP610 (algebraMap k[X] (RatFunc k) A)
          (RatFunc.C alpha) ∧
        g.coeff 7 = integratedQ610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B) (RatFunc.C beta) ∧
        g.coeff 6 = integratedR610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (RatFunc.C alpha) (RatFunc.C gamma) ∧
        g.coeff 5 = integratedS610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta) ∧
        g.coeff 4 = integratedT610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C epsilon) ∧
        g.coeff 3 = integratedU610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C delta) (RatFunc.C zeta) ∧
        g.coeff 2 = integratedV610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C eta) ∧
        g.coeff 1 = integratedW610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
          (RatFunc.C theta) ∧
        g.coeff 0 = integratedX610 (g.coeff 9)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
          (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
          (RatFunc.C eta) (RatFunc.C iota) ∧
        derivative
            (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
              zeta eta theta A B C0 D0 E0) =
          C (j / t) ∧
        (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
            eta theta A B C0 D0 E0).natDegree =
          1 := by
  dsimp only
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, ht, hj, hjdiv, hHsq, hrow, homicron,
      htraj⟩ :=
    normalized610ScaleZero_exists_integratedTrajectory hsource
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  let hRF : RatFunc k := RatFunc.C t
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 q)
  obtain ⟨hAmap, hBmap, hCmap, hDmap, hEmap⟩ :=
    constantScale_monicSextic_polynomialCore610 p t ht
  let r0 : k[X] := C ((6 * t ^ 5)⁻¹) * p.coeff 5
  let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
  let A : k[X] := p0.coeff 4
  let B : k[X] := p0.coeff 3
  let C0 : k[X] := p0.coeff 2
  let D0 : k[X] := p0.coeff 1
  let E0 : k[X] := p0.coeff 0
  have hA : algebraMap k[X] (RatFunc k) A = f.coeff 4 := by
    dsimp only [A, p0, r0, f, hRF, a5]
    exact hAmap
  have hB : algebraMap k[X] (RatFunc k) B = f.coeff 3 := by
    dsimp only [B, p0, r0, f, hRF, a5]
    exact hBmap
  have hC : algebraMap k[X] (RatFunc k) C0 = f.coeff 2 := by
    dsimp only [C0, p0, r0, f, hRF, a5]
    exact hCmap
  have hD : algebraMap k[X] (RatFunc k) D0 = f.coeff 1 := by
    dsimp only [D0, p0, r0, f, hRF, a5]
    exact hDmap
  have hE : algebraMap k[X] (RatFunc k) E0 = f.coeff 0 := by
    dsimp only [E0, p0, r0, f, hRF, a5]
    exact hEmap
  obtain ⟨hl, hP, hQ, hR, hS, hT, hU, hV, hW, hX, hprim⟩ := htraj
  have hP' : g.coeff 8 =
      integratedP610 (algebraMap k[X] (RatFunc k) A)
        (RatFunc.C alpha) := by
    simpa [hA] using hP
  have hQ' : g.coeff 7 =
      integratedQ610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B) (RatFunc.C beta) := by
    simpa [hA, hB] using hQ
  have hR' : g.coeff 6 =
      integratedR610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (RatFunc.C alpha) (RatFunc.C gamma) := by
    simpa [hA, hB, hC] using hR
  have hS' : g.coeff 5 =
      integratedS610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta) := by
    simpa [hA, hB, hC, hD] using hS
  have hT' : g.coeff 4 =
      integratedT610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C epsilon) := by
    simpa [hA, hB, hC, hD, hE] using hT
  have hU' : g.coeff 3 =
      integratedU610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C zeta) := by
    simpa [hA, hB, hC, hD, hE] using hU
  have hV' : g.coeff 2 =
      integratedV610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C eta) := by
    simpa [hA, hB, hC, hD, hE] using hV
  have hW' : g.coeff 1 =
      integratedW610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C theta) := by
    simpa [hA, hB, hC, hD, hE] using hW
  have hX' : g.coeff 0 =
      integratedX610 (g.coeff 9) (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C iota) := by
    simpa [hA, hB, hC, hD, hE] using hX
  let prim : k[X] :=
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
      theta A B C0 D0 E0
  have hprimRF :
      degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) (g.coeff 0) =
        degreeZeroIntegratedPrimitive610 (RatFunc.C l)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
          (RatFunc.C theta) := by
    rw [← hA, ← hB, ← hC, ← hD, ← hE, hP', hQ', hR', hS', hT', hU',
      hV', hW', hX', hl]
    exact
      degreeZeroPrimitive610_eq_integratedPrimitive (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C theta) (RatFunc.C iota)
  have hmap :
      algebraMap k[X] (RatFunc k) prim =
        degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) (g.coeff 0) := by
    rw [hprimRF]
    exact algebraMap_degreeZeroPrimitivePolynomial610 l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0
  have hder :
      algebraMap k[X] (RatFunc k) (derivative prim) =
        algebraMap k[X] (RatFunc k) (C (j / t)) := by
    rw [← ratFuncDerivation46_polynomial]
    have hderiv :
        Differential.deriv (algebraMap k[X] (RatFunc k) prim) =
          RatFunc.C (j / t) := by
      rw [hmap]
      exact hprim
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply,
      RatFunc.algebraMap_C] using hderiv
  have hpolyder : derivative prim = C (j / t) :=
    (RatFunc.algebraMap_injective k) hder
  have hdeg : prim.natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 prim (j / t) hjdiv
      hpolyder
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq, ?_,
    ?_, ?_⟩
  · simpa [p, q] using hrow
  · simpa [p, q] using homicron
  · exact ⟨hA, hB, hC, hD, hE, hl, hP', hQ', hR', hS', hT', hU', hV',
      hW', hX', hpolyder, hdeg⟩

end SourcePrimitiveDegree610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighACone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem uniqueHighA_impossible_of_l_ne610
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hl : l ≠ 0) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A B C0 D0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (-(10935 / 2239488 * l : k)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl)
  have hlead :
      ((-(10935 / 2239488 * l : k)) • A ^ 7).natDegree =
        7 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroPrimitiveHighARest610_natDegree_lt l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroPrimitivePolynomial610_eq_A7_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by
      rwa [hlead])] at hdeg
  rw [hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

end HighACone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighACone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem uniqueHighA_impossible_of_l_zero_B_pos610
    (alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A B C0 D0 E0)
    (hBpos : 0 < B.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  have hc : (-(62720 / 2239488 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(62720 / 2239488 : k)) • (A ^ 6 * B)).natDegree =
        6 * A.natDegree + B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 6 hA) hBne,
      natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighA_noA6B_Rest610 0 alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0).natDegree <
        6 * A.natDegree + B.natDegree := by
    rcases hcone with ⟨hApos, hBlt, hC, hD, hE⟩
    have hbase :
        (degreeZeroBaseGroupHighA_noA6B_Rest610 0 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBaseGroupHighA_noA6B_Rest610 0 A B C0 D0 E0).trans_lt ?_
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).trans_lt ?_
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).trans_lt ?_
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroDeltaGroupPolynomial610 A B C0 D0).trans_lt ?_
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEpsilonGroupPolynomial610 A B C0 D0).trans_lt ?_
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroZetaGroupPolynomial610 A B C0 D0).trans_lt ?_
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          6 * A.natDegree + B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEtaGroupPolynomial610 A B C0 D0).trans_lt ?_
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          6 * A.natDegree + B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroThetaGroupPolynomial610 A B C0 E0).trans_lt ?_
      clear * - hApos hBpos hBlt hC hD hE
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    simp only [degreeZeroPrimitiveHighA_noA6B_Rest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_A6B_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

end HighACone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighACone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem uniqueHighA_impossible_of_l_zero_B_zero_beta_ne
    (alpha beta delta epsilon zeta eta theta j : k)
    (A C0 D0 E0 : k[X]) (hj : j ≠ 0) (hbeta : beta ≠ 0)
    (hcone : UniqueHighACone610 A 0 C0 D0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon
            zeta eta theta A 0 C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta
          eta theta A 0 C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (2695 / 559872 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hbeta
  have hlead :
      ((2695 / 559872 * beta : k) • A ^ 6).natDegree =
        6 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighA_B0_noA6_Rest610 0 alpha beta delta epsilon
          zeta eta theta A C0 D0 E0).natDegree <
        6 * A.natDegree := by
    rcases hcone with ⟨hApos, _, hC, hD, hE⟩
    have hbase :
        (degreeZeroBaseGroupHighA_noA6B_Rest610 0 A 0 C0 D0 E0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBaseGroupHighA_noA6B_Rest610 0 A 0 C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A 0 C0 D0 E0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroAlphaGroupPolynomial610 A 0 C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hbetaG :
        (degreeZeroBetaGroupNoA6Polynomial610 A 0 C0 D0 E0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBetaGroupNoA6Polynomial610 A 0 C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroDeltaGroupPolynomial610 A 0 C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEpsilonGroupPolynomial610 A 0 C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroZetaGroupPolynomial610 A 0 C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEtaGroupPolynomial610 A 0 C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A 0 C0 E0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroThetaGroupPolynomial610 A 0 C0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    simp only [degreeZeroPrimitiveHighA_B0_noA6_Rest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbetaG) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_betaA6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

end HighACone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighBAndDCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem extremeHighB_impossible
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : ExtremeHighBCone610 A B C0 D0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, hAB, hA7⟩
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  have hc : (-(36864 / 2239488 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(36864 / 2239488 : k)) • B ^ 5).natDegree =
        5 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighBRest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree <
        5 * B.natDegree := by
    have hbase :
        (degreeZeroBaseGroupHighBRest610 l A B C0 D0 E0).natDegree <
          5 * B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBaseGroupHighBRest610 l A B C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          5 * B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          5 * B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroDeltaGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEpsilonGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroZetaGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEtaGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          5 * B.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroThetaGroupPolynomial610 A B C0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    simp only [degreeZeroPrimitiveHighBRest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_B5_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end HighBAndDCone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighBAndDCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- If `D₀` is the only nonconstant free-core letter, the face `D₀³` has
degree at least three. -/
theorem uniqueNonconstantD0_impossible
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hDpos : 0 < D0.natDegree)
    (hE : E0.natDegree = 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hDne : D0 ≠ 0 := by
    intro hD0
    simp [hD0] at hDpos
  have hc : (-(829440 / 2239488 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(829440 / 2239488 : k)) • D0 ^ 3).natDegree =
        3 * D0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighDRest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree <
        3 * D0.natDegree := by
    have hbase :
        (degreeZeroBaseGroupHighDRest610 l A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBaseGroupHighDRest610 l A B C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          3 * D0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroDeltaGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEpsilonGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroZetaGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          3 * D0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEtaGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          3 * D0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroThetaGroupPolynomial610 A B C0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    simp only [degreeZeroPrimitiveHighDRest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_D3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end HighBAndDCone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighBAndDCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- If `E₀` is the only nonconstant free-core letter and `β ≠ 0`, the
face `β E₀²` has degree at least two. -/
theorem uniqueNonconstantE0_impossible_of_beta_ne
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0) (hbeta : beta ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hEpos : 0 < E0.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hEne : E0 ≠ 0 := by
    intro hE0
    simp [hE0] at hEpos
  have hc : (326592 / 559872 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hbeta
  have hlead :
      ((326592 / 559872 * beta : k) • E0 ^ 2).natDegree =
        2 * E0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighERest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree <
        2 * E0.natDegree := by
    have hbase :
        (degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0).natDegree <
          2 * E0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          2 * E0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hbetaG :
        (degreeZeroBetaGroupNoE2Polynomial610 A B C0 D0 E0).natDegree <
          2 * E0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBetaGroupNoE2Polynomial610 A B C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroDeltaGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEpsilonGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroZetaGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEtaGroupPolynomial610 A B C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          2 * E0.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroThetaGroupPolynomial610 A B C0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    simp only [degreeZeroPrimitiveHighERest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbetaG) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_betaE2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end HighBAndDCone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighBAndDCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- If `B` is the only nonconstant free-core letter, the face `B⁵` has
degree at least five. -/
theorem uniqueNonconstantB_impossible
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hBpos : 0 < B.natDegree)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hcone : ExtremeHighBCone610 A B C0 D0 E0 := by
    refine ⟨⟨hBpos, hA.symm ▸ hBpos, hC.symm ▸ hBpos, hD.symm ▸ hBpos,
        hE.symm ▸ hBpos⟩, ?_, ?_⟩
    · omega
    · omega
  exact extremeHighB_impossible l alpha beta delta epsilon zeta eta theta
    j A B C0 D0 E0 hj hcone hder

end HighBAndDCone610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Residual610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Exact residual of the scale-zero cone cascade.

The free core has polynomial representatives, the integrated primitive
has Newton degree one, a constant core is impossible, the unique-`A`
cone is empty except the two leftover chambers `L = 0` with `B`
constant (and `β = 0` if `B = 0`), the extreme unique-`B` cone
`3 deg A < 2 deg B` with `7 deg A < 5 deg B` is empty, a unique
nonconstant `B` or `D₀` is empty, and a unique nonconstant `E₀` with
`β ≠ 0` is empty.

The leaf is not closed.  A nonconstant polynomial core remains in which
either two or more letters share the maximal degree, or else `A`
uniquely leads with `L = 0` and `B` a constant, and in the `B = 0`
chamber also `β = 0`, or else `E₀` is the unique nonconstant letter
with `β = 0`.  The already-constant first integrals `κ, λ, μ` and the
weight-seventy residual `ο` are not consumed. -/
theorem normalized610ScaleZero_coneCascadeResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C (j / t) ∧
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      (UniqueHighACone610 A B C0 D0 E0 →
        l = 0 ∧ B.natDegree = 0 ∧ (B = 0 → beta = 0)) ∧
      ¬ ExtremeHighBCone610 A B C0 D0 E0 ∧
      ¬ (A.natDegree = 0 ∧ 0 < B.natDegree ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ 0 < E0.natDegree ∧ beta ≠ 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
      _hrow, _homicron, hcore⟩ :=
    normalized610ScaleZero_exists_primitivePolynomial hsource
  obtain ⟨hA, hB, hC, hD, hE, hl, hP, hQ, hR, hS, hT, hU, hV, hW, hX,
      hder, hdeg⟩ := hcore
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq, hder,
    hdeg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hconst
    exact degreeZeroPrimitivePolynomial610_false_of_constant_core
      l alpha beta delta epsilon zeta eta theta (j / t) A B C0 D0 E0
      hjdiv hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.1
      hconst.2.2.2.2 hder
  · intro hcone
    refine ⟨?_, ?_, ?_⟩
    · by_contra hlne
      exact uniqueHighA_impossible_of_l_ne610 l alpha beta delta epsilon
        zeta eta theta (j / t) A B C0 D0 E0 hlne hjdiv hcone hder
    · by_contra hBpos
      have hpos : 0 < B.natDegree := Nat.pos_of_ne_zero hBpos
      have hl0 : l = 0 := by
        by_contra hlne
        exact uniqueHighA_impossible_of_l_ne610 l alpha beta delta epsilon
          zeta eta theta (j / t) A B C0 D0 E0 hlne hjdiv hcone hder
      subst hl0
      exact uniqueHighA_impossible_of_l_zero_B_pos610 alpha beta delta
        epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hcone hpos hder
    · intro hB0
      by_contra hbetane
      have hl0 : l = 0 := by
        by_contra hlne
        exact uniqueHighA_impossible_of_l_ne610 l alpha beta delta epsilon
          zeta eta theta (j / t) A B C0 D0 E0 hlne hjdiv hcone hder
      subst hl0
      subst hB0
      exact uniqueHighA_impossible_of_l_zero_B_zero_beta_ne alpha beta
        delta epsilon zeta eta theta (j / t) A C0 D0 E0 hjdiv hbetane
        hcone hder
  · intro hcone
    exact extremeHighB_impossible l alpha beta delta epsilon zeta eta
      theta (j / t) A B C0 D0 E0 hjdiv hcone hder
  · intro hBonly
    exact uniqueNonconstantB_impossible l alpha beta delta epsilon zeta
      eta theta (j / t) A B C0 D0 E0 hjdiv hBonly.1 hBonly.2.1
      hBonly.2.2.1 hBonly.2.2.2.1 hBonly.2.2.2.2 hder
  · intro hDonly
    exact uniqueNonconstantD0_impossible l alpha beta delta epsilon zeta
      eta theta (j / t) A B C0 D0 E0 hjdiv hDonly.1 hDonly.2.1
      hDonly.2.2.1 hDonly.2.2.2.1 hDonly.2.2.2.2 hder
  · intro hEonly
    exact uniqueNonconstantE0_impossible_of_beta_ne l alpha beta delta
      epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv hEonly.2.2.2.2.2
      hEonly.1 hEonly.2.1 hEonly.2.2.1 hEonly.2.2.2.1 hEonly.2.2.2.2.1
      hder

end Residual610

end Max11DegreeRoutes
