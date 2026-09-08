import Grok610ScaleZeroConeCascadePart01Scratch
import Grok610ScaleZeroConeCascadePart40Scratch
import Grok610ScaleZeroConeCascadePart49Scratch
import Grok610ScaleZeroConeCascadePart50Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section SourcePrimitiveDegree610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 32000000 in
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
