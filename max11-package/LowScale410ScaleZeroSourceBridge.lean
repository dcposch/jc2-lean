import LowScale410ScaleZeroAssembly
import LowScale810ScaleTwoSecondFace

/-!
# Source bridge for the scale-zero `(4,10)` branch

At scale zero the common leading core is constant.  Consequently the common
quartic depression is defined over `k[x]`, and every coefficient of both
depressed source polynomials has a literal polynomial representative.

The source normalization alone does not say that the Faber integration
constants `beta`, `gamma`, and `delta` vanish.  The final definition in this
file isolates precisely the additional quartic--decic coefficient lemma that
would supply those vanishings and connect the source bracket to the completed
scale-zero assembly.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section ScaleZeroSourceBridge410

variable {k : Type*} [Field k] [CharZero k]

/-- The quartic depression center is polynomial at constant scale. -/
theorem quarticDepressionR410_constantScale_eq_algebraMap
    (p : k[X][X]) (t : k) :
    quarticDepressionR46 (RatFunc.C t)
        (algebraMap k[X] (RatFunc k) (p.coeff 3)) =
      algebraMap k[X] (RatFunc k)
        (C ((4 * t ^ 3) ⁻¹) * p.coeff 3) := by
  simp only [quarticDepressionR46, map_mul, RatFunc.algebraMap_C]
  rw [map_inv₀, map_mul, map_ofNat, map_pow]
  ring

/-- Polynomial representatives of the three depressed quartic coordinates
at constant scale. -/
theorem constantScale_depressedQuartic46_polynomialRepresentatives
    (p : k[X][X]) (t : k) (r0 : k[X]) (ht : t ≠ 0)
    (A B C0 : RatFunc k)
    (hpDep : affineDepress68 (RatFunc.C t)
        (algebraMap k[X] (RatFunc k) r0) (sourceToRatFunc68 p) =
      depressedQuartic46 A B C0) :
    ∃ A0 B0 C00 : k[X],
      algebraMap k[X] (RatFunc k) A0 = A ∧
      algebraMap k[X] (RatFunc k) B0 = B ∧
      algebraMap k[X] (RatFunc k) C00 = C0 := by
  let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
  have hpmap : p0.map (algebraMap k[X] (RatFunc k)) =
      depressedQuartic46 A B C0 := by
    rw [← hpDep]
    exact (affineDepress_source_constantScale_map68 p t r0 ht).symm
  let A0 : k[X] := p0.coeff 2
  let B0 : k[X] := p0.coeff 1
  let C00 : k[X] := p0.coeff 0
  refine ⟨A0, B0, C00, ?_, ?_, ?_⟩
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 2) hpmap
    simpa [A0, depressedQuartic46, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 1) hpmap
    simpa [B0, depressedQuartic46, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) hpmap
    simpa [C00, depressedQuartic46, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h

/-- A constant-scale degree-ten source has the exact monic decic normal form,
with every displayed coefficient represented in `k[x]`. -/
theorem constantScale_sourceDecic410_polynomialNormalForm
    (q : k[X][X]) (t : k) (r0 : k[X]) (ht : t ≠ 0)
    (hq : q.natDegree = 10)
    (hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) =
      (RatFunc.C t) ^ 10) :
    ∃ L P Q R S T U V W Z : k[X],
      affineDepress68 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) r0) (sourceToRatFunc68 q) =
        depressedDecic410
          (algebraMap k[X] (RatFunc k) L)
          (algebraMap k[X] (RatFunc k) P)
          (algebraMap k[X] (RatFunc k) Q)
          (algebraMap k[X] (RatFunc k) R)
          (algebraMap k[X] (RatFunc k) S)
          (algebraMap k[X] (RatFunc k) T)
          (algebraMap k[X] (RatFunc k) U)
          (algebraMap k[X] (RatFunc k) V)
          (algebraMap k[X] (RatFunc k) W)
          (algebraMap k[X] (RatFunc k) Z) := by
  let q0 : k[X][X] := q.comp ((X - C r0) * C (C t⁻¹))
  let g : (RatFunc k)[X] := affineDepress68 (RatFunc.C t)
    (algebraMap k[X] (RatFunc k) r0) (sourceToRatFunc68 q)
  have hgmap : g = q0.map (algebraMap k[X] (RatFunc k)) := by
    exact affineDepress_source_constantScale_map68 q t r0 ht
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = (RatFunc.C t) ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  have hscale : RatFunc.C t ≠ 0 := by
    intro hzero
    apply ht
    apply RatFunc.C_injective
    simpa only [map_zero] using hzero
  obtain ⟨hg10, _hg9, _hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q)
      (RatFunc.C t) (algebraMap k[X] (RatFunc k) r0)
      hscale hgTop hg_high_src
  have hq0ten : q0.coeff 10 = 1 := by
    apply RatFunc.algebraMap_injective k
    have hcoeff := congrArg (fun f : (RatFunc k)[X] => f.coeff 10) hgmap
    rw [hg10] at hcoeff
    simpa using hcoeff.symm
  have hq0high : ∀ n, 10 < n → q0.coeff n = 0 := by
    intro n hn
    apply RatFunc.algebraMap_injective k
    have hcoeff := congrArg (fun f : (RatFunc k)[X] => f.coeff n) hgmap
    rw [hg_high n hn] at hcoeff
    simpa using hcoeff.symm
  let L : k[X] := q0.coeff 9
  let P : k[X] := q0.coeff 8
  let Q : k[X] := q0.coeff 7
  let R : k[X] := q0.coeff 6
  let S : k[X] := q0.coeff 5
  let T : k[X] := q0.coeff 4
  let U : k[X] := q0.coeff 3
  let V : k[X] := q0.coeff 2
  let W : k[X] := q0.coeff 1
  let Z : k[X] := q0.coeff 0
  let decic : (RatFunc k)[X] := depressedDecic410
    (algebraMap k[X] (RatFunc k) L)
    (algebraMap k[X] (RatFunc k) P)
    (algebraMap k[X] (RatFunc k) Q)
    (algebraMap k[X] (RatFunc k) R)
    (algebraMap k[X] (RatFunc k) S)
    (algebraMap k[X] (RatFunc k) T)
    (algebraMap k[X] (RatFunc k) U)
    (algebraMap k[X] (RatFunc k) V)
    (algebraMap k[X] (RatFunc k) W)
    (algebraMap k[X] (RatFunc k) Z)
  have hdecicDegree : decic.natDegree ≤ 10 := by
    dsimp only [decic]
    simp only [depressedDecic410]
    compute_degree
  refine ⟨L, P, Q, R, S, T, U, V, W, Z, ?_⟩
  change g = decic
  rw [hgmap]
  ext n
  by_cases hn : n ≤ 10
  · interval_cases n <;>
      simp [decic, depressedDecic410, L, P, Q, R, S, T, U, V, W, Z, hq0ten,
        coeff_add, coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow]
  · have hn' : 10 < n := by omega
    have hz := hq0high n hn'
    rw [Polynomial.coeff_map, hz, map_zero,
      coeff_eq_zero_of_natDegree_lt (hdecicDegree.trans_lt hn')]

variable [IsAlgClosed k]

/-- Unconditional source transport: a normalized scale-zero `(4,10)` Keller
source yields a depressed monic quartic--decic bracket whose thirteen
variable coefficients all lie in `k[x]`. -/
theorem normalized410ScaleZero_exists_depressedPolynomialBracket
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ (terminal : k) (A B C0 L P1 Q1 R S T U V W Z : k[X]),
      terminal ≠ 0 ∧
      differentialJacobian ratFuncDerivation46
        (depressedQuartic46
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0))
        (depressedDecic410
          (algebraMap k[X] (RatFunc k) L)
          (algebraMap k[X] (RatFunc k) P1)
          (algebraMap k[X] (RatFunc k) Q1)
          (algebraMap k[X] (RatFunc k) R)
          (algebraMap k[X] (RatFunc k) S)
          (algebraMap k[X] (RatFunc k) T)
          (algebraMap k[X] (RatFunc k) U)
          (algebraMap k[X] (RatFunc k) V)
          (algebraMap k[X] (RatFunc k) W)
          (algebraMap k[X] (RatFunc k) Z)) = C (RatFunc.C terminal) := by
  rcases hsource with
    ⟨hHne, hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp4' : p.coeff 4 = H ^ 2 := by simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hcne : c ≠ 0 := by
    intro hzero
    apply hHne
    rw [← hc, hzero, C_0]
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq c
    (by norm_num : 0 < 2)
  have htne : t ≠ 0 := by
    intro hzero
    apply hcne
    rw [← ht, hzero, zero_pow (by norm_num : 2 ≠ 0)]
  have hHsquare : H = (C t : k[X]) ^ 2 := by
    rw [← hc, ← C_pow, ht]
  have hp4t : p.coeff 4 = (C t : k[X]) ^ 4 := by
    rw [hp4', hHsquare]
    ring
  have hq10t : q.coeff 10 = (C t : k[X]) ^ 10 := by
    rw [hq10', hHsquare]
    ring
  let scale : RatFunc k := RatFunc.C t
  let r0 : k[X] := C ((4 * t ^ 3) ⁻¹) * p.coeff 3
  let r : RatFunc k := algebraMap k[X] (RatFunc k) r0
  have hscale : scale ≠ 0 := by
    intro hzero
    apply htne
    apply RatFunc.C_injective
    simpa only [scale, map_zero] using hzero
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 4) = scale ^ 4 := by
    rw [hp4t, map_pow]
    simp only [scale, RatFunc.algebraMap_C]
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = scale ^ 10 := by
    rw [hq10t, map_pow]
    simp only [scale, RatFunc.algebraMap_C]
  have hr : r = quarticDepressionR46 scale
      (algebraMap k[X] (RatFunc k) (p.coeff 3)) := by
    dsimp only [r, r0, scale]
    exact (quarticDepressionR410_constantScale_eq_algebraMap p t).symm
  let Ar := depressedA46 scale r
    (algebraMap k[X] (RatFunc k) (p.coeff 3))
    (algebraMap k[X] (RatFunc k) (p.coeff 2))
  let Br := depressedB46 scale r
    (algebraMap k[X] (RatFunc k) (p.coeff 3))
    (algebraMap k[X] (RatFunc k) (p.coeff 2))
    (algebraMap k[X] (RatFunc k) (p.coeff 1))
  let Cr := depressedC46 scale r
    (algebraMap k[X] (RatFunc k) (p.coeff 3))
    (algebraMap k[X] (RatFunc k) (p.coeff 2))
    (algebraMap k[X] (RatFunc k) (p.coeff 1))
    (algebraMap k[X] (RatFunc k) (p.coeff 0))
  have hpDep : affineDepress68 scale r (sourceToRatFunc68 p) =
      depressedQuartic46 Ar Br Cr := by
    change affineDepress46 scale r (sourceToRatFunc46 p) = _
    simpa only [Ar, Br, Cr] using
      affineDepress_sourceQuartic46 p scale r hp hscale hpTop hr
  have hpDepConstant : affineDepress68 (RatFunc.C t)
      (algebraMap k[X] (RatFunc k) r0) (sourceToRatFunc68 p) =
        depressedQuartic46 Ar Br Cr := by
    simpa only [scale, r] using hpDep
  obtain ⟨A, B, C0, hA, hB, hC0⟩ :=
    constantScale_depressedQuartic46_polynomialRepresentatives
      p t r0 htne Ar Br Cr hpDepConstant
  obtain ⟨L, P1, Q1, R, S, T, U, V, W, Z, hqDep⟩ :=
    constantScale_sourceDecic410_polynomialNormalForm
      q t r0 htne hq (by simpa only [scale] using hqTop)
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hDsrc : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  let terminal : k := j / t
  have hterminal : terminal ≠ 0 := div_ne_zero hj htne
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j scale r hscale hDsrc
  rw [hpDep, hqDep] at hbracket
  have hbracket' : differentialJacobian ratFuncDerivation46
      (depressedQuartic46
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0))
      (depressedDecic410
        (algebraMap k[X] (RatFunc k) L)
        (algebraMap k[X] (RatFunc k) P1)
        (algebraMap k[X] (RatFunc k) Q1)
        (algebraMap k[X] (RatFunc k) R)
        (algebraMap k[X] (RatFunc k) S)
        (algebraMap k[X] (RatFunc k) T)
        (algebraMap k[X] (RatFunc k) U)
        (algebraMap k[X] (RatFunc k) V)
        (algebraMap k[X] (RatFunc k) W)
        (algebraMap k[X] (RatFunc k) Z)) = C (RatFunc.C terminal) := by
    rw [hA, hB, hC0]
    simpa only [ratFuncDerivation68, scale, terminal, map_div₀,
      RatFunc.algebraMap_eq_C] using hbracket
  exact ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
    hterminal, hbracket'⟩

/-- Exact missing coefficient lemma.  It says that a polynomial depressed
quartic--decic constant bracket integrates with `L = beta = gamma = delta =
0`.  The source normalization itself does not imply these equalities; this
is the remaining early-load assertion needed by the completed assembly. -/
def ScaleZero410EarlyZeroIntegrationBridge : Prop :=
  ∀ (terminal : k) (A B C0 L P Q R S T U V W Z : k[X]),
    terminal ≠ 0 →
    differentialJacobian ratFuncDerivation46
      (depressedQuartic46
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0))
      (depressedDecic410
        (algebraMap k[X] (RatFunc k) L)
        (algebraMap k[X] (RatFunc k) P)
        (algebraMap k[X] (RatFunc k) Q)
        (algebraMap k[X] (RatFunc k) R)
        (algebraMap k[X] (RatFunc k) S)
        (algebraMap k[X] (RatFunc k) T)
        (algebraMap k[X] (RatFunc k) U)
        (algebraMap k[X] (RatFunc k) V)
        (algebraMap k[X] (RatFunc k) W)
        (algebraMap k[X] (RatFunc k) Z)) = C (RatFunc.C terminal) →
    ∃ alpha epsilon zeta eta theta iota : k,
      differentialJacobian ratFuncDerivation46
        (depressedQuartic46
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0))
        (depressedDecic410 0
          (integratedP410 (algebraMap k[X] (RatFunc k) A)
            (RatFunc.C alpha))
          (integratedQ410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B) 0)
          (integratedR410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0)
          (integratedS410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0)
          (integratedT410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0
            (RatFunc.C epsilon))
          (integratedU410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0 0
            (RatFunc.C zeta))
          (integratedV410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0 0
            (RatFunc.C epsilon) (RatFunc.C eta))
          (integratedW410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0 0
            (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C theta))
          (integratedZ410 0 (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0) (RatFunc.C alpha) 0 0 0
            (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
            (RatFunc.C iota))) = C (RatFunc.C terminal)

/-- With exactly the missing early-zero integration bridge, the completed
trajectory theorem excludes every normalized scale-zero source. -/
theorem normalized410ScaleZero_impossible_of_earlyZeroIntegrationBridge
    (hbridge : ScaleZero410EarlyZeroIntegrationBridge (k := k))
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) : False := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hbracket⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨alpha, epsilon, zeta, eta, theta, iota, hintegrated⟩ :=
    hbridge terminal A B C0 L P1 Q1 R S T U V W Z hterminal hbracket
  exact scaleZero410_integrated_constantBracket_impossible
    alpha epsilon zeta eta theta iota terminal A B C0 hterminal hintegrated

end ScaleZeroSourceBridge410

end Max11DegreeRoutes
