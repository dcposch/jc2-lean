import LowScale68SourceBridge
import Mathlib.Algebra.Polynomial.Derivation

/-! # Constant-scale polynomial bridge for the `(6,8)` source

At common scale zero, a square root of the normalized leading core is a
nonzero scalar.  The common affine depression therefore takes place over the
literal coefficient ring `k[x]`, not merely over its fraction field `k(x)`.
This module records that source-honest fact and extracts polynomial
representatives for every depressed sextic and octic coefficient.  In
particular, none of the thirteen variable coefficients can have a finite
pole in the scale-zero branch.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ConstantScaleMap68

variable {k : Type*} [Field k] [CharZero k]

/-- At a nonzero scalar scale and polynomial center, the `(6,8)` affine
depression commutes exactly with the coefficient embedding `k[x] -> k(x)`.
-/
theorem affineDepress_source_constantScale_map68
    (f : k[X][X]) (t : k) (r0 : k[X]) (ht : t ≠ 0) :
    affineDepress68 (RatFunc.C t)
        (algebraMap k[X] (RatFunc k) r0) (sourceToRatFunc68 f) =
      (f.comp ((X - C r0) * C (C t⁻¹))).map
        (algebraMap k[X] (RatFunc k)) := by
  simpa only [affineDepress68, affineDepress46, sourceToRatFunc68] using
    affineDepress_source_constantScale_map46 f t r0 ht

/-- The sextic depression center is itself the image of a coefficient
polynomial when the scale is a scalar. -/
theorem sexticDepressionR68_constantScale_eq_algebraMap
    (p : k[X][X]) (t : k) :
    sexticDepressionR68 (RatFunc.C t)
        (algebraMap k[X] (RatFunc k) (p.coeff 5)) =
      algebraMap k[X] (RatFunc k)
        (C ((6 * t ^ 5) ⁻¹) * p.coeff 5) := by
  simp only [sexticDepressionR68, map_mul, RatFunc.algebraMap_C]
  rw [map_inv₀, map_mul, map_ofNat, map_pow]
  ring

/-- Every variable coefficient of a constant-scale depressed sextic has a
literal polynomial representative. -/
theorem constantScale_depressedSextic68_polynomialRepresentatives
    (p : k[X][X]) (t : k) (r0 : k[X]) (ht : t ≠ 0)
    (A B C0 D E : RatFunc k)
    (hpDep : affineDepress68 (RatFunc.C t)
        (algebraMap k[X] (RatFunc k) r0) (sourceToRatFunc68 p) =
      depressedSextic68 A B C0 D E) :
    ∃ A0 B0 C00 D0 E0 : k[X],
      algebraMap k[X] (RatFunc k) A0 = A ∧
      algebraMap k[X] (RatFunc k) B0 = B ∧
      algebraMap k[X] (RatFunc k) C00 = C0 ∧
      algebraMap k[X] (RatFunc k) D0 = D ∧
      algebraMap k[X] (RatFunc k) E0 = E := by
  let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
  have hpmap : p0.map (algebraMap k[X] (RatFunc k)) =
      depressedSextic68 A B C0 D E := by
    rw [← hpDep]
    exact (affineDepress_source_constantScale_map68 p t r0 ht).symm
  let A0 : k[X] := p0.coeff 4
  let B0 : k[X] := p0.coeff 3
  let C00 : k[X] := p0.coeff 2
  let D0 : k[X] := p0.coeff 1
  let E0 : k[X] := p0.coeff 0
  refine ⟨A0, B0, C00, D0, E0, ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 4) hpmap
    simpa [A0, depressedSextic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 3) hpmap
    simpa [B0, depressedSextic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 2) hpmap
    simpa [C00, depressedSextic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 1) hpmap
    simpa [D0, depressedSextic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) hpmap
    simpa [E0, depressedSextic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h

/-- Every variable coefficient of the corresponding constant-scale
depressed octic likewise has a literal polynomial representative. -/
theorem constantScale_depressedOctic68_polynomialRepresentatives
    (q : k[X][X]) (t : k) (r0 : k[X]) (ht : t ≠ 0)
    (L P Q R S T U V : RatFunc k)
    (hqDep : affineDepress68 (RatFunc.C t)
        (algebraMap k[X] (RatFunc k) r0) (sourceToRatFunc68 q) =
      depressedOctic68 L P Q R S T U V) :
    ∃ L0 P0 Q0 R0 S0 T0 U0 V0 : k[X],
      algebraMap k[X] (RatFunc k) L0 = L ∧
      algebraMap k[X] (RatFunc k) P0 = P ∧
      algebraMap k[X] (RatFunc k) Q0 = Q ∧
      algebraMap k[X] (RatFunc k) R0 = R ∧
      algebraMap k[X] (RatFunc k) S0 = S ∧
      algebraMap k[X] (RatFunc k) T0 = T ∧
      algebraMap k[X] (RatFunc k) U0 = U ∧
      algebraMap k[X] (RatFunc k) V0 = V := by
  let q0 : k[X][X] := q.comp ((X - C r0) * C (C t⁻¹))
  have hqmap : q0.map (algebraMap k[X] (RatFunc k)) =
      depressedOctic68 L P Q R S T U V := by
    rw [← hqDep]
    exact (affineDepress_source_constantScale_map68 q t r0 ht).symm
  let L0 : k[X] := q0.coeff 7
  let P0 : k[X] := q0.coeff 6
  let Q0 : k[X] := q0.coeff 5
  let R0 : k[X] := q0.coeff 4
  let S0 : k[X] := q0.coeff 3
  let T0 : k[X] := q0.coeff 2
  let U0 : k[X] := q0.coeff 1
  let V0 : k[X] := q0.coeff 0
  refine ⟨L0, P0, Q0, R0, S0, T0, U0, V0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 7) hqmap
    simpa [L0, depressedOctic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 6) hqmap
    simpa [P0, depressedOctic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 5) hqmap
    simpa [Q0, depressedOctic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 4) hqmap
    simpa [R0, depressedOctic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 3) hqmap
    simpa [S0, depressedOctic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 2) hqmap
    simpa [T0, depressedOctic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 1) hqmap
    simpa [U0, depressedOctic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h
  · have h := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) hqmap
    simpa [V0, depressedOctic68, coeff_add, coeff_C_mul,
      coeff_mul_X_pow', coeff_X, coeff_X_pow] using h

end ConstantScaleMap68

section ScaleZeroIntegration68

variable {k : Type*} [Field k] [CharZero k]

/-- A polynomial killed by the standard polynomial derivation is a literal
ground-field constant. -/
theorem polynomialDerivative_zero_exists_C68 (f : k[X])
    (hf : Polynomial.derivative' f = 0) :
    ∃ c : k, f = C c := by
  exact ⟨f.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hf⟩

/- In the scale-zero branch, the two exact lower-row invariants also
descend to the literal ground field.  The companion theorem
`constantBracket_integrated68_lowerSystem` supplies the remaining three
one-form rows without repackaging their large formulas here. -/
set_option maxHeartbeats 2000000 in
theorem integratedFirstIntegrals_exist_ground68
    (A B C0 D E terminal : RatFunc k)
    (l alpha beta gamma delta epsilon zeta eta : k)
    (hbracket :
      let ck := algebraMap k (RatFunc k)
      let P := integratedP68 A (ck alpha)
      let Q := integratedQ68 (ck l) A B (ck beta)
      let R := integratedR68 (ck l) A B C0 (ck alpha) (ck gamma)
      let S := integratedS68 (ck l) A B C0 D (ck alpha) (ck beta) (ck delta)
      let T := integratedT68 (ck l) A B C0 D E (ck alpha) (ck beta)
        (ck gamma) (ck epsilon)
      let U := integratedU68 (ck l) A B C0 D E (ck alpha) (ck beta)
        (ck gamma) (ck delta) (ck zeta)
      let V := integratedV68 (ck l) A B C0 D E (ck alpha) (ck beta)
        (ck gamma) (ck delta) (ck epsilon) (ck eta)
      differentialJacobian ratFuncDerivation68 (depressedSextic68 A B C0 D E)
        (depressedOctic68 (ck l) P Q R S T U V) = C terminal) :
    ∃ i4 i3 : k,
      let ck := algebraMap k (RatFunc k)
      firstIntegralFour68 (ck l) A B C0 D E (ck beta) (ck gamma)
          (ck delta) (ck epsilon) (ck zeta) = ck i4 ∧
      firstIntegralThree68 (ck l) A B C0 D E (ck beta) (ck gamma)
          (ck delta) (ck epsilon) (ck zeta) = ck i3 := by
  let ck := algebraMap k (RatFunc k)
  dsimp only at hbracket
  have hconst (a : k) : ratFuncDerivation68 (ck a) = 0 := by
    have hp := ratFuncDerivation46_polynomial (C a : k[X])
    simpa [ck, RatFunc.algebraMap_C] using hp
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (ck l) A B C0 D E (ck alpha) (ck beta)
      (ck gamma) (ck delta) (ck epsilon) (ck zeta) (ck eta) terminal
      (hconst l) (hconst alpha) (hconst beta) (hconst gamma)
      (hconst delta) (hconst epsilon) (hconst zeta) (hconst eta) hbracket
  dsimp only at hlow
  have descend (c : RatFunc k) (hc : ratFuncDerivation68 c = 0) :
      ∃ a : k, c = ck a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hc
  obtain ⟨i4, hi4⟩ := descend
    (firstIntegralFour68 (ck l) A B C0 D E (ck beta) (ck gamma)
      (ck delta) (ck epsilon) (ck zeta)) hlow.1
  obtain ⟨i3, hi3⟩ := descend
    (firstIntegralThree68 (ck l) A B C0 D E (ck beta) (ck gamma)
      (ck delta) (ck epsilon) (ck zeta)) hlow.2.1
  exact ⟨i4, i3, hi4, hi3⟩

end ScaleZeroIntegration68

#print axioms affineDepress_source_constantScale_map68
#print axioms sexticDepressionR68_constantScale_eq_algebraMap
#print axioms constantScale_depressedSextic68_polynomialRepresentatives
#print axioms constantScale_depressedOctic68_polynomialRepresentatives
#print axioms polynomialDerivative_zero_exists_C68
#print axioms integratedFirstIntegrals_exist_ground68

end Max11DegreeRoutes
