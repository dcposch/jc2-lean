import Grok610ScaleZeroValuationEndgameScratch
import LowScale68ScaleZero

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section PolynomialCore610

variable {k : Type*} [Field k] [CharZero k]

/-- At constant scale the monic sextic depression is a polynomial
substitution, so every free-core letter has a representative in `k[x]`. -/
theorem constantScale_monicSextic_polynomialCore610
    (p : k[X][X]) (t : k) (ht : t ≠ 0) :
    let r0 : k[X] := C ((6 * t ^ 5)⁻¹) * p.coeff 5
    let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
    let f : (RatFunc k)[X] :=
      affineDepress68 (RatFunc.C t)
        (sexticDepressionR610 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) (p.coeff 5)))
        (sourceToRatFunc68 p)
    algebraMap k[X] (RatFunc k) (p0.coeff 4) = f.coeff 4 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 3) = f.coeff 3 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 2) = f.coeff 2 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 1) = f.coeff 1 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 0) = f.coeff 0 := by
  intro r0 p0 f
  have hcenter :
      sexticDepressionR610 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) (p.coeff 5)) =
        algebraMap k[X] (RatFunc k) r0 := by
    dsimp only [r0, sexticDepressionR610]
    exact sexticDepressionR68_constantScale_eq_algebraMap p t
  have hf_eq : f = p0.map (algebraMap k[X] (RatFunc k)) := by
    dsimp only [f, p0]
    rw [hcenter]
    exact affineDepress_source_constantScale_map68 p t r0 ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hf_eq, Polynomial.coeff_map])

end PolynomialCore610

end Max11DegreeRoutes
