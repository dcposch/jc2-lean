import Fable810ScaleZeroThirteenthDefectPart25Scratch

/-! Part 26 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
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

section ScaleZeroThirteenthDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false


/-! ## Degree-`4` monic Jacobian row -/

/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`3` Jacobian coefficient
is exactly
`4 T G' + 3 U F' + 2 V E' + W D'
- F U' - 2 E V' - 3 D W' - 4 C X'`.
Here `A = f.coeff 6`, `B = f.coeff 5`, `C = f.coeff 4`, `D = f.coeff 3`,
`E = f.coeff 2`, `F = f.coeff 1`, `G = f.coeff 0`, `L = g.coeff 9`,
`P = g.coeff 8`, `Q = g.coeff 7`, `R = g.coeff 6`, `S = g.coeff 5`,
`T = g.coeff 4`, `U = g.coeff 3`, `V = g.coeff 2`, `W = g.coeff 1`,
and `X = g.coeff 0`. -/
theorem scaleZero_monicOcticDecic_degree3Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 3 =
      (4 : F) * g.coeff 4 * d (f.coeff 0) +
        (3 : F) * g.coeff 3 * d (f.coeff 1) +
        (2 : F) * g.coeff 2 * d (f.coeff 2) +
        g.coeff 1 * d (f.coeff 3) -
          f.coeff 1 * d (g.coeff 3) -
          (2 : F) * f.coeff 2 * d (g.coeff 2) -
          (3 : F) * f.coeff 3 * d (g.coeff 1) -
          (4 : F) * f.coeff 4 * d (g.coeff 0) :=
  differentialJacobian_coeff_3_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL


end ScaleZeroThirteenthDefect810
end Max11DegreeRoutes
end
