import Sol610ScaleTwoAlignedFourteenthDefectSourceDescentScratch

/-! # Terminal degree-zero row for the aligned `(6,10)` source

The weight-seventy ν defect has descended to a ground scalar.  The only
remaining Jacobian coefficient is degree zero; it is inhomogeneous and equals
the Keller constant, so it produces no further first integral.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section DifferentialJacobianZeroRow

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The constant coefficient of a differential Jacobian is always the
Wronskian of the two constant/linear coefficient pairs. -/
theorem differentialJacobian_coeff_zero
    (d : Derivation k F F) (f g : F[X]) :
    (differentialJacobian d f g).coeff 0 =
      d (f.coeff 0) * g.coeff 1 - f.coeff 1 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal 0 :
      Finset (ℕ × ℕ)) = ({(0, 0)} : Finset (ℕ × ℕ)) := by decide
  simp only [differentialJacobian, Polynomial.coeff_sub,
    Polynomial.coeff_mul, hanti, Finset.sum_singleton,
    coeff_coefficientDeriv, Polynomial.coeff_derivative]
  norm_num

end DifferentialJacobianZeroRow

section AlignedFinalRow610

variable {k : Type*} [Field k] [CharZero k]

/-- The literal coefficient-zero row of the supplied source bracket. -/
theorem source610_degreeZeroJacobianRow
    (p q : k[X][X]) (j : k)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    (p.coeff 0).derivative * q.coeff 1 -
      p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  have hcoeff := congrArg (fun r : k[X][X] => r.coeff 0) hD
  simp only [Polynomial.coeff_sub, Polynomial.coeff_mul,
    Polynomial.coeff_derivative, Polynomial.coeff_C] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 0 :
      Finset (ℕ × ℕ)) = ({(0, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num at hcoeff
  linear_combination hcoeff

/-- After depressing the supplied source by its own quintic coefficient, the
same final row is `E'W - D X' = j/h`. -/
theorem alignedSquareSource610_normalized_degreeZeroRow
    (p q : k[X][X]) (h0 : k[X]) (j : k) (hh0 : h0 ≠ 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
    let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
    let f : (RatFunc k)[X] :=
      affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 p)
    let g : (RatFunc k)[X] :=
      affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 q)
    ratFuncDerivation68 (f.coeff 0) * g.coeff 1 -
      f.coeff 1 * ratFuncDerivation68 (g.coeff 0) = RatFunc.C j / hRF := by
  dsimp only
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 q)
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (sexticDepressionR610 hRF a5) hh hD
  have hcoeff := congrArg (fun t : (RatFunc k)[X] => t.coeff 0) hbracket
  rw [differentialJacobian_coeff_zero] at hcoeff
  simpa only [Polynomial.coeff_C, if_true, f, g, hRF, a5] using hcoeff

set_option maxHeartbeats 800000000 in
/-- Complete aligned terminal packet on the unchanged source: the
weight-seventy cleared defect is a scalar multiple of `h₀⁷⁰`, and the last
unused Jacobian coefficient is exactly the inhomogeneous Keller row. -/
theorem alignedSquareSource610_fourteenthDefect_and_finalRow
    (p q : k[X][X]) (H h0 : k[X]) (j : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 -
      (3 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    (∃ nu : k,
      localClearedFourteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) =
        Polynomial.C nu * h0 ^ 70) ∧
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  constructor
  · exact alignedSquareSource610_fourteenthClearedDefect_exists p q H h0 j
      hp hq hh0 hH hp6 hq10 hN hD
  · exact source610_degreeZeroJacobianRow p q j hD

#print axioms differentialJacobian_coeff_zero
#print axioms source610_degreeZeroJacobianRow
#print axioms alignedSquareSource610_normalized_degreeZeroRow
#print axioms alignedSquareSource610_fourteenthDefect_and_finalRow

end AlignedFinalRow610

end Max11DegreeRoutes
