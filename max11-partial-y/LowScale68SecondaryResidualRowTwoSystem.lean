import LowScale68SecondaryResidualDouble

/-! Residual row-two extraction from the integrated polynomial system.

After the cubic translation `C=A^2/3+c` and the residual translation
`D=A*B/3+d`, the first irreducible one-form of the constant-Jacobian
polynomial system is exactly the residual row plus the constant-load row.
The resulting equation feeds the next residual Newton faces.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualRowTwoSystem68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 2000000 in
/-- Linearity of the first one-form after both coordinate changes. -/
theorem cubicRowTwoPolynomial68_residualSplit
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) :
    let C0 := (1 / 3 : k) • A ^ 2 + c
    let D0 := (1 / 3 : k) • (A * B) + d
    let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
    lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B C0 D0)
      (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D0 E0)
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D0 E0) B C0 D0 E0 =
      secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let D0 := (1 / 3 : k) • (A * B) + d
  let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  change lowerRowTwoPolynomial68
    (integratedSPolynomial68 l alpha beta delta A B C0 D0)
    (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D0 E0)
    (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
      A B C0 D0 E0) B C0 D0 E0 = _
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D0 e
  rw [hcoords.s_eq, hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowTwoPolynomial68_split,
    show cubicHomogeneousRowTwoPolynomial68 A B c D0 e =
        secondaryResidualRowTwoPolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowTwoPolynomial68_residualCoordinates A B c d e]

/-- The residual first one-form equation extracted from the integrated
row after `C=A^2/3+c` and `D=A*B/3+d`. -/
theorem polynomialSecondaryResidualRowTwo68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X])
    (hrowTwo :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta A B C0 D0)
        (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          A B C0 D0 E0) B C0 D0 E0 = 0) :
    secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0 := by
  simpa using
    (cubicRowTwoPolynomial68_residualSplit
      l alpha beta gamma delta epsilon zeta eta A B c d e).symm.trans
      hrowTwo

/-- The same residual equation, read off the full constant-Jacobian
polynomial system after both coordinate reconstructions. -/
theorem integratedPolynomialLowerSystem68_residualRowTwo
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E c d e : k[X])
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hD : D = (1 / 3 : k) • (A * B) + d)
    (hE : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0 := by
  have hrowTwo := hsys.rowTwo
  rw [hC0, hD, hE] at hrowTwo
  exact polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta A B c d e hrowTwo

#print axioms cubicRowTwoPolynomial68_residualSplit
#print axioms polynomialSecondaryResidualRowTwo68
#print axioms integratedPolynomialLowerSystem68_residualRowTwo

end SecondaryResidualRowTwoSystem68

end Max11DegreeRoutes
