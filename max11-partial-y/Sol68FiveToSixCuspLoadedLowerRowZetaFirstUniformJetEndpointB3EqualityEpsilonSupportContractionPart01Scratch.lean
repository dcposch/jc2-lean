import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportWallScratch

/-! # Exact contraction of the post-epsilon support wall

This contracts only the six literal top-support products retained by the
support-wall module.  The sole algebraic reduction used on those products is
the cusp relation `A_top * B_top^2 + 3*c_top^2 = 0`.  In particular the
coincident wall `D=T` (where the compensated `Fce` edge is constant) is kept.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportContraction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The two edge equations and their division-free resultant at the support
wall.  All natural-number factors are left in factored form so the arithmetic
provenance of the wall remains visible. -/
def FiveToSixCuspZetaFirstB3EqualitySupportContractedScalar68
    (gamma epsilon:k) (A B c d e:k[X]) (N S:ℕ):Prop:=
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let q:=9*N-7*S
  let p:=11*N-7*S
  let a:=4*N-3*S
  let A0:=A.coeff (2*N)
  let B0:=B.coeff D
  let c0:=c.coeff Cc
  let d0:=d.coeff V
  let e0:=e.coeff E
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  A0*((2*N:ℕ):k)*(A0*Fce.coeff q-J.coeff p)+
      ((a:ℕ):k)*A0*B0^2*d0-
        (3:k)*((E:ℕ):k)*B0*c0*e0=0 ∧
    A0*Fce.coeff q*(((N:ℕ):k)-((q:ℕ):k))+
        ((p:ℕ):k)*(J.coeff p+B0^2*d0)=0 ∧
      A0*((2*N:ℕ):k)*((3*N:ℕ):k)*(A0*Fce.coeff q)+
        ((p:ℕ):k)*((E:ℕ):k)*
          (A0*B0^2*d0-(3:k)*B0*c0*e0)=0

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportContraction68
end Max11DegreeRoutes
