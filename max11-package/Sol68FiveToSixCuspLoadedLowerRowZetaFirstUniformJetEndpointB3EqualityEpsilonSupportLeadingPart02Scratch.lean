import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeadingPart01Scratch

/-! # The same-witness leading edge scalar after the support row

The retained `J` degree drop kills its actual top coefficient.  Together
with the cusp equation this is exactly `4*A_top*B_top^3+27*d_top*e_top=0`.
On the positive compensated-I4 branch, the row-one packet then gives the
additional division-free scalar `4*B_top^2*c_top+9*d_top^2=0`.  The
coefficient-zero coincidence `q=0` is kept verbatim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeading68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Small division-free elimination used after the positive `q` split. -/
theorem fiveToSix_zetaFirst_B3_equality_support_leading_algebra68
    (A0 B0 c0 d0 e0:k) (hc0:c0≠0)
    (hcusp:A0*B0^2+3*c0^2=0)
    (hsum:B0*e0+c0*d0=0)
    (hlead:4*A0*B0^3+27*d0*e0=0):
    4*B0^2*c0+9*d0^2=0:=by
  have hprod:(-3*c0)*(4*B0^2*c0+9*d0^2)=0:=by
    linear_combination B0*hlead-(4*B0^2)*hcusp-(27*d0)*hsum
  exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero (by norm_num) hc0)

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeading68
end Max11DegreeRoutes
