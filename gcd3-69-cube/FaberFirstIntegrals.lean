import FaberPoleReduction

noncomputable section

/-! # Base-field Faber first integrals

The four zero lower rows of a literal polynomial cube source are not merely
formal derivative equations: over `k(x)` they descend to four constants in
the ground field.  This is the source-facing constant tuple used by the
ordered early-load and final later-fibre routers.
-/

/-- Ground-field values of the first four Faber invariants attached to a
literal polynomial source. -/
structure GCD369CubeFaberFirstIntegralConstants
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) where
  rho1 : k
  rho2 : k
  rho3 : k
  rho4 : k
  hrho1 :
    GCD369CubeFaberR1
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        S.faberNormalForm.d S.faberNormalForm.c7
        S.faberNormalForm.c5 S.faberNormalForm.c4
        S.faberNormalForm.c3 S.faberNormalForm.c2
        S.faberNormalForm.c1 =
      algebraMap k (RatFunc k) rho1
  hrho2 :
    GCD369CubeFaberR2
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        S.faberNormalForm.d S.faberNormalForm.c7
        S.faberNormalForm.c5 S.faberNormalForm.c4
        S.faberNormalForm.c3 S.faberNormalForm.c2
        S.faberNormalForm.c1 =
      algebraMap k (RatFunc k) rho2
  hrho3 :
    GCD369CubeFaberR3
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        S.faberNormalForm.d S.faberNormalForm.c7
        S.faberNormalForm.c5 S.faberNormalForm.c4
        S.faberNormalForm.c3 S.faberNormalForm.c2
        S.faberNormalForm.c1 =
      algebraMap k (RatFunc k) rho3
  hrho4 :
    GCD369CubeFaberR4
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        S.faberNormalForm.d S.faberNormalForm.c7
        S.faberNormalForm.c5 S.faberNormalForm.c4
        S.faberNormalForm.c3 S.faberNormalForm.c2
        S.faberNormalForm.c1 =
      algebraMap k (RatFunc k) rho4

namespace GCD369CubePolynomialSource

/-- The four literal lower-row first integrals admit simultaneous
ground-field representatives. -/
theorem faberFirstIntegralConstants_nonempty
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    Nonempty (GCD369CubeFaberFirstIntegralConstants S) := by
  let N := S.faberNormalForm
  have hrows := S.faberLowerRows
  choose rho1 hrho1 using GCD369CubeRatFuncConstants
    (GCD369CubeFaberR1
      (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
      (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
      (S.normalizedP.coeff 4)
      N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) hrows.1
  choose rho2 hrho2 using GCD369CubeRatFuncConstants
    (GCD369CubeFaberR2
      (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
      (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
      (S.normalizedP.coeff 4)
      N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) hrows.2.1
  choose rho3 hrho3 using GCD369CubeRatFuncConstants
    (GCD369CubeFaberR3
      (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
      (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
      (S.normalizedP.coeff 4)
      N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) hrows.2.2.1
  choose rho4 hrho4 using GCD369CubeRatFuncConstants
    (GCD369CubeFaberR4
      (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
      (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
      (S.normalizedP.coeff 4)
      N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1) hrows.2.2.2.1
  exact ⟨{
    rho1 := rho1
    rho2 := rho2
    rho3 := rho3
    rho4 := rho4
    hrho1 := by simpa only [N] using hrho1
    hrho2 := by simpa only [N] using hrho2
    hrho3 := by simpa only [N] using hrho3
    hrho4 := by simpa only [N] using hrho4
  }⟩

/-- Canonical ground-field values of the four Faber first integrals. -/
noncomputable def faberFirstIntegralConstants
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) :
    GCD369CubeFaberFirstIntegralConstants S :=
  Classical.choice S.faberFirstIntegralConstants_nonempty

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.faberFirstIntegralConstants_nonempty
#print axioms GCD369CubePolynomialSource.faberFirstIntegralConstants
