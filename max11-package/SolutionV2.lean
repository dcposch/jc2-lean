import FinitePolynomialExclusion
import InfinityConstantCoreAssembly

/-! # Complete polynomial-cube exclusion at partial degrees `(6,9)`

The finite-pole theorem excludes a positive-degree cube root, while the
infinity theorem excludes a constant cube root.  Their degree dichotomy
therefore rules out every literal polynomial-cube source in the normalized
`(6,9)` setup.
-/

noncomputable section

open Polynomial

namespace GCD369CubePolynomialSource

/-- No literal normalized polynomial-cube source exists, whether its common
cube root is constant or nonconstant. -/
theorem empty
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) : False := by
  rcases Nat.eq_zero_or_pos S.s.natDegree with hsdegree | hsdegree
  · exact S.infinity_constantCore_empty hsdegree
  · exact S.nonconstant_cube_root_impossible hsdegree

end GCD369CubePolynomialSource

/-- Source-facing polynomial-cube exclusion, including both positive-degree
and constant common cube roots. -/
theorem GCD369PolynomialCubeSourceExclusion
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (s : k[X]) (p q : k[X][X]) (j : k)
    (hs : s ≠ 0) (hj : j ≠ 0)
    (hp : p.natDegree = 6) (hq : q.natDegree = 9)
    (hp6 : p.coeff 6 = s ^ 6) (hq9 : q.coeff 9 = s ^ 9)
    (hjac : GCD369CubeBivariateJacobian p q = C (C j)) :
    False := by
  let S : GCD369CubePolynomialSource k :=
    { s := s
      p := p
      q := q
      j := j
      hs := hs
      hj := hj
      hp := hp
      hq := hq
      hp6 := hp6
      hq9 := hq9
      hjac := hjac }
  exact S.empty

/-- Backwards-compatible versioned name for the complete cube exclusion. -/
theorem GCD369PolynomialCubeSourceExclusionV2
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (s : k[X]) (p q : k[X][X]) (j : k)
    (hs : s ≠ 0) (hj : j ≠ 0)
    (hp : p.natDegree = 6) (hq : q.natDegree = 9)
    (hp6 : p.coeff 6 = s ^ 6) (hq9 : q.coeff 9 = s ^ 9)
    (hjac : GCD369CubeBivariateJacobian p q = C (C j)) :
    False :=
  GCD369PolynomialCubeSourceExclusion s p q j hs hj hp hq hp6 hq9 hjac

#print axioms GCD369CubePolynomialSource.empty
#print axioms GCD369PolynomialCubeSourceExclusion
#print axioms GCD369PolynomialCubeSourceExclusionV2
