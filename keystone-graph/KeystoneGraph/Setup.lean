/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic and Grok / xAI
agents (formalization)
-/
import Mathlib

/-!
# Keystone 1 setup: the normalized graph of a plane Keller pair

Ambient data for the normalized-graph structure theorems: a plane Keller
pair `P, Q` over an algebraically closed field of characteristic zero,
the coordinate subalgebra `A = k[P,Q]`, and the integral closure `B` of
`A` inside the plane's coordinate ring.  Stage-1 results live at a fixed
height-one prime of `A` (the generic point of a branch of the
non-properness curve), where the base localization is a discrete
valuation ring.
-/

noncomputable section

namespace KeystoneGraph

open MvPolynomial

variable (k : Type*) [Field k] [CharZero k] [IsAlgClosed k]

/-- The plane coordinate ring. -/
abbrev Plane := MvPolynomial (Fin 2) k

variable {k}

/-- The coefficientwise Jacobian determinant of a candidate Keller pair. -/
def jacobianDet (P Q : Plane k) : Plane k :=
  pderiv 0 P * pderiv 1 Q - pderiv 1 P * pderiv 0 Q

/-- A Keller pair: polynomial pair with unit (nonzero constant) Jacobian. -/
structure IsKellerPair (P Q : Plane k) : Prop where
  isUnit_jacobianDet : IsUnit (jacobianDet P Q)

/-- The coordinate subalgebra `k[P,Q]` of the plane. -/
def coordSubalgebra (P Q : Plane k) : Subalgebra k (Plane k) :=
  Algebra.adjoin k {P, Q}

/-- The coordinate ring `k[P,Q]` as a type. -/
abbrev coordRing (P Q : Plane k) : Type _ := ↥(coordSubalgebra P Q)

/-- The integral closure of `k[P,Q]` in the plane. Finiteness and
normality are recorded in `KeystoneGraph.IntegralClosureFinite`. -/
abbrev integralClosureInPlane (P Q : Plane k) : Type _ :=
  integralClosure (coordRing P Q) (Plane k)

end KeystoneGraph
