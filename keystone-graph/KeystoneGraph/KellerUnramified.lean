/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic and Grok / xAI
agents (formalization)
-/
import Mathlib
import KeystoneGraph.Setup

/-!
# Formal unramifiedness of a plane Keller pair

For a Keller pair `P, Q` (Jacobian a unit in `k[x, y]`), the extension
`k[P, Q] ⊆ k[x, y]` is formally unramified: the Kähler module
`Ω[k[x,y] ⁄ k[P,Q]]` is a subsingleton.

The argument is the Ω-route of the Jacobian criterion (survey A.5–A.6).
`Ω[k[x,y] ⁄ k]` is free on `dx, dy`. The 2×2 change-of-basis matrix taking
`(dx, dy)` to `(dP, dQ)` is the Jacobian, hence a unit, so `dP, dQ` span.
Those two differentials lie in the range of `KaehlerDifferential.mapBaseChange`
because they are images of the two adjoined generators, so that map is
surjective. The second fundamental exact sequence then kills
`Ω[k[x,y] ⁄ k[P,Q]]`.

This does **not** use algebraic independence of `P, Q`: spanning of
`Ω[k[x,y] ⁄ k]` only needs the images of `dP` and `dQ` in the free module
on `dx, dy`.
-/

noncomputable section

namespace KeystoneGraph

open MvPolynomial
open KaehlerDifferential hiding map
open scoped TensorProduct

variable {k : Type*} [Field k]

/-! ### Jacobian matrix of a pair -/

/-- The pair `(P, Q)` as a `Fin 2`-indexed family of plane coordinates. -/
def pairCoords (P Q : Plane k) : Fin 2 → Plane k := ![P, Q]

@[simp] lemma pairCoords_zero (P Q : Plane k) : pairCoords P Q 0 = P := rfl

@[simp] lemma pairCoords_one (P Q : Plane k) : pairCoords P Q 1 = Q := rfl

/-- Jacobian matrix with columns the gradients of `P` and of `Q`:
`J i j = ∂(pairCoords P Q j) / ∂ xᵢ`. With this convention
`Matrix.toLin` on the Kähler basis `{dx, dy}` sends `dx` to `dP` and `dy`
to `dQ`. -/
def jacobianMatrix (P Q : Plane k) : Matrix (Fin 2) (Fin 2) (Plane k) :=
  fun i j => pderiv i (pairCoords P Q j)

lemma jacobianMatrix_apply (P Q : Plane k) (i j : Fin 2) :
    jacobianMatrix P Q i j = pderiv i (pairCoords P Q j) := rfl

lemma jacobianMatrix_det (P Q : Plane k) :
    (jacobianMatrix P Q).det = jacobianDet P Q := by
  simp [jacobianMatrix, jacobianDet, pairCoords, Matrix.det_fin_two]
  ring

lemma isUnit_jacobianMatrix {P Q : Plane k} (hPQ : IsKellerPair P Q) :
    IsUnit (jacobianMatrix P Q) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr <| by
    rw [jacobianMatrix_det]
    exact hPQ.isUnit_jacobianDet

/-! ### Free spanning of `Ω[k[x,y] ⁄ k]` by `dP, dQ` -/

/-- The universal derivation of a plane polynomial is the gradient pairing
against `{dx, dy}`. -/
lemma D_eq_sum_pderiv (f : Plane k) :
    D k (Plane k) f = ∑ i : Fin 2, pderiv i f • D k (Plane k) (X i) := by
  let b := mvPolynomialBasis k (Fin 2)
  calc
    D k (Plane k) f = ∑ i : Fin 2, b.repr (D k (Plane k) f) i • b i :=
      (b.sum_repr _).symm
    _ = ∑ i : Fin 2, pderiv i f • D k (Plane k) (X i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mvPolynomialBasis_repr_apply, mvPolynomialBasis_apply]

lemma toLin_jacobianMatrix_apply_basis (P Q : Plane k) (j : Fin 2) :
    Matrix.toLin (mvPolynomialBasis k (Fin 2)) (mvPolynomialBasis k (Fin 2))
        (jacobianMatrix P Q) (mvPolynomialBasis k (Fin 2) j) =
      D k (Plane k) (pairCoords P Q j) := by
  rw [Matrix.toLin_self, D_eq_sum_pderiv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mvPolynomialBasis_apply, jacobianMatrix_apply]

/-- Because the Jacobian is a unit, `dP` and `dQ` span `Ω[k[x,y] ⁄ k]`. -/
lemma span_D_pair_eq_top {P Q : Plane k} (hPQ : IsKellerPair P Q) :
    Submodule.span (Plane k) {D k (Plane k) P, D k (Plane k) Q} = ⊤ := by
  let b := mvPolynomialBasis k (Fin 2)
  let J := jacobianMatrix P Q
  have hJ : IsUnit J := isUnit_jacobianMatrix hPQ
  have hlin : IsUnit (Matrix.toLin b b J) := (Matrix.isUnit_toLin_iff b).mpr hJ
  have hsurj : Function.Surjective (Matrix.toLin b b J) :=
    ((Module.End.isUnit_iff _).mp hlin).2
  rw [eq_top_iff]
  intro ω _
  obtain ⟨x, rfl⟩ := hsurj ω
  rw [← b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [toLin_jacobianMatrix_apply_basis]
  fin_cases i
  · exact Submodule.subset_span (Set.mem_insert _ _)
  · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-! ### The two generators as elements of `k[P, Q]` -/

lemma mem_coordSubalgebra_P (P Q : Plane k) : P ∈ coordSubalgebra P Q :=
  Algebra.mem_adjoin_of_mem (Set.mem_insert P {Q})

lemma mem_coordSubalgebra_Q (P Q : Plane k) : Q ∈ coordSubalgebra P Q :=
  Algebra.mem_adjoin_of_mem (Set.mem_insert_of_mem P (Set.mem_singleton Q))

/-- The algebra map `k[P, Q] → k[x, y]` recovers `P` on the first generator. -/
lemma algebraMap_coord_P (P Q : Plane k) :
    algebraMap (coordSubalgebra P Q) (Plane k) ⟨P, mem_coordSubalgebra_P P Q⟩ = P := rfl

/-- The algebra map `k[P, Q] → k[x, y]` recovers `Q` on the second generator. -/
lemma algebraMap_coord_Q (P Q : Plane k) :
    algebraMap (coordSubalgebra P Q) (Plane k) ⟨Q, mem_coordSubalgebra_Q P Q⟩ = Q := rfl

lemma D_P_mem_range_mapBaseChange (P Q : Plane k) :
    D k (Plane k) P ∈
      LinearMap.range (mapBaseChange k (coordSubalgebra P Q) (Plane k)) := by
  refine ⟨1 ⊗ₜ D k (coordSubalgebra P Q) ⟨P, mem_coordSubalgebra_P P Q⟩, ?_⟩
  rw [mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D, algebraMap_coord_P]

lemma D_Q_mem_range_mapBaseChange (P Q : Plane k) :
    D k (Plane k) Q ∈
      LinearMap.range (mapBaseChange k (coordSubalgebra P Q) (Plane k)) := by
  refine ⟨1 ⊗ₜ D k (coordSubalgebra P Q) ⟨Q, mem_coordSubalgebra_Q P Q⟩, ?_⟩
  rw [mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D, algebraMap_coord_Q]

lemma mapBaseChange_surjective_of_isKellerPair {P Q : Plane k}
    (hPQ : IsKellerPair P Q) :
    Function.Surjective (mapBaseChange k (coordSubalgebra P Q) (Plane k)) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_D_pair_eq_top hPQ,
    Submodule.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact D_P_mem_range_mapBaseChange P Q
  · exact D_Q_mem_range_mapBaseChange P Q

/-! ### Main theorems -/

/-- For a Keller pair, `Ω[k[x,y] ⁄ k[P,Q]]` is the zero module. -/
theorem IsKellerPair.subsingleton_kaehlerDifferential {P Q : Plane k}
    (hPQ : IsKellerPair P Q) :
    Subsingleton Ω[Plane k ⁄ coordSubalgebra P Q] := by
  let A := coordSubalgebra P Q
  have hsurj : Function.Surjective (mapBaseChange k A (Plane k)) :=
    mapBaseChange_surjective_of_isKellerPair hPQ
  -- Second fundamental exact sequence: `range mapBaseChange = ker map`.
  have hzero : KaehlerDifferential.map k A (Plane k) (Plane k) = 0 := by
    rw [← LinearMap.ker_eq_top, ← range_mapBaseChange k A (Plane k),
      LinearMap.range_eq_top]
    exact hsurj
  replace hzero : KaehlerDifferential.map k A (Plane k) (Plane k) = 0 :=
    (LinearMap.surjective_iff_eq_zero_of_exact
      (exact_mapBaseChange_map k A (Plane k))).mp hsurj
  refine (subsingleton_iff_forall_eq 0).mpr fun y => ?_
  obtain ⟨x, rfl⟩ := map_surjective k A (Plane k) y
  simp [hzero]

/-- Equivalent packaging: the plane is formally unramified over `k[P, Q]`. -/
theorem IsKellerPair.formallyUnramified {P Q : Plane k} (hPQ : IsKellerPair P Q) :
    Algebra.FormallyUnramified (coordSubalgebra P Q) (Plane k) :=
  (Algebra.formallyUnramified_iff _ _).mpr hPQ.subsingleton_kaehlerDifferential

#print axioms IsKellerPair.subsingleton_kaehlerDifferential

end KeystoneGraph
