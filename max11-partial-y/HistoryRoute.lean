import DegreeRoutes
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! # The nondivisible `(6,9)` history route

This module formalizes the elementary part of the classical large-source-
shear argument.  It separates the published prime-total-degree theorem from
the remaining exact total-degree calculation for a normalized `(6,9)` source.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- The exact classical total-degree input needed after shearing a normalized
`(6,9)` source whose common-core degree is not divisible by three. -/
def PlaneKeller23PrimeTotalDegreeRoute {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (p : ℕ),
    IsPlaneKellerPair P Q → p.Prime →
    P.totalDegree = 2 * p → Q.totalDegree = 3 * p →
    PlanePairGenerates P Q

/-- Images of the variables under the triangular source shear
`(x,y) ↦ (x,y+x^L)`. -/
def planeSourceShearVars {K : Type*} [CommRing K] (L : ℕ) :
    Fin 2 → MvPolynomial (Fin 2) K := fun i =>
  if i = 0 then X 0 else X 1 + X 0 ^ L

/-- The algebra homomorphism induced by `(x,y) ↦ (x,y+x^L)`. -/
def planeSourceShearHom {K : Type*} [CommRing K] (L : ℕ) :
    MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.bind₁ (planeSourceShearVars L)

/-- Images of the variables under the inverse triangular source shear. -/
def planeSourceUnshearVars {K : Type*} [CommRing K] (L : ℕ) :
    Fin 2 → MvPolynomial (Fin 2) K := fun i =>
  if i = 0 then X 0 else X 1 - X 0 ^ L

/-- The inverse algebra homomorphism induced by `(x,y) ↦ (x,y-x^L)`. -/
def planeSourceUnshearHom {K : Type*} [CommRing K] (L : ℕ) :
    MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.bind₁ (planeSourceUnshearVars L)

@[simp]
theorem planeSourceShearHom_X_zero {K : Type*} [CommRing K] (L : ℕ) :
    planeSourceShearHom (K := K) L (X 0) = X 0 := by
  simp [planeSourceShearHom, planeSourceShearVars]

@[simp]
theorem planeSourceShearHom_X_one {K : Type*} [CommRing K] (L : ℕ) :
    planeSourceShearHom (K := K) L (X 1) = X 1 + X 0 ^ L := by
  simp [planeSourceShearHom, planeSourceShearVars]

@[simp]
theorem planeSourceUnshearHom_X_zero {K : Type*} [CommRing K] (L : ℕ) :
    planeSourceUnshearHom (K := K) L (X 0) = X 0 := by
  simp [planeSourceUnshearHom, planeSourceUnshearVars]

@[simp]
theorem planeSourceUnshearHom_X_one {K : Type*} [CommRing K] (L : ℕ) :
    planeSourceUnshearHom (K := K) L (X 1) = X 1 - X 0 ^ L := by
  simp [planeSourceUnshearHom, planeSourceUnshearVars]

/-- The triangular source shear as an algebra automorphism. -/
def planeSourceShear (K : Type*) [CommRing K] (L : ℕ) :
    MvPolynomial (Fin 2) K ≃ₐ[K] MvPolynomial (Fin 2) K :=
  AlgEquiv.ofAlgHom (planeSourceShearHom L) (planeSourceUnshearHom L)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [planeSourceShearHom, planeSourceUnshearHom,
        planeSourceShearVars, planeSourceUnshearVars])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [planeSourceShearHom, planeSourceUnshearHom,
        planeSourceShearVars, planeSourceUnshearVars])

@[simp]
theorem planeSourceShear_apply {K : Type*} [CommRing K]
    (L : ℕ) (P : MvPolynomial (Fin 2) K) :
    planeSourceShear K L P = planeSourceShearHom L P := by
  rfl

/-- Applying a coefficient-algebra automorphism simultaneously to both
coordinates preserves generation of the ambient polynomial algebra. -/
theorem planePairGenerates_algEquiv_iff {K : Type*} [Field K]
    (e : MvPolynomial (Fin 2) K ≃ₐ[K] MvPolynomial (Fin 2) K)
    (P Q : MvPolynomial (Fin 2) K) :
    PlanePairGenerates (e P) (e Q) ↔ PlanePairGenerates P Q := by
  unfold PlanePairGenerates
  have himage : e '' ({P, Q} : Set (MvPolynomial (Fin 2) K)) =
      ({e P, e Q} : Set (MvPolynomial (Fin 2) K)) := by
    ext R
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨S, hS, rfl⟩
      rcases hS with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hR
      rcases hR with rfl | rfl
      · exact ⟨P, Or.inl rfl, rfl⟩
      · exact ⟨Q, Or.inr rfl, rfl⟩
  rw [← himage]
  change Algebra.adjoin K
      (e.toAlgHom '' ({P, Q} : Set (MvPolynomial (Fin 2) K))) = ⊤ ↔
    Algebra.adjoin K ({P, Q} : Set (MvPolynomial (Fin 2) K)) = ⊤
  rw [Algebra.adjoin_image K e.toAlgHom
    ({P, Q} : Set (MvPolynomial (Fin 2) K))]
  constructor
  · intro h
    have hcomp : e.symm.toAlgHom.comp e.toAlgHom =
        AlgHom.id K (MvPolynomial (Fin 2) K) := by
      apply MvPolynomial.algHom_ext
      intro i
      exact e.symm_apply_apply (X i)
    have hrange : e.symm.toAlgHom.range =
        (⊤ : Subalgebra K (MvPolynomial (Fin 2) K)) :=
      (AlgHom.range_eq_top e.symm.toAlgHom).mpr e.symm.surjective
    have hmap := congrArg
      (fun S : Subalgebra K (MvPolynomial (Fin 2) K) =>
        S.map e.symm.toAlgHom) h
    simpa [Subalgebra.map_map, hcomp, hrange] using hmap
  · intro h
    rw [h]
    rw [Algebra.map_top]
    exact (AlgHom.range_eq_top e.toAlgHom).mpr e.surjective

/-- The concrete triangular source shear preserves coordinate generation. -/
theorem planePairGenerates_sourceShear_iff {K : Type*} [Field K]
    (L : ℕ) (P Q : MvPolynomial (Fin 2) K) :
    PlanePairGenerates (planeSourceShear K L P) (planeSourceShear K L Q) ↔
      PlanePairGenerates P Q :=
  planePairGenerates_algEquiv_iff (planeSourceShear K L) P Q

/-- The `y` partial derivative commutes with the triangular source shear. -/
theorem pderiv_one_planeSourceShearHom {K : Type*} [CommRing K]
    (L : ℕ) (P : MvPolynomial (Fin 2) K) :
    pderiv 1 (planeSourceShearHom L P) =
      planeSourceShearHom L (pderiv 1 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [planeSourceShearHom]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      fin_cases i <;> simp [Derivation.leibniz, hP]

/-- The `x` partial derivative of a source shear satisfies the expected
chain rule. -/
theorem pderiv_zero_planeSourceShearHom {K : Type*} [CommRing K]
    (L : ℕ) (P : MvPolynomial (Fin 2) K) :
    pderiv 0 (planeSourceShearHom L P) =
      planeSourceShearHom L (pderiv 0 P) +
        MvPolynomial.C (L : K) * X 0 ^ (L - 1) *
          planeSourceShearHom L (pderiv 1 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [planeSourceShearHom]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
      ring
  | mul_X P i hP =>
      fin_cases i <;>
        simp [Derivation.leibniz, hP] <;> ring

/-- A simultaneous triangular source shear transports the Jacobian
determinant by the same algebra homomorphism. -/
theorem PlaneJacobian_planeSourceShearHom {K : Type*} [CommRing K]
    (L : ℕ) (P Q : MvPolynomial (Fin 2) K) :
    PlaneJacobian (planeSourceShearHom L P) (planeSourceShearHom L Q) =
      planeSourceShearHom L (PlaneJacobian P Q) := by
  simp only [PlaneJacobian, pderiv_zero_planeSourceShearHom,
    pderiv_one_planeSourceShearHom, map_sub, map_mul]
  ring

/-- A triangular source shear preserves the Keller condition. -/
theorem IsPlaneKellerPair.sourceShear {K : Type*} [Field K]
    {P Q : MvPolynomial (Fin 2) K} (h : IsPlaneKellerPair P Q)
    (L : ℕ) :
    IsPlaneKellerPair (planeSourceShear K L P)
      (planeSourceShear K L Q) := by
  rcases h with ⟨j, hj, hjac⟩
  refine ⟨j, hj, ?_⟩
  rw [planeSourceShear_apply, planeSourceShear_apply,
    PlaneJacobian_planeSourceShearHom, hjac]
  simp [planeSourceShearHom]

/-- Dirichlet supplies an arbitrarily large shear exponent for which the
new common total-degree core is prime. -/
theorem exists_large_prime_eq_add_three_mul (H B : ℕ)
    (hH : ¬ 3 ∣ H) :
    ∃ L, B < L ∧ (H + 3 * L).Prime := by
  have hcop : H.Coprime 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd.mpr hH).symm)
  obtain ⟨p, hpbound, hpprime, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (H + 3 * B)
      (q := 3) (a := H) (by norm_num) hcop
  have hHp : H ≤ p := by omega
  obtain ⟨L, hpEq⟩ :=
    (Nat.modEq_iff_exists_eq_add hHp).mp hpmod.symm
  refine ⟨L, ?_, ?_⟩
  · omega
  · rwa [← hpEq]

/-- The exact degree calculation used by the historical source-shear
argument, exposed as a reusable proposition.

Its proof in `HistoryDegree` chooses `B` larger than all competing weighted degrees.
For every `L > B`, the terms coming from the nonzero leading `y` coefficients
`h²` and `h³` then uniquely determine the displayed total degrees. -/
def PlaneKeller69SourceShearExactTotalDegreeRoute
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : K[X]),
    Normalized69Source P Q h →
    ∃ B, ∀ L, B < L →
      (planeSourceShear K L P).totalDegree =
          2 * (h.natDegree + 3 * L) ∧
        (planeSourceShear K L Q).totalDegree =
          3 * (h.natDegree + 3 * L)

/-- The nondivisible-core `(6,9)` history route, conditional exactly on the
explicit source-shear degree calculation and the classical theorem for
prime common total-degree core.  All automorphism, Keller, generation, and
prime-selection steps are discharged in this module. -/
theorem planeKeller69NondivisibleCoreRoute_of_totalDegree23Prime
    {K : Type*} [Field K]
    (hdegree : PlaneKeller69SourceShearExactTotalDegreeRoute (K := K))
    (hprimeRoute : PlaneKeller23PrimeTotalDegreeRoute (K := K)) :
    PlaneKeller69NondivisibleCoreRoute (K := K) := by
  intro P Q h hsource hnondiv
  obtain ⟨B, hB⟩ := hdegree P Q h hsource
  obtain ⟨L, hBL, hp⟩ :=
    exists_large_prime_eq_add_three_mul h.natDegree B hnondiv
  have hKeller :
      IsPlaneKellerPair (planeSourceShear K L P)
        (planeSourceShear K L Q) :=
    IsPlaneKellerPair.sourceShear hsource.2.2.2.2.2 L
  obtain ⟨hPdegree, hQdegree⟩ := hB L hBL
  have hgenerates :
      PlanePairGenerates (planeSourceShear K L P)
        (planeSourceShear K L Q) :=
    hprimeRoute (planeSourceShear K L P) (planeSourceShear K L Q)
      (h.natDegree + 3 * L) hKeller hp hPdegree hQdegree
  exact (planePairGenerates_sourceShear_iff L P Q).mp hgenerates

end Max11DegreeRoutes
