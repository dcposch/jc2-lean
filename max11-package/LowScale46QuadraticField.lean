import LowScale46Integrality
import GCD369DivisibleSourceExclusion
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Differential.Basic

/-! # The nonsquare quadratic working field for `(4,6)`

For a polynomial `H` with no polynomial square root, this module constructs
the irreducible quadratic `Z²-H` over `k(x)`.  Its adjoined root is the
literal square root needed by the remaining aligned scale-two source bridge,
and Mathlib's algebraic differential-field instance extends ordinary
`d/dx` uniquely to that field.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

/-- Typeclass form of the nonsquare branch, used to make the induced field
and differential instances available throughout the source bridge. -/
class NonsquarePolynomial46 (H : k[X]) : Prop where
  not_sq : ∀ h0 : k[X], H ≠ h0 ^ 2

/-- The quadratic polynomial `Z²-H` over the rational function field. -/
def alignedQuadraticPolynomial46 (H : k[X]) : (RatFunc k)[X] :=
  X ^ 2 - C (algebraMap k[X] (RatFunc k) H)

theorem alignedQuadraticPolynomial46_monic (H : k[X]) :
    (alignedQuadraticPolynomial46 H).Monic := by
  exact monic_X_pow_sub_C _ (by norm_num)

theorem alignedQuadraticPolynomial46_natDegree (H : k[X]) :
    (alignedQuadraticPolynomial46 H).natDegree = 2 := by
  exact natDegree_X_pow_sub_C

theorem alignedQuadraticPolynomial46_eval₂
    {S : Type*} [Ring S] (H : k[X]) (i : RatFunc k →+* S) (z : S) :
    (alignedQuadraticPolynomial46 H).eval₂ i z =
      z ^ 2 - i (algebraMap k[X] (RatFunc k) H) := by
  simp [alignedQuadraticPolynomial46]

/-- A root in `k(x)` would be a rational square root of `H`; normality of
`k[x]` would then turn it into a forbidden polynomial square root. -/
theorem alignedQuadraticPolynomial46_not_isRoot
    (H : k[X]) (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2) (z : RatFunc k) :
    ¬ IsRoot (alignedQuadraticPolynomial46 H) z := by
  intro hz
  have hzsq : z ^ 2 = algebraMap k[X] (RatFunc k) H := by
    apply sub_eq_zero.mp
    simpa [IsRoot, alignedQuadraticPolynomial46] using hz
  obtain ⟨h0, hh0⟩ :=
    ratFunc_isPolynomial_of_sq_isPolynomial46 z H hzsq
  apply hnsq h0
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  rw [map_pow, hh0, hzsq]

/-- `Z²-H` is irreducible over `k(x)` exactly in the nonsquare branch. -/
theorem alignedQuadraticPolynomial46_irreducible
    (H : k[X]) (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2) :
    Irreducible (alignedQuadraticPolynomial46 H) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [alignedQuadraticPolynomial46_natDegree]
    norm_num
  · exact alignedQuadraticPolynomial46_not_isRoot H hnsq

noncomputable instance alignedQuadraticIrreducibleFact46
    (H : k[X]) [NonsquarePolynomial46 H] :
    Fact (Irreducible (alignedQuadraticPolynomial46 H)) :=
  ⟨alignedQuadraticPolynomial46_irreducible H
    NonsquarePolynomial46.not_sq⟩

instance alignedQuadraticMonicFact46 (H : k[X]) :
    Fact (alignedQuadraticPolynomial46 H).Monic :=
  ⟨alignedQuadraticPolynomial46_monic H⟩

/-- In the adjoined-root quotient, the distinguished generator squares to
the embedded polynomial `H`. -/
theorem alignedQuadraticRoot_sq46 (H : k[X]) :
    (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) ^ 2 =
      algebraMap (RatFunc k)
        (AdjoinRoot (alignedQuadraticPolynomial46 H))
        (algebraMap k[X] (RatFunc k) H) := by
  have hself := AdjoinRoot.mk_self
    (f := alignedQuadraticPolynomial46 H)
  simpa [alignedQuadraticPolynomial46, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq] using sub_eq_zero.mp hself

/-- The base-fixing endomorphism which sends the adjoined root to its
negative. -/
noncomputable def alignedQuadraticDeckHom46 (H : k[X]) :
    AdjoinRoot (alignedQuadraticPolynomial46 H) →ₐ[RatFunc k]
      AdjoinRoot (alignedQuadraticPolynomial46 H) :=
  AdjoinRoot.liftAlgHom (alignedQuadraticPolynomial46 H)
    (Algebra.ofId _ _) (-AdjoinRoot.root (alignedQuadraticPolynomial46 H))
    (by
      rw [alignedQuadraticPolynomial46_eval₂]
      simp only [Even.neg_pow (by norm_num : Even 2)]
      rw [alignedQuadraticRoot_sq46]
      simp [Algebra.ofId_apply])

@[simp]
theorem alignedQuadraticDeckHom46_root (H : k[X]) :
    alignedQuadraticDeckHom46 H
        (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) =
      -AdjoinRoot.root (alignedQuadraticPolynomial46 H) := by
  simp [alignedQuadraticDeckHom46]

@[simp]
theorem alignedQuadraticDeckHom46_base (H : k[X]) (c : RatFunc k) :
    alignedQuadraticDeckHom46 H
        (algebraMap (RatFunc k)
          (AdjoinRoot (alignedQuadraticPolynomial46 H)) c) =
      algebraMap (RatFunc k)
        (AdjoinRoot (alignedQuadraticPolynomial46 H)) c := by
  exact (alignedQuadraticDeckHom46 H).commutes c

/-- The nontrivial deck involution of `k(x)(√H)/k(x)`. -/
noncomputable def alignedQuadraticDeck46 (H : k[X]) :
    AdjoinRoot (alignedQuadraticPolynomial46 H) ≃+*
      AdjoinRoot (alignedQuadraticPolynomial46 H) := by
  let tau := alignedQuadraticDeckHom46 H
  have htau : tau.comp tau = AlgHom.id (RatFunc k) _ := by
    apply AdjoinRoot.algHom_ext
    simp [tau]
  exact (AlgEquiv.ofAlgHom tau tau htau htau).toRingEquiv

theorem alignedQuadraticDeck46_root (H : k[X]) :
    alignedQuadraticDeck46 H
        (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) =
      -AdjoinRoot.root (alignedQuadraticPolynomial46 H) := by
  change alignedQuadraticDeckHom46 H
    (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) = _
  exact alignedQuadraticDeckHom46_root H

theorem alignedQuadraticDeck46_base (H : k[X]) (c : RatFunc k) :
    alignedQuadraticDeck46 H
        (algebraMap (RatFunc k)
          (AdjoinRoot (alignedQuadraticPolynomial46 H)) c) =
      algebraMap (RatFunc k)
        (AdjoinRoot (alignedQuadraticPolynomial46 H)) c := by
  change alignedQuadraticDeckHom46 H
    (algebraMap (RatFunc k)
      (AdjoinRoot (alignedQuadraticPolynomial46 H)) c) = _
  exact alignedQuadraticDeckHom46_base H c

/-- The fixed field of the quadratic deck involution is exactly `k(x)`.
This is the degree-two analogue of the Kummer fixed-field descent used by
the `(6,9)` formalization. -/
theorem alignedQuadraticFixedElementDescends46
    (H : k[X])
    (z : AdjoinRoot (alignedQuadraticPolynomial46 H))
    (hz : alignedQuadraticDeck46 H z = z) :
    ∃ c : RatFunc k,
      z = algebraMap (RatFunc k)
        (AdjoinRoot (alignedQuadraticPolynomial46 H)) c := by
  let pb := AdjoinRoot.powerBasis'
    (alignedQuadraticPolynomial46_monic H)
  have hdim : pb.dim = 2 := by
    change (alignedQuadraticPolynomial46 H).natDegree = 2
    exact alignedQuadraticPolynomial46_natDegree H
  let B : Module.Basis (Fin 2) (RatFunc k)
      (AdjoinRoot (alignedQuadraticPolynomial46 H)) :=
    pb.basis.reindex (finCongr hdim)
  let c0 : RatFunc k := B.repr z 0
  let c1 : RatFunc k := B.repr z 1
  have hB0 : B (0 : Fin 2) = 1 := by
    simp [B, pb]
  have hB1 : B (1 : Fin 2) =
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) := by
    simp [B, pb]
  have hzexp : algebraMap (RatFunc k) _ c0 +
      algebraMap (RatFunc k) _ c1 *
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) = z := by
    have hsum := B.sum_repr z
    rw [Fin.sum_univ_two, hB0, hB1] at hsum
    simpa [c0, c1, Algebra.smul_def] using hsum
  have hsigexp := congrArg (alignedQuadraticDeck46 H) hzexp
  simp only [map_add, map_mul, alignedQuadraticDeck46_base,
    alignedQuadraticDeck46_root] at hsigexp
  rw [hz, ← hzexp] at hsigexp
  have hexpB : c0 • B (0 : Fin 2) + (-c1) • B (1 : Fin 2) =
      c0 • B (0 : Fin 2) + c1 • B (1 : Fin 2) := by
    rw [hB0, hB1]
    simp only [Algebra.smul_def, map_neg]
    convert hsigexp using 1 <;> ring
  have hcoords := congrArg B.repr hexpB
  have h1 := congrArg (fun v => v (1 : Fin 2)) hcoords
  simp at h1
  have hc1 : c1 = 0 := by
    linear_combination (-1 / 2 : RatFunc k) * h1
  refine ⟨c0, ?_⟩
  rw [← hzexp, hc1]
  simp

/-- The composite embedding `k[x] → k(x) → k(x)(√H)` is injective. -/
theorem alignedQuadraticPolynomialMap_injective46
    (H : k[X]) (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2) :
    Function.Injective
      (algebraMap k[X] (AdjoinRoot (alignedQuadraticPolynomial46 H))) := by
  letI : Fact (Irreducible (alignedQuadraticPolynomial46 H)) :=
    ⟨alignedQuadraticPolynomial46_irreducible H hnsq⟩
  change Function.Injective
    ((AdjoinRoot.of (alignedQuadraticPolynomial46 H)).comp
      (algebraMap k[X] (RatFunc k)))
  exact (AdjoinRoot.coe_injective' (f := alignedQuadraticPolynomial46 H)).comp
    (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))

/-- The algebraic differential on the quadratic field restricts to ordinary
polynomial differentiation on `k[x]`. -/
theorem alignedQuadraticDeriv_polynomial46
    (H : k[X]) (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2) (P : k[X]) :
    letI : Fact (Irreducible (alignedQuadraticPolynomial46 H)) :=
      ⟨alignedQuadraticPolynomial46_irreducible H hnsq⟩
    letI : Fact (alignedQuadraticPolynomial46 H).Monic :=
      ⟨alignedQuadraticPolynomial46_monic H⟩
    Differential.deriv
        (algebraMap k[X] (AdjoinRoot (alignedQuadraticPolynomial46 H)) P) =
      algebraMap k[X] (AdjoinRoot (alignedQuadraticPolynomial46 H))
        P.derivative := by
  letI : Fact (Irreducible (alignedQuadraticPolynomial46 H)) :=
    ⟨alignedQuadraticPolynomial46_irreducible H hnsq⟩
  letI : Fact (alignedQuadraticPolynomial46 H).Monic :=
    ⟨alignedQuadraticPolynomial46_monic H⟩
  change Differential.deriv
      (algebraMap (RatFunc k) (AdjoinRoot (alignedQuadraticPolynomial46 H))
        (algebraMap k[X] (RatFunc k) P)) = _
  rw [deriv_algebraMap, GCD369RatFuncDerivative]
  exact (IsScalarTower.algebraMap_apply k[X] (RatFunc k)
    (AdjoinRoot (alignedQuadraticPolynomial46 H)) P.derivative).symm

/-- Because `k` is algebraically closed and the extension is algebraic, the
quadratic working field has no new differential constants. -/
theorem alignedQuadraticConstants46 [IsAlgClosed k]
    (H : k[X]) (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (c : AdjoinRoot (alignedQuadraticPolynomial46 H))
    (hc :
      letI : Fact (Irreducible (alignedQuadraticPolynomial46 H)) :=
        ⟨alignedQuadraticPolynomial46_irreducible H hnsq⟩
      letI : Fact (alignedQuadraticPolynomial46 H).Monic :=
        ⟨alignedQuadraticPolynomial46_monic H⟩
      Differential.deriv c = 0) :
    ∃ c0 : k, c =
      algebraMap k (AdjoinRoot (alignedQuadraticPolynomial46 H)) c0 := by
  letI : Fact (Irreducible (alignedQuadraticPolynomial46 H)) :=
    ⟨alignedQuadraticPolynomial46_irreducible H hnsq⟩
  letI : Fact (alignedQuadraticPolynomial46 H).Monic :=
    ⟨alignedQuadraticPolynomial46_monic H⟩
  letI : Algebra.IsIntegral (RatFunc k)
      (AdjoinRoot (alignedQuadraticPolynomial46 H)) :=
    AdjoinRoot.isIntegral_of_monic (alignedQuadraticPolynomial46_monic H)
  exact GCD369AlgebraicDifferentialConstantsDescend
    (fun a : RatFunc k => GCD369RatFuncConstants a) c hc

end Max11DegreeRoutes
