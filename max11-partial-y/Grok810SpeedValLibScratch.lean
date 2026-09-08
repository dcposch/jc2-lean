import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Value-reflected polynomials (speed prototype, untracked)

Reflective *value* form for the machine-emitted integer polynomial `def`s of the
`NonzeroFaceSplit` / `ClearedNumerator` families: the polynomial is carried as
data (a coefficient list and a list of exponent vectors) instead of as a
several-hundred-monomial expression tree, so elaboration does not resolve
`OfNat`/`HMul`/`HPow` once per monomial over an abstract `[CommRing R]`.

No `sorry`, no new axioms; every lemma below is `simp`/`cases`. -/

namespace Max11ReflectVal

variable {R : Type*} [CommRing R]

/-- `monoR as e = ∏ aᵢ ^ eᵢ`. -/
def monoR (as : List R) (e : List ℕ) : R := (List.zipWith (fun a i => a ^ i) as e).prod

/-- `polyR as cs es = Σ cᵢ * monoR as eᵢ`. -/
def polyR (as : List R) (cs : List R) (es : List (List ℕ)) : R :=
  (List.zipWith (fun c e => c * monoR as e) cs es).sum

@[simp] theorem monoR_nil_left (e : List ℕ) : monoR ([] : List R) e = 1 := by
  cases e <;> simp [monoR]
@[simp] theorem monoR_nil_right (as : List R) : monoR as ([] : List ℕ) = 1 := by
  cases as <;> simp [monoR]
@[simp] theorem monoR_cons (a : R) (as : List R) (i : ℕ) (e : List ℕ) :
    monoR (a :: as) (i :: e) = a ^ i * monoR as e := by simp [monoR]
@[simp] theorem polyR_nil_left (as : List R) (es : List (List ℕ)) :
    polyR as ([] : List R) es = 0 := by cases es <;> simp [polyR]
@[simp] theorem polyR_nil_right (as : List R) (cs : List R) :
    polyR as cs ([] : List (List ℕ)) = 0 := by cases cs <;> simp [polyR]
@[simp] theorem polyR_cons (as : List R) (c : R) (cs : List R)
    (e : List ℕ) (es : List (List ℕ)) :
    polyR as (c :: cs) (e :: es) = c * monoR as e + polyR as cs es := by simp [polyR]

end Max11ReflectVal
