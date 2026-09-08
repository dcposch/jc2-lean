import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.BigOperators

/-! # A reflective degree checker for machine-emitted polynomial rest bounds.

SPEED (untracked working module; imported by the reflective swap-in candidates).

`compute_degree` closes `natDegree p ≤ d` by decomposing `p` structurally and
then `norm_num`-normalising the resulting `max` tree
(`Mathlib/Tactic/ComputeDegree.lean:497`).  On a rest polynomial with tens of
monomials over an abstract `[Field k]` that last step costs 40-350 s.

Here the polynomial is instead *reflected*: the CAS emits the coefficient list
and the exponent vectors, `natDegree_polyOf_le` is proved once by induction,
and the residual goal is a `max` tree of linear forms in the atom degrees that
`omega` closes directly.

No `sorry`, no new axioms.
-/

namespace Max11ReflectDeg

open Polynomial

variable {k : Type*} [CommRing k]

/-- `mono as e = ∏ aᵢ ^ eᵢ`, truncating at the shorter list. -/
noncomputable def mono (as : List k[X]) (e : List ℕ) : k[X] :=
  (List.zipWith (fun a i => a ^ i) as e).prod

/-- `polyOf as cs es = Σ cᵢ • mono as eᵢ`, truncating at the shorter list. -/
noncomputable def polyOf (as : List k[X]) (cs : List k) (es : List (List ℕ)) : k[X] :=
  (List.zipWith (fun c e => c • mono as e) cs es).sum

/-- The degree a monomial can have, as a linear form in the atom degrees. -/
def mdeg (ds : List ℕ) (e : List ℕ) : ℕ :=
  (List.zipWith (fun d i => i * d) ds e).sum

/-- **The checker.**  The largest monomial degree occurring in `es`. -/
def bnd (ds : List ℕ) (es : List (List ℕ)) : ℕ :=
  (es.map (mdeg ds)).foldr max 0

@[simp] theorem mono_nil_left (e : List ℕ) : mono ([] : List k[X]) e = 1 := by
  cases e <;> simp [mono]

@[simp] theorem mono_nil_right (as : List k[X]) : mono as ([] : List ℕ) = 1 := by
  cases as <;> simp [mono]

@[simp] theorem mono_cons (a : k[X]) (as : List k[X]) (i : ℕ) (e : List ℕ) :
    mono (a :: as) (i :: e) = a ^ i * mono as e := by
  simp [mono]

@[simp] theorem mdeg_nil_left (e : List ℕ) : mdeg [] e = 0 := by cases e <;> simp [mdeg]

@[simp] theorem mdeg_nil_right (ds : List ℕ) : mdeg ds [] = 0 := by cases ds <;> simp [mdeg]

@[simp] theorem mdeg_cons (d : ℕ) (ds : List ℕ) (i : ℕ) (e : List ℕ) :
    mdeg (d :: ds) (i :: e) = i * d + mdeg ds e := by
  simp [mdeg]

@[simp] theorem bnd_nil (ds : List ℕ) : bnd ds [] = 0 := by simp [bnd]

@[simp] theorem bnd_cons (ds : List ℕ) (e : List ℕ) (es : List (List ℕ)) :
    bnd ds (e :: es) = max (mdeg ds e) (bnd ds es) := by simp [bnd]

theorem natDegree_mono_le (as : List k[X]) (e : List ℕ) :
    (mono as e).natDegree ≤ mdeg (as.map natDegree) e := by
  induction as generalizing e with
  | nil => simp
  | cons a as ih =>
    cases e with
    | nil => simp
    | cons i e =>
      simp only [List.map_cons, mono_cons, mdeg_cons]
      refine le_trans (natDegree_mul_le) ?_
      exact Nat.add_le_add natDegree_pow_le (ih e)

@[simp] theorem polyOf_nil_left (as : List k[X]) (es : List (List ℕ)) :
    polyOf as ([] : List k) es = 0 := by cases es <;> simp [polyOf]

@[simp] theorem polyOf_nil_right (as : List k[X]) (cs : List k) :
    polyOf as cs ([] : List (List ℕ)) = 0 := by cases cs <;> simp [polyOf]

@[simp] theorem polyOf_cons (as : List k[X]) (c : k) (cs : List k)
    (e : List ℕ) (es : List (List ℕ)) :
    polyOf as (c :: cs) (e :: es) = c • mono as e + polyOf as cs es := by
  simp [polyOf]

/-- **Soundness.**  Every reflected polynomial's degree is bounded by the
checker's value on the atom degrees. -/
theorem natDegree_polyOf_le (as : List k[X]) (cs : List k) (es : List (List ℕ)) :
    (polyOf as cs es).natDegree ≤ bnd (as.map natDegree) es := by
  induction cs generalizing es with
  | nil => simp
  | cons c cs ih =>
    cases es with
    | nil => simp
    | cons e es =>
      simp only [polyOf_cons, bnd_cons]
      refine le_trans (natDegree_add_le _ _) ?_
      exact max_le_max (le_trans (natDegree_smul_le _ _) (natDegree_mono_le as e)) (ih es)

/-- The form actually used at a call site. -/
theorem natDegree_lt_of_bnd_lt {as : List k[X]} {cs : List k} {es : List (List ℕ)} {b : ℕ}
    (h : bnd (as.map natDegree) es < b) : (polyOf as cs es).natDegree < b :=
  lt_of_le_of_lt (natDegree_polyOf_le as cs es) h

/-! ## Branch-aware bound, for the `2ᵏ` case fans

The cone/kill modules prove one degree bound under hypotheses of the shape
`beta = 0 ∨ <linear inequality>` (a scalar coefficient) and
`B = 0 ∨ <linear inequality>` (a polynomial atom), and discharge them with a
`rcases … <;>` fan in which **every branch re-runs `compute_degree` on the
substituted polynomial** (`PALOMAR_COST_REPORT.md` §5 P3b: 2ᵏ `compute_degree`
calls).

`bnd` is blind to both kinds of vanishing, so it cannot see that a branch's
monomials die.  `degOk` is the branch-aware side condition instead: each
monomial either has a zero coefficient, or is itself zero (an atom occurring in
it vanished), or fits under the bound.  Reflecting once and applying
`natDegree_polyOf_lt_of_degOk` leaves a goal that is linear arithmetic over the
atom degrees plus two syntactic side conditions — so the fan runs on `omega`
and `simp`, not on `compute_degree`, and the polynomial is reflected exactly
once. -/

/-- Every monomial either has a zero coefficient, or is itself zero, or fits
strictly under `b`. -/
def degOk (as : List k[X]) (b : ℕ) : List k → List (List ℕ) → Prop
  | c :: cs, e :: es =>
      (c = 0 ∨ mono as e = 0 ∨ mdeg (as.map natDegree) e < b) ∧ degOk as b cs es
  | _, _ => True

@[simp] theorem degOk_nil_left (as : List k[X]) (b : ℕ) (es : List (List ℕ)) :
    degOk as b ([] : List k) es = True := by
  cases es <;> rfl

@[simp] theorem degOk_nil_right (as : List k[X]) (b : ℕ) (cs : List k) :
    degOk as b cs ([] : List (List ℕ)) = True := by
  cases cs <;> rfl

@[simp] theorem degOk_cons (as : List k[X]) (b : ℕ) (c : k) (cs : List k)
    (e : List ℕ) (es : List (List ℕ)) :
    degOk as b (c :: cs) (e :: es) =
      ((c = 0 ∨ mono as e = 0 ∨ mdeg (as.map natDegree) e < b) ∧ degOk as b cs es) := rfl

/-- **Soundness of the branch-aware checker.** -/
theorem natDegree_polyOf_lt_of_degOk {as : List k[X]} {cs : List k} {es : List (List ℕ)}
    {b : ℕ} (hb : 0 < b) (h : degOk as b cs es) :
    (polyOf as cs es).natDegree < b := by
  induction cs generalizing es with
  | nil => simpa using hb
  | cons c cs ih =>
    cases es with
    | nil => simpa using hb
    | cons e es =>
      rw [degOk_cons] at h
      obtain ⟨h1, h2⟩ := h
      rw [polyOf_cons]
      refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ (ih h2))
      rcases h1 with rfl | h1 | h1
      · simpa using hb
      · rw [h1, smul_zero]; simpa using hb
      · exact lt_of_le_of_lt
          (le_trans (natDegree_smul_le _ _) (natDegree_mono_le as e)) h1

/-! ## The `≤` form

Some call sites bound `natDegree p ≤ b` rather than `natDegree p < b` (a
vanishing primitive polynomial, `… .natDegree ≤ 0`).  That needs no positivity
side condition: `natDegree 0 = 0 ≤ b` for every `b : ℕ`. -/

/-- Every monomial either has a zero coefficient, or is itself zero, or fits
under `b`. -/
def degLe (as : List k[X]) (b : ℕ) : List k → List (List ℕ) → Prop
  | c :: cs, e :: es =>
      (c = 0 ∨ mono as e = 0 ∨ mdeg (as.map natDegree) e ≤ b) ∧ degLe as b cs es
  | _, _ => True

@[simp] theorem degLe_nil_left (as : List k[X]) (b : ℕ) (es : List (List ℕ)) :
    degLe as b ([] : List k) es = True := by cases es <;> rfl

@[simp] theorem degLe_nil_right (as : List k[X]) (b : ℕ) (cs : List k) :
    degLe as b cs ([] : List (List ℕ)) = True := by cases cs <;> rfl

@[simp] theorem degLe_cons (as : List k[X]) (b : ℕ) (c : k) (cs : List k)
    (e : List ℕ) (es : List (List ℕ)) :
    degLe as b (c :: cs) (e :: es) =
      ((c = 0 ∨ mono as e = 0 ∨ mdeg (as.map natDegree) e ≤ b) ∧ degLe as b cs es) := rfl

theorem natDegree_polyOf_le_of_degLe {as : List k[X]} {cs : List k}
    {es : List (List ℕ)} {b : ℕ} (h : degLe as b cs es) :
    (polyOf as cs es).natDegree ≤ b := by
  induction cs generalizing es with
  | nil => simp
  | cons c cs ih =>
    cases es with
    | nil => simp
    | cons e es =>
      rw [degLe_cons] at h
      obtain ⟨h1, h2⟩ := h
      rw [polyOf_cons]
      refine le_trans (natDegree_add_le _ _) (max_le ?_ (ih h2))
      rcases h1 with rfl | h1 | h1
      · simp
      · rw [h1, smul_zero]; simp
      · exact le_trans (le_trans (natDegree_smul_le _ _) (natDegree_mono_le as e)) h1

end Max11ReflectDeg
