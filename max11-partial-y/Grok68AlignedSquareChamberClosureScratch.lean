import Grok68AlignedSquareClearedNumeratorScratch
import Grok68AlignedSquarePoleCeilingScratch
import Grok68ScaleTwoDegreeZeroDifferentialBridgeScratch
import LowScale68ScaleTwoAlignedFace
import Grok68ScaleTwoInterfaceCompositionScratch

/-! # CLOSED. Source-facing closure of the `(6,8)` scale-two aligned-square chamber

Untracked working note.  No tracked file was edited.

Lanes W0, W, Z of `Grok68AlignedSquareTowerPlanScratch.md`.  Parents
(tracked, green):

* P1 `Grok68ScaleTwoDegreeZeroDifferentialBridgeScratch`
  (`degreeZeroPrimitive68_ratFuncDeriv_eq_simplePole`);
* C `Grok68AlignedSquareClearedNumeratorScratch`
  (`alignedSquareClearedNumerator68_eq_pow_mul_primitive`,
  `alignedSquarePrimitive68_scaledDeriv_eq_simplePole`);
* T `Grok68AlignedSquarePoleCeilingScratch`
  (`alignedSquareFace68_order65Grandchildren` on `hclear`/`hderiv`/`hj`
  with linear `h0` and a root `a`).

Model: `Grok610AlignedSquareChamberClosureScratch` instantiates
`hclear`/`hderiv` from a literal source and the wrapper; the `(4,10)`
aligned leaf then composes the emptied square chamber into the
normalized scale-two route.

* **W0.** From `SquareZeroLIntegratedLocalRootData68` alone:
  `affineDepress68` preserves degree, `depressedSextic68` /
  `depressedOctic68` are monic of degrees `6`/`8`, and
  `sextic_eq`/`octic_eq`/`center_eq` therefore force
  `p.natDegree = 6`, `q.natDegree = 8`, `algebraMap (p.coeff 6) = h^6`,
  `algebraMap (q.coeff 8) = h^8`, the aligned relation
  `3 q.coeff 7 = 4 p.coeff 5 h0^2` (`L = 0`), and
  `A = depressedA68 h r a5 a4`, …, `V = depressedV68 …`.
* **W.** `SquareZeroLIntegratedLocalRootData68.primitive_deriv_eq_simplePole68`
  from `T.source.bracket_eq` and P1, after the W0 identification of the
  source primitive with the integrated depressed coordinates.
* **Z.** `hclear` from lane C on the literal coefficients, `hderiv` from
  W (scaled by C), then `alignedSquareFace68_order65Grandchildren` at
  the root of `h0`.

**CLOSED:** `planeKeller68AlignedSquareLocalRootExclusion_closed`.
**CLOSED:** `normalized68ScaleTwo_alignedSquare_false`.
**CLOSED:** `planeKellerNormalized68ScaleTwoRoute_of_quadraticPacket`.

FLAG: 68 ALIGNED-SQUARE CLOSED

There is no unused compact-numerator order after `65`.  The remaining
open scale-two chamber is the aligned nonsquare quadratic packet.
No `sorry`, no new axioms, no finite-root shortcut, no closure
overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Depressed monic degrees -/

section DepressedMonicDegree68

variable {F : Type*} [Field F] [CharZero F]

theorem alignedSquare_coeff_depressedSextic68_six
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 6 = 1 := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedSextic68_five
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 5 = 0 := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedSextic68_four
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 4 = A := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedSextic68_three
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 3 = B := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedSextic68_two
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 2 = C0 := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedSextic68_one
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 1 = D := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedSextic68_zero
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).coeff 0 = E := by
  simp [depressedSextic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_natDegree_le_depressedSextic68
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).natDegree ≤ 6 := by
  have add6 {p q : F[X]} (hp : p.natDegree ≤ 6) (hq : q.natDegree ≤ 6) :
      (p + q).natDegree ≤ 6 :=
    (natDegree_add_le p q).trans (max_le hp hq)
  have term (c : F) (k : ℕ) (hk : k ≤ 6) :
      (C c * X ^ k : F[X]).natDegree ≤ 6 :=
    (natDegree_C_mul_X_pow_le c k).trans hk
  simp only [depressedSextic68]
  have h0 : (X ^ 6 : F[X]).natDegree ≤ 6 := natDegree_X_pow_le (R := F) 6
  have h1 : (X ^ 6 + C A * X ^ 4).natDegree ≤ 6 :=
    add6 h0 (term A 4 (by omega))
  have h2 : (X ^ 6 + C A * X ^ 4 + C B * X ^ 3).natDegree ≤ 6 :=
    add6 h1 (term B 3 (by omega))
  have h3 : (X ^ 6 + C A * X ^ 4 + C B * X ^ 3 +
      C C0 * X ^ 2).natDegree ≤ 6 :=
    add6 h2 (term C0 2 (by omega))
  have h4 : (X ^ 6 + C A * X ^ 4 + C B * X ^ 3 + C C0 * X ^ 2 +
      C D * X).natDegree ≤ 6 :=
    add6 h3 ((natDegree_C_mul_le D X).trans
      (natDegree_X_le.trans (by omega)))
  exact add6 h4 ((natDegree_C E).trans_le (by omega))

theorem alignedSquare_coeff_depressedSextic68_of_gt_six
    (A B C0 D E : F) {n : ℕ} (hn : 6 < n) :
    (depressedSextic68 A B C0 D E).coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (alignedSquare_natDegree_le_depressedSextic68 A B C0 D E) hn)

theorem alignedSquare_natDegree_depressedSextic68
    (A B C0 D E : F) :
    (depressedSextic68 A B C0 D E).natDegree = 6 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (alignedSquare_natDegree_le_depressedSextic68 A B C0 D E)
    (by
      rw [alignedSquare_coeff_depressedSextic68_six]
      exact one_ne_zero)

theorem alignedSquare_coeff_depressedOctic68_eight
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 8 = 1 := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedOctic68_seven
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 7 = L := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedOctic68_six
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 6 = P := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedOctic68_five
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 5 = Q := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedOctic68_four
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 4 = R := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedOctic68_three
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 3 = S := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedOctic68_two
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 2 = T := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedOctic68_one
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 1 = U := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_coeff_depressedOctic68_zero
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).coeff 0 = V := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

theorem alignedSquare_natDegree_le_depressedOctic68
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).natDegree ≤ 8 := by
  have add8 {p q : F[X]} (hp : p.natDegree ≤ 8) (hq : q.natDegree ≤ 8) :
      (p + q).natDegree ≤ 8 :=
    (natDegree_add_le p q).trans (max_le hp hq)
  have term (c : F) (k : ℕ) (hk : k ≤ 8) :
      (C c * X ^ k : F[X]).natDegree ≤ 8 :=
    (natDegree_C_mul_X_pow_le c k).trans hk
  simp only [depressedOctic68]
  have h0 : (X ^ 8 : F[X]).natDegree ≤ 8 := natDegree_X_pow_le (R := F) 8
  have h1 : (X ^ 8 + C L * X ^ 7).natDegree ≤ 8 :=
    add8 h0 (term L 7 (by omega))
  have h2 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6).natDegree ≤ 8 :=
    add8 h1 (term P 6 (by omega))
  have h3 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6 + C Q * X ^ 5).natDegree ≤ 8 :=
    add8 h2 (term Q 5 (by omega))
  have h4 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6 + C Q * X ^ 5 +
      C R * X ^ 4).natDegree ≤ 8 :=
    add8 h3 (term R 4 (by omega))
  have h5 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6 + C Q * X ^ 5 +
      C R * X ^ 4 + C S * X ^ 3).natDegree ≤ 8 :=
    add8 h4 (term S 3 (by omega))
  have h6 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6 + C Q * X ^ 5 +
      C R * X ^ 4 + C S * X ^ 3 + C T * X ^ 2).natDegree ≤ 8 :=
    add8 h5 (term T 2 (by omega))
  have h7 : (X ^ 8 + C L * X ^ 7 + C P * X ^ 6 + C Q * X ^ 5 +
      C R * X ^ 4 + C S * X ^ 3 + C T * X ^ 2 + C U * X).natDegree ≤ 8 :=
    add8 h6 ((natDegree_C_mul_le U X).trans
      (natDegree_X_le.trans (by omega)))
  exact add8 h7 ((natDegree_C V).trans_le (by omega))

theorem alignedSquare_coeff_depressedOctic68_of_gt_eight
    (L P Q R S T U V : F) {n : ℕ} (hn : 8 < n) :
    (depressedOctic68 L P Q R S T U V).coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (alignedSquare_natDegree_le_depressedOctic68 L P Q R S T U V) hn)

theorem alignedSquare_natDegree_depressedOctic68
    (L P Q R S T U V : F) :
    (depressedOctic68 L P Q R S T U V).natDegree = 8 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (alignedSquare_natDegree_le_depressedOctic68 L P Q R S T U V)
    (by
      rw [alignedSquare_coeff_depressedOctic68_eight]
      exact one_ne_zero)

theorem alignedSquare_natDegree_affineScale68
    (h r : F) (hh : h ≠ 0) :
    ((X - C r) * C h⁻¹).natDegree = 1 := by
  have hinv : h⁻¹ ≠ 0 := inv_ne_zero hh
  rw [mul_comm, natDegree_C_mul hinv, natDegree_X_sub_C]

theorem alignedSquare_leadingCoeff_affineScale68
    (h r : F) (hh : h ≠ 0) :
    ((X - C r) * C h⁻¹).leadingCoeff = h⁻¹ := by
  have hinv : h⁻¹ ≠ 0 := inv_ne_zero hh
  have hdeg := alignedSquare_natDegree_affineScale68 h r hh
  rw [leadingCoeff, hdeg, mul_comm, coeff_C_mul]
  simp [coeff_sub, coeff_X, coeff_C]

end DepressedMonicDegree68

#print axioms alignedSquare_natDegree_depressedSextic68
#print axioms alignedSquare_natDegree_depressedOctic68
#print axioms alignedSquare_natDegree_affineScale68
#print axioms alignedSquare_leadingCoeff_affineScale68

/-! ## W0: degrees, leadings, alignment, and coordinate identification -/

section StructureUnpack68

variable {k : Type*} [Field k] [CharZero k]

/-- A mapped source whose affine depression is a monic depressed sextic
is itself degree six with leading coefficient `h^6`. -/
theorem affineDepress_eq_depressedSextic68_degree
    (p : k[X][X]) (h r A B C0 D E : RatFunc k) (hh : h ≠ 0)
    (heq : affineDepress68 h r (sourceToRatFunc68 p) =
      depressedSextic68 A B C0 D E) :
    p.natDegree = 6 ∧
      algebraMap k[X] (RatFunc k) (p.coeff 6) = h ^ 6 := by
  let u : (RatFunc k)[X] := (X - C r) * C h⁻¹
  have hu : u.natDegree = 1 :=
    alignedSquare_natDegree_affineScale68 h r hh
  have hulead : u.leadingCoeff = h⁻¹ :=
    alignedSquare_leadingCoeff_affineScale68 h r hh
  have htop :
      (depressedSextic68 A B C0 D E).coeff 6 = 1 :=
    alignedSquare_coeff_depressedSextic68_six A B C0 D E
  have hdegS :
      (depressedSextic68 A B C0 D E).natDegree = 6 :=
    alignedSquare_natDegree_depressedSextic68 A B C0 D E
  have hpmap :
      (sourceToRatFunc68 p).natDegree = p.natDegree := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using
      Polynomial.natDegree_map_eq_of_injective
        (FaithfulSMul.algebraMap_injective k[X] (RatFunc k)) p
  have hpne : sourceToRatFunc68 p ≠ 0 := by
    intro hz
    have hzero : affineDepress68 h r (sourceToRatFunc68 p) = 0 := by
      simp [affineDepress68, hz]
    have hcoeff := congrArg (fun f : (RatFunc k)[X] => f.coeff 6) hzero
    rw [heq, htop, coeff_zero] at hcoeff
    exact one_ne_zero hcoeff
  have hcomp :
      (affineDepress68 h r (sourceToRatFunc68 p)).natDegree =
        (sourceToRatFunc68 p).natDegree * u.natDegree := by
    dsimp only [affineDepress68, u]
    rw [Polynomial.natDegree_comp]
  have hpdeg : p.natDegree = 6 := by
    have haff : (affineDepress68 h r (sourceToRatFunc68 p)).natDegree =
        6 := by
      rw [heq, hdegS]
    have : p.natDegree * 1 = 6 := by
      rw [← hpmap, ← hu, ← hcomp, haff]
    simpa using this
  refine ⟨hpdeg, ?_⟩
  have hlead_aff :
      (affineDepress68 h r (sourceToRatFunc68 p)).leadingCoeff = 1 := by
    rw [leadingCoeff, show (affineDepress68 h r (sourceToRatFunc68 p)).natDegree = 6
        by rw [heq, hdegS], heq, htop]
  have hlead_comp :
      (affineDepress68 h r (sourceToRatFunc68 p)).leadingCoeff =
        (sourceToRatFunc68 p).leadingCoeff *
          u.leadingCoeff ^ (sourceToRatFunc68 p).natDegree := by
    dsimp only [affineDepress68, u]
    exact Polynomial.leadingCoeff_comp (by rw [hu]; exact one_ne_zero)
  have hmaplead :
      (sourceToRatFunc68 p).leadingCoeff =
        algebraMap k[X] (RatFunc k) (p.coeff 6) := by
    rw [leadingCoeff, hpmap, hpdeg]
    simp [sourceToRatFunc68, sourceToRatFunc46, coeff_map]
  have hprod :
      algebraMap k[X] (RatFunc k) (p.coeff 6) * h⁻¹ ^ 6 = 1 := by
    calc
      algebraMap k[X] (RatFunc k) (p.coeff 6) * h⁻¹ ^ 6 =
          (sourceToRatFunc68 p).leadingCoeff *
            u.leadingCoeff ^ (sourceToRatFunc68 p).natDegree := by
        rw [hmaplead, hulead, hpmap, hpdeg]
      _ = (affineDepress68 h r (sourceToRatFunc68 p)).leadingCoeff :=
        hlead_comp.symm
      _ = 1 := hlead_aff
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  calc
    algebraMap k[X] (RatFunc k) (p.coeff 6) =
        algebraMap k[X] (RatFunc k) (p.coeff 6) * h⁻¹ ^ 6 * h ^ 6 := by
      field_simp [hh]
    _ = 1 * h ^ 6 := by rw [hprod]
    _ = h ^ 6 := one_mul _

/-- A mapped source whose affine depression is a monic depressed octic
is itself degree eight with leading coefficient `h^8`. -/
theorem affineDepress_eq_depressedOctic68_degree
    (q : k[X][X]) (h r L P Q R S T U V : RatFunc k) (hh : h ≠ 0)
    (heq : affineDepress68 h r (sourceToRatFunc68 q) =
      depressedOctic68 L P Q R S T U V) :
    q.natDegree = 8 ∧
      algebraMap k[X] (RatFunc k) (q.coeff 8) = h ^ 8 := by
  let u : (RatFunc k)[X] := (X - C r) * C h⁻¹
  have hu : u.natDegree = 1 :=
    alignedSquare_natDegree_affineScale68 h r hh
  have hulead : u.leadingCoeff = h⁻¹ :=
    alignedSquare_leadingCoeff_affineScale68 h r hh
  have htop :
      (depressedOctic68 L P Q R S T U V).coeff 8 = 1 :=
    alignedSquare_coeff_depressedOctic68_eight L P Q R S T U V
  have hdegO :
      (depressedOctic68 L P Q R S T U V).natDegree = 8 :=
    alignedSquare_natDegree_depressedOctic68 L P Q R S T U V
  have hqmap :
      (sourceToRatFunc68 q).natDegree = q.natDegree := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using
      Polynomial.natDegree_map_eq_of_injective
        (FaithfulSMul.algebraMap_injective k[X] (RatFunc k)) q
  have hqne : sourceToRatFunc68 q ≠ 0 := by
    intro hz
    have hzero : affineDepress68 h r (sourceToRatFunc68 q) = 0 := by
      simp [affineDepress68, hz]
    have hcoeff := congrArg (fun f : (RatFunc k)[X] => f.coeff 8) hzero
    rw [heq, htop, coeff_zero] at hcoeff
    exact one_ne_zero hcoeff
  have hcomp :
      (affineDepress68 h r (sourceToRatFunc68 q)).natDegree =
        (sourceToRatFunc68 q).natDegree * u.natDegree := by
    dsimp only [affineDepress68, u]
    rw [Polynomial.natDegree_comp]
  have hqdeg : q.natDegree = 8 := by
    have haff : (affineDepress68 h r (sourceToRatFunc68 q)).natDegree =
        8 := by
      rw [heq, hdegO]
    have : q.natDegree * 1 = 8 := by
      rw [← hqmap, ← hu, ← hcomp, haff]
    simpa using this
  refine ⟨hqdeg, ?_⟩
  have hlead_aff :
      (affineDepress68 h r (sourceToRatFunc68 q)).leadingCoeff = 1 := by
    rw [leadingCoeff, show (affineDepress68 h r (sourceToRatFunc68 q)).natDegree = 8
        by rw [heq, hdegO], heq, htop]
  have hlead_comp :
      (affineDepress68 h r (sourceToRatFunc68 q)).leadingCoeff =
        (sourceToRatFunc68 q).leadingCoeff *
          u.leadingCoeff ^ (sourceToRatFunc68 q).natDegree := by
    dsimp only [affineDepress68, u]
    exact Polynomial.leadingCoeff_comp (by rw [hu]; exact one_ne_zero)
  have hmaplead :
      (sourceToRatFunc68 q).leadingCoeff =
        algebraMap k[X] (RatFunc k) (q.coeff 8) := by
    rw [leadingCoeff, hqmap, hqdeg]
    simp [sourceToRatFunc68, sourceToRatFunc46, coeff_map]
  have hprod :
      algebraMap k[X] (RatFunc k) (q.coeff 8) * h⁻¹ ^ 8 = 1 := by
    calc
      algebraMap k[X] (RatFunc k) (q.coeff 8) * h⁻¹ ^ 8 =
          (sourceToRatFunc68 q).leadingCoeff *
            u.leadingCoeff ^ (sourceToRatFunc68 q).natDegree := by
        rw [hmaplead, hulead, hqmap, hqdeg]
      _ = (affineDepress68 h r (sourceToRatFunc68 q)).leadingCoeff :=
        hlead_comp.symm
      _ = 1 := hlead_aff
  have hh8 : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  calc
    algebraMap k[X] (RatFunc k) (q.coeff 8) =
        algebraMap k[X] (RatFunc k) (q.coeff 8) * h⁻¹ ^ 8 * h ^ 8 := by
      field_simp [hh]
    _ = 1 * h ^ 8 := by rw [hprod]
    _ = h ^ 8 := one_mul _

end StructureUnpack68

#print axioms affineDepress_eq_depressedSextic68_degree
#print axioms affineDepress_eq_depressedOctic68_degree

section LocalRootUnpack68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- **W0.** Degrees, leadings, alignment, and the identification of the
integrated coordinates with the explicit depression of the literal
source coefficients. -/
theorem SquareZeroLIntegratedLocalRootData68.coords68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    let h := algebraMap k[X] (RatFunc k) h0
    let a5 := algebraMap k[X] (RatFunc k) (p.coeff 5)
    let a4 := algebraMap k[X] (RatFunc k) (p.coeff 4)
    let a3 := algebraMap k[X] (RatFunc k) (p.coeff 3)
    let a2 := algebraMap k[X] (RatFunc k) (p.coeff 2)
    let a1 := algebraMap k[X] (RatFunc k) (p.coeff 1)
    let a0 := algebraMap k[X] (RatFunc k) (p.coeff 0)
    let b7 := algebraMap k[X] (RatFunc k) (q.coeff 7)
    let b6 := algebraMap k[X] (RatFunc k) (q.coeff 6)
    let b5 := algebraMap k[X] (RatFunc k) (q.coeff 5)
    let b4 := algebraMap k[X] (RatFunc k) (q.coeff 4)
    let b3 := algebraMap k[X] (RatFunc k) (q.coeff 3)
    let b2 := algebraMap k[X] (RatFunc k) (q.coeff 2)
    let b1 := algebraMap k[X] (RatFunc k) (q.coeff 1)
    let b0 := algebraMap k[X] (RatFunc k) (q.coeff 0)
    p.natDegree = 6 ∧
      q.natDegree = 8 ∧
      algebraMap k[X] (RatFunc k) (p.coeff 6) = h ^ 6 ∧
      algebraMap k[X] (RatFunc k) (q.coeff 8) = h ^ 8 ∧
      (3 : k[X]) * q.coeff 7 = (4 : k[X]) * p.coeff 5 * h0 ^ 2 ∧
      T.source.A = depressedA68 h T.source.r a5 a4 ∧
      T.source.B = depressedB68 h T.source.r a5 a4 a3 ∧
      T.source.C0 = depressedC68 h T.source.r a5 a4 a3 a2 ∧
      T.source.D = depressedD68 h T.source.r a5 a4 a3 a2 a1 ∧
      T.source.E = depressedE68 h T.source.r a5 a4 a3 a2 a1 a0 ∧
      depressedL68 h T.source.r b7 = RatFunc.C (0 : k) ∧
      integratedP68 T.source.A (RatFunc.C T.source.alpha) =
        depressedP68 h T.source.r b7 b6 ∧
      integratedQ68 (RatFunc.C (0 : k)) T.source.A T.source.B
          (RatFunc.C T.source.beta) =
        depressedQ68 h T.source.r b7 b6 b5 ∧
      integratedR68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.gamma) =
        depressedR68 h T.source.r b7 b6 b5 b4 ∧
      integratedS68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
          T.source.D (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.delta) =
        depressedS68 h T.source.r b7 b6 b5 b4 b3 ∧
      integratedT68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
          T.source.D T.source.E (RatFunc.C T.source.alpha)
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.epsilon) =
        depressedT68 h T.source.r b7 b6 b5 b4 b3 b2 ∧
      integratedU68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
          T.source.D T.source.E (RatFunc.C T.source.alpha)
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.delta) (RatFunc.C T.source.zeta) =
        depressedU68 h T.source.r b7 b6 b5 b4 b3 b2 b1 ∧
      integratedV68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
          T.source.D T.source.E (RatFunc.C T.source.alpha)
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
          (RatFunc.C T.source.eta) =
        depressedV68 h T.source.r b7 b6 b5 b4 b3 b2 b1 b0 := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
  have hh : h ≠ 0 := RatFunc.algebraMap_ne_zero T.scale_ne_zero
  obtain ⟨hp, hpTop⟩ :=
    affineDepress_eq_depressedSextic68_degree p h T.source.r T.source.A
      T.source.B T.source.C0 T.source.D T.source.E hh T.source.sextic_eq
  obtain ⟨hq, hqTop⟩ :=
    affineDepress_eq_depressedOctic68_degree q h T.source.r
      (RatFunc.C (0 : k))
      (integratedP68 T.source.A (RatFunc.C T.source.alpha))
      (integratedQ68 (RatFunc.C (0 : k)) T.source.A T.source.B
        (RatFunc.C T.source.beta))
      (integratedR68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
        (RatFunc.C T.source.alpha) (RatFunc.C T.source.gamma))
      (integratedS68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
        T.source.D (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
        (RatFunc.C T.source.delta))
      (integratedT68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C T.source.alpha)
        (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.epsilon))
      (integratedU68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C T.source.alpha)
        (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.delta) (RatFunc.C T.source.zeta))
      (integratedV68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C T.source.alpha)
        (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
        (RatFunc.C T.source.eta))
      hh T.source.octic_eq
  have hpDep :=
    affineDepress_sourceSextic68 p h T.source.r hp hh hpTop T.source.center_eq
  have hqDep :=
    affineDepress_sourceOctic68 q h T.source.r hq hh hqTop
  have hsextic :
      depressedSextic68
          (depressedA68 h T.source.r a5 a4)
          (depressedB68 h T.source.r a5 a4 a3)
          (depressedC68 h T.source.r a5 a4 a3 a2)
          (depressedD68 h T.source.r a5 a4 a3 a2 a1)
          (depressedE68 h T.source.r a5 a4 a3 a2 a1 a0) =
        depressedSextic68 T.source.A T.source.B T.source.C0 T.source.D
          T.source.E :=
    hpDep.symm.trans T.source.sextic_eq
  have hoctic :
      depressedOctic68
          (depressedL68 h T.source.r b7)
          (depressedP68 h T.source.r b7 b6)
          (depressedQ68 h T.source.r b7 b6 b5)
          (depressedR68 h T.source.r b7 b6 b5 b4)
          (depressedS68 h T.source.r b7 b6 b5 b4 b3)
          (depressedT68 h T.source.r b7 b6 b5 b4 b3 b2)
          (depressedU68 h T.source.r b7 b6 b5 b4 b3 b2 b1)
          (depressedV68 h T.source.r b7 b6 b5 b4 b3 b2 b1 b0) =
        depressedOctic68 (RatFunc.C (0 : k))
          (integratedP68 T.source.A (RatFunc.C T.source.alpha))
          (integratedQ68 (RatFunc.C (0 : k)) T.source.A T.source.B
            (RatFunc.C T.source.beta))
          (integratedR68 (RatFunc.C (0 : k)) T.source.A T.source.B
            T.source.C0 (RatFunc.C T.source.alpha)
            (RatFunc.C T.source.gamma))
          (integratedS68 (RatFunc.C (0 : k)) T.source.A T.source.B
            T.source.C0 T.source.D (RatFunc.C T.source.alpha)
            (RatFunc.C T.source.beta) (RatFunc.C T.source.delta))
          (integratedT68 (RatFunc.C (0 : k)) T.source.A T.source.B
            T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
            (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
            (RatFunc.C T.source.epsilon))
          (integratedU68 (RatFunc.C (0 : k)) T.source.A T.source.B
            T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
            (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
            (RatFunc.C T.source.delta) (RatFunc.C T.source.zeta))
          (integratedV68 (RatFunc.C (0 : k)) T.source.A T.source.B
            T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
            (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
            (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
            (RatFunc.C T.source.eta)) :=
    hqDep.symm.trans T.source.octic_eq
  have hA : T.source.A = depressedA68 h T.source.r a5 a4 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 4) hsextic
    rw [alignedSquare_coeff_depressedSextic68_four,
      alignedSquare_coeff_depressedSextic68_four] at hc
    exact hc.symm
  have hB : T.source.B = depressedB68 h T.source.r a5 a4 a3 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 3) hsextic
    rw [alignedSquare_coeff_depressedSextic68_three,
      alignedSquare_coeff_depressedSextic68_three] at hc
    exact hc.symm
  have hC0 : T.source.C0 = depressedC68 h T.source.r a5 a4 a3 a2 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 2) hsextic
    rw [alignedSquare_coeff_depressedSextic68_two,
      alignedSquare_coeff_depressedSextic68_two] at hc
    exact hc.symm
  have hD : T.source.D = depressedD68 h T.source.r a5 a4 a3 a2 a1 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 1) hsextic
    rw [alignedSquare_coeff_depressedSextic68_one,
      alignedSquare_coeff_depressedSextic68_one] at hc
    exact hc.symm
  have hE : T.source.E = depressedE68 h T.source.r a5 a4 a3 a2 a1 a0 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) hsextic
    rw [alignedSquare_coeff_depressedSextic68_zero,
      alignedSquare_coeff_depressedSextic68_zero] at hc
    exact hc.symm
  have hL : depressedL68 h T.source.r b7 = RatFunc.C (0 : k) := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 7) hoctic
    rw [alignedSquare_coeff_depressedOctic68_seven,
      alignedSquare_coeff_depressedOctic68_seven] at hc
    exact hc
  have hP :
      integratedP68 T.source.A (RatFunc.C T.source.alpha) =
        depressedP68 h T.source.r b7 b6 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 6) hoctic
    rw [alignedSquare_coeff_depressedOctic68_six,
      alignedSquare_coeff_depressedOctic68_six] at hc
    exact hc.symm
  have hQ :
      integratedQ68 (RatFunc.C (0 : k)) T.source.A T.source.B
          (RatFunc.C T.source.beta) =
        depressedQ68 h T.source.r b7 b6 b5 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 5) hoctic
    rw [alignedSquare_coeff_depressedOctic68_five,
      alignedSquare_coeff_depressedOctic68_five] at hc
    exact hc.symm
  have hR :
      integratedR68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
          (RatFunc.C T.source.alpha) (RatFunc.C T.source.gamma) =
        depressedR68 h T.source.r b7 b6 b5 b4 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 4) hoctic
    rw [alignedSquare_coeff_depressedOctic68_four,
      alignedSquare_coeff_depressedOctic68_four] at hc
    exact hc.symm
  have hS :
      integratedS68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
          T.source.D (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
          (RatFunc.C T.source.delta) =
        depressedS68 h T.source.r b7 b6 b5 b4 b3 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 3) hoctic
    rw [alignedSquare_coeff_depressedOctic68_three,
      alignedSquare_coeff_depressedOctic68_three] at hc
    exact hc.symm
  have hT :
      integratedT68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
          T.source.D T.source.E (RatFunc.C T.source.alpha)
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.epsilon) =
        depressedT68 h T.source.r b7 b6 b5 b4 b3 b2 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 2) hoctic
    rw [alignedSquare_coeff_depressedOctic68_two,
      alignedSquare_coeff_depressedOctic68_two] at hc
    exact hc.symm
  have hU :
      integratedU68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
          T.source.D T.source.E (RatFunc.C T.source.alpha)
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.delta) (RatFunc.C T.source.zeta) =
        depressedU68 h T.source.r b7 b6 b5 b4 b3 b2 b1 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 1) hoctic
    rw [alignedSquare_coeff_depressedOctic68_one,
      alignedSquare_coeff_depressedOctic68_one] at hc
    exact hc.symm
  have hV :
      integratedV68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
          T.source.D T.source.E (RatFunc.C T.source.alpha)
          (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
          (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
          (RatFunc.C T.source.eta) =
        depressedV68 h T.source.r b7 b6 b5 b4 b3 b2 b1 b0 := by
    have hc := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) hoctic
    rw [alignedSquare_coeff_depressedOctic68_zero,
      alignedSquare_coeff_depressedOctic68_zero] at hc
    exact hc.symm
  have haligned :
      (3 : k[X]) * q.coeff 7 = (4 : k[X]) * p.coeff 5 * h0 ^ 2 := by
    have hL' : depressedL68 h (sexticDepressionR68 h a5) b7 = 0 := by
      rw [← T.source.center_eq, hL, map_zero]
    rw [depressedL68_eq_discriminator h a5 b7 hh] at hL'
    have h3 : (3 : RatFunc k) ≠ 0 := by norm_num
    have hden : (3 : RatFunc k) * h ^ 7 ≠ 0 :=
      mul_ne_zero h3 (pow_ne_zero 7 hh)
    have hneg : -(4 * a5 * h ^ 2 - 3 * b7) = 0 :=
      (div_eq_zero_iff.mp hL').resolve_right hden
    have hnum : 4 * a5 * h ^ 2 - 3 * b7 = 0 := neg_eq_zero.mp hneg
    have halignedRF :
        (3 : RatFunc k) * b7 = (4 : RatFunc k) * a5 * h ^ 2 := by
      linear_combination -hnum
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    simpa [h, a5, b7, map_mul, map_pow, map_ofNat] using halignedRF
  exact ⟨hp, hq, hpTop, hqTop, haligned, hA, hB, hC0, hD, hE, hL, hP, hQ,
    hR, hS, hT, hU, hV⟩

end LocalRootUnpack68

#print axioms SquareZeroLIntegratedLocalRootData68.coords68

/-! ## W: wrapper derivative `ρ' = C(j)/h₀` -/

section AlignedSquareWrapper68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- **W.** The weight-13 source primitive of a zero-septic local-root
package has the ordinary simple-pole derivative supplied by
`T.source.bracket_eq` and P1. -/
theorem SquareZeroLIntegratedLocalRootData68.primitive_deriv_eq_simplePole68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) :
    Differential.deriv
        (alignedSquareSourcePrimitive68
          (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) (p.coeff 5))
          (algebraMap k[X] (RatFunc k) (p.coeff 4))
          (algebraMap k[X] (RatFunc k) (p.coeff 3))
          (algebraMap k[X] (RatFunc k) (p.coeff 2))
          (algebraMap k[X] (RatFunc k) (p.coeff 1))
          (algebraMap k[X] (RatFunc k) (p.coeff 0))
          (algebraMap k[X] (RatFunc k) (q.coeff 7))
          (algebraMap k[X] (RatFunc k) (q.coeff 6))
          (algebraMap k[X] (RatFunc k) (q.coeff 5))
          (algebraMap k[X] (RatFunc k) (q.coeff 4))
          (algebraMap k[X] (RatFunc k) (q.coeff 3))
          (algebraMap k[X] (RatFunc k) (q.coeff 2))
          (algebraMap k[X] (RatFunc k) (q.coeff 1))
          (algebraMap k[X] (RatFunc k) (q.coeff 0))) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
  obtain ⟨_hp, _hq, _hpTop, _hqTop, _haligned, hA, hB, hC0, hD, hE, hL,
      hP, hQ, hR, hS, hTcoord, hU, hV⟩ :=
    T.coords68
  have hLzero : ratFuncDerivation68 (RatFunc.C (0 : k)) = 0 := by
    have hx := ratFuncDerivation46_polynomial (C (0 : k) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C, derivative_C] using hx
  have hprim :
      Differential.deriv
          (degreeZeroPrimitive68 (RatFunc.C (0 : k)) T.source.A T.source.B
            T.source.C0 T.source.D T.source.E
            (integratedP68 T.source.A (RatFunc.C T.source.alpha))
            (integratedQ68 (RatFunc.C (0 : k)) T.source.A T.source.B
              (RatFunc.C T.source.beta))
            (integratedR68 (RatFunc.C (0 : k)) T.source.A T.source.B
              T.source.C0 (RatFunc.C T.source.alpha)
              (RatFunc.C T.source.gamma))
            (integratedS68 (RatFunc.C (0 : k)) T.source.A T.source.B
              T.source.C0 T.source.D (RatFunc.C T.source.alpha)
              (RatFunc.C T.source.beta) (RatFunc.C T.source.delta))
            (integratedT68 (RatFunc.C (0 : k)) T.source.A T.source.B
              T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
              (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
              (RatFunc.C T.source.epsilon))
            (integratedU68 (RatFunc.C (0 : k)) T.source.A T.source.B
              T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
              (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
              (RatFunc.C T.source.delta) (RatFunc.C T.source.zeta))
            (integratedV68 (RatFunc.C (0 : k)) T.source.A T.source.B
              T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
              (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
              (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
              (RatFunc.C T.source.eta))) =
        RatFunc.C j / hRF :=
    degreeZeroPrimitive68_ratFuncDeriv_eq_simplePole
      (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0 T.source.D
      T.source.E
      (integratedP68 T.source.A (RatFunc.C T.source.alpha))
      (integratedQ68 (RatFunc.C (0 : k)) T.source.A T.source.B
        (RatFunc.C T.source.beta))
      (integratedR68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
        (RatFunc.C T.source.alpha) (RatFunc.C T.source.gamma))
      (integratedS68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
        T.source.D (RatFunc.C T.source.alpha) (RatFunc.C T.source.beta)
        (RatFunc.C T.source.delta))
      (integratedT68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C T.source.alpha)
        (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.epsilon))
      (integratedU68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C T.source.alpha)
        (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.delta) (RatFunc.C T.source.zeta))
      (integratedV68 (RatFunc.C (0 : k)) T.source.A T.source.B T.source.C0
        T.source.D T.source.E (RatFunc.C T.source.alpha)
        (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
        (RatFunc.C T.source.eta))
      j hRF hLzero T.source.bracket_eq
  have hcoords :
      alignedSquareSourcePrimitive68 hRF a5 a4 a3 a2 a1 a0 b7 b6 b5 b4
          b3 b2 b1 b0 =
        degreeZeroPrimitive68 (RatFunc.C (0 : k)) T.source.A T.source.B
          T.source.C0 T.source.D T.source.E
          (integratedP68 T.source.A (RatFunc.C T.source.alpha))
          (integratedQ68 (RatFunc.C (0 : k)) T.source.A T.source.B
            (RatFunc.C T.source.beta))
          (integratedR68 (RatFunc.C (0 : k)) T.source.A T.source.B
            T.source.C0 (RatFunc.C T.source.alpha)
            (RatFunc.C T.source.gamma))
          (integratedS68 (RatFunc.C (0 : k)) T.source.A T.source.B
            T.source.C0 T.source.D (RatFunc.C T.source.alpha)
            (RatFunc.C T.source.beta) (RatFunc.C T.source.delta))
          (integratedT68 (RatFunc.C (0 : k)) T.source.A T.source.B
            T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
            (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
            (RatFunc.C T.source.epsilon))
          (integratedU68 (RatFunc.C (0 : k)) T.source.A T.source.B
            T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
            (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
            (RatFunc.C T.source.delta) (RatFunc.C T.source.zeta))
          (integratedV68 (RatFunc.C (0 : k)) T.source.A T.source.B
            T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
            (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
            (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
            (RatFunc.C T.source.eta)) := by
    dsimp only [alignedSquareSourcePrimitive68]
    rw [← T.source.center_eq, hL, ← hA, ← hB, ← hC0, ← hD, ← hE, ← hP,
      ← hQ, ← hR, ← hS, ← hTcoord, ← hU, ← hV]
  rw [hcoords]
  exact hprim

end AlignedSquareWrapper68

#print axioms SquareZeroLIntegratedLocalRootData68.primitive_deriv_eq_simplePole68

/-! ## Z: instantiate `hclear`/`hderiv` and close the chamber -/

section AlignedSquareChamber68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- **CLOSED** on a literal zero-septic local-root package.  Lane C
supplies the pole-`65` clearing; W supplies the genuine simple pole;
the order-`65` grandchildren are then False. -/
theorem alignedSquareClearedNumerator68_false_of_localRoot
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : False := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let rho : RatFunc k :=
    RatFunc.C (5642219814912 : k) *
      alignedSquareSourcePrimitive68 hRF
        (algebraMap k[X] (RatFunc k) (p.coeff 5))
        (algebraMap k[X] (RatFunc k) (p.coeff 4))
        (algebraMap k[X] (RatFunc k) (p.coeff 3))
        (algebraMap k[X] (RatFunc k) (p.coeff 2))
        (algebraMap k[X] (RatFunc k) (p.coeff 1))
        (algebraMap k[X] (RatFunc k) (p.coeff 0))
        (algebraMap k[X] (RatFunc k) (q.coeff 7))
        (algebraMap k[X] (RatFunc k) (q.coeff 6))
        (algebraMap k[X] (RatFunc k) (q.coeff 5))
        (algebraMap k[X] (RatFunc k) (q.coeff 4))
        (algebraMap k[X] (RatFunc k) (q.coeff 3))
        (algebraMap k[X] (RatFunc k) (q.coeff 2))
        (algebraMap k[X] (RatFunc k) (q.coeff 1))
        (algebraMap k[X] (RatFunc k) (q.coeff 0))
  obtain ⟨_hp, _hq, _hpTop, _hqTop, haligned, _hA, _hB, _hC0, _hD, _hE,
      _hL, _hP, _hQ, _hR, _hS, _hT, _hU, _hV⟩ :=
    T.coords68
  have hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareClearedNumerator68 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 7)
            (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
            (q.coeff 1) (q.coeff 0)) =
        hRF ^ alignedSquareRemainingPole68 * rho := by
    simpa [hRF, rho, alignedSquareRemainingPole68] using
      alignedSquareClearedNumerator68_eq_pow_mul_primitive h0
        (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
        (p.coeff 0) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
        (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
        T.scale_ne_zero haligned
  have hderiv :
      Differential.deriv rho =
        RatFunc.C (5642219814912 * j) / hRF := by
    simpa [rho, hRF] using
      alignedSquarePrimitive68_scaledDeriv_eq_simplePole h0 j
        (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
        (p.coeff 0) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
        (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
        (T.primitive_deriv_eq_simplePole68)
  have hjscaled : (5642219814912 : k) * j ≠ 0 :=
    mul_ne_zero (by norm_num) T.jacobian_ne_zero
  exact alignedSquareFace68_order65Grandchildren h0 (p.coeff 5)
    (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
    (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
    (q.coeff 2) (q.coeff 1) (q.coeff 0) rho (5642219814912 * j) T.root
    T.scale_ne_zero T.scale_degree T.root_eq hclear hderiv hjscaled

/-- **CLOSED.** The remaining aligned-square local-root exclusion of the
normalized `(6,8)` scale-two route. -/
theorem planeKeller68AlignedSquareLocalRootExclusion_closed :
    PlaneKeller68AlignedSquareLocalRootExclusion (k := k) :=
  fun _p _q _j _h0 T =>
    alignedSquareClearedNumerator68_false_of_localRoot T

/-- Source-facing exclusion of a normalized scale-two `(6,8)` aligned
square face.  The nonsquare chamber is not reopened. -/
theorem normalized68ScaleTwo_alignedSquare_false
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    False :=
  normalized68ScaleTwo_alignedSquareBranch_impossible_of_localRootExclusion
    planeKeller68AlignedSquareLocalRootExclusion_closed
    hsource hh0 hH haligned

/-- Scale-two route handoff from the remaining nonsquare quadratic
packet.  The aligned-square local-root chamber is closed. -/
theorem planeKellerNormalized68ScaleTwoRoute_of_quadraticPacket
    (hpacket : PlaneKeller68AlignedNonsquareQuadraticPacketExclusion
      (k := k)) :
    PlaneKellerNormalized68ScaleTwoRoute (k := k) :=
  planeKellerNormalized68ScaleTwoRoute_of_square_quadraticPacket
    planeKeller68AlignedSquareLocalRootExclusion_closed
    hpacket

end AlignedSquareChamber68

#print axioms alignedSquareClearedNumerator68_false_of_localRoot
#print axioms planeKeller68AlignedSquareLocalRootExclusion_closed
#print axioms normalized68ScaleTwo_alignedSquare_false
#print axioms planeKellerNormalized68ScaleTwoRoute_of_quadraticPacket

end Max11DegreeRoutes
