import Grok810ScaleZeroQuarticChamberFacesPart1Scratch
import Max11SpeedReflectDegLibScratch

/-! # Cost-argmin rest bounds, part 2/10, `(8,10)` scale zero

80 of the 655 load-free rest bounds, one per
(packet, live-letter set): the dead letters are `subst`-ed away and
each surviving monomial is below the face degree `d`, so the
chamber's ℕ conjuncts enter later by `omega`.  Depends only on
`Grok810ScaleZeroQuarticChamberFacesPart1Scratch`; the sibling `…Part*` modules are independent of each other,
so they gate in parallel.  Untracked working note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

section QuarticChamberFaces810

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_B
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hDz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF0810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF0810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF0810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BC
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hDz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF0810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF0810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hDz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF0810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hd0 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hDz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d)
    (hd3 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d)
    (hd3 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d)
    (hd3 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d)
    (hd3 : C.natDegree + F.natDegree < d)
    (hd4 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_C
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF0810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF0810` (9 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF0810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BC
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF0810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : C.natDegree + G.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : C.natDegree + G.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hd0 : C.natDegree + G.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

def muQuarticChamberRestLF0810_liveBCDEF_p2c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF0810_liveBCDEF_p2c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEF_p2c1
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF0810_liveBCDEF_p2c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF0810_liveBCDEF_p2c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_liveBCDEF_p2c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d) :
    (muQuarticChamberRestLF0810_liveBCDEF_p2c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEF_p2c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def muQuarticChamberRestLF0810_liveBCDEF_p2c2
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 128 : k) • (B ^ 2 * E))
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF0810_liveBCDEF_p2c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEF_p2c2
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF0810_liveBCDEF_p2c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(15 / 64) : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF0810_liveBCDEF_p2c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_liveBCDEF_p2c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810_liveBCDEF_p2c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEF_p2c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : muQuarticChamberRestLF0810 A B C D E F 0 = muQuarticChamberRestLF0810_liveBCDEF_p2c1 A B C D E F 0 + muQuarticChamberRestLF0810_liveBCDEF_p2c2 A B C D E F 0 := by
    simp only [muQuarticChamberRestLF0810, muQuarticChamberRestLF0810_liveBCDEF_p2c1, muQuarticChamberRestLF0810_liveBCDEF_p2c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (muQuarticChamberRestLF0810_liveBCDEF_p2c1_natDegree_lt A B C D E F 0 hdpos hd0 hd1 hd2 hd3) (muQuarticChamberRestLF0810_liveBCDEF_p2c2_natDegree_lt A B C D E F 0 hdpos hd4 hd5 hd6 hd7)))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : C.natDegree + G.natDegree < d)
    (hd6 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : C.natDegree + G.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hDz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

def muQuarticChamberRestLF0810_liveBCDEFG_p2c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF0810_liveBCDEFG_p2c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEFG_p2c1
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF0810_liveBCDEFG_p2c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF0810_liveBCDEFG_p2c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_liveBCDEFG_p2c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d) :
    (muQuarticChamberRestLF0810_liveBCDEFG_p2c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEFG_p2c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def muQuarticChamberRestLF0810_liveBCDEFG_p2c2
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 64 : k) • (B * C * D))
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF0810_liveBCDEFG_p2c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEFG_p2c2
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF0810_liveBCDEFG_p2c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 64) : k), (5 / 16 : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF0810_liveBCDEFG_p2c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_liveBCDEFG_p2c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : C.natDegree + G.natDegree < d)
    (hd7 : D.natDegree + F.natDegree < d)
    (hd8 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810_liveBCDEFG_p2c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEFG_p2c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : C.natDegree + G.natDegree < d)
    (hd7 : D.natDegree + F.natDegree < d)
    (hd8 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  have hsplit : muQuarticChamberRestLF0810 A B C D E F G = muQuarticChamberRestLF0810_liveBCDEFG_p2c1 A B C D E F G + muQuarticChamberRestLF0810_liveBCDEFG_p2c2 A B C D E F G := by
    simp only [muQuarticChamberRestLF0810, muQuarticChamberRestLF0810_liveBCDEFG_p2c1, muQuarticChamberRestLF0810_liveBCDEFG_p2c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (muQuarticChamberRestLF0810_liveBCDEFG_p2c1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4) (muQuarticChamberRestLF0810_liveBCDEFG_p2c2_natDegree_lt A B C D E F G hdpos hd5 hd6 hd7 hd8)))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_D
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF1810` (9 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (-(5 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_BD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_CD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_BCD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_BDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_BDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_BDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 4 * B.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_CDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_CDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : D.natDegree + F.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hFz : F = 0)
    (hd0 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))


end QuarticChamberFaces810

end Max11DegreeRoutes
