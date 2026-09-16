import Grok810ScaleZeroQuarticChamberFacesPart101Scratch

/-! # Cost-argmin rest bounds, part 5/10, `(8,10)` scale zero

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
/-- Reflected monomial data for `kappaQuarticChamberRestLF2810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_kappaQuarticChamberRestLF2810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `kappaQuarticChamberRestLF2810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 3 * B.natDegree < d)
    (h1 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ B.natDegree + 2 * C.natDegree < d)
    (h3 : C = 0 ∨ F = 0 ∨ C.natDegree + F.natDegree < d)
    (h4 : D = 0 ∨ E = 0 ∨ D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_kappaQuarticChamberRestLF2810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd2)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd3)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd2)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF2810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : C.natDegree + F.natDegree < d)
    (hd4 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF5810_natDegree_lt_of_live_BG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (muQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
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
  simp only [muQuarticChamberRestLF5810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF1810_natDegree_lt_of_live_CD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (xiQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
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
  simp only [xiQuarticChamberRestLF1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF1810_natDegree_lt_of_live_CDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (xiQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
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
  simp only [xiQuarticChamberRestLF1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

def xiQuarticChamberRestLF1810_liveBCDFG_p5c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF1810` (12 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF1810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF1810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF1810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ E = 0 ∨ A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ D = 0 ∨ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (h3 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h4 : B = 0 ∨ C = 0 ∨ 2 * B.natDegree + 2 * C.natDegree < d)
    (h5 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h6 : B = 0 ∨ G = 0 ∨ 2 * B.natDegree + G.natDegree < d)
    (h7 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h8 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h9 : C = 0 ∨ E = 0 ∨ 2 * C.natDegree + E.natDegree < d)
    (h10 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d)
    (h11 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF1810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h11 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF1810_liveBCDFG_p5c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF1810_liveBCDFG_p5c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF1810_liveBCDFG_p5c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF1810_liveBCDFG_p5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF1810_liveBCDFG_p5c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF1810_liveBCDFG_p5c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF1810_liveBCDFG_p5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF1810_liveBCDFG_p5c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (A * D * F))
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF1810_liveBCDFG_p5c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF1810_liveBCDFG_p5c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF1810_liveBCDFG_p5c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(5 / 64) : k), (-(25 / 128) : k),
      (5 / 32 : k)
      ]
      [
      [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF1810_liveBCDFG_p5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF1810_liveBCDFG_p5c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF1810_liveBCDFG_p5c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF1810_liveBCDFG_p5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    lt_of_le_of_lt (Nat.zero_le _) hd4⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF1810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inl hEz))
    (Or.inl hEz)
    (Or.inr (hd7))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF1810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : 2 * C.natDegree + E.natDegree < d)
    (hd2 : E.natDegree + G.natDegree < d)
    (hd3 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))

def xiQuarticChamberRestLF1810_liveBCDEFG_p5c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF1810_liveBCDEFG_p5c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF1810_liveBCDEFG_p5c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF1810_liveBCDEFG_p5c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF1810_liveBCDEFG_p5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF1810_liveBCDEFG_p5c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF1810_liveBCDEFG_p5c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF1810_liveBCDEFG_p5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF1810_liveBCDEFG_p5c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF1810_liveBCDEFG_p5c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF1810_liveBCDEFG_p5c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF1810_liveBCDEFG_p5c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF1810_liveBCDEFG_p5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF1810_liveBCDEFG_p5c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : 2 * B.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd9 : 2 * C.natDegree + E.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF1810_liveBCDEFG_p5c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF1810_liveBCDEFG_p5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF1810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd9 : 2 * C.natDegree + E.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (Or.inr (hd10)))
    (Or.inr (hd11))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_natDegree_lt_of_live_CE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (xiQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
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
  simp only [xiQuarticChamberRestLF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF2810` (12 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF2810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF2810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ E = 0 ∨ A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ D = 0 ∨ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (h3 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h4 : B = 0 ∨ C = 0 ∨ 2 * B.natDegree + 2 * C.natDegree < d)
    (h5 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h6 : B = 0 ∨ G = 0 ∨ 2 * B.natDegree + G.natDegree < d)
    (h7 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h8 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h9 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h10 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d)
    (h11 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h11 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inl hGz))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hGz))
    (Or.inr (hd4))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))
    (Or.inr (hd2))

def xiQuarticChamberRestLF2810_liveBCDEF_p5c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF2810_liveBCDEF_p5c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEF_p5c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF2810_liveBCDEF_p5c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF2810_liveBCDEF_p5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_liveBCDEF_p5c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF2810_liveBCDEF_p5c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEF_p5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF2810_liveBCDEF_p5c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (A * D * F))
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF2810_liveBCDEF_p5c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEF_p5c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF2810_liveBCDEF_p5c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (5 / 32 : k)
      ]
      [
      [1, 0, 0, 1, 0, 1, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF2810_liveBCDEF_p5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_liveBCDEF_p5c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF2810_liveBCDEF_p5c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEF_p5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inl hGz))
    (Or.inr (hd9))

def xiQuarticChamberRestLF2810_liveBCDEG_p5c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF2810_liveBCDEG_p5c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEG_p5c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF2810_liveBCDEG_p5c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF2810_liveBCDEG_p5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_liveBCDEG_p5c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF2810_liveBCDEG_p5c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEG_p5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF2810_liveBCDEG_p5c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF2810_liveBCDEG_p5c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEG_p5c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF2810_liveBCDEG_p5c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF2810_liveBCDEG_p5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_liveBCDEG_p5c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF2810_liveBCDEG_p5c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEG_p5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (hd8)))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : E.natDegree + G.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d)
    (hd2 : E.natDegree + G.natDegree < d)
    (hd3 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))

def xiQuarticChamberRestLF2810_liveBCDEFG_p5c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF2810_liveBCDEFG_p5c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEFG_p5c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF2810_liveBCDEFG_p5c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF2810_liveBCDEFG_p5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_liveBCDEFG_p5c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF2810_liveBCDEFG_p5c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEFG_p5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF2810_liveBCDEFG_p5c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF2810_liveBCDEFG_p5c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEFG_p5c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF2810_liveBCDEFG_p5c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF2810_liveBCDEFG_p5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_liveBCDEFG_p5c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : 2 * B.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF2810_liveBCDEFG_p5c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_xiQuarticChamberRestLF2810_liveBCDEFG_p5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF2810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_xiQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (Or.inr (hd10)))
    (Or.inr (hd11))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_CF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
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
  simp only [kappaQuarticChamberRestLF3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF3810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_kappaQuarticChamberRestLF3810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF3810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `kappaQuarticChamberRestLF3810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 3 * B.natDegree < d)
    (h1 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ B.natDegree + 2 * C.natDegree < d)
    (h3 : B = 0 ∨ G = 0 ∨ B.natDegree + G.natDegree < d)
    (h4 : D = 0 ∨ E = 0 ∨ D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_kappaQuarticChamberRestLF3810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_CEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_CFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_CDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_CEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd3)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF3810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + G.natDegree < d)
    (hd4 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_kappaQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF6810` (9 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF6810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF6810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (-(5 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF6810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ C = 0 ∨ A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (h1 : B = 0 ∨ 4 * B.natDegree < d)
    (h2 : B = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + F.natDegree < d)
    (h3 : D = 0 ∨ A.natDegree + 2 * D.natDegree < d)
    (h4 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h6 : C = 0 ∨ 3 * C.natDegree < d)
    (h7 : D = 0 ∨ F = 0 ∨ D.natDegree + F.natDegree < d)
    (h8 : E = 0 ∨ 2 * E.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF6810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_CG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (hd2))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_CDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hDz)
    (Or.inr (hd1))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_CFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd2))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (hd4))
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : 3 * C.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (hd3))
    (Or.inl hDz)
    (Or.inr (hd4))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (hd3))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_CDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 3 * C.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd2))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_CDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 3 * C.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_CEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hDz)
    (Or.inr (hd1))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 3 * C.natDegree < d)
    (hd6 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd2))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (hd5))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 3 * C.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (hd5))
    (Or.inr (Or.inr (hd6)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : 3 * C.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (hd4))
    (Or.inl hDz)
    (Or.inr (hd5))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 3 * C.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))

def muQuarticChamberRestLF6810_liveBCDEFG_p5c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF6810_liveBCDEFG_p5c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF6810_liveBCDEFG_p5c1
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF6810_liveBCDEFG_p5c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF6810_liveBCDEFG_p5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_liveBCDEFG_p5c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d) :
    (muQuarticChamberRestLF6810_liveBCDEFG_p5c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF6810_liveBCDEFG_p5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def muQuarticChamberRestLF6810_liveBCDEFG_p5c2
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 64 : k) • (B * C * D))
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF6810_liveBCDEFG_p5c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF6810_liveBCDEFG_p5c2
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF6810_liveBCDEFG_p5c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 64) : k), (-(5 / 128) : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF6810_liveBCDEFG_p5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_liveBCDEFG_p5c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : 3 * C.natDegree < d)
    (hd7 : D.natDegree + F.natDegree < d)
    (hd8 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF6810_liveBCDEFG_p5c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF6810_liveBCDEFG_p5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : 3 * C.natDegree < d)
    (hd7 : D.natDegree + F.natDegree < d)
    (hd8 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (hd6))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (hd8))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_natDegree_lt_of_live_CG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (muQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
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
  simp only [muQuarticChamberRestLF7810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF7810` (8 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF7810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF7810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF7810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF7810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ C = 0 ∨ A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (h1 : B = 0 ∨ 4 * B.natDegree < d)
    (h2 : B = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + F.natDegree < d)
    (h3 : D = 0 ∨ A.natDegree + 2 * D.natDegree < d)
    (h4 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h6 : D = 0 ∨ F = 0 ∨ D.natDegree + F.natDegree < d)
    (h7 : E = 0 ∨ 2 * E.natDegree < d) :
    (muQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF7810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d) :
    (muQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inr (hd0))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inl hDz)
    (Or.inr (hd3))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd2))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd5))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inl hDz)
    (Or.inr (hd4))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (hd2))

def muQuarticChamberRestLF7810_liveBCDEFG_p5c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF7810_liveBCDEFG_p5c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF7810_liveBCDEFG_p5c1
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF7810_liveBCDEFG_p5c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF7810_liveBCDEFG_p5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_liveBCDEFG_p5c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d) :
    (muQuarticChamberRestLF7810_liveBCDEFG_p5c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF7810_liveBCDEFG_p5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def muQuarticChamberRestLF7810_liveBCDEFG_p5c2
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 128 : k) • (B ^ 2 * E))
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF7810_liveBCDEFG_p5c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF7810_liveBCDEFG_p5c2
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF7810_liveBCDEFG_p5c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(15 / 64) : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF7810_liveBCDEFG_p5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_liveBCDEFG_p5c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF7810_liveBCDEFG_p5c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_muQuarticChamberRestLF7810_liveBCDEFG_p5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    lt_of_le_of_lt (Nat.zero_le _) hd4⟩

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_muQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (hd7))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_natDegree_lt_of_live_CG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (piQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
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
  simp only [piQuarticChamberRestLF1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810` (18 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 16) : k), (-(5 / 8) : k), (-(15 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `piQuarticChamberRestLF1810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart5_piQuarticChamberRestLF1810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ 2 * A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ D = 0 ∨ A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ 4 * B.natDegree + C.natDegree < d)
    (h4 : B = 0 ∨ G = 0 ∨ A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (h6 : B = 0 ∨ D = 0 ∨ E = 0 ∨ A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (h7 : C = 0 ∨ D = 0 ∨ A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (h8 : B = 0 ∨ F = 0 ∨ 3 * B.natDegree + F.natDegree < d)
    (h9 : B = 0 ∨ C = 0 ∨ E = 0 ∨ 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (h10 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + 2 * D.natDegree < d)
    (h11 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (h12 : F = 0 ∨ A.natDegree + 2 * F.natDegree < d)
    (h13 : B = 0 ∨ D = 0 ∨ G = 0 ∨ B.natDegree + D.natDegree + G.natDegree < d)
    (h14 : B = 0 ∨ E = 0 ∨ F = 0 ∨ B.natDegree + E.natDegree + F.natDegree < d)
    (h15 : C = 0 ∨ D = 0 ∨ F = 0 ∨ C.natDegree + D.natDegree + F.natDegree < d)
    (h16 : C = 0 ∨ E = 0 ∨ C.natDegree + 2 * E.natDegree < d)
    (h17 : D = 0 ∨ E = 0 ∨ 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h11 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h12 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h13 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h14 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h15 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h16 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h17 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + 2 * F.natDegree < d) :
    (piQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_piQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (hd6))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hEz))
    (Or.inl hDz)

def piQuarticChamberRestLF1810_liveBCDEG_p5c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810_liveBCDEG_p5c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDEG_p5c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810_liveBCDEG_p5c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF1810_liveBCDEG_p5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_liveBCDEG_p5c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF1810_liveBCDEG_p5c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDEG_p5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF1810_liveBCDEG_p5c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810_liveBCDEG_p5c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDEG_p5c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810_liveBCDEG_p5c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 16 : k), (5 / 32 : k), (45 / 64 : k),
      (45 / 128 : k), (45 / 64 : k)
      ]
      [
      [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 1, 2, 1, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF1810_liveBCDEG_p5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_liveBCDEG_p5c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (piQuarticChamberRestLF1810_liveBCDEG_p5c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDEG_p5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

def piQuarticChamberRestLF1810_liveBCDEG_p5c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 8 : k) • (B * D * G))
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810_liveBCDEG_p5c3` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDEG_p5c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810_liveBCDEG_p5c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 8) : k), (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [0, 1, 0, 1, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF1810_liveBCDEG_p5c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_liveBCDEG_p5c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + 2 * E.natDegree < d)
    (hd12 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF1810_liveBCDEG_p5c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDEG_p5c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + 2 * E.natDegree < d)
    (hd12 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_piQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inl hFz)
    (Or.inr (Or.inr (Or.inr (hd10))))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (hd11)))
    (Or.inr (Or.inr (hd12)))

def piQuarticChamberRestLF1810_liveBCDFG_p5c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810_liveBCDFG_p5c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDFG_p5c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810_liveBCDFG_p5c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF1810_liveBCDFG_p5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_liveBCDFG_p5c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF1810_liveBCDFG_p5c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDFG_p5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF1810_liveBCDFG_p5c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * B * C * F)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810_liveBCDFG_p5c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDFG_p5c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810_liveBCDFG_p5c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 32 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 128 : k), (45 / 64 : k)
      ]
      [
      [1, 1, 1, 0, 0, 1, 0], [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 1, 2, 1, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF1810_liveBCDFG_p5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_liveBCDFG_p5c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd7 : 3 * B.natDegree + F.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (piQuarticChamberRestLF1810_liveBCDFG_p5c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDFG_p5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

def piQuarticChamberRestLF1810_liveBCDFG_p5c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (A * F ^ 2))
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (C * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810_liveBCDFG_p5c3` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDFG_p5c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810_liveBCDFG_p5c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(5 / 8) : k), (-(15 / 16) : k)
      ]
      [
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF1810_liveBCDFG_p5c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_liveBCDFG_p5c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : A.natDegree + 2 * F.natDegree < d)
    (hd11 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF1810_liveBCDFG_p5c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCDFG_p5c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd7 : 3 * B.natDegree + F.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd10 : A.natDegree + 2 * F.natDegree < d)
    (hd11 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_piQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (hd10))
    (Or.inr (Or.inr (Or.inr (hd11))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd12))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hEz))

def piQuarticChamberRestLF1810_liveBCEFG_p5c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810_liveBCEFG_p5c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCEFG_p5c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810_liveBCEFG_p5c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(45 / 512) : k), (-(35 / 256) : k),
      (5 / 64 : k), (5 / 32 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1],
      [1, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF1810_liveBCEFG_p5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_liveBCEFG_p5c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF1810_liveBCEFG_p5c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCEFG_p5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF1810_liveBCEFG_p5c2
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 8 : k) • (C * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810_liveBCEFG_p5c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCEFG_p5c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810_liveBCEFG_p5c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 128 : k), (45 / 64 : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k)
      ]
      [
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 1, 0],
      [0, 0, 1, 0, 2, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF1810_liveBCEFG_p5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_liveBCEFG_p5c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF1810_liveBCEFG_p5c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart5_piQuarticChamberRestLF1810_liveBCEFG_p5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_piQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (hd7))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd9)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd1 : A.natDegree + 2 * F.natDegree < d)
    (hd2 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + 2 * E.natDegree < d)
    (hd4 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_piQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd1))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))


end QuarticChamberFaces810

end Max11DegreeRoutes
/-! # Cost-argmin rest bounds, part 6/10, `(8,10)` scale zero

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

def piQuarticChamberRestLF1810_liveBCDEFG_p6c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810_liveBCDEFG_p6c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_piQuarticChamberRestLF1810_liveBCDEFG_p6c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810_liveBCDEFG_p6c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF1810_liveBCDEFG_p6c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_liveBCDEFG_p6c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF1810_liveBCDEFG_p6c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_piQuarticChamberRestLF1810_liveBCDEFG_p6c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF1810_liveBCDEFG_p6c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810_liveBCDEFG_p6c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_piQuarticChamberRestLF1810_liveBCDEFG_p6c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810_liveBCDEFG_p6c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k)
      ]
      [
      [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0],
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF1810_liveBCDEFG_p6c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_liveBCDEFG_p6c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd8 : 3 * B.natDegree + F.natDegree < d)
    (hd9 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd11 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (piQuarticChamberRestLF1810_liveBCDEFG_p6c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_piQuarticChamberRestLF1810_liveBCDEFG_p6c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

def piQuarticChamberRestLF1810_liveBCDEFG_p6c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (A * F ^ 2))
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF1810_liveBCDEFG_p6c3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_piQuarticChamberRestLF1810_liveBCDEFG_p6c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF1810_liveBCDEFG_p6c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(5 / 8) : k), (-(15 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF1810_liveBCDEFG_p6c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_liveBCDEFG_p6c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd12 : A.natDegree + 2 * F.natDegree < d)
    (hd13 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd14 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF1810_liveBCDEFG_p6c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_piQuarticChamberRestLF1810_liveBCDEFG_p6c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    by simpa only [Nat.add_assoc] using hd15,
    by simpa only [Nat.add_assoc] using hd16,
    by simpa only [Nat.add_assoc] using hd17,
    lt_of_le_of_lt (Nat.zero_le _) hd12⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF1810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd8 : 3 * B.natDegree + F.natDegree < d)
    (hd9 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd11 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd12 : A.natDegree + 2 * F.natDegree < d)
    (hd13 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd14 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart5_piQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (Or.inr (hd10)))
    (Or.inr (Or.inr (Or.inr (hd11))))
    (Or.inr (hd12))
    (Or.inr (Or.inr (Or.inr (hd13))))
    (Or.inr (Or.inr (Or.inr (hd14))))
    (Or.inr (Or.inr (Or.inr (hd15))))
    (Or.inr (Or.inr (hd16)))
    (Or.inr (Or.inr (hd17)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_DE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
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
  simp only [kappaQuarticChamberRestLF4810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF4810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_kappaQuarticChamberRestLF4810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF4810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
      [0, 0, 1, 0, 0, 1, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `kappaQuarticChamberRestLF4810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 3 * B.natDegree < d)
    (h1 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ B.natDegree + 2 * C.natDegree < d)
    (h3 : B = 0 ∨ G = 0 ∨ B.natDegree + G.natDegree < d)
    (h4 : C = 0 ∨ F = 0 ∨ C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_kappaQuarticChamberRestLF4810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_BDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inl hCz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_CDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hFz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_DEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hFz : F = 0) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_BDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inl hCz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_BDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hCz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_CDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hFz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd3)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hFz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hCz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF4810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + G.natDegree < d)
    (hd4 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_DF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
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
  simp only [muQuarticChamberRestLF8810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF8810` (8 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_muQuarticChamberRestLF8810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF8810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (-(5 / 128) : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF8810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ C = 0 ∨ A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (h1 : B = 0 ∨ 4 * B.natDegree < d)
    (h2 : B = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + F.natDegree < d)
    (h3 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h4 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h5 : C = 0 ∨ 3 * C.natDegree < d)
    (h6 : C = 0 ∨ G = 0 ∨ C.natDegree + G.natDegree < d)
    (h7 : E = 0 ∨ 2 * E.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_muQuarticChamberRestLF8810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_BDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inl hCz))
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inr (Or.inl hGz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (hd0))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_DFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (hd4))
    (Or.inr (Or.inl hGz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_BDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inl hCz))
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (hd3))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inl hCz))
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inr (Or.inl hGz))
    (Or.inr (hd1))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_CDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (hd0))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 3 * C.natDegree < d)
    (hd6 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (hd5))
    (Or.inr (Or.inl hGz))
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 3 * C.natDegree < d)
    (hd5 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (hd4))
    (Or.inr (Or.inr (hd5)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inl hCz))
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (hd3))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (hd2))

def muQuarticChamberRestLF8810_liveBCDEFG_p6c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF8810_liveBCDEFG_p6c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_muQuarticChamberRestLF8810_liveBCDEFG_p6c1
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF8810_liveBCDEFG_p6c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(15 / 128) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [0, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF8810_liveBCDEFG_p6c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_liveBCDEFG_p6c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d) :
    (muQuarticChamberRestLF8810_liveBCDEFG_p6c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_muQuarticChamberRestLF8810_liveBCDEFG_p6c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def muQuarticChamberRestLF8810_liveBCDEFG_p6c2
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 64 : k) • (B * C * D))
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF8810_liveBCDEFG_p6c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_muQuarticChamberRestLF8810_liveBCDEFG_p6c2
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF8810_liveBCDEFG_p6c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 64) : k), (-(5 / 128) : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF8810_liveBCDEFG_p6c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_liveBCDEFG_p6c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 3 * C.natDegree < d)
    (hd6 : C.natDegree + G.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF8810_liveBCDEFG_p6c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_muQuarticChamberRestLF8810_liveBCDEFG_p6c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    lt_of_le_of_lt (Nat.zero_le _) hd4⟩

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 3 * C.natDegree < d)
    (hd6 : C.natDegree + G.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (hd5))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (hd7))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_DF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
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
  simp only [xiQuarticChamberRestLF3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF3810` (11 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF3810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF3810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF3810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ E = 0 ∨ A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ D = 0 ∨ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (h3 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h4 : B = 0 ∨ C = 0 ∨ 2 * B.natDegree + 2 * C.natDegree < d)
    (h5 : B = 0 ∨ G = 0 ∨ 2 * B.natDegree + G.natDegree < d)
    (h6 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h7 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h8 : C = 0 ∨ E = 0 ∨ 2 * C.natDegree + E.natDegree < d)
    (h9 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h10 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF3810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_BDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hGz))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_DFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd5)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_BDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : B.natDegree + D.natDegree + E.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hGz))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : 2 * C.natDegree + E.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_CDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hd0 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd0)))

def xiQuarticChamberRestLF3810_liveBCDEF_p6c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF3810_liveBCDEF_p6c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF3810_liveBCDEF_p6c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF3810_liveBCDEF_p6c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF3810_liveBCDEF_p6c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_liveBCDEF_p6c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF3810_liveBCDEF_p6c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF3810_liveBCDEF_p6c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF3810_liveBCDEF_p6c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF3810_liveBCDEF_p6c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF3810_liveBCDEF_p6c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF3810_liveBCDEF_p6c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF3810_liveBCDEF_p6c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_liveBCDEF_p6c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF3810_liveBCDEF_p6c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF3810_liveBCDEF_p6c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inl hGz))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd6)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd5)))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 2 * C.natDegree + E.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d)
    (hd2 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))

def xiQuarticChamberRestLF3810_liveBCDEFG_p6c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF3810_liveBCDEFG_p6c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF3810_liveBCDEFG_p6c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF3810_liveBCDEFG_p6c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF3810_liveBCDEFG_p6c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_liveBCDEFG_p6c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF3810_liveBCDEFG_p6c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF3810_liveBCDEFG_p6c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF3810_liveBCDEFG_p6c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF3810_liveBCDEFG_p6c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF3810_liveBCDEFG_p6c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF3810_liveBCDEFG_p6c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF3810_liveBCDEFG_p6c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_liveBCDEFG_p6c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : 2 * C.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF3810_liveBCDEFG_p6c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF3810_liveBCDEFG_p6c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF3810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : 2 * C.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (Or.inr (hd10)))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF4810` (12 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF4810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF4810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF4810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ E = 0 ∨ A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (h2 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ 2 * B.natDegree + 2 * C.natDegree < d)
    (h4 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h5 : B = 0 ∨ G = 0 ∨ 2 * B.natDegree + G.natDegree < d)
    (h6 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h7 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h8 : C = 0 ∨ E = 0 ∨ 2 * C.natDegree + E.natDegree < d)
    (h9 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h10 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d)
    (h11 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h11 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_natDegree_lt_of_live_BCD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd3)))
    (Or.inl hEz)
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : 2 * C.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inl hGz))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : C.natDegree + 2 * D.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd5)))
    (Or.inl hEz)
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd4)))
    (Or.inl hEz)
    (Or.inl hFz)

def xiQuarticChamberRestLF4810_liveBCDEF_p6c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF4810_liveBCDEF_p6c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEF_p6c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF4810_liveBCDEF_p6c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF4810_liveBCDEF_p6c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_liveBCDEF_p6c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF4810_liveBCDEF_p6c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEF_p6c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF4810_liveBCDEF_p6c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF4810_liveBCDEF_p6c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEF_p6c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF4810_liveBCDEF_p6c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 32 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF4810_liveBCDEF_p6c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_liveBCDEF_p6c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF4810_liveBCDEF_p6c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEF_p6c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inl hGz))
    (Or.inr (hd9))

def xiQuarticChamberRestLF4810_liveBCDEG_p6c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF4810_liveBCDEG_p6c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEG_p6c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF4810_liveBCDEG_p6c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF4810_liveBCDEG_p6c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_liveBCDEG_p6c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF4810_liveBCDEG_p6c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEG_p6c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF4810_liveBCDEG_p6c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * D * E))
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF4810_liveBCDEG_p6c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEG_p6c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF4810_liveBCDEG_p6c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k)
      ]
      [
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF4810_liveBCDEG_p6c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_liveBCDEG_p6c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * C.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF4810_liveBCDEG_p6c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEG_p6c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * C.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (hd8)))
    (Or.inl hFz)

def xiQuarticChamberRestLF4810_liveBCDFG_p6c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF4810_liveBCDFG_p6c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDFG_p6c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF4810_liveBCDFG_p6c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (55 / 1024 : k), (45 / 512 : k),
      (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF4810_liveBCDFG_p6c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_liveBCDFG_p6c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF4810_liveBCDFG_p6c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDFG_p6c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF4810_liveBCDFG_p6c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * C * F)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF4810_liveBCDFG_p6c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDFG_p6c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF4810_liveBCDFG_p6c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (5 / 32 : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF4810_liveBCDFG_p6c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_liveBCDFG_p6c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF4810_liveBCDFG_p6c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDFG_p6c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    lt_of_le_of_lt (Nat.zero_le _) hd4⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd6)))
    (Or.inl hEz)
    (Or.inr (hd7))

def xiQuarticChamberRestLF4810_liveBCDEFG_p6c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF4810_liveBCDEFG_p6c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEFG_p6c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF4810_liveBCDEFG_p6c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF4810_liveBCDEFG_p6c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_liveBCDEFG_p6c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF4810_liveBCDEFG_p6c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEFG_p6c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF4810_liveBCDEFG_p6c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF4810_liveBCDEFG_p6c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEFG_p6c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF4810_liveBCDEFG_p6c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF4810_liveBCDEFG_p6c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_liveBCDEFG_p6c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : 2 * C.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF4810_liveBCDEFG_p6c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF4810_liveBCDEFG_p6c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF4810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : 2 * C.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF4810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (Or.inr (hd10)))
    (Or.inr (hd11))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF5810` (11 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF5810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF5810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF5810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ D = 0 ∨ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ 2 * B.natDegree + 2 * C.natDegree < d)
    (h4 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h5 : B = 0 ∨ G = 0 ∨ 2 * B.natDegree + G.natDegree < d)
    (h6 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h7 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h8 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h9 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d)
    (h10 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_natDegree_lt_of_live_BCE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hGz))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inl hGz))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hGz))
    (Or.inr (hd3))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 2 * B.natDegree + G.natDegree < d)
    (hd3 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd3)))
    (Or.inl hFz)

def xiQuarticChamberRestLF5810_liveBCDEF_p6c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF5810_liveBCDEF_p6c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEF_p6c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF5810_liveBCDEF_p6c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF5810_liveBCDEF_p6c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_liveBCDEF_p6c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF5810_liveBCDEF_p6c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEF_p6c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF5810_liveBCDEF_p6c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF5810_liveBCDEF_p6c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEF_p6c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF5810_liveBCDEF_p6c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (5 / 32 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF5810_liveBCDEF_p6c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_liveBCDEF_p6c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF5810_liveBCDEF_p6c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEF_p6c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inl hGz))
    (Or.inr (hd8))

def xiQuarticChamberRestLF5810_liveBCDEG_p6c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF5810_liveBCDEG_p6c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEG_p6c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF5810_liveBCDEG_p6c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF5810_liveBCDEG_p6c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_liveBCDEG_p6c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF5810_liveBCDEG_p6c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEG_p6c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF5810_liveBCDEG_p6c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF5810_liveBCDEG_p6c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEG_p6c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF5810_liveBCDEG_p6c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF5810_liveBCDEG_p6c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_liveBCDEG_p6c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF5810_liveBCDEG_p6c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEG_p6c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    lt_of_le_of_lt (Nat.zero_le _) hd4⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (hd7)))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 2 * B.natDegree + G.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : E.natDegree + G.natDegree < d)
    (hd5 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (hd5))

def xiQuarticChamberRestLF5810_liveBCDEFG_p6c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF5810_liveBCDEFG_p6c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEFG_p6c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF5810_liveBCDEFG_p6c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF5810_liveBCDEFG_p6c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_liveBCDEFG_p6c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF5810_liveBCDEFG_p6c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEFG_p6c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF5810_liveBCDEFG_p6c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF5810_liveBCDEFG_p6c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEFG_p6c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF5810_liveBCDEFG_p6c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1],
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF5810_liveBCDEFG_p6c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_liveBCDEFG_p6c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : E.natDegree + G.natDegree < d)
    (hd10 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF5810_liveBCDEFG_p6c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF5810_liveBCDEFG_p6c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : E.natDegree + G.natDegree < d)
    (hd10 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (hd10))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF5810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_kappaQuarticChamberRestLF5810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF5810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `kappaQuarticChamberRestLF5810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF5810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 3 * B.natDegree < d)
    (h1 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ G = 0 ∨ B.natDegree + G.natDegree < d)
    (h3 : C = 0 ∨ F = 0 ∨ C.natDegree + F.natDegree < d)
    (h4 : D = 0 ∨ E = 0 ∨ D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_kappaQuarticChamberRestLF5810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF5810_natDegree_lt_of_live_BCE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d) :
    (kappaQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF5810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
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
  simp only [kappaQuarticChamberRestLF6810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF6810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_kappaQuarticChamberRestLF6810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF6810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `kappaQuarticChamberRestLF6810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF6810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + D.natDegree < d)
    (h1 : B = 0 ∨ G = 0 ∨ B.natDegree + G.natDegree < d)
    (h2 : D = 0 ∨ E = 0 ∨ D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_kappaQuarticChamberRestLF6810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd1)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF9810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_muQuarticChamberRestLF9810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF9810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2048 : k), (-(5 / 128) : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (5 / 16 : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF9810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF9810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ 4 * B.natDegree < d)
    (h1 : D = 0 ∨ A.natDegree + 2 * D.natDegree < d)
    (h2 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h4 : C = 0 ∨ G = 0 ∨ C.natDegree + G.natDegree < d)
    (h5 : D = 0 ∨ F = 0 ∨ D.natDegree + F.natDegree < d)
    (h6 : E = 0 ∨ 2 * E.natDegree < d) :
    (muQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_muQuarticChamberRestLF9810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d) :
    (muQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF9810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_muQuarticChamberRestLF9810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (xiQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
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
  simp only [xiQuarticChamberRestLF6810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF6810` (9 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF6810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF6810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (15 / 256 : k), (55 / 1024 : k),
      (-(5 / 64) : k), (-(5 / 64) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k)
      ]
      [
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF6810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF6810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ E = 0 ∨ A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ D = 0 ∨ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h3 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h4 : B = 0 ∨ G = 0 ∨ 2 * B.natDegree + G.natDegree < d)
    (h5 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h6 : C = 0 ∨ E = 0 ∨ 2 * C.natDegree + E.natDegree < d)
    (h7 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h8 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_xiQuarticChamberRestLF6810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_xiQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hDz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF7810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart6_kappaQuarticChamberRestLF7810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF7810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `kappaQuarticChamberRestLF7810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF7810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + D.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ B.natDegree + 2 * C.natDegree < d)
    (h2 : C = 0 ∨ F = 0 ∨ C.natDegree + F.natDegree < d)
    (h3 : D = 0 ∨ E = 0 ∨ D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart6_kappaQuarticChamberRestLF7810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart6_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)


end QuarticChamberFaces810

end Max11DegreeRoutes
