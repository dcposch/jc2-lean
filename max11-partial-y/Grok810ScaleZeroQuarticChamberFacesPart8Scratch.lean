import Grok810ScaleZeroQuarticChamberFacesPart101Scratch

/-! # Cost-argmin rest bounds, part 8/10, `(8,10)` scale zero

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
theorem muQuarticChamberRestLF11810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0) :
    (muQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
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
  simp only [muQuarticChamberRestLF11810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF11810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF11810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF11810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [muQuarticChamberRestLF11810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF11810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF11810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ C = 0 ∨ A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (h1 : B = 0 ∨ 4 * B.natDegree < d)
    (h2 : B = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + F.natDegree < d)
    (h3 : D = 0 ∨ A.natDegree + 2 * D.natDegree < d)
    (h4 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h6 : D = 0 ∨ F = 0 ∨ D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF11810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
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


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF11810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF11810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF11810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF11810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0) :
    (piQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
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
  simp only [piQuarticChamberRestLF4810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF4810` (17 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF4810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF4810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 16) : k), (-(5 / 8) : k), (-(15 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `piQuarticChamberRestLF4810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF4810
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
    (h16 : D = 0 ∨ E = 0 ∨ 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF4810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
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
theorem piQuarticChamberRestLF4810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd1 : A.natDegree + 2 * F.natDegree < d)
    (hd2 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF4810 A B C D E F G hdpos
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

def piQuarticChamberRestLF4810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF4810_liveBCDEFG_p8c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF4810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF4810_liveBCDEFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF4810_liveBCDEFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF4810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF4810_liveBCDEFG_p8c1]
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

def piQuarticChamberRestLF4810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF4810_liveBCDEFG_p8c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF4810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF4810_liveBCDEFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k)
      ]
      [
      [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0],
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF4810_liveBCDEFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd8 : 3 * B.natDegree + F.natDegree < d)
    (hd9 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd11 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (piQuarticChamberRestLF4810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF4810_liveBCDEFG_p8c2]
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

def piQuarticChamberRestLF4810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (A * F ^ 2))
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF4810_liveBCDEFG_p8c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF4810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF4810_liveBCDEFG_p8c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(5 / 8) : k), (-(15 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k)
      ]
      [
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF4810_liveBCDEFG_p8c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_liveBCDEFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd12 : A.natDegree + 2 * F.natDegree < d)
    (hd13 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd14 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF4810_liveBCDEFG_p8c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF4810_liveBCDEFG_p8c3]
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
    lt_of_le_of_lt (Nat.zero_le _) hd12⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_natDegree_lt_of_live_BCDEFG
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
    (hd16 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF4810 A B C D E F G hdpos
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

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF12810` (8 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF12810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF12810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (5 / 16 : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF12810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF12810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF12810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ C = 0 ∨ A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (h1 : B = 0 ∨ 4 * B.natDegree < d)
    (h2 : B = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + F.natDegree < d)
    (h3 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h4 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h5 : C = 0 ∨ G = 0 ∨ C.natDegree + G.natDegree < d)
    (h6 : D = 0 ∨ F = 0 ∨ D.natDegree + F.natDegree < d)
    (h7 : E = 0 ∨ 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF12810]
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
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd4))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd4)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : D.natDegree + F.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d)
    (hd6 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd5))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : C.natDegree + G.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (hd2))

def muQuarticChamberRestLF12810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF12810_liveBCDEFG_p8c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF12810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF12810_liveBCDEFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(15 / 128) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [0, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF12810_liveBCDEFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d) :
    (muQuarticChamberRestLF12810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF12810_liveBCDEFG_p8c1]
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

def muQuarticChamberRestLF12810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 64 : k) • (B * C * D))
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF12810_liveBCDEFG_p8c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF12810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF12810_liveBCDEFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 64) : k), (5 / 16 : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF12810_liveBCDEFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : C.natDegree + G.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF12810_liveBCDEFG_p8c2]
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
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : C.natDegree + G.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (hd7))

def piQuarticChamberRestLF5810_liveBCDE_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 16 : k) • (A * B * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810` (19 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k),
      (5 / 16 : k), (25 / 128 : k), (45 / 64 : k),
      (45 / 128 : k), (45 / 64 : k), (-(5 / 16) : k),
      (-(5 / 8) : k), (-(15 / 16) : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k),
      (5 / 4 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 1, 0],
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0],
      [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `piQuarticChamberRestLF5810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF5810
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
    (h7 : B = 0 ∨ F = 0 ∨ 3 * B.natDegree + F.natDegree < d)
    (h8 : B = 0 ∨ C = 0 ∨ E = 0 ∨ 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (h9 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + 2 * D.natDegree < d)
    (h10 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (h11 : F = 0 ∨ A.natDegree + 2 * F.natDegree < d)
    (h12 : B = 0 ∨ D = 0 ∨ G = 0 ∨ B.natDegree + D.natDegree + G.natDegree < d)
    (h13 : B = 0 ∨ E = 0 ∨ F = 0 ∨ B.natDegree + E.natDegree + F.natDegree < d)
    (h14 : C = 0 ∨ G = 0 ∨ 2 * C.natDegree + G.natDegree < d)
    (h15 : C = 0 ∨ D = 0 ∨ F = 0 ∨ C.natDegree + D.natDegree + F.natDegree < d)
    (h16 : C = 0 ∨ E = 0 ∨ C.natDegree + 2 * E.natDegree < d)
    (h17 : D = 0 ∨ E = 0 ∨ 2 * D.natDegree + E.natDegree < d)
    (h18 : G = 0 ∨ 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
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
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hz2 | hb
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
  · rcases h9 with hz0 | hz1 | hb
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
  · rcases h10 with hz0 | hz1 | hz2 | hb
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
  · rcases h11 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h12 with hz0 | hz1 | hz2 | hb
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
  · rcases h14 with hz0 | hz1 | hb
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
  · rcases h18 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDE_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDE_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDE_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 16 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 1, 0, 1, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDE_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDE_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDE_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDE_p8c1]
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

def piQuarticChamberRestLF5810_liveBCDE_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDE_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDE_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDE_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 1, 0, 2, 0, 0],
      [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDE_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDE_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : C.natDegree + 2 * E.natDegree < d)
    (hd9 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDE_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDE_p8c2]
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
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : C.natDegree + 2 * E.natDegree < d)
    (hd9 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inl hFz)
    (Or.inr (Or.inr (Or.inl hGz)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (hd9)))
    (Or.inl hGz)

def piQuarticChamberRestLF5810_liveBCDF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDF_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDF_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDF_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 32 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDF_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDF_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDF_p8c1]
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

def piQuarticChamberRestLF5810_liveBCDF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (C * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDF_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDF_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDF_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 128 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 16) : k), (-(15 / 16) : k)
      ]
      [
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0],
      [0, 0, 1, 1, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDF_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : A.natDegree + 2 * F.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDF_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDF_p8c2]
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
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : A.natDegree + 2 * F.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (hd8))
    (Or.inr (Or.inr (Or.inl hGz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hEz))
    (Or.inl hGz)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * F.natDegree < d)
    (hd1 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd2 : C.natDegree + 2 * E.natDegree < d)
    (hd3 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inl hGz)

def piQuarticChamberRestLF5810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDEF_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDEF_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 32 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDEF_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEF_p8c1]
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

def piQuarticChamberRestLF5810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDEF_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDEF_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 16 : k), (25 / 128 : k), (45 / 64 : k),
      (45 / 128 : k), (45 / 64 : k)
      ]
      [
      [1, 1, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 1, 2, 1, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDEF_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEF_p8c2]
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

def piQuarticChamberRestLF5810_liveBCDEF_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (A * F ^ 2))
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDEF_p8c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEF_p8c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDEF_p8c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(15 / 16) : k), (-(15 / 16) : k),
      (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0],
      [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDEF_p8c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEF_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : A.natDegree + 2 * F.natDegree < d)
    (hd11 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + 2 * E.natDegree < d)
    (hd14 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEF_p8c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEF_p8c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd10 : A.natDegree + 2 * F.natDegree < d)
    (hd11 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + 2 * E.natDegree < d)
    (hd14 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (hd10))
    (Or.inr (Or.inr (Or.inl hGz)))
    (Or.inr (Or.inr (Or.inr (hd11))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd12))))
    (Or.inr (Or.inr (hd13)))
    (Or.inr (Or.inr (hd14)))
    (Or.inl hGz)

def piQuarticChamberRestLF5810_liveBCDEG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDEG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEG_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDEG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDEG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEG_p8c1]
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

def piQuarticChamberRestLF5810_liveBCDEG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (A * B * D * E)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDEG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEG_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDEG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 16 : k), (45 / 64 : k), (45 / 128 : k),
      (45 / 64 : k), (-(5 / 8) : k)
      ]
      [
      [1, 1, 0, 1, 1, 0, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDEG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEG_p8c2]
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

def piQuarticChamberRestLF5810_liveBCDEG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (C ^ 2 * G))
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDEG_p8c3` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEG_p8c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDEG_p8c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k),
      (5 / 4 : k)
      ]
      [
      [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDEG_p8c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : 2 * C.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + 2 * E.natDegree < d)
    (hd12 : 2 * D.natDegree + E.natDegree < d)
    (hd13 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEG_p8c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEG_p8c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDEG
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
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd10 : 2 * C.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + 2 * E.natDegree < d)
    (hd12 : 2 * D.natDegree + E.natDegree < d)
    (hd13 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inl hFz)
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (hd10)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (hd11)))
    (Or.inr (Or.inr (hd12)))
    (Or.inr (hd13))

def piQuarticChamberRestLF5810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDFG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDFG_p8c1]
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

def piQuarticChamberRestLF5810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDFG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 32 : k), (25 / 128 : k), (45 / 128 : k),
      (45 / 64 : k), (-(5 / 16) : k)
      ]
      [
      [1, 1, 1, 0, 0, 1, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [1, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : A.natDegree + 2 * F.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDFG_p8c2]
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

def piQuarticChamberRestLF5810_liveBCDFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 8 : k) • (B * D * G))
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDFG_p8c3` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDFG_p8c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDFG_p8c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 8) : k), (-(5 / 16) : k), (-(15 / 16) : k),
      (5 / 4 : k)
      ]
      [
      [0, 1, 0, 1, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDFG_p8c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDFG_p8c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDFG_p8c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDFG
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
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : A.natDegree + 2 * F.natDegree < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (hd9))
    (Or.inr (Or.inr (Or.inr (hd10))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd11)))
    (Or.inr (Or.inr (Or.inr (hd12))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hEz))
    (Or.inr (hd13))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * F.natDegree < d)
    (hd1 : 2 * C.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + 2 * E.natDegree < d)
    (hd4 : 2 * D.natDegree + E.natDegree < d)
    (hd5 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (hd5))

def piQuarticChamberRestLF5810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDEFG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDEFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDEFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEFG_p8c1]
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

def piQuarticChamberRestLF5810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDEFG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDEFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 32 : k), (5 / 16 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k)
      ]
      [
      [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0],
      [0, 2, 0, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDEFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 3 * B.natDegree + F.natDegree < d)
    (hd8 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEFG_p8c2]
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

def piQuarticChamberRestLF5810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDEFG_p8c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDEFG_p8c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (-(5 / 16) : k), (-(5 / 8) : k),
      (-(15 / 16) : k), (-(5 / 16) : k)
      ]
      [
      [0, 1, 2, 1, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0],
      [0, 0, 2, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDEFG_p8c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd11 : A.natDegree + 2 * F.natDegree < d)
    (hd12 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd13 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd14 : 2 * C.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEFG_p8c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEFG_p8c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

def piQuarticChamberRestLF5810_liveBCDEFG_p8c4
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 16 : k) • (C * D * F))
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5810_liveBCDEFG_p8c4` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEFG_p8c4
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5810_liveBCDEFG_p8c4 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k),
      (5 / 4 : k)
      ]
      [
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF5810_liveBCDEFG_p8c4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEFG_p8c4_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d)
    (hd18 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEFG_p8c4 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF5810_liveBCDEFG_p8c4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd15,
    by simpa only [Nat.add_assoc] using hd16,
    by simpa only [Nat.add_assoc] using hd17,
    by simpa only [Nat.add_assoc] using hd18,
    lt_of_le_of_lt (Nat.zero_le _) hd15⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDEFG
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
    (hd7 : 3 * B.natDegree + F.natDegree < d)
    (hd8 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd10 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd11 : A.natDegree + 2 * F.natDegree < d)
    (hd12 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd13 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd14 : 2 * C.natDegree + G.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d)
    (hd18 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF5810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (Or.inr (Or.inr (hd10))))
    (Or.inr (hd11))
    (Or.inr (Or.inr (Or.inr (hd12))))
    (Or.inr (Or.inr (Or.inr (hd13))))
    (Or.inr (Or.inr (hd14)))
    (Or.inr (Or.inr (Or.inr (hd15))))
    (Or.inr (Or.inr (hd16)))
    (Or.inr (Or.inr (hd17)))
    (Or.inr (hd18))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF8810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_kappaQuarticChamberRestLF8810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF8810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `kappaQuarticChamberRestLF8810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF8810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + D.natDegree < d)
    (h1 : B = 0 ∨ G = 0 ∨ B.natDegree + G.natDegree < d)
    (h2 : C = 0 ∨ F = 0 ∨ C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_kappaQuarticChamberRestLF8810]
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
theorem kappaQuarticChamberRestLF8810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd1)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hFz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF13810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF13810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF13810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2048 : k), (-(5 / 64) : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [muQuarticChamberRestLF13810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF13810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF13810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ 4 * B.natDegree < d)
    (h1 : B = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + F.natDegree < d)
    (h2 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h4 : C = 0 ∨ G = 0 ∨ C.natDegree + G.natDegree < d)
    (h5 : D = 0 ∨ F = 0 ∨ D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF13810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
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


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF13810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d) :
    (muQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF13810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF13810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd4)))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF13810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hFz))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF13810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF6810` (15 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF6810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 64 : k),
      (5 / 32 : k), (25 / 128 : k), (45 / 64 : k),
      (45 / 128 : k), (45 / 64 : k), (-(5 / 16) : k),
      (-(5 / 8) : k), (-(15 / 16) : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (5 / 4 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1],
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `piQuarticChamberRestLF6810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF6810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ D = 0 ∨ A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ 4 * B.natDegree + C.natDegree < d)
    (h2 : B = 0 ∨ G = 0 ∨ A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (h4 : B = 0 ∨ F = 0 ∨ 3 * B.natDegree + F.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ E = 0 ∨ 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (h6 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + 2 * D.natDegree < d)
    (h7 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (h8 : F = 0 ∨ A.natDegree + 2 * F.natDegree < d)
    (h9 : B = 0 ∨ D = 0 ∨ G = 0 ∨ B.natDegree + D.natDegree + G.natDegree < d)
    (h10 : B = 0 ∨ E = 0 ∨ F = 0 ∨ B.natDegree + E.natDegree + F.natDegree < d)
    (h11 : C = 0 ∨ G = 0 ∨ 2 * C.natDegree + G.natDegree < d)
    (h12 : C = 0 ∨ D = 0 ∨ F = 0 ∨ C.natDegree + D.natDegree + F.natDegree < d)
    (h13 : D = 0 ∨ E = 0 ∨ 2 * D.natDegree + E.natDegree < d)
    (h14 : G = 0 ∨ 2 * G.natDegree < d) :
    (piQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
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
  · rcases h1 with hz0 | hz1 | hb
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
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
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
  · rcases h6 with hz0 | hz1 | hb
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
  · rcases h7 with hz0 | hz1 | hz2 | hb
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
  · rcases h8 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hz2 | hb
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
  · rcases h10 with hz0 | hz1 | hz2 | hb
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
  · rcases h11 with hz0 | hz1 | hb
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
  · rcases h12 with hz0 | hz1 | hz2 | hb
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
  · rcases h13 with hz0 | hz1 | hb
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
  · rcases h14 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd5 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inl hFz)
    (Or.inr (Or.inr (Or.inl hGz)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (hd5)))
    (Or.inl hGz)

def piQuarticChamberRestLF6810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF6810_liveBCDEF_p8c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF6810_liveBCDEF_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 32 : k),
      (25 / 128 : k), (45 / 64 : k), (45 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0], [0, 3, 0, 0, 0, 1, 0],
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF6810_liveBCDEF_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEF_p8c1]
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

def piQuarticChamberRestLF6810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF6810_liveBCDEF_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF6810_liveBCDEF_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (-(5 / 16) : k), (-(15 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k)
      ]
      [
      [0, 1, 2, 1, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF6810_liveBCDEF_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd10 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEF_p8c2]
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
theorem piQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd10 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (hd7))
    (Or.inr (Or.inr (Or.inl hGz)))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (Or.inr (hd10)))
    (Or.inl hGz)

def piQuarticChamberRestLF6810_liveBCDEG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF6810_liveBCDEG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEG_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF6810_liveBCDEG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 64 : k),
      (45 / 64 : k), (45 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [0, 2, 1, 0, 1, 0, 0],
      [0, 2, 0, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF6810_liveBCDEG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEG_p8c1]
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

def piQuarticChamberRestLF6810_liveBCDEG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF6810_liveBCDEG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEG_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF6810_liveBCDEG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (-(5 / 8) : k), (-(5 / 16) : k),
      (-(5 / 8) : k), (5 / 4 : k)
      ]
      [
      [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1], [0, 0, 0, 2, 1, 0, 0],
      [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF6810_liveBCDEG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd7 : 2 * C.natDegree + G.natDegree < d)
    (hd8 : 2 * D.natDegree + E.natDegree < d)
    (hd9 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEG_p8c2]
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
theorem piQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd7 : 2 * C.natDegree + G.natDegree < d)
    (hd8 : 2 * D.natDegree + E.natDegree < d)
    (hd9 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inl hFz)
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (hd9))

def piQuarticChamberRestLF6810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF6810_liveBCDEFG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF6810_liveBCDEFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 64 : k),
      (5 / 32 : k), (25 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0],
      [0, 3, 0, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF6810_liveBCDEFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEFG_p8c1]
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

def piQuarticChamberRestLF6810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF6810_liveBCDEFG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF6810_liveBCDEFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 16) : k), (-(5 / 8) : k)
      ]
      [
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0],
      [0, 1, 0, 1, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF6810_liveBCDEFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : A.natDegree + 2 * F.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEFG_p8c2]
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

def piQuarticChamberRestLF6810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 16 : k) • (B * E * F))
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF6810_liveBCDEFG_p8c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF6810_liveBCDEFG_p8c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 16) : k), (-(5 / 16) : k), (-(15 / 16) : k),
      (-(5 / 8) : k), (5 / 4 : k)
      ]
      [
      [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 0, 2, 1, 0, 0],
      [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF6810_liveBCDEFG_p8c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : 2 * D.natDegree + E.natDegree < d)
    (hd14 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEFG_p8c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF6810_liveBCDEFG_p8c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : A.natDegree + 2 * F.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd10 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : 2 * D.natDegree + E.natDegree < d)
    (hd14 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF6810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (hd8))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (Or.inr (Or.inr (hd10))))
    (Or.inr (Or.inr (hd11)))
    (Or.inr (Or.inr (Or.inr (hd12))))
    (Or.inr (Or.inr (hd13)))
    (Or.inr (hd14))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF13810` (10 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF13810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF13810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (55 / 1024 : k), (45 / 512 : k),
      (-(5 / 64) : k), (-(5 / 64) : k), (-(25 / 128) : k),
      (-(25 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF13810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF13810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF13810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ 2 * B.natDegree + 2 * C.natDegree < d)
    (h3 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h4 : B = 0 ∨ G = 0 ∨ 2 * B.natDegree + G.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h6 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h7 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h8 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d)
    (h9 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF13810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
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
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF13810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hGz))
    (Or.inl hFz)

def xiQuarticChamberRestLF13810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF13810_liveBCDEF_p8c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF13810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF13810_liveBCDEF_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (55 / 1024 : k), (45 / 512 : k),
      (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF13810_liveBCDEF_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF13810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF13810_liveBCDEF_p8c1]
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

def xiQuarticChamberRestLF13810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF13810_liveBCDEF_p8c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF13810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF13810_liveBCDEF_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (5 / 32 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF13810_liveBCDEF_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF13810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF13810_liveBCDEF_p8c2]
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
theorem xiQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF13810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inl hGz))
    (Or.inr (hd7))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : C.natDegree + 2 * D.natDegree < d)
    (hd6 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF13810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (hd6)))
    (Or.inl hFz)

def xiQuarticChamberRestLF13810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF13810_liveBCDEFG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF13810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF13810_liveBCDEFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (55 / 1024 : k), (45 / 512 : k),
      (-(5 / 64) : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF13810_liveBCDEFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF13810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF13810_liveBCDEFG_p8c1]
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

def xiQuarticChamberRestLF13810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF13810_liveBCDEFG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF13810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF13810_liveBCDEFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1],
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF13810_liveBCDEFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : E.natDegree + G.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF13810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF13810_liveBCDEFG_p8c2]
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
theorem xiQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : E.natDegree + G.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF13810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (hd9))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF14810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF14810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF14810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2048 : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1],
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF14810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF14810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF14810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ 4 * B.natDegree < d)
    (h1 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h3 : C = 0 ∨ G = 0 ∨ C.natDegree + G.natDegree < d)
    (h4 : D = 0 ∨ F = 0 ∨ D.natDegree + F.natDegree < d)
    (h5 : E = 0 ∨ 2 * E.natDegree < d) :
    (muQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF14810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
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
  · rcases h5 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF14810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF14810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF14810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : D.natDegree + F.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF14810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (hd4))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF14810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : C.natDegree + G.natDegree < d)
    (hd3 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF14810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF14810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : C.natDegree + G.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF14810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (hd5))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF7810` (15 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF7810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 64 : k),
      (5 / 16 : k), (25 / 128 : k), (45 / 64 : k),
      (45 / 128 : k), (45 / 64 : k), (-(5 / 8) : k),
      (-(15 / 16) : k), (-(5 / 16) : k), (-(15 / 16) : k),
      (-(5 / 8) : k), (-(5 / 8) : k), (5 / 4 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `piQuarticChamberRestLF7810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF7810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ D = 0 ∨ A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ 4 * B.natDegree + C.natDegree < d)
    (h2 : B = 0 ∨ G = 0 ∨ A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (h3 : B = 0 ∨ D = 0 ∨ E = 0 ∨ A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (h4 : B = 0 ∨ F = 0 ∨ 3 * B.natDegree + F.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ E = 0 ∨ 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (h6 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + 2 * D.natDegree < d)
    (h7 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (h8 : B = 0 ∨ D = 0 ∨ G = 0 ∨ B.natDegree + D.natDegree + G.natDegree < d)
    (h9 : B = 0 ∨ E = 0 ∨ F = 0 ∨ B.natDegree + E.natDegree + F.natDegree < d)
    (h10 : C = 0 ∨ G = 0 ∨ 2 * C.natDegree + G.natDegree < d)
    (h11 : C = 0 ∨ D = 0 ∨ F = 0 ∨ C.natDegree + D.natDegree + F.natDegree < d)
    (h12 : C = 0 ∨ E = 0 ∨ C.natDegree + 2 * E.natDegree < d)
    (h13 : D = 0 ∨ E = 0 ∨ 2 * D.natDegree + E.natDegree < d)
    (h14 : G = 0 ∨ 2 * G.natDegree < d) :
    (piQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
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
  · rcases h1 with hz0 | hz1 | hb
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
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
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
  · rcases h6 with hz0 | hz1 | hb
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
  · rcases h7 with hz0 | hz1 | hz2 | hb
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
  · rcases h9 with hz0 | hz1 | hz2 | hb
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
  · rcases h10 with hz0 | hz1 | hb
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
  · rcases h11 with hz0 | hz1 | hz2 | hb
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
  · rcases h12 with hz0 | hz1 | hb
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
  · rcases h13 with hz0 | hz1 | hb
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
  · rcases h14 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd5 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (Or.inl hGz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hEz))
    (Or.inl hGz)

def piQuarticChamberRestLF7810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF7810_liveBCDEF_p8c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF7810_liveBCDEF_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 16 : k),
      (25 / 128 : k), (45 / 64 : k), (45 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 1, 0],
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF7810_liveBCDEF_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDEF_p8c1]
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

def piQuarticChamberRestLF7810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF7810_liveBCDEF_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF7810_liveBCDEF_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (-(15 / 16) : k), (-(15 / 16) : k),
      (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0],
      [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF7810_liveBCDEF_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd8 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + 2 * E.natDegree < d)
    (hd10 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDEF_p8c2]
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
theorem piQuarticChamberRestLF7810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd8 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + 2 * E.natDegree < d)
    (hd10 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (Or.inl hGz)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (Or.inr (hd10)))
    (Or.inl hGz)

def piQuarticChamberRestLF7810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF7810_liveBCDFG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF7810_liveBCDFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 64 : k),
      (25 / 128 : k), (45 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 0, 1, 0],
      [0, 2, 0, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF7810_liveBCDFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDFG_p8c1]
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

def piQuarticChamberRestLF7810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF7810_liveBCDFG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF7810_liveBCDFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (-(5 / 8) : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (5 / 4 : k)
      ]
      [
      [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF7810_liveBCDFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd7 : 2 * C.natDegree + G.natDegree < d)
    (hd8 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd9 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDFG_p8c2]
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
theorem piQuarticChamberRestLF7810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd7 : 2 * C.natDegree + G.natDegree < d)
    (hd8 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd9 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hEz))
    (Or.inr (hd9))

def piQuarticChamberRestLF7810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF7810_liveBCDEFG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF7810_liveBCDEFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 64 : k),
      (5 / 16 : k), (25 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 0],
      [0, 3, 0, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF7810_liveBCDEFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDEFG_p8c1]
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

def piQuarticChamberRestLF7810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF7810_liveBCDEFG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF7810_liveBCDEFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 8) : k), (-(15 / 16) : k)
      ]
      [
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1],
      [0, 1, 0, 0, 1, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF7810_liveBCDEFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd9 : B.natDegree + E.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDEFG_p8c2]
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

def piQuarticChamberRestLF7810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (C ^ 2 * G))
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF7810_liveBCDEFG_p8c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF7810_liveBCDEFG_p8c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(15 / 16) : k), (-(5 / 8) : k),
      (-(5 / 8) : k), (5 / 4 : k)
      ]
      [
      [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0],
      [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF7810_liveBCDEFG_p8c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDEFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : 2 * C.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + 2 * E.natDegree < d)
    (hd13 : 2 * D.natDegree + E.natDegree < d)
    (hd14 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDEFG_p8c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF7810_liveBCDEFG_p8c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd9 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd10 : 2 * C.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + 2 * E.natDegree < d)
    (hd13 : 2 * D.natDegree + E.natDegree < d)
    (hd14 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (Or.inr (hd10)))
    (Or.inr (Or.inr (Or.inr (hd11))))
    (Or.inr (Or.inr (hd12)))
    (Or.inr (Or.inr (hd13)))
    (Or.inr (hd14))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF14810` (11 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF14810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF14810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(25 / 128) : k),
      (-(25 / 128) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF14810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF14810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF14810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ E = 0 ∨ A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (h2 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ 2 * B.natDegree + 2 * C.natDegree < d)
    (h4 : B = 0 ∨ G = 0 ∨ 2 * B.natDegree + G.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h6 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h7 : C = 0 ∨ E = 0 ∨ 2 * C.natDegree + E.natDegree < d)
    (h8 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h9 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d)
    (h10 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF14810]
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
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
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
theorem xiQuarticChamberRestLF14810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : C.natDegree + 2 * D.natDegree < d)
    (hd5 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF14810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd4)))
    (Or.inl hEz)
    (Or.inr (hd5))

def xiQuarticChamberRestLF14810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (25 / 128 : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF14810_liveBCDEF_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF14810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF14810_liveBCDEF_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(25 / 128) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [0, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF14810_liveBCDEF_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF14810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF14810_liveBCDEF_p8c1]
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

def xiQuarticChamberRestLF14810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * D * E))
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF14810_liveBCDEF_p8c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF14810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF14810_liveBCDEF_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 32 : k)
      ]
      [
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF14810_liveBCDEF_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * C.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF14810_liveBCDEF_p8c2]
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
theorem xiQuarticChamberRestLF14810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * C.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF14810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inl hGz))
    (Or.inr (hd8))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : C.natDegree + 2 * D.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF14810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd5)))
    (Or.inl hEz)
    (Or.inr (hd6))

def xiQuarticChamberRestLF14810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF14810_liveBCDEFG_p8c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF14810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF14810_liveBCDEFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(25 / 128) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF14810_liveBCDEFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF14810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF14810_liveBCDEFG_p8c1]
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

def xiQuarticChamberRestLF14810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * D * E))
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF14810_liveBCDEFG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF14810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF14810_liveBCDEFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1],
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF14810_liveBCDEFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : E.natDegree + G.natDegree < d)
    (hd10 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF14810_liveBCDEFG_p8c2]
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
theorem xiQuarticChamberRestLF14810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : E.natDegree + G.natDegree < d)
    (hd10 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF14810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (hd10))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF15810` (12 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF15810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF15810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF15810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF15810
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
    (h10 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d)
    (h11 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810]
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
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BCDF
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
    (hd5 : C.natDegree + 2 * D.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF15810 A B C D E F G hdpos
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
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF15810 A B C D E F G hdpos
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
    (Or.inr (hd4))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + G.natDegree < d)
    (hd3 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF15810 A B C D E F G hdpos
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
    (Or.inr (hd3))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : 2 * C.natDegree + E.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF15810 A B C D E F G hdpos
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
    (Or.inr (hd2))

def xiQuarticChamberRestLF15810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF15810_liveBCDEF_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF15810_liveBCDEF_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF15810_liveBCDEF_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDEF_p8c1]
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

def xiQuarticChamberRestLF15810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF15810_liveBCDEF_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF15810_liveBCDEF_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 32 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF15810_liveBCDEF_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDEF_p8c2]
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
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BCDEF
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
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF15810 A B C D E F G hdpos
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
    (Or.inr (hd9))

def xiQuarticChamberRestLF15810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF15810_liveBCDFG_p8c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF15810_liveBCDFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF15810_liveBCDFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDFG_p8c1]
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

def xiQuarticChamberRestLF15810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * C * F)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF15810_liveBCDFG_p8c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF15810_liveBCDFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (5 / 32 : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF15810_liveBCDFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDFG_p8c2]
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
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BCDFG
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
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF15810 A B C D E F G hdpos
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
    (Or.inr (hd7))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : E.natDegree + G.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF15810 A B C D E F G hdpos
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
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 2 * C.natDegree + E.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d)
    (hd2 : E.natDegree + G.natDegree < d)
    (hd3 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF15810 A B C D E F G hdpos
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
    (Or.inr (hd3))

def xiQuarticChamberRestLF15810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF15810_liveBCDEFG_p8c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF15810_liveBCDEFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF15810_liveBCDEFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDEFG_p8c1]
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

def xiQuarticChamberRestLF15810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF15810_liveBCDEFG_p8c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF15810_liveBCDEFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF15810_liveBCDEFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : 2 * C.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF15810_liveBCDEFG_p8c2]
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
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BCDEFG
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
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF15810 A B C D E F G hdpos
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
    (Or.inr (hd11))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF9810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_kappaQuarticChamberRestLF9810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF9810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `kappaQuarticChamberRestLF9810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF9810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + D.natDegree < d)
    (h1 : C = 0 ∨ F = 0 ∨ C.natDegree + F.natDegree < d)
    (h2 : D = 0 ∨ E = 0 ∨ D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_kappaQuarticChamberRestLF9810]
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
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF9810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF9810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF9810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd1)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF9810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF9810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF9810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF8810` (15 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF8810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 16) : k), (-(5 / 8) : k), (-(15 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 1, 2, 1, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0],
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `piQuarticChamberRestLF8810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF8810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ D = 0 ∨ A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ 4 * B.natDegree + C.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (h3 : B = 0 ∨ D = 0 ∨ E = 0 ∨ A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (h4 : C = 0 ∨ D = 0 ∨ A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (h5 : B = 0 ∨ F = 0 ∨ 3 * B.natDegree + F.natDegree < d)
    (h6 : B = 0 ∨ C = 0 ∨ E = 0 ∨ 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (h7 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + 2 * D.natDegree < d)
    (h8 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (h9 : F = 0 ∨ A.natDegree + 2 * F.natDegree < d)
    (h10 : B = 0 ∨ D = 0 ∨ G = 0 ∨ B.natDegree + D.natDegree + G.natDegree < d)
    (h11 : B = 0 ∨ E = 0 ∨ F = 0 ∨ B.natDegree + E.natDegree + F.natDegree < d)
    (h12 : C = 0 ∨ D = 0 ∨ F = 0 ∨ C.natDegree + D.natDegree + F.natDegree < d)
    (h13 : C = 0 ∨ E = 0 ∨ C.natDegree + 2 * E.natDegree < d)
    (h14 : D = 0 ∨ E = 0 ∨ 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
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
  · rcases h1 with hz0 | hz1 | hb
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
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
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
  · rcases h6 with hz0 | hz1 | hz2 | hb
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
  · rcases h7 with hz0 | hz1 | hb
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
  · rcases h8 with hz0 | hz1 | hz2 | hb
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
  · rcases h9 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hz1 | hz2 | hb
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
  · rcases h11 with hz0 | hz1 | hz2 | hb
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
  · rcases h12 with hz0 | hz1 | hz2 | hb
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
  · rcases h13 with hz0 | hz1 | hb
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
  · rcases h14 with hz0 | hz1 | hb
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
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inl hFz)
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : 4 * B.natDegree + C.natDegree < d)
    (hd1 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inl hFz)
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)

def piQuarticChamberRestLF8810_liveBCDEG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (45 / 64 : k) • (B ^ 2 * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF8810_liveBCDEG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDEG_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF8810_liveBCDEG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 16 : k),
      (5 / 32 : k), (45 / 64 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 2, 1, 0, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF8810_liveBCDEG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDEG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDEG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDEG_p8c1]
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

def piQuarticChamberRestLF8810_liveBCDEG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF8810_liveBCDEG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDEG_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF8810_liveBCDEG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 128 : k), (45 / 64 : k), (-(5 / 8) : k),
      (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0],
      [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF8810_liveBCDEG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDEG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd8 : C.natDegree + 2 * E.natDegree < d)
    (hd9 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDEG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDEG_p8c2]
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
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd8 : C.natDegree + 2 * E.natDegree < d)
    (hd9 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inl hFz)
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (hd9)))

def piQuarticChamberRestLF8810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF8810_liveBCDFG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF8810_liveBCDFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 32 : k),
      (5 / 32 : k), (25 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF8810_liveBCDFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDFG_p8c1]
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

def piQuarticChamberRestLF8810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (C * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF8810_liveBCDFG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF8810_liveBCDFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 128 : k), (45 / 64 : k), (-(5 / 16) : k),
      (-(5 / 8) : k), (-(15 / 16) : k)
      ]
      [
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF8810_liveBCDFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDFG_p8c2]
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
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (hd7))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : 4 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + 2 * F.natDegree < d)
    (hd5 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd6 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (hd4))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd6)))
    (Or.inl hDz)

def piQuarticChamberRestLF8810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF8810_liveBCDEFG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF8810_liveBCDEFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF8810_liveBCDEFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDEFG_p8c1]
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

def piQuarticChamberRestLF8810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF8810_liveBCDEFG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF8810_liveBCDEFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 128 : k), (45 / 64 : k), (45 / 128 : k),
      (45 / 64 : k), (-(5 / 16) : k)
      ]
      [
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [1, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [piQuarticChamberRestLF8810_liveBCDEFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : A.natDegree + 2 * F.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDEFG_p8c2]
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

def piQuarticChamberRestLF8810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 8 : k) • (B * D * G))
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF8810_liveBCDEFG_p8c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF8810_liveBCDEFG_p8c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 8) : k), (-(15 / 16) : k), (-(15 / 16) : k),
      (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0],
      [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF8810_liveBCDEFG_p8c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDEFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + 2 * E.natDegree < d)
    (hd14 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDEFG_p8c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_piQuarticChamberRestLF8810_liveBCDEFG_p8c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : A.natDegree + 2 * F.natDegree < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + 2 * E.natDegree < d)
    (hd14 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_piQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (hd9))
    (Or.inr (Or.inr (Or.inr (hd10))))
    (Or.inr (Or.inr (Or.inr (hd11))))
    (Or.inr (Or.inr (Or.inr (hd12))))
    (Or.inr (Or.inr (hd13)))
    (Or.inr (Or.inr (hd14)))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF15810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF15810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF15810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2048 : k), (-(5 / 128) : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [muQuarticChamberRestLF15810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF15810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF15810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ 4 * B.natDegree < d)
    (h1 : D = 0 ∨ A.natDegree + 2 * D.natDegree < d)
    (h2 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h4 : C = 0 ∨ G = 0 ∨ C.natDegree + G.natDegree < d)
    (h5 : D = 0 ∨ F = 0 ∨ D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_muQuarticChamberRestLF15810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
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


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF15810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d) :
    (muQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF15810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF15810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF15810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd4)))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF15810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF15810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF15810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_muQuarticChamberRestLF15810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF16810` (10 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF16810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF16810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF16810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF16810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF16810
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
    (h9 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF16810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF16810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
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
  · rcases h9 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF16810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF16810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF16810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF16810_natDegree_lt_of_live_BCDEG
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
    (hd6 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF16810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF16810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF16810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 2 * B.natDegree + G.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF16810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF16810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (hd4))

def xiQuarticChamberRestLF16810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF16810_liveBCDEFG_p8c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF16810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF16810_liveBCDEFG_p8c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF16810_liveBCDEFG_p8c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF16810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF16810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF16810_liveBCDEFG_p8c1]
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

def xiQuarticChamberRestLF16810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF16810_liveBCDEFG_p8c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF16810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF16810_liveBCDEFG_p8c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (5 / 32 : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF16810_liveBCDEFG_p8c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF16810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF16810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_xiQuarticChamberRestLF16810_liveBCDEFG_p8c2]
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
theorem xiQuarticChamberRestLF16810_natDegree_lt_of_live_BCDEFG
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
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF16810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_xiQuarticChamberRestLF16810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (hd9))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF10810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart8_kappaQuarticChamberRestLF10810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF10810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k)
      ]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `kappaQuarticChamberRestLF10810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF10810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 3 * B.natDegree < d)
    (h1 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + D.natDegree < d)
    (h2 : C = 0 ∨ F = 0 ∨ C.natDegree + F.natDegree < d)
    (h3 : D = 0 ∨ E = 0 ∨ D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart8_kappaQuarticChamberRestLF10810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, True.intro⟩
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


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF10810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d) :
    (kappaQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart8_kappaQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)


end QuarticChamberFaces810

end Max11DegreeRoutes
