import Grok810DegreeZeroSourceNumeratorScratch

/-! # Compact residual bridge for the `(8,10)` degree-zero primitive

Lane Z7 parent.  Unfolds the nested residual expansion
`compact = 2^{28} ρ` and records the integer-cleared coordinates
`h^{7d} · depressed`.  The source-clearing identity and head vanishing
live in `Grok810DegreeZeroClearingDischargeScratch`.

No chamber is closed.  Constants are `119 / 17 / 102`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Bookkeeping: extra compact-to-source integer scale -/

/-- Remaining integer scale after the grouped compact `2^{28}` is
removed from the source numerator `2^{62}`. -/
def degreeZeroCompactToSourceIntegerScale810 : ℕ := 17179869184

theorem degreeZeroCompactToSourceIntegerScale810_eq :
    degreeZeroCompactToSourceIntegerScale810 = 17179869184 := rfl

theorem degreeZeroCompactToSourceIntegerScale810_eq_pow :
    degreeZeroCompactToSourceIntegerScale810 = 2 ^ 34 := rfl

theorem degreeZeroClearedIntegerScale810_eq_grouped_mul_compact :
    degreeZeroClearedIntegerScale810 =
      degreeZeroGroupedIntegerScale810 *
        degreeZeroCompactToSourceIntegerScale810 :=
  rfl

theorem degreeZeroSourceClearingPower810_eq_base_add_effective :
    degreeZeroSourceClearingPower810 =
      degreeZeroSourceBaseOrder810 +
        degreeZeroEffectiveTowerLength810 :=
  rfl

#print axioms degreeZeroCompactToSourceIntegerScale810_eq_pow
#print axioms degreeZeroClearedIntegerScale810_eq_grouped_mul_compact
#print axioms degreeZeroSourceClearingPower810_eq_base_add_effective

/-! ## Nested residual expansion `compact = 2^{28} ρ` -/

section DegreeZeroCompactResidual810

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- Exact numerical clearing from the grouped primitive to the compact
integer numerator.  The nested residuals `β` through `θ` are unfolded;
this is the `(8,10)` analog of `degreeZeroPrimitive610_eq_clearedCompact`. -/
theorem rhoResidual810_eq_clearedCompact
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) :
    degreeZeroClearedCompact810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0
        W0 =
      (degreeZeroGroupedIntegerScale810 : F) *
        rhoResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h512 : (512 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h4096 : (4096 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h16384 : (16384 : F) ≠ 0 := by norm_num
  have h32768 : (32768 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h524288 : (524288 : F) ≠ 0 := by norm_num
  have h1048576 : (1048576 : F) ≠ 0 := by norm_num
  have h268435456 : (268435456 : F) ≠ 0 := by norm_num
  simp only [degreeZeroClearedCompact810, rhoResidual810,
    rhoBaseGroup810, rhoBetaGroup810, rhoGammaGroup810,
    rhoDeltaGroup810, rhoEpsilonGroup810, rhoZetaGroup810,
    rhoEtaGroup810, rhoThetaGroup810, alphaResidual810,
    betaResidual810, gammaResidual810, deltaResidual810,
    epsilonResidual810, zetaResidual810, etaResidual810,
    thetaResidual810, degreeZeroGroupedIntegerScale810]
  field_simp [h2, h4, h8, h16, h32, h64, h128, h256, h512, h1024, h2048,
    h4096, h8192, h16384, h32768, h65536, h131072, h262144, h524288,
    h1048576, h268435456]
  ring

#print axioms rhoResidual810_eq_clearedCompact

end DegreeZeroCompactResidual810

/-! ## Integer-cleared coordinates `h^{7d} · depressed` -/

section DegreeZeroScaledDepressed810

variable {F : Type*} [Field F] [CharZero F]

theorem degreeZeroScaledDepressedL810
    (h a7 b9 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    h ^ 7 * depressedL810 h (octicDepressionR810 h a7) b9 =
      -lambda * h ^ 7 / 4 := by
  rw [depressedL810_eq_of_ninthPower h a7 b9 lambda hh hN]
  field_simp

theorem degreeZeroScaledDepressedA810
    (h a7 a6 : F) (hh : h ≠ 0) :
    h ^ 14 * depressedA810 h (octicDepressionR810 h a7) a7 a6 =
      (16 * a6 * h ^ 8 - 7 * a7 ^ 2) / 16 := by
  rw [depressedA810_eq_cleared h a7 a6 hh]
  have h16 : (16 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  field_simp [hh, h16, hh14]

theorem degreeZeroScaledDepressedB810
    (h a7 a6 a5 : F) (hh : h ≠ 0) :
    h ^ 21 * depressedB810 h (octicDepressionR810 h a7) a7 a6 a5 =
      (32 * a5 * h ^ 16 - 24 * a6 * a7 * h ^ 8 + 7 * a7 ^ 3) / 32 := by
  rw [depressedB810_eq_cleared h a7 a6 a5 hh]
  have h32 : (32 : F) ≠ 0 := by norm_num
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  field_simp [hh, h32, hh21]

theorem degreeZeroScaledDepressedC810
    (h a7 a6 a5 a4 : F) (hh : h ≠ 0) :
    h ^ 28 * depressedC810 h (octicDepressionR810 h a7) a7 a6 a5 a4 =
      (2048 * a4 * h ^ 24 - 1280 * a5 * a7 * h ^ 16 +
          480 * a6 * a7 ^ 2 * h ^ 8 - 105 * a7 ^ 4) / 2048 := by
  rw [depressedC810_eq_cleared h a7 a6 a5 a4 hh]
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  field_simp [hh, h2048, hh28]

theorem degreeZeroScaledDepressedD810
    (h a7 a6 a5 a4 a3 : F) (hh : h ≠ 0) :
    h ^ 35 * depressedD810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 =
      (1024 * a3 * h ^ 32 - 512 * a4 * a7 * h ^ 24 +
          160 * a5 * a7 ^ 2 * h ^ 16 - 40 * a6 * a7 ^ 3 * h ^ 8 +
          7 * a7 ^ 5) / 1024 := by
  rw [depressedD810_eq_cleared h a7 a6 a5 a4 a3 hh]
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  field_simp [hh, h1024, hh35]

theorem degreeZeroScaledDepressedE810
    (h a7 a6 a5 a4 a3 a2 : F) (hh : h ≠ 0) :
    h ^ 42 * depressedE810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3
        a2 =
      (65536 * a2 * h ^ 40 - 24576 * a3 * a7 * h ^ 32 +
          6144 * a4 * a7 ^ 2 * h ^ 24 - 1280 * a5 * a7 ^ 3 * h ^ 16 +
          240 * a6 * a7 ^ 4 * h ^ 8 - 35 * a7 ^ 6) / 65536 := by
  rw [depressedE810_eq_cleared h a7 a6 a5 a4 a3 a2 hh]
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  field_simp [hh, h65536, hh42]

theorem degreeZeroScaledDepressedF810
    (h a7 a6 a5 a4 a3 a2 a1 : F) (hh : h ≠ 0) :
    h ^ 49 * depressedF810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3
        a2 a1 =
      (131072 * a1 * h ^ 48 - 32768 * a2 * a7 * h ^ 40 +
          6144 * a3 * a7 ^ 2 * h ^ 32 - 1024 * a4 * a7 ^ 3 * h ^ 24 +
          160 * a5 * a7 ^ 4 * h ^ 16 - 24 * a6 * a7 ^ 5 * h ^ 8 +
          3 * a7 ^ 7) / 131072 := by
  rw [depressedF810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 hh]
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  field_simp [hh, h131072, hh49]

theorem degreeZeroScaledDepressedG810
    (h a7 a6 a5 a4 a3 a2 a1 a0 : F) (hh : h ≠ 0) :
    h ^ 56 * depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3
        a2 a1 a0 =
      (16777216 * a0 * h ^ 56 - 2097152 * a1 * a7 * h ^ 48 +
          262144 * a2 * a7 ^ 2 * h ^ 40 - 32768 * a3 * a7 ^ 3 * h ^ 32 +
          4096 * a4 * a7 ^ 4 * h ^ 24 - 512 * a5 * a7 ^ 5 * h ^ 16 +
          64 * a6 * a7 ^ 6 * h ^ 8 - 7 * a7 ^ 8) / 16777216 := by
  rw [depressedG810_eq_cleared h a7 a6 a5 a4 a3 a2 a1 a0 hh]
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  field_simp [hh, h16777216, hh56]

theorem degreeZeroScaledDepressedP810
    (h a7 b9 b8 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    h ^ 14 * depressedP810 h (octicDepressionR810 h a7) b9 b8 =
      (-45 * a7 ^ 2 + 18 * lambda * a7 * h ^ 7 + 64 * b8 * h ^ 6) /
        64 := by
  rw [depressedP810_eq_cleared_ninthPower h a7 b9 b8 lambda hh hN]
  have h64 : (64 : F) ≠ 0 := by norm_num
  have hh14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  field_simp [hh, h64, hh14]

theorem degreeZeroScaledDepressedQ810
    (h a7 b9 b8 b7 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    h ^ 21 * depressedQ810 h (octicDepressionR810 h a7) b9 b8 b7 =
      (64 * b7 * h ^ 14 - 64 * a7 * b8 * h ^ 6 -
          9 * lambda * a7 ^ 2 * h ^ 7 + 30 * a7 ^ 3) / 64 := by
  rw [depressedQ810_eq_cleared h a7 b9 b8 b7 lambda hh hN]
  have h64 : (64 : F) ≠ 0 := by norm_num
  have hh21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  field_simp [hh, h64, hh21]

theorem degreeZeroScaledDepressedR810
    (h a7 b9 b8 b7 b6 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    h ^ 28 * depressedR810 h (octicDepressionR810 h a7) b9 b8 b7 b6 =
      (-315 * a7 ^ 4 + 84 * lambda * a7 ^ 3 * h ^ 7 +
          896 * a7 ^ 2 * b8 * h ^ 6 - 1792 * a7 * b7 * h ^ 14 +
          2048 * b6 * h ^ 22) / 2048 := by
  rw [depressedR810_eq_cleared h a7 b9 b8 b7 b6 lambda hh hN]
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have hh28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  field_simp [hh, h2048, hh28]

theorem degreeZeroScaledDepressedS810
    (h a7 b9 b8 b7 b6 b5 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    h ^ 35 * depressedS810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 =
      (252 * a7 ^ 5 - 63 * lambda * a7 ^ 4 * h ^ 7 -
          896 * a7 ^ 3 * b8 * h ^ 6 + 2688 * a7 ^ 2 * b7 * h ^ 14 -
          6144 * a7 * b6 * h ^ 22 + 8192 * b5 * h ^ 30) / 8192 := by
  rw [depressedS810_eq_cleared h a7 b9 b8 b7 b6 b5 lambda hh hN]
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  field_simp [hh, h8192, hh35]

theorem degreeZeroScaledDepressedT810
    (h a7 b9 b8 b7 b6 b5 b4 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    h ^ 42 * depressedT810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5
        b4 =
      (-525 * a7 ^ 6 + 126 * lambda * a7 ^ 5 * h ^ 7 +
          2240 * a7 ^ 4 * b8 * h ^ 6 - 8960 * a7 ^ 3 * b7 * h ^ 14 +
          30720 * a7 ^ 2 * b6 * h ^ 22 - 81920 * a7 * b5 * h ^ 30 +
          131072 * b4 * h ^ 38) / 131072 := by
  rw [depressedT810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 lambda hh hN]
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have hh42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  field_simp [hh, h131072, hh42]

theorem degreeZeroScaledDepressedU810
    (h a7 b9 b8 b7 b6 b5 b4 b3 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    h ^ 49 * depressedU810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5
        b4 b3 =
      (90 * a7 ^ 7 - 21 * lambda * a7 ^ 6 * h ^ 7 -
          448 * a7 ^ 5 * b8 * h ^ 6 + 2240 * a7 ^ 4 * b7 * h ^ 14 -
          10240 * a7 ^ 3 * b6 * h ^ 22 + 40960 * a7 ^ 2 * b5 * h ^ 30 -
          131072 * a7 * b4 * h ^ 38 + 262144 * b3 * h ^ 46) /
        262144 := by
  rw [depressedU810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 lambda hh hN]
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have hh49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  field_simp [hh, h262144, hh49]

theorem degreeZeroScaledDepressedV810
    (h a7 b9 b8 b7 b6 b5 b4 b3 b2 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    h ^ 56 * depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5
        b4 b3 b2 =
      (-315 * a7 ^ 8 + 72 * lambda * a7 ^ 7 * h ^ 7 +
          1792 * a7 ^ 6 * b8 * h ^ 6 - 10752 * a7 ^ 5 * b7 * h ^ 14 +
          61440 * a7 ^ 4 * b6 * h ^ 22 - 327680 * a7 ^ 3 * b5 * h ^ 30 +
          1572864 * a7 ^ 2 * b4 * h ^ 38 -
          6291456 * a7 * b3 * h ^ 46 + 16777216 * b2 * h ^ 54) /
        16777216 := by
  rw [depressedV810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh
    hN]
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  field_simp [hh, h16777216, hh56]

theorem degreeZeroScaledDepressedW810
    (h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    h ^ 63 * depressedW810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5
        b4 b3 b2 b1 =
      (40 * a7 ^ 9 - 9 * lambda * a7 ^ 8 * h ^ 7 -
          256 * a7 ^ 7 * b8 * h ^ 6 + 1792 * a7 ^ 6 * b7 * h ^ 14 -
          12288 * a7 ^ 5 * b6 * h ^ 22 + 81920 * a7 ^ 4 * b5 * h ^ 30 -
          524288 * a7 ^ 3 * b4 * h ^ 38 +
          3145728 * a7 ^ 2 * b3 * h ^ 46 -
          16777216 * a7 * b2 * h ^ 54 + 67108864 * b1 * h ^ 62) /
        67108864 := by
  rw [depressedW810_eq_cleared h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda
    hh hN]
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  have hh63 : h ^ 63 ≠ 0 := pow_ne_zero 63 hh
  field_simp [hh, h67108864, hh63]

#print axioms degreeZeroScaledDepressedL810
#print axioms degreeZeroScaledDepressedA810
#print axioms degreeZeroScaledDepressedG810
#print axioms degreeZeroScaledDepressedW810

end DegreeZeroScaledDepressed810

end Max11DegreeRoutes
