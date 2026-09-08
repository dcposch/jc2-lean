import Grok610ScaleZeroCubicLoadWallsPart185Scratch
import Grok610ScaleZeroCubicLoadWallsPart187Scratch
import Grok610ScaleZeroCubicLoadWallsPart189Scratch
import Grok610ScaleZeroCubicLoadWallsPart193Scratch
import Grok610ScaleZeroCubicLoadWallsPart195Scratch
import Grok610ScaleZeroCubicLoadWallsPart196Scratch
import Grok610ScaleZeroCubicLoadWallsPart198Scratch

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
set_option maxRecDepth 100000000

section CubicLoadCDChamber610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Chamber `E ≠ 0`.  κ's `DE` column kills all but two residual
loci (`α = 0 ∧ e = 0`, and `α ≠ 0 ∧ e = c`), which are finished by
ο and the λ/ο combination at degree `3c`. -/
theorem cubicLoadSigmaCone_CD_chamber_Ene_impossible
    (alpha epsilon eta : k) (A C D E : k[X])
    (hAne : A ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0)
    (hApos : 0 < A.natDegree)
    (hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree)
    (hTle : 2 * C.natDegree + D.natDegree ≤ A.natDegree)
    (hEcmp : 2 * E.natDegree < 3 * C.natDegree)
    (hlam : (degreeZeroLambdaCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 0 alpha 0 0 epsilon 0 eta 0
          A 0 C D E).natDegree = 0) :
    False := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hCpos : 0 < C.natDegree := by
    have : ¬ C.natDegree = 0 := by intro hc0; omega
    exact Nat.pos_of_ne_zero this
  have h2c_gt : C.natDegree + 2 * D.natDegree < 2 * C.natDegree := by omega
  -- Easy κ kills: `DE` strictly tops unless `e ≤ c`.
  by_cases hgt : C.natDegree < E.natDegree
  · -- e > c: κ face is DE
    have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
    have hlead :
        ((10 / 9 : k) • (D * E)).natDegree = D.natDegree + E.natDegree := by
      rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
    have hrestAlpha :
        ((4 / 9 * alpha : k) • (C * D)).natDegree <
          D.natDegree + E.natDegree := by
      refine (natDegree_smul_le610 _ _).trans_lt ?_
      have : (C * D).natDegree = C.natDegree + D.natDegree :=
        natDegree_mul hCne hDne
      rw [this]; omega
    have hrestEps :
        ((2 / 3 * epsilon : k) • D).natDegree <
          D.natDegree + E.natDegree := by
      refine (natDegree_smul_le610 _ _).trans_lt ?_
      omega
    have hkap0 := hkap
    rw [degreeZeroKappaCubic610_eq_chamber alpha epsilon eta A C D E] at hkap0
    simp only [kappaChamberCD610] at hkap0
    have hsum :
        ((10 / 9 : k) • (D * E) + (4 / 9 * alpha : k) • (C * D) +
            (2 / 3 * epsilon : k) • D).natDegree =
          D.natDegree + E.natDegree := by
      have h12 :
          ((10 / 9 : k) • (D * E) + (4 / 9 * alpha : k) • (C * D)).natDegree =
            D.natDegree + E.natDegree := by
        rw [← hlead]
        refine natDegree_add_eq_left_of_natDegree_lt ?_
        rw [hlead]
        exact hrestAlpha
      rw [← h12]
      refine natDegree_add_eq_left_of_natDegree_lt ?_
      rw [h12]
      exact hrestEps
    rw [hsum] at hkap0
    omega
  -- Remaining: e ≤ c.
  have hele : E.natDegree ≤ C.natDegree := Nat.le_of_not_lt hgt
  by_cases halpha : alpha = 0
  · subst halpha
    by_cases he0 : E.natDegree = 0
    · -- α = 0, e = 0: E is a nonzero constant, so C²-terms are a scalar
      -- times C².  If that scalar is nonzero, ο has degree 2c > 0; if it
      -- vanishes, ο reduces to C D² of degree c+2d > 0.
      have hblk := omicronC2Block_of_natDegree_E_eq_zero epsilon C E he0
      have hom0 := homi
      rw [degreeZeroOmicronCubic610_eq_chamber 0 epsilon eta A C D E] at hom0
      have hpoly :
          omicronChamberCD610 0 epsilon eta A C D E =
            ((-(5 / 27 : k)) • (C ^ 2 * E) +
                (-(1 / 9 * epsilon : k)) • C ^ 2) +
              ((-(5 / 27 : k)) • (C * D ^ 2) + (1 / 3 * eta : k) • E) := by
        rw [omicronChamberCD610_of_alpha_eq_zero]
        abel
      rw [hpoly] at hom0
      by_cases hsc0 :
          (-(5 / 27 : k)) * E.leadingCoeff + (-(1 / 9 * epsilon : k)) = 0
      · -- scalar vanished: ο = (-5/27) C D² + (1/3) η E
        have hcancel :
            (-(5 / 27 : k)) • (C ^ 2 * E) +
              (-(1 / 9 * epsilon : k)) • C ^ 2 = 0 := by
          rw [hblk, hsc0, zero_smul]
        rw [hcancel, zero_add] at hom0
        have hc : (-(5 / 27 : k)) ≠ 0 :=
          neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
        have hlead :
            ((-(5 / 27 : k)) • (C * D ^ 2)).natDegree =
              C.natDegree + 2 * D.natDegree := by
          rw [natDegree_smul _ hc, natDegree_mul hCne (pow_ne_zero 2 hDne),
            natDegree_pow]
        have hrest :
            ((1 / 3 * eta : k) • E).natDegree <
              C.natDegree + 2 * D.natDegree := by
          refine (natDegree_smul_le610 _ _).trans_lt ?_
          rw [he0]; omega
        have hdeg :
            ((-(5 / 27 : k)) • (C * D ^ 2) + (1 / 3 * eta : k) • E).natDegree =
              C.natDegree + 2 * D.natDegree := by
          rw [← hlead]
          refine natDegree_add_eq_left_of_natDegree_lt ?_
          rw [hlead]
          exact hrest
        rw [hdeg] at hom0
        omega
      · -- 2c block is the top
        have hc : (-(5 / 27 : k)) * E.leadingCoeff +
            (-(1 / 9 * epsilon : k)) ≠ 0 := hsc0
        have htop :
            ((-(5 / 27 : k)) • (C ^ 2 * E) +
                (-(1 / 9 * epsilon : k)) • C ^ 2).natDegree =
              2 * C.natDegree := by
          rw [hblk, natDegree_smul _ hc, natDegree_pow]
        have hrest :
            ((-(5 / 27 : k)) • (C * D ^ 2) + (1 / 3 * eta : k) • E).natDegree <
              2 * C.natDegree := by
          have h1 : ((-(5 / 27 : k)) • (C * D ^ 2)).natDegree <
              2 * C.natDegree := by
            refine (natDegree_smul_le610 _ _).trans_lt ?_
            have : (C * D ^ 2).natDegree = C.natDegree + 2 * D.natDegree := by
              rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
            rw [this]; omega
          have h2 : ((1 / 3 * eta : k) • E).natDegree < 2 * C.natDegree := by
            refine (natDegree_smul_le610 _ _).trans_lt ?_
            rw [he0]; omega
          exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt h1 h2)
        have hdeg :
            (((-(5 / 27 : k)) • (C ^ 2 * E) +
                (-(1 / 9 * epsilon : k)) • C ^ 2) +
              ((-(5 / 27 : k)) • (C * D ^ 2) + (1 / 3 * eta : k) • E)).natDegree =
              2 * C.natDegree := by
          rw [← htop]
          refine natDegree_add_eq_left_of_natDegree_lt ?_
          rw [htop]
          exact hrest
        rw [hdeg] at hom0
        omega
    · -- α = 0, e > 0: κ face is DE
      have hepos : 0 < E.natDegree := Nat.pos_of_ne_zero he0
      have hc : (10 / 9 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
      have hlead :
          ((10 / 9 : k) • (D * E)).natDegree = D.natDegree + E.natDegree := by
        rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
      have hrestEps :
          ((2 / 3 * epsilon : k) • D).natDegree <
            D.natDegree + E.natDegree := by
        refine (natDegree_smul_le610 _ _).trans_lt ?_
        omega
      have hkap0 := hkap
      rw [degreeZeroKappaCubic610_eq_chamber 0 epsilon eta A C D E] at hkap0
      simp only [kappaChamberCD610, mul_zero, zero_smul, add_zero] at hkap0
      have hdeg :
          ((10 / 9 : k) • (D * E) + (2 / 3 * epsilon : k) • D).natDegree =
            D.natDegree + E.natDegree := by
        rw [← hlead]
        refine natDegree_add_eq_left_of_natDegree_lt ?_
        rw [hlead]
        exact hrestEps
      rw [hdeg] at hkap0
      omega
  · -- α ≠ 0.  If e < c, kappa face is α C D.
    by_cases hlt : E.natDegree < C.natDegree
    · have hc : (4 / 9 * alpha : k) ≠ 0 :=
        mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) halpha
      have hlead :
          ((4 / 9 * alpha : k) • (C * D)).natDegree =
            C.natDegree + D.natDegree := by
        rw [natDegree_smul _ hc, natDegree_mul hCne hDne]
      have hrestDE :
          ((10 / 9 : k) • (D * E)).natDegree <
            C.natDegree + D.natDegree := by
        refine (natDegree_smul_le610 _ _).trans_lt ?_
        have : (D * E).natDegree = D.natDegree + E.natDegree :=
          natDegree_mul hDne hEne
        rw [this]; omega
      have hrestEps :
          ((2 / 3 * epsilon : k) • D).natDegree <
            C.natDegree + D.natDegree := by
        refine (natDegree_smul_le610 _ _).trans_lt ?_
        omega
      have hkap0 := hkap
      rw [degreeZeroKappaCubic610_eq_chamber alpha epsilon eta A C D E] at hkap0
      simp only [kappaChamberCD610] at hkap0
      have h12 :
          ((10 / 9 : k) • (D * E) + (4 / 9 * alpha : k) • (C * D)).natDegree =
            C.natDegree + D.natDegree := by
        rw [← hlead]
        refine natDegree_add_eq_right_of_natDegree_lt ?_
        rw [hlead]
        exact hrestDE
      have hdeg :
          ((10 / 9 : k) • (D * E) + (4 / 9 * alpha : k) • (C * D) +
              (2 / 3 * epsilon : k) • D).natDegree =
            C.natDegree + D.natDegree := by
        rw [← h12]
        refine natDegree_add_eq_left_of_natDegree_lt ?_
        rw [h12]
        exact hrestEps
      rw [hdeg] at hkap0
      omega
    · -- e = c (since e ≤ c and ¬ e < c)
      have heq : E.natDegree = C.natDegree :=
        le_antisymm hele (Nat.le_of_not_lt hlt)
      -- lambda inner 3ad²+c³ = 0, then omicron at 3c with C²E included.
      have hfaceDeg : 0 < A.natDegree + 2 * D.natDegree := by omega
      have hltLam :
          (degreeZeroLambdaCubic610 0 alpha 0 0 epsilon 0 eta 0
              A 0 C D E).natDegree < A.natDegree + 2 * D.natDegree := by
        rw [hlam]
        exact hfaceDeg
      have hzLam : (degreeZeroLambdaCubic610 0 alpha 0 0 epsilon 0 eta 0
            A 0 C D E).coeff (A.natDegree + 2 * D.natDegree) = 0 :=
        coeff_eq_zero_of_natDegree_lt hltLam
      rw [degreeZeroLambdaCubic610_eq_sigmaCD_add_rest, coeff_add] at hzLam
      have hrestLam :
          (degreeZeroLambdaCubicNoSigmaCD610 0 alpha 0 0 epsilon 0 eta 0
              A 0 C D E).natDegree < A.natDegree + 2 * D.natDegree := by
        rw [degreeZeroLambdaCubicNoSigmaCD610_eq_chamberRest]
        rw [speedRefl_lambdaChamberRestCD610_eq_polyOf_dupfix]
        first
          | refine Max11ReflectDeg.natDegree_polyOf_le_of_degLe ?_
          | refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
        simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
          Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.degLe_cons,
                  Max11ReflectDeg.degLe_nil_left, Max11ReflectDeg.degLe_nil_right,
                  Max11ReflectDeg.mdeg_cons,
          Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
          List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
          Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
          mul_one, one_mul, and_true, true_and, natDegree_zero]
        repeat' apply And.intro
        all_goals first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial
      rw [coeff_eq_zero_of_natDegree_lt hrestLam, add_zero] at hzLam
      have hinner :
          lambdaCubicSigmaInnerCD610 A.leadingCoeff C.leadingCoeff
            D.leadingCoeff = 0 := by
        have hdeg_AD2 : ((A * D ^ 2)).natDegree =
            A.natDegree + 2 * D.natDegree := by
          rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
        have hcf_AD2 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) =
            A.leadingCoeff * D.leadingCoeff ^ 2 := by
          rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
        have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
          rw [natDegree_pow]; omega
        have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) =
            C.leadingCoeff ^ 3 := by
          rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
        simp only [lambdaCubicSigmaFaceCD610, lambdaCubicSigmaInnerCD610,
          coeff_add, coeff_sub, coeff_smul, smul_eq_mul] at hzLam
        rw [hcf_AD2, hcf_C3] at hzLam
        have hden : (-(5 / 81 : k)) ≠ 0 :=
          neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
        have : (-(5 / 81 : k)) *
            (3 * A.leadingCoeff * D.leadingCoeff ^ 2 +
              C.leadingCoeff ^ 3) = 0 := by
          convert hzLam using 1
          ring
        rcases mul_eq_zero.mp this with h | h
        · exact (hden h).elim
        · exact h
      -- κ tie: (10/9) D E + (4/9)α C D at c+d
      have hltKap :
          (degreeZeroKappaCubic610 0 alpha 0 0 epsilon 0 eta 0
              A 0 C D E).natDegree < C.natDegree + D.natDegree := by
        rw [hkap]
        omega
      have hzKap : (degreeZeroKappaCubic610 0 alpha 0 0 epsilon 0 eta 0
            A 0 C D E).coeff (C.natDegree + D.natDegree) = 0 :=
        coeff_eq_zero_of_natDegree_lt hltKap
      rw [degreeZeroKappaCubic610_eq_chamber alpha epsilon eta A C D E] at hzKap
      simp only [kappaChamberCD610, coeff_add, coeff_smul, smul_eq_mul] at hzKap
      have hdeg_DE : (D * E).natDegree = C.natDegree + D.natDegree := by
        rw [natDegree_mul hDne hEne, heq, add_comm]
      have hcf_DE : (D * E).coeff (C.natDegree + D.natDegree) =
          D.leadingCoeff * E.leadingCoeff := by
        rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
      have hdeg_CD : (C * D).natDegree = C.natDegree + D.natDegree :=
        natDegree_mul hCne hDne
      have hcf_CD : (C * D).coeff (C.natDegree + D.natDegree) =
          C.leadingCoeff * D.leadingCoeff := by
        rw [← hdeg_CD, coeff_natDegree, leadingCoeff_mul]
      have hmiss_D : D.coeff (C.natDegree + D.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        omega
      simp only [hcf_DE, hcf_CD, hmiss_D, mul_zero, add_zero] at hzKap
      -- (10/9) D.lc E.lc + (4/9)α C.lc D.lc = 0
      have hrel : E.leadingCoeff =
          -((2 / 5 : k) * alpha * C.leadingCoeff) := by
        have hden : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
        have : (10 / 9 : k) * D.leadingCoeff * E.leadingCoeff +
            (4 / 9 * alpha : k) * C.leadingCoeff * D.leadingCoeff = 0 := by
          convert hzKap using 1
          ring
        have hfac :
            D.leadingCoeff *
              ((10 / 9 : k) * E.leadingCoeff +
                (4 / 9 * alpha : k) * C.leadingCoeff) = 0 := by
          convert this using 1
          ring
        have hlin :
            (10 / 9 : k) * E.leadingCoeff +
              (4 / 9 * alpha : k) * C.leadingCoeff = 0 := by
          rcases mul_eq_zero.mp hfac with h | h
          · exact (hden h).elim
          · exact h
        have hadd : E.leadingCoeff +
            ((2 / 5 : k) * alpha * C.leadingCoeff) = 0 := by
          linear_combination (9 / 10 : k) * hlin
        exact eq_neg_of_add_eq_zero_left hadd
      -- ο at 3c = a+2d
      have hzOmi : (degreeZeroOmicronCubic610 0 alpha 0 0 epsilon 0 eta 0
            A 0 C D E).coeff (A.natDegree + 2 * D.natDegree) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [homi]; exact hfaceDeg)
      rw [degreeZeroOmicronCubic610_eq_chamber] at hzOmi
      simp only [omicronChamberCD610, coeff_add, coeff_smul, smul_eq_mul] at hzOmi
      have hdeg_C2E : (C ^ 2 * E).natDegree =
          A.natDegree + 2 * D.natDegree := by
        have hC2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hCne
        rw [natDegree_mul hC2 hEne, natDegree_pow, heq]
        omega
      have hcf_C2E : (C ^ 2 * E).coeff (A.natDegree + 2 * D.natDegree) =
          C.leadingCoeff ^ 2 * E.leadingCoeff := by
        rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
      have hdeg_AD2 : (A * D ^ 2).natDegree =
          A.natDegree + 2 * D.natDegree := by
        rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
      have hcf_AD2 : (A * D ^ 2).coeff (A.natDegree + 2 * D.natDegree) =
          A.leadingCoeff * D.leadingCoeff ^ 2 := by
        rw [← hdeg_AD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
      have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
        rw [natDegree_pow]; omega
      have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) =
          C.leadingCoeff ^ 3 := by
        rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
      have hmiss_CD2 : (C * D ^ 2).coeff (A.natDegree + 2 * D.natDegree) =
          0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have : (C * D ^ 2).natDegree = C.natDegree + 2 * D.natDegree := by
          rw [natDegree_mul hCne (pow_ne_zero 2 hDne), natDegree_pow]
        rw [this]
        omega
      have hmiss_E2 : (E ^ 2).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_pow, heq]
        omega
      have hmiss_C2 : (C ^ 2).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_pow]; omega
      have hmiss_E : E.coeff (A.natDegree + 2 * D.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [heq]; omega
      simp only [hcf_C2E, hcf_AD2, hcf_C3, hmiss_CD2, hmiss_E2, hmiss_C2,
        hmiss_E, mul_zero, add_zero] at hzOmi
      -- ο coeff = (-5/27) c² e + (-2/27 α) a d² + (-4/81 α) c³ = 0
      have hzOmi' :
          (-(5 / 27 : k)) * C.leadingCoeff ^ 2 * E.leadingCoeff
            + (-(2 / 27 * alpha : k)) * A.leadingCoeff * D.leadingCoeff ^ 2
            + (-(4 / 81 * alpha : k)) * C.leadingCoeff ^ 3 = 0 := by
        convert hzOmi using 1
        ring
      have hid := cubicChamber_ec_scalar_identity A.leadingCoeff
          C.leadingCoeff D.leadingCoeff alpha E.leadingCoeff hrel
      have hinner0 : 3 * A.leadingCoeff * D.leadingCoeff ^ 2 +
          C.leadingCoeff ^ 3 = 0 := by
        simpa [lambdaCubicSigmaInnerCD610] using hinner
      have hfin :
          ((4 / 81 : k) * alpha) * C.leadingCoeff ^ 3 = 0 := by
        have := hzOmi'
        rw [hid, hinner0, mul_zero, add_zero] at this
        exact this
      have hden : (4 / 81 : k) ≠ 0 :=
        div_ne_zero (by norm_num) (by norm_num)
      rcases mul_eq_zero.mp hfin with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact (hden h).elim
        · exact halpha h
      · exact leadingCoeff_ne_zero.mpr hCne
          ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp h)

end CubicLoadCDChamber610

end Max11DegreeRoutes
