import Sol410ScaleTwoAlignedNonsquareGDivisorEliminatedScratch

/-! # Eleventh-row descent on the complementary `(4,10)` divisor -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- The new companion wall after writing the old terminal factor as `H l`. -/
def alignedEleventhComplementWall410
    (p0 g f l : K[X]) (κ3 κ7 : K) : K[X] :=
  (60 : K[X]) * f ^ 4 + (240 : K[X]) * f ^ 2 * g * l +
    (24 : K[X]) * Polynomial.C κ3 * f ^ 2 -
    (7680 : K[X]) * p0 * f ^ 2 +
    (320 : K[X]) * g ^ 2 * l ^ 2 +
    (48 : K[X]) * Polynomial.C κ3 * g * l -
    (15360 : K[X]) * p0 * g * l -
    (1536 : K[X]) * Polynomial.C κ3 * p0 - Polynomial.C κ7 +
    (245760 : K[X]) * p0 ^ 2

set_option maxHeartbeats 8000000 in
/-- Exact cancellation after substituting
`4p₂ = g²-Hf` and `8p₁ = Hl-gf` into the eleventh block. -/
theorem alignedNonsquareEleventh_complementSolved_410
    (H p0 p1 p2 g f l : K[X]) (κ3 κ7 : K)
    (hH : H ≠ 0)
    (hgf : g ^ 2 - (4 : K[X]) * p2 = H * f)
    (hL : g * f + (8 : K[X]) * p1 = H * l)
    (hblk :
      (1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 -
            (104 : K[X]) * p2 * g ^ 2 + (48 : K[X]) * p2 ^ 2) * f ^ 3 +
          (30720 : K[X]) * p1 *
            ((33 : K[X]) * g ^ 4 - (72 : K[X]) * p2 * g ^ 2 +
              (16 : K[X]) * p2 ^ 2) * f ^ 2 +
          (3932160 : K[X]) * p1 ^ 2 * g ^ 3 * f +
          (5242880 : K[X]) * p1 ^ 3 *
            ((3 : K[X]) * g ^ 2 - (4 : K[X]) * p2) =
        H * (((((983040 : K[X]) * p0 -
              Polynomial.C κ3 * (3072 : K[X])) * g ^ 2 -
              (2949120 : K[X]) * p1 ^ 2) * g * f ^ 2) +
          (((15728640 : K[X]) * p0 -
              Polynomial.C κ3 * (49152 : K[X])) * p1 * g ^ 2 * f) +
          (((62914560 : K[X]) * p0 -
              Polynomial.C κ3 * (196608 : K[X])) * g * p1 ^ 2) +
          H * ((((491520 : K[X]) * p0 -
                Polynomial.C κ3 * (1536 : K[X])) * g * f ^ 3) +
            (((3932160 : K[X]) * p0 -
                Polynomial.C κ3 * (12288 : K[X])) * p1 * f ^ 2) +
            (Polynomial.C κ3 * ((1536 : K[X]) * p0) +
                Polynomial.C κ7 - (245760 : K[X]) * p0 ^ 2) *
              ((64 : K[X]) * g * f + (512 : K[X]) * p1)))) :
    (64 : K[X]) * l * alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
      (10240 : K[X]) * H * f * l ^ 3 = 0 := by
  let U : K[X] := (8 : K[X]) * p1
  let V : K[X] := (4 : K[X]) * p2
  have hscaled :
      (1280 : K[X]) * g * ((39 : K[X]) * g ^ 4 -
            (26 : K[X]) * V * g ^ 2 + (3 : K[X]) * V ^ 2) * f ^ 3 +
          (3840 : K[X]) * U * ((33 : K[X]) * g ^ 4 -
            (18 : K[X]) * V * g ^ 2 + V ^ 2) * f ^ 2 +
          (61440 : K[X]) * U ^ 2 * g ^ 3 * f +
          (10240 : K[X]) * U ^ 3 * ((3 : K[X]) * g ^ 2 - V) =
        H * (((((983040 : K[X]) * p0 -
              Polynomial.C κ3 * (3072 : K[X])) * g ^ 2 -
              (46080 : K[X]) * U ^ 2) * g * f ^ 2) +
          (((1966080 : K[X]) * p0 -
              Polynomial.C κ3 * (6144 : K[X])) * U * g ^ 2 * f) +
          (((983040 : K[X]) * p0 -
              Polynomial.C κ3 * (3072 : K[X])) * g * U ^ 2) +
          H * ((((491520 : K[X]) * p0 -
                Polynomial.C κ3 * (1536 : K[X])) * g * f ^ 3) +
            (((491520 : K[X]) * p0 -
                Polynomial.C κ3 * (1536 : K[X])) * U * f ^ 2) +
            (64 : K[X]) *
              (Polynomial.C κ3 * ((1536 : K[X]) * p0) +
                Polynomial.C κ7 - (245760 : K[X]) * p0 ^ 2) *
              (g * f + U))) := by
    dsimp only [U, V]
    linear_combination hblk
  have hU : U = H * l - g * f := by
    dsimp only [U]
    linear_combination hL
  have hV : V = g ^ 2 - H * f := by
    dsimp only [V]
    linear_combination -hgf
  rw [hU, hV] at hscaled
  have hfactored :
      H ^ 3 * ((64 : K[X]) * l *
          alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
        (10240 : K[X]) * H * f * l ^ 3) = 0 := by
    simp only [alignedEleventhComplementWall410]
    linear_combination hscaled
  exact (mul_eq_zero.mp hfactored).resolve_left (pow_ne_zero 3 hH)

/-- The cancelled row gives a new two-factor product at each root of `H`. -/
theorem alignedNonsquareEleventh_complementRootProduct_410
    (H p0 g f l : K[X]) (κ3 κ7 x : K)
    (hrow :
      (64 : K[X]) * l * alignedEleventhComplementWall410 p0 g f l κ3 κ7 +
        (10240 : K[X]) * H * f * l ^ 3 = 0)
    (hx : H.eval x = 0) :
    l.eval x *
      (alignedEleventhComplementWall410 p0 g f l κ3 κ7).eval x = 0 := by
  have hev := congrArg (fun w : K[X] => w.eval x) hrow
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat] at hev
  rw [hx] at hev
  norm_num at hev
  exact mul_eq_zero.mpr hev

#print axioms alignedNonsquareEleventh_complementSolved_410
#print axioms alignedNonsquareEleventh_complementRootProduct_410

end Max11DegreeRoutes
