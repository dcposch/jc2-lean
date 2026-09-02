import Sol68ScaleTwoAlignedNonsquareTerminalFactorsSourceScratch

/-! # Derivative-order clearing below the terminal cubic-defect face -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

section TerminalDerivativeClearing68

variable {F : Type*} [Field F]

theorem derivation_div_cube_68
    (D : Derivation ℤ F F) (H E : F) (hH : H ≠ 0) :
    D (E / H ^ 3) = (H * D E - 3 * D H * E) / H ^ 4 := by
  rw [Derivation.leibniz_div, Derivation.leibniz_pow]
  simp only [Nat.cast_ofNat, nsmul_eq_mul, smul_eq_mul]
  field_simp [hH]
  ring

theorem derivation_div_fourth_68
    (D : Derivation ℤ F F) (H V : F) (hH : H ≠ 0) :
    D (V / H ^ 4) = (H * D V - 4 * D H * V) / H ^ 5 := by
  rw [Derivation.leibniz_div, Derivation.leibniz_pow]
  simp only [Nat.cast_ofNat, nsmul_eq_mul, smul_eq_mul]
  field_simp [hH]
  ring

/-- Clearing the additional four and five powers of the quadratic core
created by differentiating `E/H^3` and `V/H^4`. -/
theorem terminalLastRow_clear_derivativeOrders_68
    (D : Derivation ℤ F F) (H b w d EN VN c j : F) (hH : H ≠ 0)
    (hrow :
      b * (w / H) * D (EN / H ^ 3) -
          (d / H) * (D (VN / H ^ 4) - (c / H) * D (EN / H ^ 3)) = j) :
    H * b * w * (H * D EN - 3 * D H * EN) -
        d * (H * D VN - 4 * D H * VN - c * (H * D EN - 3 * D H * EN)) =
      j * H ^ 6 := by
  rw [derivation_div_cube_68 D H EN hH,
    derivation_div_fourth_68 D H VN hH] at hrow
  field_simp [hH] at hrow ⊢
  linear_combination hrow

/-- Instance-insensitive form of the same clearing, taking the two exact
derivative quotient formulas as inputs. -/
theorem terminalLastRow_clear_derivativeValues_68
    (H b w d EN VN c j eDer vDer dH dEN dVN : F) (hH : H ≠ 0)
    (heDer : eDer = (H * dEN - 3 * dH * EN) / H ^ 4)
    (hvDer : vDer = (H * dVN - 4 * dH * VN) / H ^ 5)
    (hrow : b * (w / H) * eDer -
      (d / H) * (vDer - (c / H) * eDer) = j) :
    H * b * w * (H * dEN - 3 * dH * EN) -
        d * (H * dVN - 4 * dH * VN - c * (H * dEN - 3 * dH * EN)) =
      j * H ^ 6 := by
  rw [heDer, hvDer] at hrow
  field_simp [hH] at hrow ⊢
  linear_combination hrow

end TerminalDerivativeClearing68

section TerminalDerivativePolynomials68

variable {k : Type*} [Field k] [CharZero k]

def terminalCShiftNumerator68 (H A0 : k[X]) (alpha : k) : k[X] :=
  C (4 / 9 : k) * A0 + C alpha * H

def terminalVNumerator68
    (H A0 b1 C0 d1 E0 : k[X]) (alpha gamma epsilon eta : k) : k[X] :=
  C (2 / 9 : k) * C0 ^ 2 + C (4 / 9 : k) * H ^ 2 * b1 * d1 +
    C (4 / 9 : k) * A0 * E0 - C (4 / 27 : k) * H ^ 2 * A0 * b1 ^ 2 -
    C (4 / 27 : k) * A0 ^ 2 * C0 + C (5 / 243 : k) * A0 ^ 4 +
    C alpha * H * E0 +
    C gamma * H ^ 2 * (C (2 / 3 : k) * C0 - C (1 / 9 : k) * A0 ^ 2) +
    C (1 / 3 : k) * C epsilon * H ^ 3 * A0 + C eta * H ^ 4

def terminalEDerivativeNumerator68 (H E0 : k[X]) : k[X] :=
  H * E0.derivative - C (3 : k) * H.derivative * E0

def terminalVDerivativeNumerator68 (H V0 : k[X]) : k[X] :=
  H * V0.derivative - C (4 : k) * H.derivative * V0

def terminalTransverseDerivativeNumerator68
    (H E0 V0 c0 : k[X]) : k[X] :=
  terminalVDerivativeNumerator68 H V0 -
    c0 * terminalEDerivativeNumerator68 H E0

/-- Pure polynomial consequence of the six-times-cleared last row. -/
theorem terminalLastRow_root_transverse_zero_68
    (H b1 w1 d1 eDot kDot : k[X]) (j a : k)
    (hclear : H * b1 * w1 * eDot - d1 * kDot = C j * H ^ 6)
    (ha : H.eval a = 0) :
    d1.eval a * kDot.eval a = 0 := by
  have h := congrArg (fun f : k[X] => f.eval a) hclear
  simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat, eval_zero,
    ha, zero_mul, zero_pow, OfNat.zero_ne_ofNat] at h
  linear_combination -h

/-- On either refined transverse component, the derivative clearing reduces
the residual further to `b=0` or vanishing of the transverse derivative
numerator. -/
theorem terminalRefinedBranch_derivative_residual_68
    (r b d kDot : k) (hr : r ≠ 0)
    (hdzero : d * kDot = 0)
    (hd : d = -(5 / 36 : k) * r ^ 2 * b ∨
      d = -(1 / 36 : k) * r ^ 2 * b) :
    b = 0 ∨ kDot = 0 := by
  rcases hd with hd | hd
  · rw [hd] at hdzero
    rcases mul_eq_zero.mp hdzero with hcoef | hk
    · left
      rcases mul_eq_zero.mp hcoef with hrzero | hb
      · exact ((mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)) hrzero).elim
      · exact hb
    · exact Or.inr hk
  · rw [hd] at hdzero
    rcases mul_eq_zero.mp hdzero with hcoef | hk
    · left
      rcases mul_eq_zero.mp hcoef with hrzero | hb
      · exact ((mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)) hrzero).elim
      · exact hb
    · exact Or.inr hk

end TerminalDerivativePolynomials68

section TerminalDerivativeSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance terminalDerivativeCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- The actual source last row, with all differentiated terminal denominators
cleared.  This is the order-sensitive replacement for evaluating the merely
`H`-cleared homogeneous row at a root. -/
theorem NonsquareAlignedSourceCurveData68.terminalDerivativeClearIdentity
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3)
    {g r t b1 d1 w1 : k[X]}
    (hg : p.coeff 5 = H * g) (hr : g = H * r)
    (ht : p.coeff 4 = H * t)
    (hb1 : cubicBNumerator68 (p.coeff 3) t r = H * b1)
    (hd1 : cubicDNumerator68 H (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r = H * d1)
    (hw1 : cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma =
      H * w1) :
    let A0 := cubicANumerator68 t r
    let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
    let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r
    let c0 := terminalCShiftNumerator68 H A0 S.alpha
    let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
      S.epsilon S.eta
    let eDot := terminalEDerivativeNumerator68 H E0
    let kDot := terminalTransverseDerivativeNumerator68 H E0 V0 c0
    H * b1 * w1 * eDot - d1 * kDot = C j * H ^ 6 := by
  dsimp only
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let rF : F68 := quadraticCoefficientMap46 H r
  let tF : F68 := quadraticCoefficientMap46 H t
  let a3 : F68 := quadraticCoefficientMap46 H (p.coeff 3)
  let a2 : F68 := quadraticCoefficientMap46 H (p.coeff 2)
  let a1 : F68 := quadraticCoefficientMap46 H (p.coeff 1)
  let a0 : F68 := quadraticCoefficientMap46 H (p.coeff 0)
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let c0 := terminalCShiftNumerator68 H A0 S.alpha
  let V0 := terminalVNumerator68 H A0 b1 C0 d1 E0 S.alpha S.gamma
    S.epsilon S.eta
  have hroot : h ^ 2 = quadraticCoefficientMap46 H H :=
    alignedQuadraticRoot_sq46 H
  have hh : h ≠ 0 := S.scale_ne_zero
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hcoeffC (c : k) : quadraticCoefficientMap46 H (C c) =
      algebraMap k F68 c := by
    rw [quadraticCoefficientMap46_eq_algebraMap]
    simpa using (IsScalarTower.algebraMap_apply k k[X] F68 c).symm
  have htop : quadraticCoefficientMap46 H (p.coeff 6) = h ^ 6 := by
    rw [hp6, map_pow, ← hroot]
    ring
  have hpRaw := sourceToQuadratic68_eq_rawSextic H p h hp htop
  have hsextic := S.sextic_eq
  rw [hpRaw] at hsextic
  let a5 : F68 := quadraticCoefficientMap46 H (p.coeff 5)
  let a4 : F68 := quadraticCoefficientMap46 H (p.coeff 4)
  have hcoeff5 := congrArg (fun f : F68[X] => f.coeff 5) hsextic
  have hcenter : S.r = sexticDepressionR68 h a5 := by
    apply r_eq_sexticDepression_of_coeff_five h S.r a5 a4 a3 a2 a1 a0 hh
    simpa only [depressedSextic68_coeff_five] using hcoeff5
  have hpDep := affineDepress_rawSextic68 h S.r a5 a4 a3 a2 a1 a0 hh hcenter
  have hsame := hpDep.symm.trans hsextic
  have hA : depressedA68 h S.r a5 a4 = S.A := by
    have hc := congrArg (fun f : F68[X] => f.coeff 4) hsame
    simpa [depressedSextic68] using hc
  have hB : depressedB68 h S.r a5 a4 a3 = S.B := by
    have hc := congrArg (fun f : F68[X] => f.coeff 3) hsame
    simpa [depressedSextic68] using hc
  have hC : depressedC68 h S.r a5 a4 a3 a2 = S.C0 := by
    have hc := congrArg (fun f : F68[X] => f.coeff 2) hsame
    simpa [depressedSextic68] using hc
  have hD : depressedD68 h S.r a5 a4 a3 a2 a1 = S.D := by
    have hc := congrArg (fun f : F68[X] => f.coeff 1) hsame
    simpa [depressedSextic68] using hc
  have hE : depressedE68 h S.r a5 a4 a3 a2 a1 a0 = S.E := by
    have hc := congrArg (fun f : F68[X] => f.coeff 0) hsame
    simpa [depressedSextic68] using hc
  have ha5 : a5 = h ^ 4 * rF := by
    dsimp only [a5, rF]
    rw [hg, hr, map_mul, map_mul, ← hroot]
    ring
  have ha4 : a4 = h ^ 2 * tF := by
    dsimp only [a4, tF]
    rw [ht, map_mul, ← hroot]
  have hcenter' : S.r = rF / (6 * h) := by
    rw [hcenter, sexticDepressionR68, ha5]
    field_simp [hh]
  rw [ha5, ha4] at hA hB hC hD hE
  obtain ⟨hAc, hBc, hCc, hDc, hEc⟩ :=
    cubicDepressedCoordinates_cleared_68 h S.r rF tF a3 a2 a1 a0 hh hcenter'
  rw [hA] at hAc
  rw [hB] at hBc
  rw [hC] at hCc
  rw [hD] at hDc
  rw [hE] at hEc
  dsimp only [a3, a2, a1, a0, tF, rF, A0, C0, E0,
    cubicANumerator68, cubicCNumerator68, cubicENumerator68] at hAc hBc hCc hDc hEc
  have hBc1 : h ^ 3 * S.B = quadraticCoefficientMap46 H (H * b1) := by
    rw [← hb1]
    simpa only [cubicBNumerator68, map_add, map_sub, map_mul, map_pow,
      hcoeffC, map_div₀, map_ofNat, map_one]
      using hBc
  have hDc1 : h ^ 5 * S.D = quadraticCoefficientMap46 H (H * d1) := by
    rw [← hd1]
    dsimp only [cubicDNumerator68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [← hroot]
    convert hDc using 1 <;> ring
  have hWc1 : h ^ 4 *
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) =
        quadraticCoefficientMap46 H (H * w1) := by
    rw [← hw1]
    calc
      h ^ 4 * alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) =
          (4 / 9 : F68) * (h ^ 4 * S.C0) -
            (4 / 27 : F68) * (h ^ 2 * S.A) ^ 2 +
            (2 / 3 : F68) * algebraMap k F68 S.gamma * (h ^ 2) ^ 2 := by
        simp only [alignedLastRowShiftW68]
        ring
      _ = quadraticCoefficientMap46 H
          (cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma) := by
        dsimp only [cubicWNumerator68, cubicANumerator68, cubicCNumerator68]
        simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
          map_ofNat, map_one]
        rw [← hroot, hAc, hCc]
  have hAmap : quadraticCoefficientMap46 H A0 = h ^ 2 * S.A := by
    dsimp only [A0, cubicANumerator68]
    simp only [map_sub, map_mul, map_pow, hcoeffC, map_div₀, map_ofNat,
      map_one]
    exact hAc.symm
  have hCmap : quadraticCoefficientMap46 H C0 = h ^ 4 * S.C0 := by
    dsimp only [C0, cubicCNumerator68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [← hroot]
    convert hCc.symm using 1 <;> ring
  have hEmap : quadraticCoefficientMap46 H E0 = h ^ 6 * S.E := by
    dsimp only [E0, cubicENumerator68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [← hroot]
    convert hEc.symm using 1 <;> ring
  have hBscaled : h * S.B = quadraticCoefficientMap46 H b1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh)
    calc
      h ^ 2 * (h * S.B) = h ^ 3 * S.B := by ring
      _ = quadraticCoefficientMap46 H (H * b1) := hBc1
      _ = h ^ 2 * quadraticCoefficientMap46 H b1 := by
        rw [map_mul, ← hroot]
  have hDscaled : h ^ 3 * S.D = quadraticCoefficientMap46 H d1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh)
    calc
      h ^ 2 * (h ^ 3 * S.D) = h ^ 5 * S.D := by ring
      _ = quadraticCoefficientMap46 H (H * d1) := hDc1
      _ = h ^ 2 * quadraticCoefficientMap46 H d1 := by
        rw [map_mul, ← hroot]
  have hVscaled : h ^ 8 *
      integratedV68 0 S.A S.B S.C0 S.D S.E
        (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
        (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
      quadraticCoefficientMap46 H V0 := by
    calc
      h ^ 8 * integratedV68 0 S.A S.B S.C0 S.D S.E
          (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
          (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
        (2 / 9 : F68) * (h ^ 4 * S.C0) ^ 2 +
          (4 / 9 : F68) * (h ^ 3 * S.B) * (h ^ 5 * S.D) +
          (4 / 9 : F68) * (h ^ 2 * S.A) * (h ^ 6 * S.E) -
          (4 / 27 : F68) * (h ^ 2 * S.A) * (h ^ 3 * S.B) ^ 2 -
          (4 / 27 : F68) * (h ^ 2 * S.A) ^ 2 * (h ^ 4 * S.C0) +
          (5 / 243 : F68) * (h ^ 2 * S.A) ^ 4 +
          algebraMap k F68 S.alpha * (h ^ 2) * (h ^ 6 * S.E) +
          algebraMap k F68 S.gamma * (h ^ 2) ^ 2 *
            ((2 / 3 : F68) * (h ^ 4 * S.C0) -
              (1 / 9 : F68) * (h ^ 2 * S.A) ^ 2) +
          (1 / 3 : F68) * algebraMap k F68 S.epsilon * (h ^ 2) ^ 3 *
            (h ^ 2 * S.A) + algebraMap k F68 S.eta * (h ^ 2) ^ 4 := by
        simp only [integratedV68]
        ring
      _ = quadraticCoefficientMap46 H V0 := by
        dsimp only [V0, terminalVNumerator68]
        simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
          map_ofNat, map_one]
        rw [hAmap, hCmap, hEmap, ← hBscaled, ← hDscaled, ← hroot]
        ring
  have hWscaled : h ^ 2 * alignedLastRowShiftW68 S.A S.C0
      (algebraMap k F68 S.gamma) = quadraticCoefficientMap46 H w1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh)
    calc
      h ^ 2 * (h ^ 2 * alignedLastRowShiftW68 S.A S.C0
          (algebraMap k F68 S.gamma)) =
          h ^ 4 * alignedLastRowShiftW68 S.A S.C0
            (algebraMap k F68 S.gamma) := by ring
      _ = quadraticCoefficientMap46 H (H * w1) := hWc1
      _ = h ^ 2 * quadraticCoefficientMap46 H w1 := by
        rw [map_mul, ← hroot]
  have hAq : S.A = quadraticCoefficientMap46 H A0 /
      quadraticCoefficientMap46 H H := by
    rw [← hroot]
    field_simp [hh]
    simpa only [mul_comm] using hAmap.symm
  have hBq : h * S.B = quadraticCoefficientMap46 H b1 := by
    exact hBscaled
  have hCq : S.C0 = quadraticCoefficientMap46 H C0 /
      quadraticCoefficientMap46 H (H ^ 2) := by
    rw [map_pow, ← hroot]
    field_simp [hh]
    simpa only [mul_comm] using hCmap.symm
  have hDq : h * S.D = quadraticCoefficientMap46 H d1 /
      quadraticCoefficientMap46 H H := by
    rw [← hroot]
    field_simp [hh]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hDscaled
  have hEq : S.E = quadraticCoefficientMap46 H E0 /
      quadraticCoefficientMap46 H (H ^ 3) := by
    rw [map_pow, ← hroot]
    field_simp [hh]
    simpa only [mul_comm] using hEmap.symm
  have hWq : alignedLastRowShiftW68 S.A S.C0
      (algebraMap k F68 S.gamma) = quadraticCoefficientMap46 H w1 /
        quadraticCoefficientMap46 H H := by
    rw [← hroot]
    field_simp [hh]
    simpa only [mul_comm] using hWscaled
  have hVq : integratedV68 0 S.A S.B S.C0 S.D S.E
      (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
      (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta) =
        quadraticCoefficientMap46 H V0 /
          quadraticCoefficientMap46 H (H ^ 4) := by
    rw [map_pow, ← hroot]
    field_simp [hh]
    simpa only [mul_comm] using hVscaled
  obtain ⟨mB, wR, eR, mD, aR, vR, hmB, hwR, heR, hmD, haR, hvR,
      hlast⟩ := S.lastRow_W_ratFunc (H := H)
  let ιp := algebraMap k[X] (RatFunc k)
  have hι : Function.Injective (algebraMap (RatFunc k) F68) :=
    (algebraMap (RatFunc k) F68).injective
  have htower (P : k[X]) : quadraticCoefficientMap46 H P =
      algebraMap (RatFunc k) F68 (ιp P) := by
    rw [quadraticCoefficientMap46_eq_algebraMap]
    exact IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68 P
  have hmBeq : mB = ιp b1 := by
    apply hι
    calc
      algebraMap (RatFunc k) F68 mB = h * S.B := hmB.symm
      _ = quadraticCoefficientMap46 H b1 := hBq
      _ = algebraMap (RatFunc k) F68 (ιp b1) := htower b1
  have hwReq : wR = ιp w1 / ιp H := by
    apply hι
    rw [map_div₀, ← htower, ← htower]
    exact hwR.symm.trans hWq
  have heReq : eR = ιp E0 / ιp (H ^ 3) := by
    apply hι
    rw [map_div₀, ← htower, ← htower]
    exact heR.symm.trans hEq
  have hmDeq : mD = ιp d1 / ιp H := by
    apply hι
    rw [map_div₀, ← htower, ← htower]
    exact hmD.symm.trans hDq
  have haReq : aR = ιp A0 / ιp H := by
    apply hι
    rw [map_div₀, ← htower, ← htower]
    exact haR.symm.trans hAq
  have hvReq : vR = ιp V0 / ιp (H ^ 4) := by
    apply hι
    rw [map_div₀, ← htower, ← htower]
    exact hvR.symm.trans hVq
  have hceq : (4 / 9 : RatFunc k) * aR +
        algebraMap k (RatFunc k) S.alpha = ιp c0 / ιp H := by
    rw [haReq]
    dsimp only [c0, terminalCShiftNumerator68, ιp]
    simp only [map_add, map_mul, RatFunc.algebraMap_C]
    simp only [← RatFunc.algebraMap_eq_C]
    have h49 : algebraMap k (RatFunc k) (4 / 9 : k) =
        (4 / 9 : RatFunc k) := by rw [map_div₀, map_ofNat, map_ofNat]
    rw [h49]
    have hHRF : algebraMap k[X] (RatFunc k) H ≠ 0 :=
      RatFunc.algebraMap_ne_zero hH
    field_simp [hHRF]
  rw [hmBeq, hwReq, heReq, hmDeq, hvReq, hceq] at hlast
  simp only [map_pow] at hlast
  have hmapH : ιp H ≠ 0 := RatFunc.algebraMap_ne_zero hH
  have hderE : Differential.deriv (ιp E0 / (ιp H) ^ 3) =
      (ιp H * Differential.deriv (ιp E0) -
        3 * Differential.deriv (ιp H) * ιp E0) / (ιp H) ^ 4 := by
    simp only [Derivation.leibniz_div, Derivation.leibniz_pow,
      Nat.cast_ofNat, nsmul_eq_mul, smul_eq_mul]
    field_simp [hmapH]
    ring
  have hderV : Differential.deriv (ιp V0 / (ιp H) ^ 4) =
      (ιp H * Differential.deriv (ιp V0) -
        4 * Differential.deriv (ιp H) * ιp V0) / (ιp H) ^ 5 := by
    simp only [Derivation.leibniz_div, Derivation.leibniz_pow,
      Nat.cast_ofNat, nsmul_eq_mul, smul_eq_mul]
    field_simp [hmapH]
    ring
  have hclear := terminalLastRow_clear_derivativeValues_68
    (ιp H) (ιp b1) (ιp w1) (ιp d1) (ιp E0) (ιp V0) (ιp c0)
      (algebraMap k (RatFunc k) j)
      (Differential.deriv (ιp E0 / (ιp H) ^ 3))
      (Differential.deriv (ιp V0 / (ιp H) ^ 4))
      (Differential.deriv (ιp H)) (Differential.deriv (ιp E0))
      (Differential.deriv (ιp V0)) hmapH hderE hderV hlast
  dsimp only [ιp] at hclear
  simp only [GCD369RatFuncDerivative, map_mul, map_sub, map_pow,
    RatFunc.algebraMap_C] at hclear
  apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
  dsimp only [terminalEDerivativeNumerator68,
    terminalTransverseDerivativeNumerator68, terminalVDerivativeNumerator68]
  simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_C]
  simp only [← RatFunc.algebraMap_eq_C]
  have h3 : algebraMap k (RatFunc k) (3 : k) = 3 := by rw [map_ofNat]
  have h4 : algebraMap k (RatFunc k) (4 : k) = 4 := by rw [map_ofNat]
  rw [h3, h4]
  simpa only [mul_assoc] using hclear

end TerminalDerivativeSource68

end Max11DegreeRoutes
