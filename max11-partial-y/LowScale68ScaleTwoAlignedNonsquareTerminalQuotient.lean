import LowScale68ScaleTwoAlignedNonsquareTerminalValuation

/-! # Source transport for the terminal I4 quotient face -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

section TerminalClearingAlgebra68

variable {F : Type*} [Field F] [CharZero F]

/-- Clearing the common depression denominators in the five sextic
coordinates. -/
theorem cubicDepressedCoordinates_cleared_68
    (h center r t a3 a2 a1 a0 : F) (hh : h ≠ 0)
    (hc : center = r / (6 * h)) :
    h ^ 2 * depressedA68 h center (h ^ 4 * r) (h ^ 2 * t) =
        t - (5 / 12 : F) * r ^ 2 ∧
    h ^ 3 * depressedB68 h center (h ^ 4 * r) (h ^ 2 * t) a3 =
        a3 - (2 / 3 : F) * t * r + (5 / 27 : F) * r ^ 3 ∧
    h ^ 4 * depressedC68 h center (h ^ 4 * r) (h ^ 2 * t) a3 a2 =
        h ^ 2 * a2 - (1 / 2 : F) * a3 * r +
          (1 / 6 : F) * t * r ^ 2 - (5 / 144 : F) * r ^ 4 ∧
    h ^ 5 * depressedD68 h center (h ^ 4 * r) (h ^ 2 * t) a3 a2 a1 =
        h ^ 4 * a1 - (1 / 3 : F) * h ^ 2 * a2 * r +
          (1 / 12 : F) * a3 * r ^ 2 - (1 / 54 : F) * t * r ^ 3 +
          (1 / 324 : F) * r ^ 5 ∧
    h ^ 6 * depressedE68 h center (h ^ 4 * r) (h ^ 2 * t) a3 a2 a1 a0 =
        h ^ 6 * a0 - (1 / 6 : F) * h ^ 4 * a1 * r +
          (1 / 36 : F) * h ^ 2 * a2 * r ^ 2 -
          (1 / 216 : F) * a3 * r ^ 3 + (1 / 1296 : F) * t * r ^ 4 -
          (5 / 46656 : F) * r ^ 6 := by
  subst center
  simp only [depressedA68, depressedB68, depressedC68, depressedD68,
    depressedE68]
  field_simp [hh]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Common-denominator clearing of `B Φ + 6 W D = 0`. -/
theorem terminalI4_cleared_of_scaled_68
    (h B D W Phi b d w phi : F)
    (hB : h ^ 3 * B = b) (hD : h ^ 5 * D = d)
    (hW : h ^ 4 * W = w) (hPhi : h ^ 6 * Phi = phi)
    (hI4 : B * Phi + 6 * W * D = 0) :
    b * phi + 6 * w * d = 0 := by
  calc
    b * phi + 6 * w * d =
        (h ^ 3 * B) * (h ^ 6 * Phi) +
          6 * (h ^ 4 * W) * (h ^ 5 * D) := by rw [hB, hD, hW, hPhi]
    _ = h ^ 9 * (B * Phi + 6 * W * D) := by ring
    _ = 0 := by rw [hI4, mul_zero]

end TerminalClearingAlgebra68

section TerminalI4Source68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance terminalQuotientCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- Exact source identity obtained by transporting and clearing terminal
`I₄`. -/
theorem NonsquareAlignedSourceCurveData68.terminalI4_cleared_source_identity
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3)
    {g r t : k[X]} (hg : p.coeff 5 = H * g) (hr : g = H * r)
    (ht : p.coeff 4 = H * t) :
    cubicBNumerator68 (p.coeff 3) t r *
          cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r S.gamma S.epsilon +
        (6 : k[X]) *
          cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma *
          cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r = 0 := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let rF : F68 := quadraticCoefficientMap46 H r
  let tF : F68 := quadraticCoefficientMap46 H t
  let a3 : F68 := quadraticCoefficientMap46 H (p.coeff 3)
  let a2 : F68 := quadraticCoefficientMap46 H (p.coeff 2)
  let a1 : F68 := quadraticCoefficientMap46 H (p.coeff 1)
  let a0 : F68 := quadraticCoefficientMap46 H (p.coeff 0)
  have hroot : h ^ 2 = quadraticCoefficientMap46 H H :=
    alignedQuadraticRoot_sq46 H
  have hh : h ≠ 0 := S.scale_ne_zero
  have hphi : Function.Injective (quadraticCoefficientMap46 H) :=
    (algebraMap (RatFunc k) F68).injective.comp
      (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hpTop : quadraticCoefficientMap46 H (p.coeff 6) = h ^ 6 := by
    rw [hp6, map_pow, ← hroot]
    ring
  have hpRaw := sourceToQuadratic68_eq_rawSextic H p h hp hpTop
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
    cubicDepressedCoordinates_cleared_68 h S.r rF tF a3 a2 a1 a0 hh
      hcenter'
  rw [hA] at hAc
  rw [hB] at hBc
  rw [hC] at hCc
  rw [hD] at hDc
  rw [hE] at hEc
  dsimp only [a3, a2, a1, a0, tF, rF] at hAc hBc hCc hDc hEc
  let bF := quadraticCoefficientMap46 H (cubicBNumerator68 (p.coeff 3) t r)
  let dF := quadraticCoefficientMap46 H
    (cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r)
  let wF := quadraticCoefficientMap46 H
    (cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma)
  let phiF := quadraticCoefficientMap46 H
    (cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r S.gamma S.epsilon)
  have hcoeffC (c : k) : quadraticCoefficientMap46 H (C c) =
      algebraMap k F68 c := by
    rw [quadraticCoefficientMap46_eq_algebraMap]
    simpa using (IsScalarTower.algebraMap_apply k k[X] F68 c).symm
  have hBc' : h ^ 3 * S.B = bF := by
    dsimp only [bF, cubicBNumerator68, a3, tF, rF]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [← hBc]
  have hDc' : h ^ 5 * S.D = dF := by
    dsimp only [dF, cubicDNumerator68, a3, a2, a1, tF, rF]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [← hroot]
    convert hDc using 1 <;> ring
  have hWc' : h ^ 4 *
      alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma) = wF := by
    calc
      h ^ 4 * alignedLastRowShiftW68 S.A S.C0
          (algebraMap k F68 S.gamma) =
          (4 / 9 : F68) * (h ^ 4 * S.C0) -
            (4 / 27 : F68) * (h ^ 2 * S.A) ^ 2 +
            (2 / 3 : F68) * (algebraMap k F68 S.gamma) * (h ^ 2) ^ 2 := by
        simp only [alignedLastRowShiftW68]
        ring
      _ = wF := by
        dsimp only [wF, cubicWNumerator68, cubicANumerator68,
          cubicCNumerator68, a3, a2, tF, rF]
        simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
          map_ofNat, map_one]
        rw [← hroot, hAc, hCc]
  have hPhic' : h ^ 6 *
      alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
        (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) = phiF := by
    calc
      h ^ 6 * alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
          (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon) =
          -(8 / 27 : F68) * (h ^ 3 * S.B) ^ 2 +
            (8 / 3 : F68) * (h ^ 6 * S.E) +
            2 * (algebraMap k F68 S.epsilon) * (h ^ 2) ^ 3 +
            (40 / 81 : F68) * (h ^ 2 * S.A) ^ 3 -
            (16 / 9 : F68) * (h ^ 2 * S.A) * (h ^ 4 * S.C0) -
            (4 / 3 : F68) * (algebraMap k F68 S.gamma) *
              (h ^ 2 * S.A) * (h ^ 2) ^ 2 := by
        simp only [alignedFirstIntegralFourOddPart68]
        ring
      _ = phiF := by
        dsimp only [phiF, cubicPhiNumerator68, cubicANumerator68,
          cubicBNumerator68, cubicCNumerator68, cubicENumerator68,
          a3, a2, a1, a0, tF, rF]
        simp only [map_add, map_sub, map_neg, map_mul, map_pow, hcoeffC,
          map_div₀, map_ofNat, map_one]
        rw [← hroot, hAc, hBc, hCc, hEc]
        ring
  have hclear := terminalI4_cleared_of_scaled_68 h S.B S.D
    (alignedLastRowShiftW68 S.A S.C0 (algebraMap k F68 S.gamma))
    (alignedFirstIntegralFourOddPart68 S.A S.B S.C0 S.E
      (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon))
    bF dF wF phiF hBc' hDc' hWc' hPhic' S.I4_factor
  apply hphi
  dsimp only [bF, dF, wF, phiF] at hclear ⊢
  simpa only [map_add, map_mul, map_zero, map_ofNat] using hclear

end TerminalI4Source68

end Max11DegreeRoutes
