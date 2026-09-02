import Sol68ScaleTwoAlignedNonsquareTerminalMixedRootsI3Scratch

/-! # Source transport of constant I3 and mixed-root deletion -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section TerminalI3Source68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance terminalI3SourceCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- Exact source transport of the constant `I₃`, with all five depressed
coordinates cleared to weights `2,3,4,5,6`. -/
theorem NonsquareAlignedSourceCurveData68.terminalI3_cleared_source_identity
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3)
    {g r t : k[X]} (hg : p.coeff 5 = H * g) (hr : g = H * r)
    (ht : p.coeff 4 = H * t) :
    ∃ i3 : k,
      terminalGReducedI3ScaledPolynomial68 H
        (cubicANumerator68 t r)
        (cubicBNumerator68 (p.coeff 3) t r)
        (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
        (cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r)
        (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r)
        S.gamma S.epsilon = C i3 * H ^ 5 := by
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
  let AF := quadraticCoefficientMap46 H (cubicANumerator68 t r)
  let BF := quadraticCoefficientMap46 H
    (cubicBNumerator68 (p.coeff 3) t r)
  let CF := quadraticCoefficientMap46 H
    (cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r)
  let DF := quadraticCoefficientMap46 H
    (cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r)
  let EF := quadraticCoefficientMap46 H
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
  have hcoeffC (c : k) : quadraticCoefficientMap46 H (C c) =
      algebraMap k F68 c := by
    rw [quadraticCoefficientMap46_eq_algebraMap]
    simpa using (IsScalarTower.algebraMap_apply k k[X] F68 c).symm
  have hAF : h ^ 2 * S.A = AF := by
    dsimp only [AF, cubicANumerator68]
    simp only [map_sub, map_mul, map_pow, hcoeffC]
    simpa only [map_div₀, map_ofNat, map_one] using hAc
  have hBF : h ^ 3 * S.B = BF := by
    dsimp only [BF, cubicBNumerator68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
    simpa only [map_div₀, map_ofNat, map_one] using hBc
  have hCF : h ^ 4 * S.C0 = CF := by
    dsimp only [CF, cubicCNumerator68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
    rw [← hroot]
    simpa only [map_div₀, map_ofNat, map_one] using hCc
  have hDF : h ^ 5 * S.D = DF := by
    dsimp only [DF, cubicDNumerator68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
    rw [← hroot]
    convert hDc using 1 <;>
      simp only [map_div₀, map_one, map_ofNat] <;> ring
  have hEF : h ^ 6 * S.E = EF := by
    dsimp only [EF, cubicENumerator68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
    rw [← hroot]
    convert hEc using 1 <;>
      simp only [map_div₀, map_one, map_ofNat] <;> ring
  obtain ⟨i3, hi3⟩ := (S.residualPacket).2.1
  refine ⟨i3, ?_⟩
  have hscaled := terminalI3_scaled_of_coordinates_68
    h (quadraticCoefficientMap46 H H) S.A S.B S.C0 S.D S.E
    AF BF CF DF EF (algebraMap k F68 S.gamma)
    (algebraMap k F68 S.epsilon) (algebraMap k F68 i3)
    hroot hAF hBF hCF hDF hEF hi3
  apply hphi
  dsimp only [AF, BF, CF, DF, EF] at hscaled ⊢
  simp only [terminalGReducedI3ScaledPolynomial68,
    terminalGReducedI3Scaled68, map_add, map_sub, map_neg, map_mul, map_pow,
    map_div₀, map_ofNat, map_zero, hcoeffC] at hscaled ⊢
  exact hscaled

end TerminalI3Source68

section TerminalI3RigidBranchSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing deletion of the rigid local component.  The hypotheses
`hu,hquad` are precisely the already-proved output of the mixed-root
I4/terminal packet; no new local assumption is introduced. -/
theorem NonsquareAlignedSourceCurveData68.terminalRZero_nonzeroB_impossible_I3
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3)
    {g r t X Yd : k[X]}
    (hg : p.coeff 5 = H * g) (hgr : g = H * r)
    (ht : p.coeff 4 = H * t)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X)
    (hY : (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd)
    (a : k) (ha : H.eval a = 0) (hr0 : r.eval a = 0)
    (hy : Yd.eval a ≠ 0) (hu : (p.coeff 2).eval a ≠ 0)
    (hquad : (Yd.eval a) ^ 2 + 1458 * X.eval a * (p.coeff 2).eval a = 0) :
    False := by
  obtain ⟨i3, hI3source⟩ :=
    S.terminalI3_cleared_source_identity (H := H) hp hp6 hg hgr ht
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
  rw [hA, hB, hC, hD, hE] at hI3source
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hh : H.derivative.eval a ≠ 0 :=
    nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  exact terminalRZero_impossible_of_reduced_I3_68
    H r X Yd (p.coeff 0) (p.coeff 1) (p.coeff 2)
    S.gamma S.epsilon i3 a ha hr0 hh hy hu hquad hI3source

end TerminalI3RigidBranchSource68

end Max11DegreeRoutes
