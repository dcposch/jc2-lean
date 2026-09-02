import Sol68ScaleTwoAlignedNonsquareTerminalLowerOneBoundaryScratch

/-! # Exact source transport of the terminal lower row -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7000000

section TerminalLowerOneAbstractClearing68

variable {F : Type*} [Field F]

/-- Homogeneous denominator clearing of the independent lower row.  The
four derivative inputs already include the extra factors introduced by
differentiating odd and even powers of the quadratic scale. -/
theorem terminalLowerOneCleared_of_scaled_values_68
    (h C0 D T U dD dE dV dU c d t u dd de dv du : F)
    (hC : h ^ 4 * C0 = c) (hD : h ^ 3 * D = d)
    (hT : h ^ 6 * T = t) (hU : h ^ 5 * U = u)
    (hdD : 2 * h ^ 5 * dD = dd) (hdE : h ^ 8 * dE = de)
    (hdV : h ^ 10 * dV = dv) (hdU : 2 * h ^ 7 * dU = du)
    (hrow : U * dD + 2 * T * dE - 2 * C0 * dV - D * dU = 0) :
    h ^ 4 * u * dd + 4 * t * de - 4 * c * dv - h ^ 4 * d * du = 0 := by
  rw [← hC, ← hD, ← hT, ← hU, ← hdD, ← hdE, ← hdV, ← hdU]
  linear_combination 2 * h ^ 14 * hrow

end TerminalLowerOneAbstractClearing68

section TerminalLowerOneSourceTransport68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance terminalLowerOneTransportCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- The raw quadratic-field lower row clears exactly to the base-polynomial
identity used by the terminal local calculation. -/
theorem NonsquareAlignedSourceCurveData68.terminalLowerOneClearedTransport_source
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hp6 : p.coeff 6 = H ^ 3)
    {g r t X Yd : k[X]}
    (hg : p.coeff 5 = H * g) (hgr : g = H * r)
    (ht : p.coeff 4 = H * t)
    (hX : (3 : k[X]) * t - r ^ 2 = H * X)
    (hY : (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd) :
    S.TerminalLowerOneClearedTransport H r X Yd := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let M := quadraticCoefficientMap46 H
  let dQ := quadraticDerivation46 H
  let rF : F68 := M r
  let tF : F68 := M t
  let a3 : F68 := M (p.coeff 3)
  let a2 : F68 := M (p.coeff 2)
  let a1 : F68 := M (p.coeff 1)
  let a0 : F68 := M (p.coeff 0)
  have hroot : h ^ 2 = M H := alignedQuadraticRoot_sq46 H
  have hh : h ≠ 0 := S.scale_ne_zero
  have hM : Function.Injective M :=
    (algebraMap (RatFunc k) F68).injective.comp
      (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hcoeffC (c : k) : M (C c) = algebraMap k F68 c := by
    dsimp only [M]
    rw [quadraticCoefficientMap46_eq_algebraMap]
    simpa using (IsScalarTower.algebraMap_apply k k[X] F68 c).symm
  have hdmap (P : k[X]) : dQ (M P) = M P.derivative := by
    dsimp only [dQ, M]
    rw [quadraticDerivation46_apply, quadraticCoefficientMap46_eq_algebraMap,
      quadraticCoefficientMap46_eq_algebraMap]
    exact alignedQuadraticDeriv_polynomial46 H
      NonsquarePolynomial46.not_sq P
  have hpTop : M (p.coeff 6) = h ^ 6 := by
    rw [hp6, map_pow, ← hroot]
    ring
  have hpRaw := sourceToQuadratic68_eq_rawSextic H p h hp hpTop
  have hsextic := S.sextic_eq
  rw [hpRaw] at hsextic
  let a5 : F68 := M (p.coeff 5)
  let a4 : F68 := M (p.coeff 4)
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
    rw [hg, hgr, map_mul, map_mul, ← hroot]
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
  let A0 := terminalGReducedA68 H r X
  let b0 := terminalGReducedB68 r X Yd
  let C0 := terminalGReducedC68 H r X Yd (p.coeff 2)
  let D0 := terminalGReducedD68 H r X Yd (p.coeff 1) (p.coeff 2)
  let E0 := terminalGReducedE68 H r X Yd (p.coeff 0) (p.coeff 1)
    (p.coeff 2)
  obtain ⟨hAred, hBred, hCred, hDred, hEred⟩ :=
    cubicCoordinates_eq_terminalGReduced_68 H r t (p.coeff 3)
      (p.coeff 0) (p.coeff 1) (p.coeff 2) X Yd hX hY
  have hAmap : M A0 = h ^ 2 * S.A := by
    dsimp only [A0]
    rw [← hAred]
    dsimp only [cubicANumerator68]
    simp only [map_sub, map_mul, map_pow, hcoeffC]
    simpa only [map_div₀, map_ofNat, map_one] using hAc.symm
  have hBmap : M b0 = h * S.B := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh)
    calc
      h ^ 2 * M b0 = M (H * b0) := by rw [map_mul, ← hroot]
      _ = M (cubicBNumerator68 (p.coeff 3) t r) := by rw [hBred]
      _ = h ^ 3 * S.B := by
        dsimp only [cubicBNumerator68]
        simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
        simpa only [map_div₀, map_ofNat, map_one] using hBc.symm
      _ = h ^ 2 * (h * S.B) := by ring
  have hCmap : M C0 = h ^ 4 * S.C0 := by
    dsimp only [C0]
    rw [← hCred]
    dsimp only [cubicCNumerator68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
    rw [← hroot]
    convert hCc.symm using 1 <;>
      simp only [map_div₀, map_one, map_ofNat] <;> ring
  have hDmap : M D0 = h ^ 3 * S.D := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh)
    calc
      h ^ 2 * M D0 = M (H * D0) := by rw [map_mul, ← hroot]
      _ = M (cubicDNumerator68 H (p.coeff 1) (p.coeff 2)
          (p.coeff 3) t r) := by rw [hDred]
      _ = h ^ 5 * S.D := by
        dsimp only [cubicDNumerator68]
        simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
        rw [← hroot]
        convert hDc.symm using 1 <;>
          simp only [map_div₀, map_one, map_ofNat] <;> ring
      _ = h ^ 2 * (h ^ 3 * S.D) := by ring
  have hEmap : M E0 = h ^ 6 * S.E := by
    dsimp only [E0]
    rw [← hEred]
    dsimp only [cubicENumerator68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC]
    rw [← hroot]
    convert hEc.symm using 1 <;>
      simp only [map_div₀, map_one, map_ofNat] <;> ring
  let T0 := terminalLowerOneTNumerator68 H A0 b0 C0 E0
    S.alpha S.gamma S.epsilon
  let U0 := terminalLowerOneUNumerator68 H A0 b0 C0 D0 S.alpha S.gamma
  let V0 := terminalVNumerator68 H A0 b0 C0 D0 E0
    S.alpha S.gamma S.epsilon S.eta
  let T := integratedT68 0 S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma)
    (algebraMap k F68 S.epsilon)
  let U := integratedU68 0 S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0
  let V := integratedV68 0 S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
    (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta)
  have hTmap : M T0 = h ^ 6 * T := by
    dsimp only [T0, T, terminalLowerOneTNumerator68, integratedT68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [hAmap, hBmap, hCmap, hEmap, ← hroot]
    ring
  have hUmap : M U0 = h ^ 5 * U := by
    dsimp only [U0, U, terminalLowerOneUNumerator68, integratedU68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [hAmap, hBmap, hCmap, hDmap, ← hroot]
    ring
  have hVmap : M V0 = h ^ 8 * V := by
    dsimp only [V0, V, terminalVNumerator68, integratedV68]
    simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, map_div₀,
      map_ofNat, map_one]
    rw [hAmap, hBmap, hCmap, hDmap, hEmap, ← hroot]
    ring
  have hhder := congrArg dQ hroot
  simp only [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul] at hhder
  rw [hdmap H] at hhder
  have hhder' : M H.derivative = 2 * h * dQ h := by
    calc
      M H.derivative = 2 * (h * dQ h) := by
        simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat] using hhder.symm
      _ = 2 * h * dQ h := by ring
  have hDder := congrArg dQ hDmap
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hDder
  rw [hdmap D0] at hDder
  have hDder' : M D0.derivative =
      3 * h ^ 2 * dQ h * S.D + h ^ 3 * dQ S.D := by
    linear_combination hDder
  have hEder := congrArg dQ hEmap
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hEder
  rw [hdmap E0] at hEder
  have hEder' : M E0.derivative =
      6 * h ^ 5 * dQ h * S.E + h ^ 6 * dQ S.E := by
    linear_combination hEder
  have hUder := congrArg dQ hUmap
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hUder
  rw [hdmap U0] at hUder
  have hUder' : M U0.derivative =
      5 * h ^ 4 * dQ h * U + h ^ 5 * dQ U := by
    linear_combination hUder
  have hVder := congrArg dQ hVmap
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
    smul_eq_mul] at hVder
  rw [hdmap V0] at hVder
  have hVder' : M V0.derivative =
      8 * h ^ 7 * dQ h * V + h ^ 8 * dQ V := by
    linear_combination hVder
  let DD0 := terminalLowerOneDTwoDot68 H D0
  let ED0 := terminalEDerivativeNumerator68 H E0
  let VD0 := terminalVDerivativeNumerator68 H V0
  let UD0 := terminalLowerOneUTwoDot68 H U0
  have hDDmap : M DD0 = 2 * h ^ 5 * dQ S.D := by
    dsimp only [DD0, terminalLowerOneDTwoDot68]
    simp only [map_sub, map_mul, hcoeffC, map_ofNat]
    rw [← hroot, hDmap, hhder', hDder']
    ring
  have hEDmap : M ED0 = h ^ 8 * dQ S.E := by
    dsimp only [ED0, terminalEDerivativeNumerator68]
    simp only [map_sub, map_mul, hcoeffC, map_ofNat]
    rw [← hroot, hEmap, hhder', hEder']
    ring
  have hVDmap : M VD0 = h ^ 10 * dQ V := by
    dsimp only [VD0, terminalVDerivativeNumerator68]
    simp only [map_sub, map_mul, hcoeffC, map_ofNat]
    rw [← hroot, hVmap, hhder', hVder']
    ring
  have hUDmap : M UD0 = 2 * h ^ 7 * dQ U := by
    dsimp only [UD0, terminalLowerOneUTwoDot68]
    simp only [map_sub, map_mul, hcoeffC, map_ofNat]
    rw [← hroot, hUmap, hhder', hUder']
    ring
  have hraw := S.terminalLowerOneRawSourceIdentity (H := H)
  dsimp only at hraw
  have hclearF : M (terminalLowerOneCleared68 H A0 b0 C0 D0 E0
      S.alpha S.gamma S.epsilon S.eta) = 0 := by
    change M (H ^ 2 * U0 * DD0 + C 4 * T0 * ED0 -
      C 4 * C0 * VD0 - H ^ 2 * D0 * UD0) = 0
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, hcoeffC,
      map_ofNat]
    rw [← hroot]
    convert terminalLowerOneCleared_of_scaled_values_68
      h S.C0 S.D T U (dQ S.D) (dQ S.E) (dQ V) (dQ U)
      (M C0) (M D0) (M T0) (M U0)
      (M DD0) (M ED0) (M VD0) (M UD0)
      hCmap.symm hDmap.symm hTmap.symm hUmap.symm hDDmap.symm hEDmap.symm
      hVDmap.symm hUDmap.symm hraw using 1 <;> ring
  apply hM
  simpa only [A0, b0, C0, D0, E0, map_zero] using hclearF

/-- The terminal nonzero-`W` residual is eliminated by the independently
transported lower row.  The existing `W=0` sibling is preserved exactly. -/
theorem NonsquareAlignedSourceCurveData68.terminalLowerOneSourcePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (g r t X Yd b1 d1 w1 : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      cubicBNumerator68 (p.coeff 3) t r = H * b1 ∧
      cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r = H * d1 ∧
      cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma = H * w1 ∧
      (∀ a : k, H.eval a = 0 →
        b1.eval a = 0 ∧ d1.eval a = 0 ∧ w1.eval a = 0) ∧
      H ∣ w1 ∧ H ^ 2 ∣
        cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma := by
  obtain ⟨g, r, t, X, Yd, b1, d1, w1, hg, hgr, ht, hX, hY, hb1, hd1,
      hw1, hroots⟩ := S.terminalRZeroXZeroFifthRowSourcePacket (H := H)
    hdeg hp hq hp6 hq8 haligned hjac hj
  have htransport := S.terminalLowerOneClearedTransport_source (H := H)
    hp hp6 hg hgr ht hX hY
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hroot : ∀ a : k, H.eval a = 0 →
      b1.eval a = 0 ∧ d1.eval a = 0 ∧ w1.eval a = 0 := by
    intro a ha
    have hr := hroots a ha
    refine ⟨hr.1, hr.2.1, ?_⟩
    rcases hr.2.2 with hw | hres
    · exact hw
    · exact False.elim (S.terminalResidual_impossible_of_lowerOneTransport
        (H := H) htransport a ha hres.1 hres.2.1 hres.2.2.1
        (hsimple a ha) hres.2.2.2.1)
  have hdvd : H ∣ w1 :=
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hroot a ha).2.2)
  have hsq : H ^ 2 ∣
      cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma := by
    rw [hw1]
    simpa [pow_two] using mul_dvd_mul_left H hdvd
  exact ⟨g, r, t, X, Yd, b1, d1, w1, hg, hgr, ht, hX, hY, hb1, hd1,
    hw1, hroot, hdvd, hsq⟩

end TerminalLowerOneSourceTransport68

end Max11DegreeRoutes
