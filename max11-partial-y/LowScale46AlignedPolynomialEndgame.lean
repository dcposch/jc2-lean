import LowScale46AlignedFinitePoles

/-! # Polynomial endgame for the aligned `(4,6)` chart

This module transports the exact coefficient-curve equations and last-row
one-form to the shifted aligned variables `X=B+beta`, `V=U-8gamma/3` over a
polynomial base.  It then instantiates the aligned degree cones on the actual
polynomial equations.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ShiftedPolynomialEquations

variable {F : Type*} [Field F] [CharZero F]

/-- Polynomial version of the aligned `Phi(A)` curve function. -/
def alignedPhiPolynomial46
    (beta gamma delta k2 : F) (A : F[X]) : F[X] :=
  C ((4 / 3 : F) * delta) * A + C ((1 / 2 : F) * beta) * A ^ 2 -
    C ((4 / 3 : F) * (k2 + 2 * beta * gamma))

/-- Polynomial version of the aligned `R(A,X)` curve function. -/
def alignedRPolynomial46
    (beta gamma delta k1 : F) (A X : F[X]) : F[X] :=
  C (8 : F) * (A * X * (X - C beta)) -
    C ((32 / 3 : F) * delta) * (X - C beta) +
    C ((32 / 3 : F) * (k1 + (2 / 3 : F) * gamma ^ 2))

/-- Pullback of the aligned shifted one-form along a polynomial trajectory. -/
def alignedEtaPolynomial46
    (beta delta : F) (A X V : F[X]) : F[X] :=
  (C (3 / 16 : F) * ((X - C beta) * V) +
      C ((3 / 8 : F) * beta) * A ^ 2 +
      C ((1 / 2 : F) * delta) * A) * derivative A -
    C (3 / 4 : F) * (X * (X - C beta)) * derivative X +
    (C ((-3 / 16 : F) * beta) * A + C (-1 / 4 * delta)) * derivative V

/-- Exact shifted first coefficient-curve identity over `F[x]`. -/
theorem alignedPolynomial_curveTwo_identity
    (A B U : F[X]) (beta gamma delta k2 : F) :
    (B + C beta) * (U - C ((8 / 3 : F) * gamma)) -
        alignedPhiPolynomial46 beta gamma delta k2 A =
      C (-4 / 3 : F) *
        (coefficientCurveTwoPolynomial46 0 beta gamma delta A B U - C k2) := by
  simp only [alignedPhiPolynomial46, coefficientCurveTwoPolynomial46]
  simp only [map_mul, map_add, map_ofNat, map_zero]
  have hn4 : C (-4 / 3 : F) = -C (4 / 3 : F) := by
    rw [show (-4 / 3 : F) = -(4 / 3 : F) by ring, map_neg]
  have hn3 : C (-3 / 4 : F) = -C (3 / 4 : F) := by
    rw [show (-3 / 4 : F) = -(3 / 4 : F) by ring, map_neg]
  rw [hn4, hn3]
  have h43p : C (4 / 3 : F) * C (3 / 4 : F) = 1 := by
    rw [← Polynomial.C_mul]
    norm_num
  have h38p : C (4 / 3 : F) * C (3 / 8 : F) = C (1 / 2 : F) := by
    rw [← Polynomial.C_mul]
    norm_num
  have h8p : C (4 / 3 : F) * 2 = C (8 / 3 : F) := by
    change C (4 / 3 : F) * C (2 : F) = C (8 / 3 : F)
    rw [← Polynomial.C_mul]
    norm_num
  linear_combination
    -(B * U + C beta * U) * h43p +
      (B * C gamma + C beta * C gamma) * h8p +
      (C beta * A ^ 2) * h38p

/-- Exact shifted second coefficient-curve identity over `F[x]`. -/
theorem alignedPolynomial_curveOne_identity
    (A B U : F[X]) (beta gamma delta k1 : F) :
    (U - C ((8 / 3 : F) * gamma)) ^ 2 -
        alignedRPolynomial46 beta gamma delta k1 A (B + C beta) =
      C (32 / 3 : F) *
        (coefficientCurveOnePolynomial46 0 beta gamma delta A B U - C k1) := by
  simp only [alignedRPolynomial46, coefficientCurveOnePolynomial46]
  simp only [map_mul, map_add, map_ofNat, map_pow, map_zero]
  have hn12 : C (-1 / 2 : F) = -C (1 / 2 : F) := by
    rw [show (-1 / 2 : F) = -(1 / 2 : F) by ring, map_neg]
  have hn34 : C (-3 / 4 : F) = -C (3 / 4 : F) := by
    rw [show (-3 / 4 : F) = -(3 / 4 : F) by ring, map_neg]
  rw [hn12, hn34]
  have hu2 : C (32 / 3 : F) * C (3 / 32 : F) = 1 := by
    rw [← Polynomial.C_mul]
    norm_num
  have hg : C (8 / 3 : F) ^ 2 =
      C (32 / 3 : F) * C (2 / 3 : F) := by
    norm_num [pow_two, ← Polynomial.C_mul]
  have hup : C (32 / 3 : F) * C (1 / 2 : F) =
      C (8 / 3 : F) * 2 := by
    change C (32 / 3 : F) * C (1 / 2 : F) =
      C (8 / 3 : F) * C (2 : F)
    rw [← Polynomial.C_mul, ← Polynomial.C_mul]
    norm_num
  have h8p : C (32 / 3 : F) * C (3 / 4 : F) = 8 := by
    change C (32 / 3 : F) * C (3 / 4 : F) = C (8 : F)
    rw [← Polynomial.C_mul]
    norm_num
  linear_combination
    (U * C gamma) * hup - U ^ 2 * hu2 +
      (A * B * C beta + A * B ^ 2) * h8p
      + C gamma ^ 2 * hg

/-- Exact shift of the polynomial last-row pullback. -/
theorem alignedPolynomial_eta_identity
    (A B U : F[X]) (beta gamma delta : F) :
    alignedEtaPolynomial46 beta delta A (B + C beta)
        (U - C ((8 / 3 : F) * gamma)) =
      etaPolynomial46 0 beta gamma delta A B U := by
  simp only [alignedEtaPolynomial46, etaPolynomial46, etaAPolynomial46,
    etaBPolynomial46, etaUPolynomial46, derivative_add, derivative_sub,
    derivative_C, add_zero, sub_zero]
  simp only [map_mul, map_zero]
  have hn34 : C (-3 / 4 : F) = -C (3 / 4 : F) := by
    rw [show (-3 / 4 : F) = -(3 / 4 : F) by ring, map_neg]
  have hn12 : C (-1 / 2 : F) = -C (1 / 2 : F) := by
    rw [show (-1 / 2 : F) = -(1 / 2 : F) by ring, map_neg]
  rw [hn34, hn12]
  have h : C (3 / 16 : F) * C (8 / 3 : F) = C (1 / 2 : F) := by
    rw [← Polynomial.C_mul]
    norm_num
  linear_combination -(B * C gamma * derivative A) * h

/-- The two original constant-value coefficient-curve rows imply the exact
shifted equations `X*V=Phi(A)` and `V²=R(A,X)`. -/
theorem alignedPolynomial_shifted_curve_equations
    (A B U : F[X]) (beta gamma delta k2 k1 : F)
    (hJ2 : coefficientCurveTwoPolynomial46 0 beta gamma delta A B U = C k2)
    (hJ1 : coefficientCurveOnePolynomial46 0 beta gamma delta A B U = C k1) :
    let X := B + C beta
    let V := U - C ((8 / 3 : F) * gamma)
    X * V = alignedPhiPolynomial46 beta gamma delta k2 A ∧
      V ^ 2 = alignedRPolynomial46 beta gamma delta k1 A X := by
  dsimp
  constructor
  · have h := alignedPolynomial_curveTwo_identity A B U beta gamma delta k2
    rw [hJ2, sub_self, mul_zero] at h
    exact sub_eq_zero.mp h
  · have h := alignedPolynomial_curveOne_identity A B U beta gamma delta k1
    rw [hJ1, sub_self, mul_zero] at h
    exact sub_eq_zero.mp h

end ShiftedPolynomialEquations

section ShiftedPolynomialDegreeCones

variable {F : Type*} [Field F] [CharZero F]

/-- The actual shifted beta-stratum polynomial equations force the primitive
degree cone `(deg A,deg X,deg V)=(4n,3n,5n)`. -/
theorem alignedBetaPolynomialDegreeCone46
    (beta gamma delta k2 k1 : F) (A X V : F[X])
    (hbeta : beta ≠ 0)
    (ha : 0 < A.natDegree) (hx : 0 < X.natDegree) (hv : 0 < V.natDegree)
    (hXV : X * V = alignedPhiPolynomial46 beta gamma delta k2 A)
    (hV2 : V ^ 2 = alignedRPolynomial46 beta gamma delta k1 A X) :
    ∃ n : ℕ, 0 < n ∧ A.natDegree = 4 * n ∧
      X.natDegree = 3 * n ∧ V.natDegree = 5 * n := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at ha
    simp at ha
  have hX : X ≠ 0 := by
    intro h
    rw [h] at hx
    simp at hx
  have hV : V ≠ 0 := by
    intro h
    rw [h] at hv
    simp at hv
  let pPhi : F[X] := C ((1 / 2 : F) * beta) * A ^ 2
  let tPhi : F[X] := C ((4 / 3 : F) * delta) * A -
    C ((4 / 3 : F) * (k2 + 2 * beta * gamma))
  have hpPhi : pPhi ≠ 0 := by
    dsimp [pPhi]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hbeta))
      (pow_ne_zero 2 hA)
  have hpPhiDeg : pPhi.natDegree = 2 * A.natDegree := by
    dsimp [pPhi]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hbeta), natDegree_pow]
  have htPhi : tPhi.natDegree ≤ A.natDegree := by
    dsimp [tPhi]
    compute_degree
  have htPhiLt : tPhi.natDegree < pPhi.natDegree := by
    rw [hpPhiDeg]
    omega
  have hPhiSplit : alignedPhiPolynomial46 beta gamma delta k2 A =
      pPhi + tPhi := by
    dsimp [alignedPhiPolynomial46, pPhi, tPhi]
    ring
  have hPhiDeg : (alignedPhiPolynomial46 beta gamma delta k2 A).natDegree =
      2 * A.natDegree := by
    rw [hPhiSplit, natDegree_add_eq_left_of_natDegree_lt htPhiLt, hpPhiDeg]
  have hXVDeg : (X * V).natDegree = X.natDegree + V.natDegree :=
    natDegree_mul hX hV
  have hPhiDegreeEquation : X.natDegree + V.natDegree =
      2 * A.natDegree := by
    rw [← hXVDeg, hXV, hPhiDeg]
  let pR : F[X] := C (8 : F) * (A * X ^ 2)
  let tR : F[X] := -(C (8 : F) * (A * X * C beta)) -
      C ((32 / 3 : F) * delta) * X +
      C ((32 / 3 : F) * delta) * C beta +
      C ((32 / 3 : F) * (k1 + (2 / 3 : F) * gamma ^ 2))
  have hpR : pR ≠ 0 := by
    dsimp [pR]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num))
      (mul_ne_zero hA (pow_ne_zero 2 hX))
  have hpRDeg : pR.natDegree = A.natDegree + 2 * X.natDegree := by
    dsimp [pR]
    rw [natDegree_C_mul (by norm_num), natDegree_mul hA (pow_ne_zero 2 hX),
      natDegree_pow]
  have htR : tR.natDegree ≤ max (A.natDegree + X.natDegree) X.natDegree := by
    dsimp [tR]
    compute_degree
    omega
  have htRLt : tR.natDegree < pR.natDegree := by
    rw [hpRDeg]
    omega
  have hRSplit : alignedRPolynomial46 beta gamma delta k1 A X = pR + tR := by
    dsimp [alignedRPolynomial46, pR, tR]
    ring
  have hRDeg : (alignedRPolynomial46 beta gamma delta k1 A X).natDegree =
      A.natDegree + 2 * X.natDegree := by
    rw [hRSplit, natDegree_add_eq_left_of_natDegree_lt htRLt, hpRDeg]
  have hV2Deg : (V ^ 2).natDegree = 2 * V.natDegree := by
    simp
  have hRDegreeEquation : 2 * V.natDegree =
      A.natDegree + 2 * X.natDegree := by
    rw [← hV2Deg, hV2, hRDeg]
  exact alignedBetaDegreeCone46 A.natDegree X.natDegree V.natDegree
    ha hx hv hPhiDegreeEquation hRDegreeEquation

/-- The actual shifted delta-stratum equations force the primitive degree
cone `(deg A,deg X,deg V)=(4n,n,3n)`. -/
theorem alignedDeltaPolynomialDegreeCone46
    (gamma delta k2 k1 : F) (A X V : F[X])
    (hdelta : delta ≠ 0)
    (ha : 0 < A.natDegree) (hx : 0 < X.natDegree) (hv : 0 < V.natDegree)
    (hXV : X * V = alignedPhiPolynomial46 0 gamma delta k2 A)
    (hV2 : V ^ 2 = alignedRPolynomial46 0 gamma delta k1 A X) :
    ∃ n : ℕ, 0 < n ∧ A.natDegree = 4 * n ∧
      X.natDegree = n ∧ V.natDegree = 3 * n := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at ha
    simp at ha
  have hX : X ≠ 0 := by
    intro h
    rw [h] at hx
    simp at hx
  have hV : V ≠ 0 := by
    intro h
    rw [h] at hv
    simp at hv
  let pPhi : F[X] := C ((4 / 3 : F) * delta) * A
  let tPhi : F[X] := -C ((4 / 3 : F) * k2)
  have hpPhi : pPhi ≠ 0 := by
    dsimp [pPhi]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta)) hA
  have hpPhiDeg : pPhi.natDegree = A.natDegree := by
    dsimp [pPhi]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hdelta)]
  have htPhiLt : tPhi.natDegree < pPhi.natDegree := by
    dsimp [tPhi]
    rw [natDegree_neg, natDegree_C, hpPhiDeg]
    exact ha
  have hPhiSplit : alignedPhiPolynomial46 0 gamma delta k2 A =
      pPhi + tPhi := by
    simp [alignedPhiPolynomial46, pPhi, tPhi, sub_eq_add_neg]
  have hPhiDeg : (alignedPhiPolynomial46 0 gamma delta k2 A).natDegree =
      A.natDegree := by
    rw [hPhiSplit, natDegree_add_eq_left_of_natDegree_lt htPhiLt, hpPhiDeg]
  have hXVDeg : (X * V).natDegree = X.natDegree + V.natDegree :=
    natDegree_mul hX hV
  have hPhiDegreeEquation : X.natDegree + V.natDegree = A.natDegree := by
    rw [← hXVDeg, hXV, hPhiDeg]
  let pR : F[X] := C (8 : F) * (A * X ^ 2)
  let tR : F[X] := -C ((32 / 3 : F) * delta) * X +
    C ((32 / 3 : F) * (k1 + (2 / 3 : F) * gamma ^ 2))
  have hpR : pR ≠ 0 := by
    dsimp [pR]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num))
      (mul_ne_zero hA (pow_ne_zero 2 hX))
  have hpRDeg : pR.natDegree = A.natDegree + 2 * X.natDegree := by
    dsimp [pR]
    rw [natDegree_C_mul (by norm_num), natDegree_mul hA (pow_ne_zero 2 hX),
      natDegree_pow]
  have htR : tR.natDegree ≤ X.natDegree := by
    dsimp [tR]
    compute_degree
  have htRLt : tR.natDegree < pR.natDegree := by
    rw [hpRDeg]
    omega
  have hRSplit : alignedRPolynomial46 0 gamma delta k1 A X = pR + tR := by
    dsimp [alignedRPolynomial46, pR, tR]
    simp only [map_zero, sub_zero]
    ring
  have hRDeg : (alignedRPolynomial46 0 gamma delta k1 A X).natDegree =
      A.natDegree + 2 * X.natDegree := by
    rw [hRSplit, natDegree_add_eq_left_of_natDegree_lt htRLt, hpRDeg]
  have hV2Deg : (V ^ 2).natDegree = 2 * V.natDegree := by
    simp
  have hRDegreeEquation : 2 * V.natDegree =
      A.natDegree + 2 * X.natDegree := by
    rw [← hV2Deg, hV2, hRDeg]
  exact alignedDeltaDegreeCone46 A.natDegree X.natDegree V.natDegree
    ha hx hv hPhiDegreeEquation hRDegreeEquation

end ShiftedPolynomialDegreeCones

section ShiftedPolynomialLeadingTerms

variable {F : Type*} [Field F]

/-- On the beta aligned cone, the first shifted curve equation gives the
reviewed leading relation `X₀V₀=(1/2)beta A₀²`. -/
theorem alignedBetaPolynomialLeadingRelation46
    (beta gamma delta k2 : F) (A X V : F[X]) (n : ℕ)
    (hn : 0 < n) (_hA : A ≠ 0) (hX : X ≠ 0) (hV : V ≠ 0)
    (hAdeg : A.natDegree = 4 * n) (hXdeg : X.natDegree = 3 * n)
    (hVdeg : V.natDegree = 5 * n)
    (hXV : X * V = alignedPhiPolynomial46 beta gamma delta k2 A) :
    X.leadingCoeff * V.leadingCoeff =
      (1 / 2 : F) * beta * A.leadingCoeff ^ 2 := by
  have hA2deg : (A ^ 2).natDegree = 8 * n := by
    rw [natDegree_pow, hAdeg]
    omega
  have hXVdeg : (X * V).natDegree = 8 * n := by
    rw [natDegree_mul hX hV, hXdeg, hVdeg]
    omega
  have hcXV : (X * V).coeff (8 * n) =
      X.leadingCoeff * V.leadingCoeff := by
    rw [← hXVdeg, coeff_natDegree, leadingCoeff_mul]
  have hcA2 : (A ^ 2).coeff (8 * n) = A.leadingCoeff ^ 2 := by
    rw [← hA2deg, coeff_natDegree, leadingCoeff_pow]
  have hcA : A.coeff (8 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [hAdeg]; omega)
  have h8n : 8 * n ≠ 0 := by omega
  have hcoeff := congrArg (fun P : F[X] => P.coeff (8 * n)) hXV
  simp only [alignedPhiPolynomial46, coeff_sub, coeff_add, coeff_C_mul,
    hcXV, hcA, hcA2, mul_zero, zero_add] at hcoeff
  simp [coeff_C, h8n] at hcoeff
  simpa [div_eq_mul_inv] using hcoeff

/-- On the delta aligned cone, the first shifted curve equation gives the
reviewed leading relation `X₀V₀=(4/3)delta A₀`. -/
theorem alignedDeltaPolynomialLeadingRelation46
    (gamma delta k2 : F) (A X V : F[X]) (n : ℕ)
    (hn : 0 < n) (_hA : A ≠ 0) (hX : X ≠ 0) (hV : V ≠ 0)
    (hAdeg : A.natDegree = 4 * n) (hXdeg : X.natDegree = n)
    (hVdeg : V.natDegree = 3 * n)
    (hXV : X * V = alignedPhiPolynomial46 0 gamma delta k2 A) :
    X.leadingCoeff * V.leadingCoeff =
      (4 / 3 : F) * delta * A.leadingCoeff := by
  have hXVdeg : (X * V).natDegree = 4 * n := by
    rw [natDegree_mul hX hV, hXdeg, hVdeg]
    omega
  have hcXV : (X * V).coeff (4 * n) =
      X.leadingCoeff * V.leadingCoeff := by
    rw [← hXVdeg, coeff_natDegree, leadingCoeff_mul]
  have hcA : A.coeff (4 * n) = A.leadingCoeff := by
    rw [← hAdeg, coeff_natDegree]
  have h4n : 4 * n ≠ 0 := by omega
  have hcoeff := congrArg (fun P : F[X] => P.coeff (4 * n)) hXV
  simp only [alignedPhiPolynomial46, map_zero, mul_zero, zero_mul, add_zero,
    coeff_sub, coeff_C_mul, hcXV, hcA] at hcoeff
  simp [coeff_C, h4n] at hcoeff
  exact hcoeff

end ShiftedPolynomialLeadingTerms

section ShiftedPolynomialEtaEndgame

variable {F : Type*} [Field F] [CharZero F]

/-- In the all-nonconstant beta aligned cone, the shifted last-row pullback
has degree exactly `12n-1`.  Its top coefficient is the reviewed
`(15/32) beta A₀²`, so it cannot cancel. -/
theorem alignedBetaPolynomialEtaNatDegree46
    (beta delta : F) (A X V : F[X]) (n : ℕ)
    (hn : 0 < n) (hbeta : beta ≠ 0)
    (hA : A ≠ 0) (hX : X ≠ 0) (hV : V ≠ 0)
    (hAdeg : A.natDegree = 4 * n) (hXdeg : X.natDegree = 3 * n)
    (hVdeg : V.natDegree = 5 * n)
    (hlead : X.leadingCoeff * V.leadingCoeff =
      (1 / 2 : F) * beta * A.leadingCoeff ^ 2) :
    (alignedEtaPolynomial46 beta delta A X V).natDegree = 12 * n - 1 := by
  let topCoefficient : F[X] :=
    C (3 / 16 : F) * (X * V) + C ((3 / 8 : F) * beta) * A ^ 2
  let restA : F[X] :=
    C ((-3 / 16 : F) * beta) * V + C ((1 / 2 : F) * delta) * A
  let rest : F[X] :=
    restA * derivative A -
      C (3 / 4 : F) * (X * (X - C beta)) * derivative X +
      (C ((-3 / 16 : F) * beta) * A + C (-1 / 4 * delta)) * derivative V
  have hAlead : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have htopCoeff : topCoefficient.coeff (8 * n) =
      (15 / 32 : F) * beta * A.leadingCoeff ^ 2 := by
    have hA2deg : (A ^ 2).natDegree = 8 * n := by
      rw [natDegree_pow, hAdeg]
      omega
    have hXVdeg : (X * V).natDegree = 8 * n := by
      rw [natDegree_mul hX hV, hXdeg, hVdeg]
      omega
    have hcA2 : (A ^ 2).coeff (8 * n) = A.leadingCoeff ^ 2 := by
      rw [← hA2deg, coeff_natDegree, leadingCoeff_pow]
    have hcXV : (X * V).coeff (8 * n) =
        X.leadingCoeff * V.leadingCoeff := by
      rw [← hXVdeg, coeff_natDegree, leadingCoeff_mul]
    dsimp [topCoefficient]
    rw [coeff_add, coeff_C_mul, coeff_C_mul, hcXV, hcA2]
    simpa [mul_assoc] using
      (aligned_beta_leadingEtaCoefficient A.leadingCoeff X.leadingCoeff
        V.leadingCoeff beta hbeta hAlead hlead).1
  have htopCoeffNe : topCoefficient.coeff (8 * n) ≠ 0 := by
    rw [htopCoeff]
    exact (aligned_beta_leadingEtaCoefficient A.leadingCoeff X.leadingCoeff
      V.leadingCoeff beta hbeta hAlead hlead).2
  have htopDegreeLe : topCoefficient.natDegree ≤ 8 * n := by
    dsimp [topCoefficient]
    compute_degree
    omega
  have htopDegree : topCoefficient.natDegree = 8 * n :=
    natDegree_eq_of_le_of_coeff_ne_zero htopDegreeLe htopCoeffNe
  have htopCoefficient : topCoefficient ≠ 0 := by
    intro hz
    rw [hz, coeff_zero] at htopCoeffNe
    exact htopCoeffNe rfl
  have hderA : derivative A ≠ 0 := derivative_ne_zero.mpr (by omega)
  have htop : (topCoefficient * derivative A).natDegree = 12 * n - 1 := by
    rw [natDegree_mul htopCoefficient hderA, htopDegree,
      natDegree_derivative, hAdeg]
    omega
  have hrestA : restA.natDegree ≤ 5 * n := by
    dsimp [restA]
    compute_degree
    omega
  have hrest : rest.natDegree ≤ 9 * n - 1 := by
    dsimp [rest]
    have hdA := natDegree_derivative A
    have hdX := natDegree_derivative X
    have hdV := natDegree_derivative V
    have hmulA := natDegree_mul_le (p := restA) (q := derivative A)
    have hmulX := natDegree_mul_le
      (p := C (3 / 4 : F) * (X * (X - C beta))) (q := derivative X)
    have hmulV := natDegree_mul_le
      (p := C ((-3 / 16 : F) * beta) * A + C (-1 / 4 * delta))
      (q := derivative V)
    have hcoefX :
        (C (3 / 4 : F) * (X * (X - C beta))).natDegree ≤
          2 * X.natDegree := by
      compute_degree
      omega
    have hcoefV :
        (C ((-3 / 16 : F) * beta) * A + C (-1 / 4 * delta)).natDegree ≤
          A.natDegree := by
      compute_degree
    have hsub := natDegree_sub_le
      (restA * derivative A)
      (C (3 / 4 : F) * (X * (X - C beta)) * derivative X)
    have hadd := natDegree_add_le
      (restA * derivative A -
        C (3 / 4 : F) * (X * (X - C beta)) * derivative X)
      ((C ((-3 / 16 : F) * beta) * A + C (-1 / 4 * delta)) * derivative V)
    rw [hAdeg] at hdA hcoefV
    rw [hXdeg] at hdX hcoefX
    rw [hVdeg] at hdV
    omega
  have hrestlt : rest.natDegree <
      (topCoefficient * derivative A).natDegree := by
    rw [htop]
    omega
  have hsplit : alignedEtaPolynomial46 beta delta A X V =
      topCoefficient * derivative A + rest := by
    dsimp [alignedEtaPolynomial46, topCoefficient, restA, rest]
    simp only [map_mul]
    have hn316 : C (-3 / 16 : F) = -C (3 / 16 : F) := by
      rw [show (-3 / 16 : F) = -(3 / 16 : F) by ring, map_neg]
    rw [hn316]
    ring
  rw [hsplit, natDegree_add_eq_left_of_natDegree_lt hrestlt, htop]

/-- In the all-nonconstant delta aligned cone, the shifted last-row pullback
has degree exactly `8n-1`.  Its top coefficient is the reviewed
`(3/4) delta A₀`, so it cannot cancel. -/
theorem alignedDeltaPolynomialEtaNatDegree46
    (delta : F) (A X V : F[X]) (n : ℕ)
    (hn : 0 < n) (hdelta : delta ≠ 0)
    (hA : A ≠ 0) (hX : X ≠ 0) (hV : V ≠ 0)
    (hAdeg : A.natDegree = 4 * n) (hXdeg : X.natDegree = n)
    (hVdeg : V.natDegree = 3 * n)
    (hlead : X.leadingCoeff * V.leadingCoeff =
      (4 / 3 : F) * delta * A.leadingCoeff) :
    (alignedEtaPolynomial46 0 delta A X V).natDegree = 8 * n - 1 := by
  let topCoefficient : F[X] :=
    C (3 / 16 : F) * (X * V) + C ((1 / 2 : F) * delta) * A
  let rest : F[X] :=
    -(C (3 / 4 : F) * X ^ 2 * derivative X) +
      C (-1 / 4 * delta) * derivative V
  have hAlead : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have htopCoeff : topCoefficient.coeff (4 * n) =
      (3 / 4 : F) * delta * A.leadingCoeff := by
    have hXVdeg : (X * V).natDegree = 4 * n := by
      rw [natDegree_mul hX hV, hXdeg, hVdeg]
      omega
    have hcXV : (X * V).coeff (4 * n) =
        X.leadingCoeff * V.leadingCoeff := by
      rw [← hXVdeg, coeff_natDegree, leadingCoeff_mul]
    have hcA : A.coeff (4 * n) = A.leadingCoeff := by
      rw [← hAdeg, coeff_natDegree]
    dsimp [topCoefficient]
    rw [coeff_add, coeff_C_mul, coeff_C_mul, hcXV, hcA]
    simpa [mul_assoc] using
      (aligned_delta_leadingEtaCoefficient A.leadingCoeff X.leadingCoeff
        V.leadingCoeff delta hdelta hAlead hlead).1
  have htopCoeffNe : topCoefficient.coeff (4 * n) ≠ 0 := by
    rw [htopCoeff]
    exact (aligned_delta_leadingEtaCoefficient A.leadingCoeff X.leadingCoeff
      V.leadingCoeff delta hdelta hAlead hlead).2
  have htopDegreeLe : topCoefficient.natDegree ≤ 4 * n := by
    dsimp [topCoefficient]
    compute_degree
    omega
  have htopDegree : topCoefficient.natDegree = 4 * n :=
    natDegree_eq_of_le_of_coeff_ne_zero htopDegreeLe htopCoeffNe
  have htopCoefficient : topCoefficient ≠ 0 := by
    intro hz
    rw [hz, coeff_zero] at htopCoeffNe
    exact htopCoeffNe rfl
  have hderA : derivative A ≠ 0 := derivative_ne_zero.mpr (by omega)
  have htop : (topCoefficient * derivative A).natDegree = 8 * n - 1 := by
    rw [natDegree_mul htopCoefficient hderA, htopDegree,
      natDegree_derivative, hAdeg]
    omega
  have hrest : rest.natDegree ≤ 3 * n - 1 := by
    dsimp [rest]
    have hdX := natDegree_derivative X
    have hdV := natDegree_derivative V
    have hmulX := natDegree_mul_le
      (p := C (3 / 4 : F) * X ^ 2) (q := derivative X)
    have hmulV := natDegree_mul_le
      (p := C (-1 / 4 * delta)) (q := derivative V)
    have hneg := natDegree_neg (C (3 / 4 : F) * X ^ 2 * derivative X)
    have hadd := natDegree_add_le
      (-(C (3 / 4 : F) * X ^ 2 * derivative X))
      (C (-1 / 4 * delta) * derivative V)
    have hcoefX : (C (3 / 4 : F) * X ^ 2).natDegree ≤
        2 * X.natDegree := by
      compute_degree
    have hcoefV : (C (-1 / 4 * delta) : F[X]).natDegree ≤ 0 := by
      compute_degree
    rw [hXdeg] at hdX hcoefX
    rw [hVdeg] at hdV
    omega
  have hrestlt : rest.natDegree <
      (topCoefficient * derivative A).natDegree := by
    rw [htop]
    omega
  have hsplit : alignedEtaPolynomial46 0 delta A X V =
      topCoefficient * derivative A + rest := by
    dsimp [alignedEtaPolynomial46, topCoefficient, rest]
    simp only [map_zero, mul_zero, zero_mul, sub_zero, zero_add]
    ring
  rw [hsplit, natDegree_add_eq_left_of_natDegree_lt hrestlt, htop]

/-- The exact shifted curve rows rule out a constant last row on every beta
aligned polynomial trajectory for which `A`, `X`, and `V` are all
nonconstant. -/
theorem alignedBetaPolynomial_allNonconstant_impossible46
    (beta gamma delta k2 k1 j : F) (A X V : F[X])
    (hbeta : beta ≠ 0)
    (hAdeg : 0 < A.natDegree) (hXdeg : 0 < X.natDegree)
    (hVdeg : 0 < V.natDegree)
    (hXV : X * V = alignedPhiPolynomial46 beta gamma delta k2 A)
    (hV2 : V ^ 2 = alignedRPolynomial46 beta gamma delta k1 A X)
    (hlast : alignedEtaPolynomial46 beta delta A X V = C j) : False := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at hAdeg
    simp at hAdeg
  have hX : X ≠ 0 := by
    intro h
    rw [h] at hXdeg
    simp at hXdeg
  have hV : V ≠ 0 := by
    intro h
    rw [h] at hVdeg
    simp at hVdeg
  obtain ⟨n, hn, hnA, hnX, hnV⟩ :=
    alignedBetaPolynomialDegreeCone46 beta gamma delta k2 k1 A X V hbeta
      hAdeg hXdeg hVdeg hXV hV2
  have hlead := alignedBetaPolynomialLeadingRelation46 beta gamma delta k2
    A X V n hn hA hX hV hnA hnX hnV hXV
  have heta := alignedBetaPolynomialEtaNatDegree46 beta delta A X V n hn
    hbeta hA hX hV hnA hnX hnV hlead
  have hpositive : 0 <
      (alignedEtaPolynomial46 beta delta A X V).natDegree := by
    rw [heta]
    omega
  rw [hlast, natDegree_C] at hpositive
  omega

/-- The exact shifted curve rows rule out a constant last row on every delta
aligned polynomial trajectory for which `A`, `X`, and `V` are all
nonconstant. -/
theorem alignedDeltaPolynomial_allNonconstant_impossible46
    (gamma delta k2 k1 j : F) (A X V : F[X])
    (hdelta : delta ≠ 0)
    (hAdeg : 0 < A.natDegree) (hXdeg : 0 < X.natDegree)
    (hVdeg : 0 < V.natDegree)
    (hXV : X * V = alignedPhiPolynomial46 0 gamma delta k2 A)
    (hV2 : V ^ 2 = alignedRPolynomial46 0 gamma delta k1 A X)
    (hlast : alignedEtaPolynomial46 0 delta A X V = C j) : False := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at hAdeg
    simp at hAdeg
  have hX : X ≠ 0 := by
    intro h
    rw [h] at hXdeg
    simp at hXdeg
  have hV : V ≠ 0 := by
    intro h
    rw [h] at hVdeg
    simp at hVdeg
  obtain ⟨n, hn, hnA, hnX, hnV⟩ :=
    alignedDeltaPolynomialDegreeCone46 gamma delta k2 k1 A X V hdelta
      hAdeg hXdeg hVdeg hXV hV2
  have hlead := alignedDeltaPolynomialLeadingRelation46 gamma delta k2
    A X V n hn hA hX hV hnA hnX hnV hXV
  have heta := alignedDeltaPolynomialEtaNatDegree46 delta A X V n hn
    hdelta hA hX hV hnA hnX hnV hlead
  have hpositive : 0 <
      (alignedEtaPolynomial46 0 delta A X V).natDegree := by
    rw [heta]
    omega
  rw [hlast, natDegree_C] at hpositive
  omega

end ShiftedPolynomialEtaEndgame

section ShiftedPolynomialDegenerateEndgame

variable {F : Type*} [Field F] [CharZero F]

/-- The beta-aligned curve function has its expected quadratic degree on a
nonconstant polynomial `A`. -/
theorem alignedBetaPhiPolynomialNatDegree46
    (beta gamma delta k2 : F) (A : F[X])
    (hbeta : beta ≠ 0) (hA : A ≠ 0) (hAdeg : 0 < A.natDegree) :
    (alignedPhiPolynomial46 beta gamma delta k2 A).natDegree =
      2 * A.natDegree := by
  let p : F[X] := C ((1 / 2 : F) * beta) * A ^ 2
  let t : F[X] := C ((4 / 3 : F) * delta) * A -
    C ((4 / 3 : F) * (k2 + 2 * beta * gamma))
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hbeta))
      (pow_ne_zero 2 hA)
  have hpdeg : p.natDegree = 2 * A.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hbeta), natDegree_pow]
  have ht : t.natDegree ≤ A.natDegree := by
    dsimp [t]
    compute_degree
  have htlt : t.natDegree < p.natDegree := by
    rw [hpdeg]
    omega
  have hsplit : alignedPhiPolynomial46 beta gamma delta k2 A = p + t := by
    dsimp [alignedPhiPolynomial46, p, t]
    ring
  rw [hsplit, natDegree_add_eq_left_of_natDegree_lt htlt, hpdeg]

/-- The delta-aligned curve function has its expected linear degree on a
nonconstant polynomial `A`. -/
theorem alignedDeltaPhiPolynomialNatDegree46
    (gamma delta k2 : F) (A : F[X])
    (hdelta : delta ≠ 0) (hA : A ≠ 0) (hAdeg : 0 < A.natDegree) :
    (alignedPhiPolynomial46 0 gamma delta k2 A).natDegree = A.natDegree := by
  let p : F[X] := C ((4 / 3 : F) * delta) * A
  let t : F[X] := -C ((4 / 3 : F) * k2)
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta)) hA
  have hpdeg : p.natDegree = A.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hdelta)]
  have htlt : t.natDegree < p.natDegree := by
    dsimp [t]
    rw [natDegree_neg, natDegree_C, hpdeg]
    exact hAdeg
  have hsplit : alignedPhiPolynomial46 0 gamma delta k2 A = p + t := by
    simp [alignedPhiPolynomial46, p, t, sub_eq_add_neg]
  rw [hsplit, natDegree_add_eq_left_of_natDegree_lt htlt, hpdeg]

/-- Whenever both `A` and `X` are nonconstant, the cubic monomial `A*X²`
is uniquely top in the aligned second curve function. -/
theorem alignedRPolynomialNatDegree46
    (beta gamma delta k1 : F) (A X : F[X])
    (hA : A ≠ 0) (hX : X ≠ 0)
    (hAdeg : 0 < A.natDegree) (hXdeg : 0 < X.natDegree) :
    (alignedRPolynomial46 beta gamma delta k1 A X).natDegree =
      A.natDegree + 2 * X.natDegree := by
  let p : F[X] := C (8 : F) * (A * X ^ 2)
  let t : F[X] := -(C (8 : F) * (A * X * C beta)) -
      C ((32 / 3 : F) * delta) * X +
      C ((32 / 3 : F) * delta) * C beta +
      C ((32 / 3 : F) * (k1 + (2 / 3 : F) * gamma ^ 2))
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num))
      (mul_ne_zero hA (pow_ne_zero 2 hX))
  have hpdeg : p.natDegree = A.natDegree + 2 * X.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (by norm_num), natDegree_mul hA (pow_ne_zero 2 hX),
      natDegree_pow]
  have ht : t.natDegree ≤ max (A.natDegree + X.natDegree) X.natDegree := by
    dsimp [t]
    compute_degree
    omega
  have htlt : t.natDegree < p.natDegree := by
    rw [hpdeg]
    omega
  have hsplit : alignedRPolynomial46 beta gamma delta k1 A X = p + t := by
    dsimp [alignedRPolynomial46, p, t]
    ring
  rw [hsplit, natDegree_add_eq_left_of_natDegree_lt htlt, hpdeg]

omit [CharZero F] in
/-- If `A` is nonconstant and `X` is constant, any aligned first-row degree
`d` with `deg A < 2d` is incompatible with the second curve row. -/
theorem alignedPolynomial_A_nonconstant_X_constant_impossible46
    (beta gamma delta k2 k1 x : F) (A V : F[X]) (d : ℕ)
    (_hAdeg : 0 < A.natDegree) (hd : 0 < d)
    (hPhiDeg : (alignedPhiPolynomial46 beta gamma delta k2 A).natDegree = d)
    (hgap : A.natDegree < 2 * d)
    (hXV : C x * V = alignedPhiPolynomial46 beta gamma delta k2 A)
    (hV2 : V ^ 2 = alignedRPolynomial46 beta gamma delta k1 A (C x)) : False := by
  have hPhi : alignedPhiPolynomial46 beta gamma delta k2 A ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hPhiDeg
    omega
  have hprod : C x * V ≠ 0 := by
    rw [hXV]
    exact hPhi
  have hCx : C x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hprod
    exact hprod rfl
  have hV : V ≠ 0 := by
    intro hv
    rw [hv, mul_zero] at hprod
    exact hprod rfl
  have hVdeg : V.natDegree = d := by
    calc
      V.natDegree = (C x * V).natDegree := by
        rw [natDegree_mul hCx hV, natDegree_C, zero_add]
      _ = d := by rw [hXV, hPhiDeg]
  have hRbound :
      (alignedRPolynomial46 beta gamma delta k1 A (C x)).natDegree ≤
        A.natDegree := by
    dsimp [alignedRPolynomial46]
    compute_degree
  have hV2deg : (V ^ 2).natDegree = 2 * V.natDegree := by
    rw [natDegree_pow]
  rw [hV2] at hV2deg
  omega

/-- If `A` is nonconstant and `V` is constant, a positive-degree aligned
first curve function forces `X` nonconstant, after which `A*X²` contradicts
the constant second row. -/
theorem alignedPolynomial_A_nonconstant_V_constant_impossible46
    (beta gamma delta k2 k1 v : F) (A X : F[X]) (d : ℕ)
    (hAdeg : 0 < A.natDegree) (hd : 0 < d)
    (hPhiDeg : (alignedPhiPolynomial46 beta gamma delta k2 A).natDegree = d)
    (hXV : X * C v = alignedPhiPolynomial46 beta gamma delta k2 A)
    (hV2 : (C v) ^ 2 = alignedRPolynomial46 beta gamma delta k1 A X) : False := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at hAdeg
    simp at hAdeg
  have hPhi : alignedPhiPolynomial46 beta gamma delta k2 A ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hPhiDeg
    omega
  have hprod : X * C v ≠ 0 := by
    rw [hXV]
    exact hPhi
  have hX : X ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hprod
    exact hprod rfl
  have hCv : C v ≠ 0 := by
    intro hv
    rw [hv, mul_zero] at hprod
    exact hprod rfl
  have hXdeg : X.natDegree = d := by
    calc
      X.natDegree = (X * C v).natDegree := by
        rw [natDegree_mul hX hCv, natDegree_C, add_zero]
      _ = d := by rw [hXV, hPhiDeg]
  have hXpos : 0 < X.natDegree := by omega
  have hRdeg := alignedRPolynomialNatDegree46 beta gamma delta k1 A X
    hA hX hAdeg hXpos
  have hconstant : ((C v) ^ 2).natDegree = 0 := by simp
  rw [hV2, hRdeg] at hconstant
  omega

/-- No beta-aligned polynomial trajectory can have nonconstant `A` and
constant `X`. -/
theorem alignedBetaPolynomial_A_nonconstant_X_constant_impossible46
    (beta gamma delta k2 k1 x : F) (A V : F[X])
    (hbeta : beta ≠ 0) (hAdeg : 0 < A.natDegree)
    (hXV : C x * V = alignedPhiPolynomial46 beta gamma delta k2 A)
    (hV2 : V ^ 2 = alignedRPolynomial46 beta gamma delta k1 A (C x)) : False := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at hAdeg
    simp at hAdeg
  have hPhiDeg := alignedBetaPhiPolynomialNatDegree46 beta gamma delta k2 A
    hbeta hA hAdeg
  exact alignedPolynomial_A_nonconstant_X_constant_impossible46
    beta gamma delta k2 k1 x A V (2 * A.natDegree) hAdeg (by omega)
      hPhiDeg (by omega) hXV hV2

/-- No delta-aligned polynomial trajectory can have nonconstant `A` and
constant `X`. -/
theorem alignedDeltaPolynomial_A_nonconstant_X_constant_impossible46
    (gamma delta k2 k1 x : F) (A V : F[X])
    (hdelta : delta ≠ 0) (hAdeg : 0 < A.natDegree)
    (hXV : C x * V = alignedPhiPolynomial46 0 gamma delta k2 A)
    (hV2 : V ^ 2 = alignedRPolynomial46 0 gamma delta k1 A (C x)) : False := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at hAdeg
    simp at hAdeg
  have hPhiDeg := alignedDeltaPhiPolynomialNatDegree46 gamma delta k2 A
    hdelta hA hAdeg
  exact alignedPolynomial_A_nonconstant_X_constant_impossible46
    0 gamma delta k2 k1 x A V A.natDegree hAdeg hAdeg hPhiDeg
      (by omega) hXV hV2

/-- No beta-aligned polynomial trajectory can have nonconstant `A` and
constant `V`. -/
theorem alignedBetaPolynomial_A_nonconstant_V_constant_impossible46
    (beta gamma delta k2 k1 v : F) (A X : F[X])
    (hbeta : beta ≠ 0) (hAdeg : 0 < A.natDegree)
    (hXV : X * C v = alignedPhiPolynomial46 beta gamma delta k2 A)
    (hV2 : (C v) ^ 2 = alignedRPolynomial46 beta gamma delta k1 A X) : False := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at hAdeg
    simp at hAdeg
  have hPhiDeg := alignedBetaPhiPolynomialNatDegree46 beta gamma delta k2 A
    hbeta hA hAdeg
  exact alignedPolynomial_A_nonconstant_V_constant_impossible46
    beta gamma delta k2 k1 v A X (2 * A.natDegree) hAdeg (by omega)
      hPhiDeg hXV hV2

/-- No delta-aligned polynomial trajectory can have nonconstant `A` and
constant `V`. -/
theorem alignedDeltaPolynomial_A_nonconstant_V_constant_impossible46
    (gamma delta k2 k1 v : F) (A X : F[X])
    (hdelta : delta ≠ 0) (hAdeg : 0 < A.natDegree)
    (hXV : X * C v = alignedPhiPolynomial46 0 gamma delta k2 A)
    (hV2 : (C v) ^ 2 = alignedRPolynomial46 0 gamma delta k1 A X) : False := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at hAdeg
    simp at hAdeg
  have hPhiDeg := alignedDeltaPhiPolynomialNatDegree46 gamma delta k2 A
    hdelta hA hAdeg
  exact alignedPolynomial_A_nonconstant_V_constant_impossible46
    0 gamma delta k2 k1 v A X A.natDegree hAdeg hAdeg hPhiDeg hXV hV2

omit [CharZero F] in
/-- If `A` is constant, the first shifted curve row cannot have both `X`
and `V` nonconstant. -/
theorem alignedPolynomial_A_constant_XV_nonconstant_impossible46
    (beta gamma delta k2 a : F) (X V : F[X])
    (hXdeg : 0 < X.natDegree) (hVdeg : 0 < V.natDegree)
    (hXV : X * V = alignedPhiPolynomial46 beta gamma delta k2 (C a)) : False := by
  have hX : X ≠ 0 := by
    intro h
    rw [h] at hXdeg
    simp at hXdeg
  have hV : V ≠ 0 := by
    intro h
    rw [h] at hVdeg
    simp at hVdeg
  have hproddeg := natDegree_mul hX hV
  have hPhiBound :
      (alignedPhiPolynomial46 beta gamma delta k2 (C a)).natDegree ≤ 0 := by
    dsimp [alignedPhiPolynomial46]
    compute_degree
  rw [hXV] at hproddeg
  omega

omit [CharZero F] in
/-- If `A` and `X` are constant, the second shifted curve row cannot have
nonconstant `V`. -/
theorem alignedPolynomial_A_X_constant_V_nonconstant_impossible46
    (beta gamma delta k1 a x : F) (V : F[X])
    (hVdeg : 0 < V.natDegree)
    (hV2 : V ^ 2 = alignedRPolynomial46 beta gamma delta k1 (C a) (C x)) :
    False := by
  have hRBound :
      (alignedRPolynomial46 beta gamma delta k1 (C a) (C x)).natDegree ≤ 0 := by
    dsimp [alignedRPolynomial46]
    compute_degree
  have hV2deg : (V ^ 2).natDegree = 2 * V.natDegree := by
    rw [natDegree_pow]
  rw [hV2] at hV2deg
  omega

/-- With constant nonzero `A` and nonconstant `X`, the quadratic term in
`R(A,X)` is uniquely top. -/
theorem alignedRPolynomial_constantA_nonzero_natDegree46
    (beta gamma delta k1 a : F) (X : F[X])
    (ha : a ≠ 0) (hX : X ≠ 0) (hXdeg : 0 < X.natDegree) :
    (alignedRPolynomial46 beta gamma delta k1 (C a) X).natDegree =
      2 * X.natDegree := by
  let p : F[X] := C (8 : F) * (C a * X ^ 2)
  let t : F[X] := -(C (8 : F) * (C a * X * C beta)) -
      C ((32 / 3 : F) * delta) * X +
      C ((32 / 3 : F) * delta) * C beta +
      C ((32 / 3 : F) * (k1 + (2 / 3 : F) * gamma ^ 2))
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num))
      (mul_ne_zero (C_ne_zero.mpr ha) (pow_ne_zero 2 hX))
  have hpdeg : p.natDegree = 2 * X.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (by norm_num),
      natDegree_mul (C_ne_zero.mpr ha) (pow_ne_zero 2 hX), natDegree_C,
      zero_add, natDegree_pow]
  have ht : t.natDegree ≤ X.natDegree := by
    dsimp [t]
    compute_degree
  have htlt : t.natDegree < p.natDegree := by
    rw [hpdeg]
    omega
  have hsplit : alignedRPolynomial46 beta gamma delta k1 (C a) X = p + t := by
    dsimp [alignedRPolynomial46, p, t]
    ring
  rw [hsplit, natDegree_add_eq_left_of_natDegree_lt htlt, hpdeg]

/-- With `A=0`, `delta != 0`, and nonconstant `X`, the linear term in
`R(0,X)` is uniquely top. -/
theorem alignedRPolynomial_zeroA_delta_natDegree46
    (beta gamma delta k1 : F) (X : F[X])
    (hdelta : delta ≠ 0) (hX : X ≠ 0) (hXdeg : 0 < X.natDegree) :
    (alignedRPolynomial46 beta gamma delta k1 0 X).natDegree = X.natDegree := by
  let p : F[X] := -C ((32 / 3 : F) * delta) * X
  let t : F[X] := C ((32 / 3 : F) * delta) * C beta +
    C ((32 / 3 : F) * (k1 + (2 / 3 : F) * gamma ^ 2))
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (neg_ne_zero.mpr
      (C_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))) hX
  have hpdeg : p.natDegree = X.natDegree := by
    dsimp [p]
    rw [natDegree_mul (neg_ne_zero.mpr
      (C_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))) hX,
      natDegree_neg, natDegree_C, zero_add]
  have htlt : t.natDegree < p.natDegree := by
    dsimp [t]
    compute_degree
    rw [hpdeg]
    exact hXdeg
  have hsplit : alignedRPolynomial46 beta gamma delta k1 0 X = p + t := by
    dsimp [alignedRPolynomial46, p, t]
    simp only [zero_mul, mul_zero]
    ring
  rw [hsplit, natDegree_add_eq_left_of_natDegree_lt htlt, hpdeg]

/-- With `A,V` constant and `X` nonconstant, the second shifted curve row is
impossible unless simultaneously `A=0` and `delta=0`. -/
theorem alignedPolynomial_A_V_constant_X_nonconstant_impossible_of_ne46
    (beta gamma delta k1 a v : F) (X : F[X])
    (hne : a ≠ 0 ∨ delta ≠ 0) (hXdeg : 0 < X.natDegree)
    (hV2 : (C v) ^ 2 = alignedRPolynomial46 beta gamma delta k1 (C a) X) :
    False := by
  have hX : X ≠ 0 := by
    intro h
    rw [h] at hXdeg
    simp at hXdeg
  have hconstant : ((C v) ^ 2).natDegree = 0 := by simp
  rcases hne with ha | hdelta
  · have hRdeg := alignedRPolynomial_constantA_nonzero_natDegree46
      beta gamma delta k1 a X ha hX hXdeg
    rw [hV2, hRdeg] at hconstant
    omega
  · by_cases ha : a = 0
    · subst a
      have hRdeg := alignedRPolynomial_zeroA_delta_natDegree46
        beta gamma delta k1 X hdelta hX hXdeg
      simp only [map_zero] at hV2 hconstant
      rw [hV2, hRdeg] at hconstant
      omega
    · have hRdeg := alignedRPolynomial_constantA_nonzero_natDegree46
        beta gamma delta k1 a X ha hX hXdeg
      rw [hV2, hRdeg] at hconstant
      omega

omit [CharZero F] in
/-- If `A,V` are constant while `X` is nonconstant, the first shifted curve
row forces the scalar value of `V` to vanish. -/
theorem alignedPolynomial_A_V_constant_X_nonconstant_forces_v_zero46
    (beta gamma delta k2 a v : F) (X : F[X])
    (hXdeg : 0 < X.natDegree)
    (hXV : X * C v = alignedPhiPolynomial46 beta gamma delta k2 (C a)) :
    v = 0 := by
  by_contra hv
  have hX : X ≠ 0 := by
    intro h
    rw [h] at hXdeg
    simp at hXdeg
  have hCv : C v ≠ 0 := C_ne_zero.mpr hv
  have hproddeg : (X * C v).natDegree = X.natDegree := by
    rw [natDegree_mul hX hCv, natDegree_C, add_zero]
  have hPhiBound :
      (alignedPhiPolynomial46 beta gamma delta k2 (C a)).natDegree ≤ 0 := by
    dsimp [alignedPhiPolynomial46]
    compute_degree
  rw [hXV] at hproddeg
  omega

/-- On the only degenerate beta-aligned line left by the two curve rows,
`A=V=delta=0`, a nonconstant `X` makes the last row have degree
`3 deg(X)-1`. -/
theorem alignedBetaPolynomial_specialLine_X_nonconstant_impossible46
    (beta j : F) (X : F[X]) (hXdeg : 0 < X.natDegree)
    (hlast : alignedEtaPolynomial46 beta 0 0 X 0 = C j) : False := by
  have hX : X ≠ 0 := by
    intro h
    rw [h] at hXdeg
    simp at hXdeg
  have hsubdeg : (X - C beta).natDegree = X.natDegree := natDegree_sub_C
  have hsub : X - C beta ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hsubdeg
    omega
  have hderX : derivative X ≠ 0 := derivative_ne_zero.mpr hXdeg.ne'
  let top : F[X] :=
    -(C (3 / 4 : F) * (X * (X - C beta)) * derivative X)
  have hXX : X * (X - C beta) ≠ 0 := mul_ne_zero hX hsub
  have hcoefficient : C (3 / 4 : F) * (X * (X - C beta)) ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr (by norm_num)) hXX
  have hcoefficientDegree :
      (C (3 / 4 : F) * (X * (X - C beta))).natDegree =
        2 * X.natDegree := by
    rw [natDegree_mul (C_ne_zero.mpr (by norm_num)) hXX, natDegree_C,
      natDegree_mul hX hsub, hsubdeg]
    omega
  have htopDegree : top.natDegree = 3 * X.natDegree - 1 := by
    dsimp [top]
    rw [natDegree_neg, natDegree_mul hcoefficient hderX,
      hcoefficientDegree, natDegree_derivative]
    omega
  have hsplit : alignedEtaPolynomial46 beta 0 0 X 0 = top := by
    dsimp [alignedEtaPolynomial46, top]
    simp only [map_zero, mul_zero, pow_two, add_zero, zero_sub]
  have hetaDegree : (alignedEtaPolynomial46 beta 0 0 X 0).natDegree =
      3 * X.natDegree - 1 := by rw [hsplit, htopDegree]
  have hpositive : 0 < (alignedEtaPolynomial46 beta 0 0 X 0).natDegree := by
    rw [hetaDegree]
    omega
  rw [hlast, natDegree_C] at hpositive
  omega

set_option maxHeartbeats 800000 in
/-- Complete beta-aligned polynomial endgame.  The two exact shifted curve
rows and a nonzero constant last row are inconsistent for every
constant/nonconstant pattern of `A,X,V`. -/
theorem alignedBetaPolynomialTrajectory_impossible46
    (beta gamma delta k2 k1 j : F) (A X V : F[X])
    (hbeta : beta ≠ 0) (hj : j ≠ 0)
    (hXV : X * V = alignedPhiPolynomial46 beta gamma delta k2 A)
    (hV2 : V ^ 2 = alignedRPolynomial46 beta gamma delta k1 A X)
    (hlast : alignedEtaPolynomial46 beta delta A X V = C j) : False := by
  by_cases hA0 : A.natDegree = 0
  · obtain ⟨a, ha⟩ := natDegree_eq_zero.mp hA0
    rw [← ha] at hXV hV2 hlast
    by_cases hX0 : X.natDegree = 0
    · obtain ⟨x, hx⟩ := natDegree_eq_zero.mp hX0
      rw [← hx] at hXV hV2 hlast
      by_cases hV0 : V.natDegree = 0
      · obtain ⟨v, hv⟩ := natDegree_eq_zero.mp hV0
        rw [← hv] at hXV hV2 hlast
        have heta : alignedEtaPolynomial46 beta delta (C a) (C x) (C v) = 0 := by
          simp [alignedEtaPolynomial46]
        rw [heta] at hlast
        have hj0 : C j = C (0 : F) := by simpa using hlast.symm
        exact hj (C_injective hj0)
      · exact alignedPolynomial_A_X_constant_V_nonconstant_impossible46
          beta gamma delta k1 a x V (Nat.pos_of_ne_zero hV0) hV2
    · have hXpos := Nat.pos_of_ne_zero hX0
      by_cases hV0 : V.natDegree = 0
      · obtain ⟨v, hv⟩ := natDegree_eq_zero.mp hV0
        rw [← hv] at hXV hV2 hlast
        by_cases ha0 : a = 0
        · subst a
          by_cases hdelta0 : delta = 0
          · subst delta
            have hv0 := alignedPolynomial_A_V_constant_X_nonconstant_forces_v_zero46
              beta gamma 0 k2 0 v X hXpos hXV
            subst v
            simp only [map_zero] at hlast
            exact alignedBetaPolynomial_specialLine_X_nonconstant_impossible46
              beta j X hXpos hlast
          · exact alignedPolynomial_A_V_constant_X_nonconstant_impossible_of_ne46
              beta gamma delta k1 0 v X (Or.inr hdelta0) hXpos hV2
        · exact alignedPolynomial_A_V_constant_X_nonconstant_impossible_of_ne46
            beta gamma delta k1 a v X (Or.inl ha0) hXpos hV2
      · exact alignedPolynomial_A_constant_XV_nonconstant_impossible46
          beta gamma delta k2 a X V hXpos (Nat.pos_of_ne_zero hV0) hXV
  · have hApos := Nat.pos_of_ne_zero hA0
    by_cases hX0 : X.natDegree = 0
    · obtain ⟨x, hx⟩ := natDegree_eq_zero.mp hX0
      rw [← hx] at hXV hV2 hlast
      exact alignedBetaPolynomial_A_nonconstant_X_constant_impossible46
        beta gamma delta k2 k1 x A V hbeta hApos hXV hV2
    · have hXpos := Nat.pos_of_ne_zero hX0
      by_cases hV0 : V.natDegree = 0
      · obtain ⟨v, hv⟩ := natDegree_eq_zero.mp hV0
        rw [← hv] at hXV hV2 hlast
        exact alignedBetaPolynomial_A_nonconstant_V_constant_impossible46
          beta gamma delta k2 k1 v A X hbeta hApos hXV hV2
      · exact alignedBetaPolynomial_allNonconstant_impossible46
          beta gamma delta k2 k1 j A X V hbeta hApos hXpos
            (Nat.pos_of_ne_zero hV0) hXV hV2 hlast

set_option maxHeartbeats 800000 in
/-- Complete delta-aligned polynomial endgame.  The two exact shifted curve
rows and a nonzero constant last row are inconsistent for every
constant/nonconstant pattern of `A,X,V`. -/
theorem alignedDeltaPolynomialTrajectory_impossible46
    (gamma delta k2 k1 j : F) (A X V : F[X])
    (hdelta : delta ≠ 0) (hj : j ≠ 0)
    (hXV : X * V = alignedPhiPolynomial46 0 gamma delta k2 A)
    (hV2 : V ^ 2 = alignedRPolynomial46 0 gamma delta k1 A X)
    (hlast : alignedEtaPolynomial46 0 delta A X V = C j) : False := by
  by_cases hA0 : A.natDegree = 0
  · obtain ⟨a, ha⟩ := natDegree_eq_zero.mp hA0
    rw [← ha] at hXV hV2 hlast
    by_cases hX0 : X.natDegree = 0
    · obtain ⟨x, hx⟩ := natDegree_eq_zero.mp hX0
      rw [← hx] at hXV hV2 hlast
      by_cases hV0 : V.natDegree = 0
      · obtain ⟨v, hv⟩ := natDegree_eq_zero.mp hV0
        rw [← hv] at hXV hV2 hlast
        have heta : alignedEtaPolynomial46 0 delta (C a) (C x) (C v) = 0 := by
          simp [alignedEtaPolynomial46]
        rw [heta] at hlast
        have hj0 : C j = C (0 : F) := by simpa using hlast.symm
        exact hj (C_injective hj0)
      · exact alignedPolynomial_A_X_constant_V_nonconstant_impossible46
          0 gamma delta k1 a x V (Nat.pos_of_ne_zero hV0) hV2
    · have hXpos := Nat.pos_of_ne_zero hX0
      by_cases hV0 : V.natDegree = 0
      · obtain ⟨v, hv⟩ := natDegree_eq_zero.mp hV0
        rw [← hv] at hXV hV2 hlast
        exact alignedPolynomial_A_V_constant_X_nonconstant_impossible_of_ne46
          0 gamma delta k1 a v X (Or.inr hdelta) hXpos hV2
      · exact alignedPolynomial_A_constant_XV_nonconstant_impossible46
          0 gamma delta k2 a X V hXpos (Nat.pos_of_ne_zero hV0) hXV
  · have hApos := Nat.pos_of_ne_zero hA0
    by_cases hX0 : X.natDegree = 0
    · obtain ⟨x, hx⟩ := natDegree_eq_zero.mp hX0
      rw [← hx] at hXV hV2 hlast
      exact alignedDeltaPolynomial_A_nonconstant_X_constant_impossible46
        gamma delta k2 k1 x A V hdelta hApos hXV hV2
    · have hXpos := Nat.pos_of_ne_zero hX0
      by_cases hV0 : V.natDegree = 0
      · obtain ⟨v, hv⟩ := natDegree_eq_zero.mp hV0
        rw [← hv] at hXV hV2 hlast
        exact alignedDeltaPolynomial_A_nonconstant_V_constant_impossible46
          gamma delta k2 k1 v A X hdelta hApos hXV hV2
      · exact alignedDeltaPolynomial_allNonconstant_impossible46
          gamma delta k2 k1 j A X V hdelta hApos hXpos
            (Nat.pos_of_ne_zero hV0) hXV hV2 hlast

/-- Literal-row beta-aligned polynomial exclusion in the original variables
`A,B,U`.  The shift to `X=B+beta`, `V=U-8gamma/3` is performed internally. -/
theorem alignedBetaOriginalPolynomialTrajectory_impossible46
    (beta gamma delta k2 k1 j : F) (A B U : F[X])
    (hbeta : beta ≠ 0) (hj : j ≠ 0)
    (hJ2 : coefficientCurveTwoPolynomial46 0 beta gamma delta A B U = C k2)
    (hJ1 : coefficientCurveOnePolynomial46 0 beta gamma delta A B U = C k1)
    (hlast : etaPolynomial46 0 beta gamma delta A B U = C j) : False := by
  let Xs : F[X] := B + C beta
  let Vs : F[X] := U - C ((8 / 3 : F) * gamma)
  have hcurves := alignedPolynomial_shifted_curve_equations
    A B U beta gamma delta k2 k1 hJ2 hJ1
  have hlastShift : alignedEtaPolynomial46 beta delta A Xs Vs = C j := by
    dsimp [Xs, Vs]
    rw [alignedPolynomial_eta_identity]
    exact hlast
  exact alignedBetaPolynomialTrajectory_impossible46
    beta gamma delta k2 k1 j A Xs Vs hbeta hj hcurves.1 hcurves.2 hlastShift

/-- Literal-row delta-aligned polynomial exclusion in the original variables
`A,B,U`.  The shift to `X=B`, `V=U-8gamma/3` is performed internally. -/
theorem alignedDeltaOriginalPolynomialTrajectory_impossible46
    (gamma delta k2 k1 j : F) (A B U : F[X])
    (hdelta : delta ≠ 0) (hj : j ≠ 0)
    (hJ2 : coefficientCurveTwoPolynomial46 0 0 gamma delta A B U = C k2)
    (hJ1 : coefficientCurveOnePolynomial46 0 0 gamma delta A B U = C k1)
    (hlast : etaPolynomial46 0 0 gamma delta A B U = C j) : False := by
  let Xs : F[X] := B + C 0
  let Vs : F[X] := U - C ((8 / 3 : F) * gamma)
  have hcurves := alignedPolynomial_shifted_curve_equations
    A B U 0 gamma delta k2 k1 hJ2 hJ1
  have hlastShift : alignedEtaPolynomial46 0 delta A Xs Vs = C j := by
    dsimp [Xs, Vs]
    rw [alignedPolynomial_eta_identity]
    exact hlast
  exact alignedDeltaPolynomialTrajectory_impossible46
    gamma delta k2 k1 j A Xs Vs hdelta hj hcurves.1 hcurves.2 hlastShift

/-- Complete final-stratum polynomial endgame with `beta=delta=0`.  If
`k2 != 0`, the unit product `B*V` freezes `B,V`, and the second curve row
freezes `A`.  If `k2=0`, the exact components are `B=0` and `V=0`; the
former has zero last row and the latter is the square unit-product
contradiction. -/
theorem alignedZeroPolynomialTrajectory_impossible46
    (gamma k2 k1 j : F) (A B V : F[X]) (hj : j ≠ 0)
    (hBV : B * V = alignedPhiPolynomial46 0 gamma 0 k2 A)
    (hV2 : V ^ 2 = alignedRPolynomial46 0 gamma 0 k1 A B)
    (hlast : alignedEtaPolynomial46 0 0 A B V = C j) : False := by
  by_cases hk2 : k2 = 0
  · subst k2
    have hproduct : B * V = 0 := by
      simpa [alignedPhiPolynomial46] using hBV
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hproduct with hB | hV
    · rw [hB] at hlast
      simp [alignedEtaPolynomial46] at hlast
      have hj0 : C j = C (0 : F) := by simpa using hlast.symm
      exact hj (C_injective hj0)
    · rw [hV] at hlast
      have hn34 : C (-3 / 4 : F) = -C (3 / 4 : F) := by
        rw [show (-3 / 4 : F) = -(3 / 4 : F) by ring, map_neg]
      have hrestricted :
          C (-3 / 4 : F) * (1 : F[X]) * B ^ 2 * derivative B = C j := by
        rw [hn34]
        simpa [alignedEtaPolynomial46, pow_two, mul_assoc] using hlast
      exact square_aligned_unitProduct_impossible46 1 B j hj hrestricted
  · have hc : (-4 / 3 : F) * k2 ≠ 0 := mul_ne_zero (by norm_num) hk2
    have hproduct : B * V = C ((-4 / 3 : F) * k2) := by
      calc
        B * V = alignedPhiPolynomial46 0 gamma 0 k2 A := hBV
        _ = C ((-4 / 3 : F) * k2) := by
          simp only [alignedPhiPolynomial46, map_zero, mul_zero, zero_mul,
            add_zero, zero_sub]
          rw [show (-4 / 3 : F) * k2 = -((4 / 3 : F) * k2) by ring,
            map_neg]
    have hproductUnit : IsUnit (B * V) := by
      rw [hproduct]
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
    have hBUnit : IsUnit B := (IsUnit.mul_iff.mp hproductUnit).1
    have hVUnit : IsUnit V := (IsUnit.mul_iff.mp hproductUnit).2
    obtain ⟨b, hb, hBc⟩ := Polynomial.isUnit_iff.mp hBUnit
    obtain ⟨v, _hv, hVc⟩ := Polynomial.isUnit_iff.mp hVUnit
    rw [← hBc, ← hVc] at hV2 hlast
    have hA0 : A.natDegree = 0 := by
      by_contra hA0
      have hApos := Nat.pos_of_ne_zero hA0
      have hA : A ≠ 0 := by
        intro h
        rw [h] at hApos
        simp at hApos
      let p : F[X] := C (8 : F) * (A * (C b) ^ 2)
      let t : F[X] :=
        C ((32 / 3 : F) * (k1 + (2 / 3 : F) * gamma ^ 2)) - (C v) ^ 2
      have hp : p ≠ 0 := by
        dsimp [p]
        exact mul_ne_zero (C_ne_zero.mpr (by norm_num))
          (mul_ne_zero hA (pow_ne_zero 2 (C_ne_zero.mpr hb.ne_zero)))
      have hpdeg : p.natDegree = A.natDegree := by
        dsimp [p]
        rw [natDegree_C_mul (by norm_num),
          natDegree_mul hA (pow_ne_zero 2 (C_ne_zero.mpr hb.ne_zero)),
          natDegree_pow, natDegree_C, mul_zero, add_zero]
      have htlt : t.natDegree < p.natDegree := by
        dsimp [t]
        compute_degree
        rw [hpdeg]
        exact hApos
      have hsum : p + t = 0 := by
        calc
          p + t = alignedRPolynomial46 0 gamma 0 k1 A (C b) - (C v) ^ 2 := by
            dsimp [p, t, alignedRPolynomial46]
            simp only [map_zero, mul_zero, zero_mul, sub_zero]
            ring
          _ = 0 := sub_eq_zero.mpr hV2.symm
      have hsumdeg : (p + t).natDegree = p.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt htlt
      rw [hsum, natDegree_zero, hpdeg] at hsumdeg
      omega
    obtain ⟨a, ha⟩ := natDegree_eq_zero.mp hA0
    rw [← ha] at hlast
    simp [alignedEtaPolynomial46] at hlast
    have hj0 : C j = C (0 : F) := by simpa using hlast.symm
    exact hj (C_injective hj0)

/-- Literal-row final-stratum polynomial exclusion in the original variables
`A,B,U`, with `V=U-8gamma/3` introduced internally. -/
theorem alignedZeroOriginalPolynomialTrajectory_impossible46
    (gamma k2 k1 j : F) (A B U : F[X]) (hj : j ≠ 0)
    (hJ2 : coefficientCurveTwoPolynomial46 0 0 gamma 0 A B U = C k2)
    (hJ1 : coefficientCurveOnePolynomial46 0 0 gamma 0 A B U = C k1)
    (hlast : etaPolynomial46 0 0 gamma 0 A B U = C j) : False := by
  let Xs : F[X] := B + C 0
  let Vs : F[X] := U - C ((8 / 3 : F) * gamma)
  have hcurves := alignedPolynomial_shifted_curve_equations
    A B U 0 gamma 0 k2 k1 hJ2 hJ1
  have hlastShift : alignedEtaPolynomial46 0 0 A Xs Vs = C j := by
    dsimp [Xs, Vs]
    rw [alignedPolynomial_eta_identity]
    exact hlast
  exact alignedZeroPolynomialTrajectory_impossible46
    gamma k2 k1 j A Xs Vs hj hcurves.1 hcurves.2 hlastShift

end ShiftedPolynomialDegenerateEndgame

end Max11DegreeRoutes
