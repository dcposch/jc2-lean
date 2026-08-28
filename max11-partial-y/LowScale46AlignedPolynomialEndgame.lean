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

end Max11DegreeRoutes
