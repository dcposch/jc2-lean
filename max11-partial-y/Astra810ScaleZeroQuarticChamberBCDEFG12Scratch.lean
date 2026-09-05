import Grok810ScaleZeroQuarticTowerScratch

/-! # The BCDEFG12 scale-zero chamber

The chamber is closed by the tracked Open-II six-face certificate.
The auxiliary N7 + (1/4) A C kappa cancels its load-free face at cost 4s,
where s = 3 deg(A) - 2 deg(B). Its remaining terms give strict bands
for l, beta, delta, zeta, theta, including every load wall. These bands
isolate the kappa, mu, xi, pi, N2 and N6 faces throughout the chamber,
including deg(B) = 0. Every compute_degree target has at most six monomials.

Only the git-tracked Tower module is imported. The proof uses full
polynomial identities and coefficient extraction; there are no new axioms
or finite-root shortcuts. No sub-cells remain open.
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


set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, load-free chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestFree1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (23 / 8192 : k) • (A * B ^ 5)
  + (-(5 / 512 : k)) • (A * B ^ 3 * E)
  + (-(125 / 2048 : k)) • (B ^ 4 * D)
  + (-(265 / 2048 : k)) • (B ^ 3 * C ^ 2)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, load-free chunk 2; at most six monomials. -/
def bandAuxBCDEFG12RestFree2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (-(5 / 16 : k)) • (B * E * G)
  + (-(5 / 16 : k)) • (B * F ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, load-free chunk 3; at most six monomials. -/
def bandAuxBCDEFG12RestFree3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (C * D * G)
  + (-(5 / 8 : k)) • (C * E * F)
  + (-(5 / 16 : k)) • (D ^ 2 * F)
  + (-(5 / 16 : k)) • (D * E ^ 2)
  + (-(15 / 512 : k)) • (A * B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestL1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (693 / 1048576 * l : k) • (A ^ 6 * C)
  + (-(315 / 2097152 * l : k)) • (A ^ 5 * B ^ 2)
  + (315 / 131072 * l : k) • (A ^ 5 * E)
  + (-(315 / 262144 * l : k)) • (A ^ 4 * B * D)
  + (2205 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  + (315 / 32768 * l : k) • (A ^ 4 * G)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 2; at most six monomials. -/
def bandAuxBCDEFG12RestL2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(81 / 131072 * l : k)) • (A ^ 3 * B ^ 2 * C)
  + (-(45 / 8192 * l : k)) • (A ^ 3 * B * F)
  + (225 / 8192 * l : k) • (A ^ 3 * C * E)
  + (-(45 / 16384 * l : k)) • (A ^ 3 * D ^ 2)
  + (-(45 / 524288 * l : k)) • (A ^ 2 * B ^ 4)
  + (-(45 / 16384 * l : k)) • (A ^ 2 * B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 3; at most six monomials. -/
def bandAuxBCDEFG12RestL3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 4096 * l : k)) • (A ^ 2 * B * C * D)
  + (9 / 8192 * l : k) • (A ^ 2 * C ^ 3)
  + (27 / 256 * l : k) • (A ^ 2 * C * G)
  + (-(27 / 1024 * l : k)) • (A ^ 2 * D * F)
  + (81 / 2048 * l : k) • (A ^ 2 * E ^ 2)
  + (-(27 / 4096 * l : k)) • (A * B ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 4; at most six monomials. -/
def bandAuxBCDEFG12RestL4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 2048 * l : k)) • (A * B ^ 2 * C ^ 2)
  + (-(9 / 512 * l : k)) • (A * B ^ 2 * G)
  + (9 / 32 * l : k) • (A * E * G)
  + (-(9 / 128 * l : k)) • (A * F ^ 2)
  + (-(567 / 16384 * l : k)) • (B ^ 4 * C)
  + (27 / 512 * l : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 5; at most six monomials. -/
def bandAuxBCDEFG12RestL5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (-(9 / 64 * l : k)) • (B * D * G)
  + (-(9 / 32 * l : k)) • (B * E * F)
  + (63 / 4096 * l : k) • (C ^ 4)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, l chunk 6; at most six monomials. -/
def bandAuxBCDEFG12RestL6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 128 * l : k)) • (C ^ 2 * G)
  + (-(9 / 32 * l : k)) • (C * D * F)
  + (-(9 / 64 * l : k)) • (C * E ^ 2)
  + (-(9 / 64 * l : k)) • (D ^ 2 * E)
  + (9 / 16 * l : k) • (G ^ 2)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, beta chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestBeta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (315 / 131072 * beta : k) • (A ^ 5 * C)
  + (-(35 / 65536 * beta : k)) • (A ^ 4 * B ^ 2)
  + (35 / 4096 * beta : k) • (A ^ 4 * E)
  + (-(35 / 8192 * beta : k)) • (A ^ 3 * B * D)
  + (175 / 16384 * beta : k) • (A ^ 3 * C ^ 2)
  + (-(7 / 16384 * beta : k)) • (A ^ 2 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, beta chunk 2; at most six monomials. -/
def bandAuxBCDEFG12RestBeta2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 1024 * beta : k) • (A ^ 2 * C * E)
  + (-(21 / 2048 * beta : k)) • (A ^ 2 * D ^ 2)
  + (49 / 32768 * beta : k) • (A * B ^ 4)
  + (-(7 / 1024 * beta : k)) • (A * B ^ 2 * E)
  + (7 / 128 * beta : k) • (A * E ^ 2)
  + (-(7 / 128 * beta : k)) • (B ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, beta chunk 3; at most six monomials. -/
def bandAuxBCDEFG12RestBeta3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(91 / 1024 * beta : k)) • (B ^ 2 * C ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)
  + (7 / 64 * beta : k) • (C * D ^ 2)
  + (-(7 / 16 * beta : k)) • (F ^ 2)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, beta chunk 4; at most six monomials. -/
def bandAuxBCDEFG12RestBeta4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 64 * beta : k)) • (A * D * F)
  + (-(21 / 1024 * beta : k)) • (A ^ 2 * B * F)
  + (35 / 1024 * beta : k) • (A ^ 3 * G)
  + (7 / 32 * beta : k) • (A * C * G)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, gamma chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestGamma1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(27 / 256 * gamma : k)) • (B ^ 3 * C)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  + (-(3 / 4 * gamma : k)) • (E * F)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, delta chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestDelta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 4096 * delta : k) • (A ^ 4 * C)
  + (-(15 / 8192 * delta : k)) • (A ^ 3 * B ^ 2)
  + (15 / 512 * delta : k) • (A ^ 3 * E)
  + (-(15 / 1024 * delta : k)) • (A ^ 2 * B * D)
  + (45 / 2048 * delta : k) • (A ^ 2 * C ^ 2)
  + (-(5 / 1024 * delta : k)) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, delta chunk 2; at most six monomials. -/
def bandAuxBCDEFG12RestDelta2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • (A * C * E)
  + (-(5 / 128 * delta : k)) • (A * D ^ 2)
  + (-(135 / 4096 * delta : k)) • (B ^ 4)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • (C ^ 3)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, delta chunk 3; at most six monomials. -/
def bandAuxBCDEFG12RestDelta3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 8 * delta : k)) • (D * F)
  + (-(5 / 16 * delta : k)) • (E ^ 2)
  + (-(5 / 64 * delta : k)) • (A * B * F)
  + (15 / 128 * delta : k) • (A ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, epsilon chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestEpsilon1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  + (-(1 / 2 * epsilon : k)) • (C * F)
  + (-(1 / 2 * epsilon : k)) • (D * E)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, zeta chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestZeta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 * zeta : k) • (A ^ 3 * C)
  + (-(3 / 512 * zeta : k)) • (A ^ 2 * B ^ 2)
  + (3 / 32 * zeta : k) • (A ^ 2 * E)
  + (-(3 / 64 * zeta : k)) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  + (-(3 / 8 * zeta : k)) • (B * F)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, zeta chunk 2; at most six monomials. -/
def bandAuxBCDEFG12RestZeta2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 8 * zeta : k)) • (C * E)
  + (-(3 / 16 * zeta : k)) • (D ^ 2)
  + (3 / 128 * zeta : k) • (A * C ^ 2)
  + (3 / 8 * zeta : k) • (A * G)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, eta chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestEta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * eta : k) • (B ^ 3)
  + (-(1 / 4 * eta : k)) • (B * E)
  + (-(1 / 4 * eta : k)) • (C * D)

set_option maxHeartbeats 64000000 in
/-- The auxiliary remainder, theta chunk 1; at most six monomials. -/
def bandAuxBCDEFG12RestTheta1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32 * theta : k) • (A ^ 2 * C)
  + (-(1 / 64 * theta : k)) • (A * B ^ 2)
  + (1 / 4 * theta : k) • (A * E)
  + (-(1 / 8 * theta : k)) • (B * D)
  + (-(1 / 16 * theta : k)) • (C ^ 2)
  + (1 / 1 * theta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- The tower auxiliary whose cost-four-s load-free face cancels. -/
def degreeZeroBandAuxBCDEFG12810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (1 / 4 : k) • (A * C * (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G))

set_option maxHeartbeats 64000000 in
/-- The auxiliary with its five pure-A load monomials removed. -/
def bandAuxBCDEFG12Rest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bandAuxBCDEFG12RestFree1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestFree2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestFree3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestL6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestBeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestBeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestBeta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestBeta4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestGamma1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestDelta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestDelta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestDelta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestEpsilon1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestZeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestZeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestEta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bandAuxBCDEFG12RestTheta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- An exact expansion of the auxiliary; the remaining polynomial is grouped into small chunks. -/
theorem degreeZeroBandAuxBCDEFG12810_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticLTowerFace810 l A +
      n7QuarticBetaTowerFace810 beta A +
      n7QuarticDeltaTowerFace810 delta A +
      n7QuarticZetaTowerFace810 zeta A +
      n7QuarticThetaTowerFace810 theta A +
      bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroBandAuxBCDEFG12810,
    degreeZeroN7TowerQuartic810,
    degreeZeroPrimitiveQuartic810,
    rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810,
    rhoGammaGroupQuartic810,
    rhoDeltaGroupQuartic810,
    rhoEpsilonGroupQuartic810,
    rhoZetaGroupQuartic810,
    rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810,
    degreeZeroOmicronQuartic810,
    degreeZeroNuQuartic810,
    degreeZeroKappaQuartic810,
    bandAuxBCDEFG12Rest810,
    bandAuxBCDEFG12RestFree1810,
    bandAuxBCDEFG12RestFree2810,
    bandAuxBCDEFG12RestFree3810,
    bandAuxBCDEFG12RestL1810,
    bandAuxBCDEFG12RestL2810,
    bandAuxBCDEFG12RestL3810,
    bandAuxBCDEFG12RestL4810,
    bandAuxBCDEFG12RestL5810,
    bandAuxBCDEFG12RestL6810,
    bandAuxBCDEFG12RestBeta1810,
    bandAuxBCDEFG12RestBeta2810,
    bandAuxBCDEFG12RestBeta3810,
    bandAuxBCDEFG12RestBeta4810,
    bandAuxBCDEFG12RestGamma1810,
    bandAuxBCDEFG12RestDelta1810,
    bandAuxBCDEFG12RestDelta2810,
    bandAuxBCDEFG12RestDelta3810,
    bandAuxBCDEFG12RestEpsilon1810,
    bandAuxBCDEFG12RestZeta1810,
    bandAuxBCDEFG12RestZeta2810,
    bandAuxBCDEFG12RestEta1810,
    bandAuxBCDEFG12RestTheta1810,
    n7QuarticLTowerFace810,
    n7QuarticBetaTowerFace810,
    n7QuarticDeltaTowerFace810,
    n7QuarticZetaTowerFace810,
    n7QuarticThetaTowerFace810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- The auxiliary retains the degree bound of N7 on this chamber. -/
theorem degreeZeroBandAuxBCDEFG12810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree := by
  have hcone := hc.1
  obtain ⟨ha, hab, hac, had, hae, haf, hag⟩ := hcone
  have hn := degreeZeroN7TowerQuartic810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G
    ha hprim homi hnu hkap
  have hm : ((1 / 4 : k) • (A * C * (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G))).natDegree ≤
      3 * A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have h1 : (A * C * (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤
        (A * C).natDegree + (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    have h2 : (A * C).natDegree ≤ A.natDegree + C.natDegree := natDegree_mul_le
    rw [hkap] at h1
    omega
  exact natDegree_add_le810 hn hm

set_option maxHeartbeats 64000000 in
/-- Every non-pure auxiliary monomial is strictly below the candidate pure load degree, including equality at the old tower face. -/
theorem bandAuxBCDEFG12Rest810_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hd : 5 * A.natDegree + 8 * B.natDegree ≤ 2 * d)
    (hl : l = 0 ∨ 8 * A.natDegree ≤ d)
    (hbeta : beta = 0 ∨ 7 * A.natDegree ≤ d)
    (hdelta : delta = 0 ∨ 6 * A.natDegree ≤ d)
    (hzeta : zeta = 0 ∨ 5 * A.natDegree ≤ d)
    (htheta : theta = 0 ∨ 4 * A.natDegree ≤ d)
    : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  simp only [QuarticChamberBCDEFG12810, QuarticRatioConeA810] at hc
  rcases hc with ⟨⟨ha, hab, hac, had, hae, haf, hag⟩, hB, hC, hD, hE, hF, hG,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22⟩
  have hc0 : (bandAuxBCDEFG12RestFree1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestFree1810]
    compute_degree
    omega
  have hc1 : (bandAuxBCDEFG12RestFree2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestFree2810]
    compute_degree
    omega
  have hc2 : (bandAuxBCDEFG12RestFree3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestFree3810]
    compute_degree
    omega
  have hc3 : (bandAuxBCDEFG12RestL1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL1810]
      compute_degree
      omega
  have hc4 : (bandAuxBCDEFG12RestL2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL2810]
      compute_degree
      omega
  have hc5 : (bandAuxBCDEFG12RestL3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL3810]
      compute_degree
      omega
  have hc6 : (bandAuxBCDEFG12RestL4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL4810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL4810]
      compute_degree
      omega
  have hc7 : (bandAuxBCDEFG12RestL5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL5810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL5810]
      compute_degree
      omega
  have hc8 : (bandAuxBCDEFG12RestL6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hl with hz | hdload
    · simp only [bandAuxBCDEFG12RestL6810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestL6810]
      compute_degree
      omega
  have hc9 : (bandAuxBCDEFG12RestBeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestBeta1810]
      compute_degree
      omega
  have hc10 : (bandAuxBCDEFG12RestBeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestBeta2810]
      compute_degree
      omega
  have hc11 : (bandAuxBCDEFG12RestBeta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestBeta3810]
      compute_degree
      omega
  have hc12 : (bandAuxBCDEFG12RestBeta4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hbeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestBeta4810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestBeta4810]
      compute_degree
      omega
  have hc13 : (bandAuxBCDEFG12RestGamma1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestGamma1810]
    compute_degree
    omega
  have hc14 : (bandAuxBCDEFG12RestDelta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    · simp only [bandAuxBCDEFG12RestDelta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestDelta1810]
      compute_degree
      omega
  have hc15 : (bandAuxBCDEFG12RestDelta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    · simp only [bandAuxBCDEFG12RestDelta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestDelta2810]
      compute_degree
      omega
  have hc16 : (bandAuxBCDEFG12RestDelta3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hdelta with hz | hdload
    · simp only [bandAuxBCDEFG12RestDelta3810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestDelta3810]
      compute_degree
      omega
  have hc17 : (bandAuxBCDEFG12RestEpsilon1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestEpsilon1810]
    compute_degree
    omega
  have hc18 : (bandAuxBCDEFG12RestZeta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hzeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestZeta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestZeta1810]
      compute_degree
      omega
  have hc19 : (bandAuxBCDEFG12RestZeta2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases hzeta with hz | hdload
    · simp only [bandAuxBCDEFG12RestZeta2810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestZeta2810]
      compute_degree
      omega
  have hc20 : (bandAuxBCDEFG12RestEta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    simp only [bandAuxBCDEFG12RestEta1810]
    compute_degree
    omega
  have hc21 : (bandAuxBCDEFG12RestTheta1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
    rcases htheta with hz | hdload
    · simp only [bandAuxBCDEFG12RestTheta1810, hz, mul_zero, zero_mul, zero_smul,
        add_zero, neg_zero, natDegree_zero]
      omega
    · simp only [bandAuxBCDEFG12RestTheta1810]
      compute_degree
      omega
  simp only [bandAuxBCDEFG12Rest810]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc0 hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9) hc10) hc11) hc12) hc13) hc14) hc15) hc16) hc17) hc18) hc19) hc20) hc21)

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills l whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_l_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 11 * A.natDegree)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    l = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 8 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticBetaTowerFace810 beta A + n7QuarticDeltaTowerFace810 delta A + n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 8 * A.natDegree := by
    simp only [S, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticLTowerFace810 l A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    dsimp [S]
    abel
  have hlead : (n7QuarticLTowerFace810 l A).natDegree = 8 * A.natDegree := by
    simp only [n7QuarticLTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills beta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_beta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 9 * A.natDegree)
    (hl0 : l = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    beta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticDeltaTowerFace810 delta A + n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 7 * A.natDegree := by
    simp only [S, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticBetaTowerFace810 beta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, n7QuarticLTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticBetaTowerFace810 beta A).natDegree = 7 * A.natDegree := by
    simp only [n7QuarticBetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills delta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_delta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 7 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    delta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticZetaTowerFace810 zeta A + n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 6 * A.natDegree := by
    simp only [S, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticDeltaTowerFace810 delta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticDeltaTowerFace810 delta A).natDegree = 6 * A.natDegree := by
    simp only [n7QuarticDeltaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills zeta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_zeta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 5 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    zeta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inl hdelta0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let S : k[X] := n7QuarticThetaTowerFace810 theta A
  have hs : S.natDegree < 5 * A.natDegree := by
    simp only [S, n7QuarticThetaTowerFace810]
    compute_degree
    omega
  have hrem := natDegree_add_lt810 hs hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticZetaTowerFace810 zeta A +
      (S + bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, hdelta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
    dsimp [S]
    abel
  have hlead : (n7QuarticZetaTowerFace810 zeta A).natDegree = 5 * A.natDegree := by
    simp only [n7QuarticZetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- The auxiliary kills theta whenever its pure-A term reaches the old tower face. -/
theorem quarticBCDEFG12_theta_eq_zero_of_low810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hband : 8 * B.natDegree ≤ 3 * A.natDegree)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (hzeta0 : zeta = 0)
    (haux : (degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree) :
    theta = 0 := by
  have ha := hc.1.1
  by_contra hne
  have hrest : (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
    apply bandAuxBCDEFG12Rest810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc (by omega)
    · exact Or.inl hl0
    · exact Or.inl hbeta0
    · exact Or.inl hdelta0
    · exact Or.inl hzeta0
    · exact Or.inr (by omega)
  have hrem := hrest
  have heq : degreeZeroBandAuxBCDEFG12810 l beta gamma delta epsilon zeta eta theta A B C D E F G = n7QuarticThetaTowerFace810 theta A +
      (bandAuxBCDEFG12Rest810 l beta gamma delta epsilon zeta eta theta A B C D E F G) := by
    rw [degreeZeroBandAuxBCDEFG12810_split]
    simp only [hl0, hbeta0, hdelta0, hzeta0, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, mul_zero, zero_smul, zero_add, add_zero]
  have hlead : (n7QuarticThetaTowerFace810 theta A).natDegree = 4 * A.natDegree := by
    simp only [n7QuarticThetaTowerFace810]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hne), natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at haux
  omega

set_option maxHeartbeats 64000000 in
/-- Strict bands for all five pure-A loads throughout the maximal-tie chamber. -/
theorem quarticBCDEFG12_loadBands810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) ∧
    (beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) ∧
    (delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) ∧
    (zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree) ∧
    (theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) := by
  have haux := degreeZeroBandAuxBCDEFG12810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G
    hc hprim homi hnu hkap
  have hl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 11 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      exact quarticBCDEFG12_l_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) haux
  have hbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 9 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      exact quarticBCDEFG12_beta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 haux
  have hdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 7 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      have hbeta0 : beta = 0 := by
        rcases hbeta with hz | hh
        · exact hz
        · omega
      exact quarticBCDEFG12_delta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 hbeta0 haux
  have hzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 5 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      have hbeta0 : beta = 0 := by
        rcases hbeta with hz | hh
        · exact hz
        · omega
      have hdelta0 : delta = 0 := by
        rcases hdelta with hz | hh
        · exact hz
        · omega
      exact quarticBCDEFG12_zeta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 hbeta0 hdelta0 haux
  have htheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree := by
    by_cases hhigh : 3 * A.natDegree < 8 * B.natDegree
    · exact Or.inr hhigh
    · apply Or.inl
      have hl0 : l = 0 := by
        rcases hl with hz | hh
        · exact hz
        · omega
      have hbeta0 : beta = 0 := by
        rcases hbeta with hz | hh
        · exact hz
        · omega
      have hdelta0 : delta = 0 := by
        rcases hdelta with hz | hh
        · exact hz
        · omega
      have hzeta0 : zeta = 0 := by
        rcases hzeta with hz | hh
        · exact hz
        · omega
      exact quarticBCDEFG12_theta_eq_zero_of_low810 l beta gamma delta epsilon zeta eta theta A B C D E F G
        hc (by omega) hl0 hbeta0 hdelta0 hzeta0 haux
  exact ⟨hl, hbeta, hdelta, hzeta, htheta⟩

set_option maxHeartbeats 64000000 in
/-- The load-free top polynomial on BCDEFG12. -/
def bcdefg12KappaFace810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3) +
    (-15 / 128 : k) • (B * C ^ 2) +
    (5 / 16 : k) • (B * G) +
    (5 / 16 : k) • (C * F) +
    (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12KappaRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-15 / 128 : k) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12KappaRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * l : k) • (A ^ 5) +
    (45 / 8192 * l : k) • (A ^ 3 * C) +
    (-9 / 16384 * l : k) • (A ^ 2 * B ^ 2) +
    (27 / 1024 * l : k) • (A ^ 2 * E) +
    (-9 / 512 * l : k) • (A * B * D) +
    (9 / 1024 * l : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def bcdefg12KappaRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 64 * l : k) • (A * G) +
    (-63 / 1024 * l : k) • (B ^ 2 * C) +
    (9 / 64 * l : k) • (B * F) +
    (9 / 64 * l : k) • (C * E) +
    (9 / 128 * l : k) • (D ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12KappaRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * beta : k) • (A ^ 4) +
    (21 / 1024 * beta : k) • (A ^ 2 * C) +
    (7 / 1024 * beta : k) • (A * B ^ 2) +
    (7 / 64 * beta : k) • (A * E) +
    (-7 / 64 * beta : k) • (B * D) +
    (-7 / 128 * beta : k) • (C ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12KappaRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 8 * beta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12KappaRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 16 * gamma : k) • (B * C) +
    (3 / 4 * gamma : k) • (F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12KappaRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 1024 * delta : k) • (A ^ 3) +
    (5 / 64 * delta : k) • (A * C) +
    (-15 / 128 * delta : k) • (B ^ 2) +
    (5 / 8 * delta : k) • (E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12KappaRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 2 * epsilon : k) • (D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12KappaRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * zeta : k) • (A ^ 2) +
    (3 / 8 * zeta : k) • (C)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12KappaRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • (B)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12KappaRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • (A)

set_option maxHeartbeats 64000000 in
/-- The remainder after the chamber face. -/
def bcdefg12KappaRest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12KappaRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12KappaRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The integral splits into its chamber face and remainder. -/
theorem bcdefg12Kappa_split810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12KappaFace810 A B C D E F G + bcdefg12KappaRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, bcdefg12KappaFace810, bcdefg12KappaRest810, bcdefg12KappaRest0810, bcdefg12KappaRest1810, bcdefg12KappaRest2810, bcdefg12KappaRest3810, bcdefg12KappaRest4810, bcdefg12KappaRest5810, bcdefg12KappaRest6810, bcdefg12KappaRest7810, bcdefg12KappaRest8810, bcdefg12KappaRest9810, bcdefg12KappaRest10810]
  module

set_option maxHeartbeats 64000000 in
/-- All remainder chunks lie strictly below the face under the strict load bands. -/
theorem bcdefg12Kappa_rest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12KappaRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hr0 : (bcdefg12KappaRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    simp only [bcdefg12KappaRest0810]
    compute_degree
    omega
  have hr1 : (bcdefg12KappaRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12KappaRest1810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest1810]
      compute_degree
      omega
  have hr2 : (bcdefg12KappaRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12KappaRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest2810]
      compute_degree
      omega
  have hr3 : (bcdefg12KappaRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12KappaRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest3810]
      compute_degree
      omega
  have hr4 : (bcdefg12KappaRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12KappaRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest4810]
      compute_degree
      omega
  have hr5 : (bcdefg12KappaRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    simp only [bcdefg12KappaRest5810]
    compute_degree
    omega
  have hr6 : (bcdefg12KappaRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbdelta with hz | hb
    · simp only [bcdefg12KappaRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest6810]
      compute_degree
      omega
  have hr7 : (bcdefg12KappaRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    simp only [bcdefg12KappaRest7810]
    compute_degree
    omega
  have hr8 : (bcdefg12KappaRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbzeta with hz | hb
    · simp only [bcdefg12KappaRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest8810]
      compute_degree
      omega
  have hr9 : (bcdefg12KappaRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    simp only [bcdefg12KappaRest9810]
    compute_degree
    omega
  have hr10 : (bcdefg12KappaRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree := by
    rcases hbtheta with hz | hb
    · simp only [bcdefg12KappaRest10810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12KappaRest10810]
      compute_degree
      omega
  unfold bcdefg12KappaRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10)

set_option maxHeartbeats 64000000 in
/-- Coefficient of the chamber face at its common monomial degree. -/
theorem bcdefg12Kappa_face_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12KappaFace810 A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) =
      (5 / 512 : k) * kappaQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A * B ^ 3).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm0 : (A * B ^ 3).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (B * C ^ 2).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm1 : (B * C ^ 2).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (B * G).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm2 : (B * G).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C * F).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm3 : (C * F).coeff (A.natDegree + 3 * B.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (D * E).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne hEne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm4 : (D * E).coeff (A.natDegree + 3 * B.natDegree) = D.leadingCoeff * E.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12KappaFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, hm4, kappaQuarticOpenIIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar chamber face vanishes, using the full constant-integral hypothesis. -/
theorem bcdefg12KappaFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    kappaQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := bcdefg12Kappa_rest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta
  have ht := bcdefg12Kappa_face_coeff810 A B C D E F G hc
  have hd : 0 < A.natDegree + 3 * B.natDegree := by
    obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
    obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < A.natDegree + 3 * B.natDegree by omega)
  rw [bcdefg12Kappa_split810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

set_option maxHeartbeats 64000000 in
/-- The load-free top polynomial on BCDEFG12. -/
def bcdefg12MuFace810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C) +
    (-5 / 64 : k) • (A * B * F) +
    (-5 / 128 : k) • (A * D ^ 2) +
    (-5 / 128 : k) • (C ^ 3) +
    (5 / 16 : k) • (C * G) +
    (5 / 32 : k) • (E ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12MuRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • (B ^ 4) +
    (-15 / 128 : k) • (B ^ 2 * E) +
    (-15 / 64 : k) • (B * C * D) +
    (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12MuRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-45 / 262144 * l : k) • (A ^ 4 * B) +
    (-9 / 8192 * l : k) • (A ^ 3 * D) +
    (-9 / 8192 * l : k) • (A ^ 2 * B * C) +
    (-9 / 1024 * l : k) • (A ^ 2 * F) +
    (63 / 8192 * l : k) • (A * B ^ 3) +
    (-9 / 512 * l : k) • (A * B * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12MuRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-9 / 512 * l : k) • (A * C * D) +
    (-63 / 1024 * l : k) • (B ^ 2 * D) +
    (-63 / 1024 * l : k) • (B * C ^ 2) +
    (9 / 64 * l : k) • (B * G) +
    (9 / 64 * l : k) • (C * F) +
    (9 / 64 * l : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12MuRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 8192 * beta : k) • (A ^ 3 * B) +
    (-7 / 1024 * beta : k) • (A ^ 2 * D) +
    (7 / 512 * beta : k) • (A * B * C) +
    (-7 / 64 * beta : k) • (A * F) +
    (21 / 1024 * beta : k) • (B ^ 3) +
    (-7 / 64 * beta : k) • (B * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12MuRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 64 * beta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12MuRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * gamma : k) • (A * B ^ 2) +
    (-3 / 16 * gamma : k) • (B * D) +
    (-3 / 32 * gamma : k) • (C ^ 2) +
    (3 / 4 * gamma : k) • (G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12MuRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 1024 * delta : k) • (A ^ 2 * B) +
    (-5 / 64 * delta : k) • (A * D) +
    (-15 / 64 * delta : k) • (B * C) +
    (5 / 8 * delta : k) • (F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12MuRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 8 * epsilon : k) • (B ^ 2) +
    (1 / 2 * epsilon : k) • (E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12MuRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 64 * zeta : k) • (A * B) +
    (3 / 8 * zeta : k) • (D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12MuRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • (C)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12MuRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • (B)

set_option maxHeartbeats 64000000 in
/-- The remainder after the chamber face. -/
def bcdefg12MuRest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12MuRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12MuRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The integral splits into its chamber face and remainder. -/
theorem bcdefg12Mu_split810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12MuFace810 A B C D E F G + bcdefg12MuRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroMuQuartic810, bcdefg12MuFace810, bcdefg12MuRest810, bcdefg12MuRest0810, bcdefg12MuRest1810, bcdefg12MuRest2810, bcdefg12MuRest3810, bcdefg12MuRest4810, bcdefg12MuRest5810, bcdefg12MuRest6810, bcdefg12MuRest7810, bcdefg12MuRest8810, bcdefg12MuRest9810, bcdefg12MuRest10810]
  module

set_option maxHeartbeats 64000000 in
/-- All remainder chunks lie strictly below the face under the strict load bands. -/
theorem bcdefg12Mu_rest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12MuRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hr0 : (bcdefg12MuRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    simp only [bcdefg12MuRest0810]
    compute_degree
    omega
  have hr1 : (bcdefg12MuRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12MuRest1810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12MuRest1810]
      compute_degree
      omega
  have hr2 : (bcdefg12MuRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12MuRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12MuRest2810]
      compute_degree
      omega
  have hr3 : (bcdefg12MuRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12MuRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12MuRest3810]
      compute_degree
      omega
  have hr4 : (bcdefg12MuRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12MuRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12MuRest4810]
      compute_degree
      omega
  have hr5 : (bcdefg12MuRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    simp only [bcdefg12MuRest5810]
    compute_degree
    omega
  have hr6 : (bcdefg12MuRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbdelta with hz | hb
    · simp only [bcdefg12MuRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12MuRest6810]
      compute_degree
      omega
  have hr7 : (bcdefg12MuRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    simp only [bcdefg12MuRest7810]
    compute_degree
    omega
  have hr8 : (bcdefg12MuRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbzeta with hz | hb
    · simp only [bcdefg12MuRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12MuRest8810]
      compute_degree
      omega
  have hr9 : (bcdefg12MuRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    simp only [bcdefg12MuRest9810]
    compute_degree
    omega
  have hr10 : (bcdefg12MuRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree := by
    rcases hbtheta with hz | hb
    · simp only [bcdefg12MuRest10810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12MuRest10810]
      compute_degree
      omega
  unfold bcdefg12MuRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10)

set_option maxHeartbeats 64000000 in
/-- Coefficient of the chamber face at its common monomial degree. -/
theorem bcdefg12Mu_face_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12MuFace810 A B C D E F G).coeff (3 * C.natDegree) =
      (5 / 512 : k) * muQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A * B ^ 2 * C).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm0 : (A * B ^ 2 * C).coeff (3 * C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A * B * F).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm1 : (A * B * F).coeff (3 * C.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (A * D ^ 2).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm2 : (A * D ^ 2).coeff (3 * C.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C ^ 3).natDegree = 3 * C.natDegree := by
    rw [natDegree_pow] <;> omega
  have hm3 : (C ^ 3).coeff (3 * C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (C * G).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hCne hGne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm4 : (C * G).coeff (3 * C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : (E ^ 2).natDegree = 3 * C.natDegree := by
    rw [natDegree_pow] <;> omega
  have hm5 : (E ^ 2).coeff (3 * C.natDegree) = E.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12MuFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, hm4, hm5, muQuarticOpenIIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar chamber face vanishes, using the full constant-integral hypothesis. -/
theorem bcdefg12MuFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    muQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := bcdefg12Mu_rest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta
  have ht := bcdefg12Mu_face_coeff810 A B C D E F G hc
  have hd : 0 < 3 * C.natDegree := by
    obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
    obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 3 * C.natDegree by omega)
  rw [bcdefg12Mu_split810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

set_option maxHeartbeats 64000000 in
/-- The load-free top polynomial on BCDEFG12. -/
def bcdefg12XiFace810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E) +
    (15 / 256 : k) • (A * B * C * D) +
    (-5 / 64 : k) • (A * D * F) +
    (-15 / 128 : k) • (C ^ 2 * E) +
    (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12XiRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-15 / 2048 : k) • (A * B ^ 4) +
    (55 / 1024 : k) • (B ^ 3 * D) +
    (45 / 512 : k) • (B ^ 2 * C ^ 2) +
    (-5 / 64 : k) • (B ^ 2 * G) +
    (-25 / 128 : k) • (B * C * F) +
    (-25 / 128 : k) • (B * D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12XiRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-15 / 128 : k) • (C * D ^ 2) +
    (5 / 32 : k) • (F ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12XiRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-45 / 262144 * l : k) • (A ^ 4 * D) +
    (9 / 16384 * l : k) • (A ^ 3 * B * C) +
    (-9 / 8192 * l : k) • (A ^ 3 * F) +
    (-9 / 16384 * l : k) • (A ^ 2 * B ^ 3) +
    (9 / 4096 * l : k) • (A ^ 2 * B * E) +
    (-9 / 8192 * l : k) • (A ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12XiRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (171 / 8192 * l : k) • (A * B ^ 2 * D) +
    (9 / 1024 * l : k) • (A * B * C ^ 2) +
    (-9 / 512 * l : k) • (A * C * F) +
    (-9 / 512 * l : k) • (A * D * E) +
    (63 / 2048 * l : k) • (B ^ 3 * C) +
    (-45 / 1024 * l : k) • (B ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def bcdefg12XiRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-27 / 256 * l : k) • (B * C * E) +
    (-27 / 512 * l : k) • (B * D ^ 2) +
    (-63 / 1024 * l : k) • (C ^ 2 * D) +
    (9 / 64 * l : k) • (D * G) +
    (9 / 64 * l : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12XiRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 8192 * beta : k) • (A ^ 3 * D) +
    (7 / 2048 * beta : k) • (A ^ 2 * B * C) +
    (-7 / 1024 * beta : k) • (A ^ 2 * F) +
    (-7 / 1024 * beta : k) • (A * B ^ 3) +
    (7 / 256 * beta : k) • (A * B * E) +
    (7 / 512 * beta : k) • (A * C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12XiRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (49 / 1024 * beta : k) • (B ^ 2 * D) +
    (7 / 128 * beta : k) • (B * C ^ 2) +
    (-7 / 64 * beta : k) • (C * F) +
    (-7 / 64 * beta : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def bcdefg12XiRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * gamma : k) • (A * B * D) +
    (3 / 32 * gamma : k) • (B ^ 2 * C) +
    (-3 / 32 * gamma : k) • (B * F) +
    (-3 / 16 * gamma : k) • (C * E) +
    (-3 / 32 * gamma : k) • (D ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12XiRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 1024 * delta : k) • (A ^ 2 * D) +
    (5 / 128 * delta : k) • (A * B * C) +
    (-5 / 64 * delta : k) • (A * F) +
    (5 / 128 * delta : k) • (B ^ 3) +
    (-5 / 32 * delta : k) • (B * E) +
    (-15 / 64 * delta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12XiRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 32 * epsilon : k) • (A * B ^ 2) +
    (-3 / 16 * epsilon : k) • (B * D) +
    (-1 / 8 * epsilon : k) • (C ^ 2) +
    (1 / 2 * epsilon : k) • (G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 3 monomials. -/
def bcdefg12XiRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 64 * zeta : k) • (A * D) +
    (-3 / 16 * zeta : k) • (B * C) +
    (3 / 8 * zeta : k) • (F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12XiRest11810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 16 * eta : k) • (B ^ 2) +
    (1 / 4 * eta : k) • (E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 1 monomial. -/
def bcdefg12XiRest12810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • (D)

set_option maxHeartbeats 64000000 in
/-- The remainder after the chamber face. -/
def bcdefg12XiRest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12XiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12XiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The integral splits into its chamber face and remainder. -/
theorem bcdefg12Xi_split810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12XiFace810 A B C D E F G + bcdefg12XiRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroXiQuartic810, bcdefg12XiFace810, bcdefg12XiRest810, bcdefg12XiRest0810, bcdefg12XiRest1810, bcdefg12XiRest2810, bcdefg12XiRest3810, bcdefg12XiRest4810, bcdefg12XiRest5810, bcdefg12XiRest6810, bcdefg12XiRest7810, bcdefg12XiRest8810, bcdefg12XiRest9810, bcdefg12XiRest10810, bcdefg12XiRest11810, bcdefg12XiRest12810]
  module

set_option maxHeartbeats 64000000 in
/-- All remainder chunks lie strictly below the face under the strict load bands. -/
theorem bcdefg12Xi_rest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12XiRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hr0 : (bcdefg12XiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    simp only [bcdefg12XiRest0810]
    compute_degree
    omega
  have hr1 : (bcdefg12XiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    simp only [bcdefg12XiRest1810]
    compute_degree
    omega
  have hr2 : (bcdefg12XiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12XiRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest2810]
      compute_degree
      omega
  have hr3 : (bcdefg12XiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12XiRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest3810]
      compute_degree
      omega
  have hr4 : (bcdefg12XiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12XiRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest4810]
      compute_degree
      omega
  have hr5 : (bcdefg12XiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12XiRest5810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest5810]
      compute_degree
      omega
  have hr6 : (bcdefg12XiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12XiRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest6810]
      compute_degree
      omega
  have hr7 : (bcdefg12XiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    simp only [bcdefg12XiRest7810]
    compute_degree
    omega
  have hr8 : (bcdefg12XiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbdelta with hz | hb
    · simp only [bcdefg12XiRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest8810]
      compute_degree
      omega
  have hr9 : (bcdefg12XiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    simp only [bcdefg12XiRest9810]
    compute_degree
    omega
  have hr10 : (bcdefg12XiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbzeta with hz | hb
    · simp only [bcdefg12XiRest10810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest10810]
      compute_degree
      omega
  have hr11 : (bcdefg12XiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    simp only [bcdefg12XiRest11810]
    compute_degree
    omega
  have hr12 : (bcdefg12XiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree := by
    rcases hbtheta with hz | hb
    · simp only [bcdefg12XiRest12810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12XiRest12810]
      compute_degree
      omega
  unfold bcdefg12XiRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10) hr11) hr12)

set_option maxHeartbeats 64000000 in
/-- Coefficient of the chamber face at its common monomial degree. -/
theorem bcdefg12Xi_face_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12XiFace810 A B C D E F G).coeff (E.natDegree + G.natDegree) =
      (5 / 512 : k) * xiQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A * B ^ 2 * E).natDegree = E.natDegree + G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm0 : (A * B ^ 2 * E).coeff (E.natDegree + G.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A * B * C * D).natDegree = E.natDegree + G.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm1 : (A * B * C * D).coeff (E.natDegree + G.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (A * D * F).natDegree = E.natDegree + G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm2 : (A * D * F).coeff (E.natDegree + G.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C ^ 2 * E).natDegree = E.natDegree + G.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm3 : (C ^ 2 * E).coeff (E.natDegree + G.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (E * G).natDegree = E.natDegree + G.natDegree := by
    rw [natDegree_mul hEne hGne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm4 : (E * G).coeff (E.natDegree + G.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12XiFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, hm4, xiQuarticOpenIIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar chamber face vanishes, using the full constant-integral hypothesis. -/
theorem bcdefg12XiFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    xiQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := bcdefg12Xi_rest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta
  have ht := bcdefg12Xi_face_coeff810 A B C D E F G hc
  have hd : 0 < E.natDegree + G.natDegree := by
    obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
    obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < E.natDegree + G.natDegree by omega)
  rw [bcdefg12Xi_split810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

set_option maxHeartbeats 64000000 in
/-- The load-free top polynomial on BCDEFG12. -/
def bcdefg12PiFace810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4) +
    (-45 / 512 : k) • (A * B ^ 2 * C ^ 2) +
    (5 / 64 : k) • (A * B ^ 2 * G) +
    (5 / 32 : k) • (A * B * C * F) +
    (5 / 16 : k) • (A * B * D * E) +
    (5 / 32 : k) • (A * C * D ^ 2) +
    (-5 / 16 : k) • (A * F ^ 2) +
    (15 / 256 : k) • (C ^ 4) +
    (-5 / 16 : k) • (C ^ 2 * G) +
    (-5 / 8 : k) • (C * E ^ 2) +
    (5 / 4 : k) • (G ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest0810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-15 / 128 : k) • (A * B ^ 3 * D) +
    (-35 / 256 : k) • (B ^ 4 * C) +
    (25 / 128 : k) • (B ^ 3 * F) +
    (45 / 64 : k) • (B ^ 2 * C * E) +
    (45 / 128 : k) • (B ^ 2 * D ^ 2) +
    (45 / 64 : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12PiRest1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 8 : k) • (B * D * G) +
    (-15 / 16 : k) • (B * E * F) +
    (-15 / 16 : k) • (C * D * F) +
    (-5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 131072 * l : k) • (A ^ 4 * B * C) +
    (-45 / 32768 * l : k) • (A ^ 4 * F) +
    (-3 / 32768 * l : k) • (A ^ 3 * B ^ 3) +
    (9 / 4096 * l : k) • (A ^ 3 * B * E) +
    (9 / 4096 * l : k) • (A ^ 3 * C * D) +
    (-27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2) +
    (-27 / 1024 * l : k) • (A ^ 2 * C * F) +
    (9 / 512 * l : k) • (A ^ 2 * D * E) +
    (-189 / 4096 * l : k) • (A * B ^ 3 * C) +
    (63 / 1024 * l : k) • (A * B ^ 2 * F) +
    (9 / 128 * l : k) • (A * B * C * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 256 * l : k) • (A * B * D ^ 2) +
    (9 / 256 * l : k) • (A * C ^ 2 * D) +
    (-9 / 64 * l : k) • (A * E * F) +
    (-63 / 4096 * l : k) • (B ^ 5) +
    (63 / 512 * l : k) • (B ^ 3 * E) +
    (189 / 512 * l : k) • (B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 512 * l : k) • (B * C ^ 3) +
    (-9 / 32 * l : k) • (B * C * G) +
    (-27 / 64 * l : k) • (B * D * F) +
    (-9 / 32 * l : k) • (B * E ^ 2) +
    (-27 / 128 * l : k) • (C ^ 2 * F) +
    (-9 / 16 * l : k) • (C * D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12PiRest6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 32 * l : k) • (D ^ 3) +
    (9 / 8 * l : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 4096 * beta : k) • (A ^ 3 * B * C) +
    (-7 / 1024 * beta : k) • (A ^ 3 * F) +
    (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3) +
    (7 / 512 * beta : k) • (A ^ 2 * B * E) +
    (7 / 512 * beta : k) • (A ^ 2 * C * D) +
    (-21 / 256 * beta : k) • (A * B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest8810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 256 * beta : k) • (A * B * C ^ 2) +
    (-7 / 64 * beta : k) • (A * C * F) +
    (7 / 32 * beta : k) • (A * D * E) +
    (-63 / 512 * beta : k) • (B ^ 3 * C) +
    (21 / 128 * beta : k) • (B ^ 2 * F) +
    (7 / 16 * beta : k) • (B * C * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 3 monomials. -/
def bcdefg12PiRest9810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 32 * beta : k) • (B * D ^ 2) +
    (7 / 32 * beta : k) • (C ^ 2 * D) +
    (-7 / 8 * beta : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest10810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 32 * gamma : k) • (A * B ^ 2 * C) +
    (3 / 16 * gamma : k) • (A * D ^ 2) +
    (-15 / 256 * gamma : k) • (B ^ 4) +
    (3 / 8 * gamma : k) • (B ^ 2 * E) +
    (3 / 4 * gamma : k) • (B * C * D) +
    (1 / 8 * gamma : k) • (C ^ 3)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12PiRest11810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 4 * gamma : k) • (D * F) +
    (-3 / 4 * gamma : k) • (E ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 6 monomials. -/
def bcdefg12PiRest12810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 * delta : k) • (A ^ 2 * B * C) +
    (-5 / 128 * delta : k) • (A ^ 2 * F) +
    (-15 / 256 * delta : k) • (A * B ^ 3) +
    (5 / 32 * delta : k) • (A * B * E) +
    (5 / 32 * delta : k) • (A * C * D) +
    (15 / 32 * delta : k) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 3 monomials. -/
def bcdefg12PiRest13810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 32 * delta : k) • (B * C ^ 2) +
    (-5 / 8 * delta : k) • (C * F) +
    (-5 / 4 * delta : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def bcdefg12PiRest14810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * epsilon : k) • (A * B * D) +
    (1 / 2 * epsilon : k) • (B ^ 2 * C) +
    (-1 / 2 * epsilon : k) • (B * F) +
    (-1 * epsilon : k) • (C * E) +
    (-1 / 2 * epsilon : k) • (D ^ 2)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 5 monomials. -/
def bcdefg12PiRest15810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32 * zeta : k) • (A * B * C) +
    (-3 / 8 * zeta : k) • (A * F) +
    (5 / 32 * zeta : k) • (B ^ 3) +
    (-3 / 4 * zeta : k) • (B * E) +
    (-3 / 4 * zeta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 4 monomials. -/
def bcdefg12PiRest16810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 16 * eta : k) • (A * B ^ 2) +
    (-1 / 2 * eta : k) • (B * D) +
    (-1 / 4 * eta : k) • (C ^ 2) +
    (2 * eta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- A remainder chunk with 2 monomials. -/
def bcdefg12PiRest17810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 4 * theta : k) • (B * C) +
    (1 * theta : k) • (F)

set_option maxHeartbeats 64000000 in
/-- The remainder after the chamber face. -/
def bcdefg12PiRest810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12PiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest13810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest14810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest15810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest16810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12PiRest17810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- The integral splits into its chamber face and remainder. -/
theorem bcdefg12Pi_split810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12PiFace810 A B C D E F G + bcdefg12PiRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroPiQuartic810, bcdefg12PiFace810, bcdefg12PiRest810, bcdefg12PiRest0810, bcdefg12PiRest1810, bcdefg12PiRest2810, bcdefg12PiRest3810, bcdefg12PiRest4810, bcdefg12PiRest5810, bcdefg12PiRest6810, bcdefg12PiRest7810, bcdefg12PiRest8810, bcdefg12PiRest9810, bcdefg12PiRest10810, bcdefg12PiRest11810, bcdefg12PiRest12810, bcdefg12PiRest13810, bcdefg12PiRest14810, bcdefg12PiRest15810, bcdefg12PiRest16810, bcdefg12PiRest17810, piBaseGroupQuartic810, piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810, piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810, piThetaGroupQuartic810]
  module

set_option maxHeartbeats 64000000 in
/-- All remainder chunks lie strictly below the face under the strict load bands. -/
theorem bcdefg12Pi_rest_lt810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12PiRest810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hr0 : (bcdefg12PiRest0810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    simp only [bcdefg12PiRest0810]
    compute_degree
    omega
  have hr1 : (bcdefg12PiRest1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    simp only [bcdefg12PiRest1810]
    compute_degree
    omega
  have hr2 : (bcdefg12PiRest2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12PiRest2810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest2810]
      compute_degree
      omega
  have hr3 : (bcdefg12PiRest3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12PiRest3810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest3810]
      compute_degree
      omega
  have hr4 : (bcdefg12PiRest4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12PiRest4810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest4810]
      compute_degree
      omega
  have hr5 : (bcdefg12PiRest5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12PiRest5810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest5810]
      compute_degree
      omega
  have hr6 : (bcdefg12PiRest6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbl with hz | hb
    · simp only [bcdefg12PiRest6810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest6810]
      compute_degree
      omega
  have hr7 : (bcdefg12PiRest7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12PiRest7810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest7810]
      compute_degree
      omega
  have hr8 : (bcdefg12PiRest8810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12PiRest8810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest8810]
      compute_degree
      omega
  have hr9 : (bcdefg12PiRest9810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbbeta with hz | hb
    · simp only [bcdefg12PiRest9810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest9810]
      compute_degree
      omega
  have hr10 : (bcdefg12PiRest10810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    simp only [bcdefg12PiRest10810]
    compute_degree
    omega
  have hr11 : (bcdefg12PiRest11810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    simp only [bcdefg12PiRest11810]
    compute_degree
    omega
  have hr12 : (bcdefg12PiRest12810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbdelta with hz | hb
    · simp only [bcdefg12PiRest12810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest12810]
      compute_degree
      omega
  have hr13 : (bcdefg12PiRest13810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbdelta with hz | hb
    · simp only [bcdefg12PiRest13810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest13810]
      compute_degree
      omega
  have hr14 : (bcdefg12PiRest14810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    simp only [bcdefg12PiRest14810]
    compute_degree
    omega
  have hr15 : (bcdefg12PiRest15810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbzeta with hz | hb
    · simp only [bcdefg12PiRest15810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest15810]
      compute_degree
      omega
  have hr16 : (bcdefg12PiRest16810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    simp only [bcdefg12PiRest16810]
    compute_degree
    omega
  have hr17 : (bcdefg12PiRest17810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree := by
    rcases hbtheta with hz | hb
    · simp only [bcdefg12PiRest17810, hz, mul_zero, zero_smul, add_zero, natDegree_zero]
      omega
    · simp only [bcdefg12PiRest17810]
      compute_degree
      omega
  unfold bcdefg12PiRest810
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hr1) hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9) hr10) hr11) hr12) hr13) hr14) hr15) hr16) hr17)

set_option maxHeartbeats 64000000 in
/-- Coefficient of the chamber face at its common monomial degree. -/
theorem bcdefg12Pi_face_coeff810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12PiFace810 A B C D E F G).coeff (2 * G.natDegree) =
      (5 / 4096 : k) * piQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  have hd0 : (A ^ 2 * B ^ 4).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm0 : (A ^ 2 * B ^ 4).coeff (2 * G.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A * B ^ 2 * C ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm1 : (A * B ^ 2 * C ^ 2).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (A * B ^ 2 * G).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm2 : (A * B ^ 2 * G).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (A * B * C * F).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm3 : (A * B * C * F).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (A * B * D * E).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne] <;> (try simp only [natDegree_pow]) <;> omega
  have hm4 : (A * B * D * E).coeff (2 * G.natDegree) = A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : (A * C * D ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne, natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm5 : (A * C * D ^ 2).coeff (2 * G.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd6 : (A * F ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm6 : (A * F ^ 2).coeff (2 * G.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd6, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd7 : (C ^ 4).natDegree = 2 * G.natDegree := by
    rw [natDegree_pow] <;> omega
  have hm7 : (C ^ 4).coeff (2 * G.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd7, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd8 : (C ^ 2 * G).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm8 : (C ^ 2 * G).coeff (2 * G.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd8, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd9 : (C * E ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow] <;> (try simp only [natDegree_pow]) <;> omega
  have hm9 : (C * E ^ 2).coeff (2 * G.natDegree) = C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hd9, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd10 : (G ^ 2).natDegree = 2 * G.natDegree := by
    rw [natDegree_pow] <;> omega
  have hm10 : (G ^ 2).coeff (2 * G.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd10, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12PiFace810, coeff_add, coeff_smul, smul_eq_mul, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, piQuarticOpenIIFace810]
  ring

set_option maxHeartbeats 64000000 in
/-- The scalar chamber face vanishes, using the full constant-integral hypothesis. -/
theorem bcdefg12PiFace_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbl : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbbeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbdelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbzeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbtheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    piQuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hr := bcdefg12Pi_rest_lt810 l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta
  have ht := bcdefg12Pi_face_coeff810 A B C D E F G hc
  have hd : 0 < 2 * G.natDegree := by
    obtain ⟨hcone, hBne, hCne, hDne, hEne, hFne, hGne, heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt8, hlt9, hlt10, hlt11, hlt12⟩ := hc
    obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := hcone
    omega
  have hh := coeff_eq_zero_of_natDegree_lt (show (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 2 * G.natDegree by omega)
  rw [bcdefg12Pi_split810, coeff_add, coeff_eq_zero_of_natDegree_lt hr, add_zero, ht] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

set_option maxHeartbeats 64000000 in
/-- The polynomial face of N2 on BCDEFG12. -/
def bcdefg12N2Face
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (-15 / 64 : k) • (B * C * E)
  + (-15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestLF0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 512 : k) • (B ^ 3 * C)
  + (-15 / 128 : k) • (B ^ 2 * F)
  + (-15 / 128 : k) • (B * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestLF0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2RestLF0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N2RestLF0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestL0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * l : k) • (A ^ 6)
  + (315 / 262144 * l : k) • (A ^ 4 * C)
  + (45 / 8192 * l : k) • (A ^ 3 * E)
  + (-9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 8192 * l : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestL0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestL0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N2RestL0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestL0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestL1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (315 / 32768 * l : k) • (B ^ 4)
  + (27 / 1024 * l : k) • (A ^ 2 * G)
  + (-9 / 512 * l : k) • (A * B * F)
  + (-9 / 1024 * l : k) • (A * D ^ 2)
  + (-63 / 1024 * l : k) • (B ^ 2 * E)
  + (-63 / 512 * l : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestL1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestL1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N2RestL1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestL1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestL2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-21 / 1024 * l : k) • (C ^ 3)
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • (E ^ 2)
  + (-9 / 131072 * l : k) • (A ^ 3 * B ^ 2)
  + (9 / 512 * l : k) • (A * C * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestL2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestL2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N2RestL2, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestL2]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestBeta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * beta : k) • (A ^ 5)
  + (35 / 8192 * beta : k) • (A ^ 3 * C)
  + (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (21 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 512 * beta : k) • (A * B * D)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestBeta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestBeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N2RestBeta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestBeta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestBeta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 64 * beta : k) • (B * F)
  + (-7 / 64 * beta : k) • (C * E)
  + (-7 / 128 * beta : k) • (D ^ 2)
  + (-7 / 1024 * beta : k) • (A * C ^ 2)
  + (7 / 64 * beta : k) • (A * G)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestBeta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestBeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N2RestBeta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestBeta1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestGamma0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 128 * gamma : k) • (B ^ 3)
  + (-3 / 16 * gamma : k) • (B * E)
  + (-3 / 16 * gamma : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestGamma0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2RestGamma0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N2RestGamma0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestDelta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * delta : k) • (A ^ 4)
  + (15 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 1024 * delta : k) • (A * B ^ 2)
  + (-15 / 64 * delta : k) • (B * D)
  + (-15 / 128 * delta : k) • (C ^ 2)
  + (5 / 8 * delta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestDelta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N2RestDelta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestDelta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestDelta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • (A * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestDelta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N2RestDelta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestDelta1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestEpsilon0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • (F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestEpsilon0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N2RestEpsilon0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestZeta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 1024 * zeta : k) • (A ^ 3)
  + (-15 / 128 * zeta : k) • (B ^ 2)
  + (3 / 8 * zeta : k) • (E)
  + (3 / 64 * zeta : k) • (A * C)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestZeta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst zeta
    simp only [bcdefg12N2RestZeta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestZeta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestEta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • (D)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestEta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N2RestEta0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N2RestTheta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * theta : k) • (A ^ 2)
  + (1 / 8 * theta : k) • (C)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N2RestTheta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst theta
    simp only [bcdefg12N2RestTheta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N2RestTheta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- The sum of the remainder chunks. -/
def bcdefg12N2Rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12N2RestLF0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestL0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestL1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestL2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestBeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestBeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestGamma0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N2RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Exact expansion into face and remainder. -/
theorem bcdefg12N2_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12N2Face A B C D E F G + bcdefg12N2Rest l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN2Quartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, bcdefg12N2Face, bcdefg12N2Rest, bcdefg12N2RestLF0, bcdefg12N2RestL0, bcdefg12N2RestL1, bcdefg12N2RestL2, bcdefg12N2RestBeta0, bcdefg12N2RestBeta1, bcdefg12N2RestGamma0, bcdefg12N2RestDelta0, bcdefg12N2RestDelta1, bcdefg12N2RestEpsilon0, bcdefg12N2RestZeta0, bcdefg12N2RestEta0, bcdefg12N2RestTheta0]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Strict load bands put the whole remainder below the face. -/
theorem bcdefg12N2Rest_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbL : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbBeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbDelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbZeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbTheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N2Rest l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  have hb0 := bcdefg12N2RestLF0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb1 := bcdefg12N2RestL0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb2 := bcdefg12N2RestL1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb3 := bcdefg12N2RestL2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb4 := bcdefg12N2RestBeta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb5 := bcdefg12N2RestBeta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb6 := bcdefg12N2RestGamma0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb7 := bcdefg12N2RestDelta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbDelta
  have hb8 := bcdefg12N2RestDelta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbDelta
  have hb9 := bcdefg12N2RestEpsilon0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb10 := bcdefg12N2RestZeta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbZeta
  have hb11 := bcdefg12N2RestEta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb12 := bcdefg12N2RestTheta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbTheta
  unfold bcdefg12N2Rest
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hb0 hb1) hb2) hb3) hb4) hb5) hb6) hb7) hb8) hb9) hb10) hb11) hb12)

set_option maxHeartbeats 64000000 in
/-- Coefficient of the homogeneous polynomial face. -/
theorem bcdefg12N2Face_coeff
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N2Face A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) =
      (5 / 512 : k) * n2QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  have hA : A ≠ 0 := by intro hz; simp [hz] at hApos
  have hd0 : (A * B ^ 2 * D).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hD, natDegree_mul hA (pow_ne_zero 2 hB)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf0 : (A * B ^ 2 * D).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd0, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (B * C * E).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hB hC) hE, natDegree_mul hB hC] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf1 : (B * C * E).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (C ^ 2 * D).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hC) hD] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf2 : (C ^ 2 * D).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd2, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (D * G).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hD hG] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf3 : (D * G).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = D.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (E * F).natDegree = A.natDegree + 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hE hF] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf4 : (E * F).coeff (A.natDegree + 2 * B.natDegree + D.natDegree) = E.leadingCoeff * F.leadingCoeff := by
    rw [← hd4, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12N2Face, n2QuarticOpenIIFace810, coeff_add, coeff_smul, smul_eq_mul, hcf0, hcf1, hcf2, hcf3, hcf4]
  ring

set_option maxHeartbeats 64000000 in
/-- Vanishing of the scalar N2 face under the strict load bands. -/
theorem bcdefg12N2Face_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbL : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbBeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbDelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbZeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbTheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    n2QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hrest := bcdefg12N2Rest_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL hbBeta hbDelta hbZeta hbTheta
  have hface := bcdefg12N2Face_coeff A B C D E F G hc
  have hApos := hc.1.1
  have hcarrier := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G hnu hkap
  have htop : A.natDegree < A.natDegree + 2 * B.natDegree + D.natDegree := by
    rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    have hApos := hcone.1
    omega
  have hz := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hcarrier htop)
  rw [bcdefg12N2_split, coeff_add, coeff_eq_zero_of_natDegree_lt hrest, add_zero, hface] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num : (5 / 512 : k) ≠ 0)

set_option maxHeartbeats 64000000 in
/-- The polynomial face of N6 on BCDEFG12. -/
def bcdefg12N6Face
    (A B C D E F G : k[X]) : k[X] :=
  (145 / 12288 : k) • (A ^ 2 * B ^ 3 * C)
  + (-25 / 1536 : k) • (A ^ 2 * B ^ 2 * F)
  + (-25 / 768 : k) • (A ^ 2 * B * D ^ 2)
  + (-45 / 1024 : k) • (A * B * C ^ 3)
  + (15 / 128 : k) • (A * B * C * G)
  + (25 / 192 : k) • (A * B * E ^ 2)
  + (95 / 384 : k) • (A * C * D * E)
  + (-25 / 48 : k) • (A * F * G)
  + (5 / 96 : k) • (A * C ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestLF0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (93 / 8192 : k) • (A * B ^ 5)
  + (-115 / 1536 : k) • (A * B ^ 3 * E)
  + (-225 / 1024 : k) • (A * B ^ 2 * C * D)
  + (-125 / 2048 : k) • (B ^ 4 * D)
  + (-265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (25 / 96 : k) • (A * B * D * F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestLF0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestLF0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestLF0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestLF1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 384 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestLF1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestLF1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestLF1]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestLF2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 128 : k) • (C ^ 3 * D)
  + (-5 / 16 : k) • (B * E * G)
  + (-5 / 16 : k) • (B * F ^ 2)
  + (-5 / 16 : k) • (C * D * G)
  + (-5 / 8 : k) • (C * E * F)
  + (-5 / 16 : k) • (D ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestLF2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestLF2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestLF2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestLF3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestLF3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestLF3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestLF3]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (715 / 268435456 * l : k) • (A ^ 8)
  + (105 / 1048576 * l : k) • (A ^ 6 * C)
  + (-255 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (105 / 262144 * l : k) • (A ^ 5 * E)
  + (-135 / 262144 * l : k) • (A ^ 4 * B * D)
  + (585 / 524288 * l : k) • (A ^ 4 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-93 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (1425 / 524288 * l : k) • (A ^ 2 * B ^ 4)
  + (15 / 32768 * l : k) • (A ^ 4 * G)
  + (81 / 8192 * l : k) • (A ^ 3 * C * E)
  + (-15 / 8192 * l : k) • (A ^ 3 * D ^ 2)
  + (-135 / 16384 * l : k) • (A ^ 2 * B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-51 / 4096 * l : k) • (A ^ 2 * B * C * D)
  + (11 / 8192 * l : k) • (A ^ 2 * C ^ 3)
  + (-369 / 8192 * l : k) • (A * B ^ 3 * D)
  + (-765 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  + (-567 / 16384 * l : k) • (B ^ 4 * C)
  + (3 / 256 * l : k) • (A ^ 2 * C * G)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL2, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL2]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 1024 * l : k) • (A ^ 2 * D * F)
  + (51 / 2048 * l : k) • (A ^ 2 * E ^ 2)
  + (27 / 1024 * l : k) • (A * B ^ 2 * G)
  + (21 / 256 * l : k) • (A * B * C * F)
  + (75 / 512 * l : k) • (A * B * D * E)
  + (39 / 1024 * l : k) • (A * C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL3, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL3]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 128 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • (C ^ 4)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL4, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL4]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * l : k) • (A * E * G)
  + (-3 / 16 * l : k) • (A * F ^ 2)
  + (-9 / 64 * l : k) • (B * D * G)
  + (-9 / 32 * l : k) • (B * E * F)
  + (-9 / 128 * l : k) • (C ^ 2 * G)
  + (-9 / 32 * l : k) • (C * D * F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL5 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL5, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL5]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestL6
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-9 / 64 * l : k) • (C * E ^ 2)
  + (-9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • (G ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestL6_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestL6 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst l
    simp only [bcdefg12N6RestL6, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestL6]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestBeta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (11 / 1048576 * beta : k) • (A ^ 7)
  + (35 / 98304 * beta : k) • (A ^ 5 * C)
  + (-35 / 131072 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 24576 * beta : k) • (A ^ 4 * E)
  + (-35 / 12288 * beta : k) • (A ^ 3 * B * D)
  + (7 / 2048 * beta : k) • (A ^ 3 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestBeta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N6RestBeta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestBeta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestBeta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (175 / 49152 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (91 / 8192 * beta : k) • (A * B ^ 4)
  + (35 / 1024 * beta : k) • (A ^ 2 * C * E)
  + (-133 / 6144 * beta : k) • (A ^ 2 * D ^ 2)
  + (-49 / 768 * beta : k) • (A * B ^ 2 * E)
  + (-7 / 64 * beta : k) • (A * B * C * D)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestBeta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N6RestBeta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestBeta1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestBeta2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-7 / 128 * beta : k) • (B ^ 3 * D)
  + (-91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 48 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestBeta2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N6RestBeta2, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestBeta2]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestBeta3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 64 * beta : k) • (C * D ^ 2)
  + (-7 / 16 * beta : k) • (F ^ 2)
  + (-7 / 768 * beta : k) • (A * C ^ 3)
  + (7 / 96 * beta : k) • (A * D * F)
  + (7 / 3072 * beta : k) • (A ^ 2 * B * F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestBeta3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestBeta3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst beta
    simp only [bcdefg12N6RestBeta3, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestBeta3]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestGamma0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 768 * gamma : k) • (A ^ 2 * B ^ 3)
  + (-15 / 128 * gamma : k) • (A * B ^ 2 * D)
  + (-9 / 128 * gamma : k) • (A * B * C ^ 2)
  + (-27 / 256 * gamma : k) • (B ^ 3 * C)
  + (-1 / 32 * gamma : k) • (A * C * F)
  + (5 / 16 * gamma : k) • (A * D * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestGamma0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestGamma0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestGamma0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestGamma1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  + (-3 / 4 * gamma : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestGamma1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestGamma1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestGamma1]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestDelta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 524288 * delta : k) • (A ^ 6)
  + (5 / 4096 * delta : k) • (A ^ 4 * C)
  + (-65 / 49152 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  + (-95 / 3072 * delta : k) • (A ^ 2 * B * D)
  + (65 / 6144 * delta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestDelta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N6RestDelta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestDelta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestDelta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-125 / 1024 * delta : k) • (A * B ^ 2 * C)
  + (-135 / 4096 * delta : k) • (B ^ 4)
  + (35 / 192 * delta : k) • (A * C * E)
  + (5 / 32 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestDelta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N6RestDelta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestDelta1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestDelta2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • (C ^ 3)
  + (-5 / 8 * delta : k) • (D * F)
  + (-5 / 16 * delta : k) • (E ^ 2)
  + (5 / 96 * delta : k) • (A * B * F)
  + (-5 / 384 * delta : k) • (A ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestDelta2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestDelta2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst delta
    simp only [bcdefg12N6RestDelta2, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestDelta2]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestEpsilon0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-5 / 96 * epsilon : k) • (A * B ^ 3)
  + (5 / 24 * epsilon : k) • (A * B * E)
  + (3 / 16 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  + (-1 / 2 * epsilon : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestEpsilon0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestEpsilon0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestEpsilon1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-1 / 2 * epsilon : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestEpsilon1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestEpsilon1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestEpsilon1]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestZeta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 49152 * zeta : k) • (A ^ 5)
  + (1 / 256 * zeta : k) • (A ^ 3 * C)
  + (-11 / 1024 * zeta : k) • (A ^ 2 * B ^ 2)
  + (1 / 64 * zeta : k) • (A ^ 2 * E)
  + (3 / 16 * zeta : k) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestZeta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst zeta
    simp only [bcdefg12N6RestZeta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestZeta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestZeta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-3 / 8 * zeta : k) • (B * F)
  + (-3 / 8 * zeta : k) • (C * E)
  + (-3 / 16 * zeta : k) • (D ^ 2)
  + (3 / 64 * zeta : k) • (A * C ^ 2)
  + (-1 / 4 * zeta : k) • (A * G)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestZeta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestZeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst zeta
    simp only [bcdefg12N6RestZeta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestZeta1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestEta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • (B ^ 3)
  + (-5 / 12 * eta : k) • (A * F)
  + (-1 / 4 * eta : k) • (B * E)
  + (-1 / 4 * eta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestEta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  simp only [bcdefg12N6RestEta0]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestTheta0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 12288 * theta : k) • (A ^ 4)
  + (1 / 96 * theta : k) • (A ^ 2 * C)
  + (3 / 128 * theta : k) • (A * B ^ 2)
  + (1 / 24 * theta : k) • (A * E)
  + (-1 / 8 * theta : k) • (B * D)
  + (-1 / 16 * theta : k) • (C ^ 2)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestTheta0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst theta
    simp only [bcdefg12N6RestTheta0, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestTheta0]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- A chunk with at most six monomials. -/
def bcdefg12N6RestTheta1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 * theta : k) • (G)

set_option maxHeartbeats 64000000 in
/-- This chunk lies below the face degree. -/
theorem bcdefg12N6RestTheta1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hb : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6RestTheta1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  rcases hb with hz | hb
  · subst theta
    simp only [bcdefg12N6RestTheta1, mul_zero, zero_smul, add_zero, natDegree_zero]
    omega
  · simp only [bcdefg12N6RestTheta1]
    compute_degree
    omega

set_option maxHeartbeats 64000000 in
/-- The sum of the remainder chunks. -/
def bcdefg12N6Rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  bcdefg12N6RestLF0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestLF1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestLF2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestLF3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL4 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL5 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestL6 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestBeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestBeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestBeta2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestBeta3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestGamma0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestGamma1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestDelta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestDelta1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestDelta2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestEpsilon0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestEpsilon1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestZeta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestZeta1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestEta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestTheta0 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    bcdefg12N6RestTheta1 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Exact expansion into face and remainder. -/
theorem bcdefg12N6_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN6TowerQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      bcdefg12N6Face A B C D E F G + bcdefg12N6Rest l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN6TowerQuartic810, degreeZeroPrimitiveQuartic810, degreeZeroOmicronQuartic810, degreeZeroNuQuartic810, rhoBaseGroupQuartic810, rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810, rhoThetaGroupQuartic810, bcdefg12N6Face, bcdefg12N6Rest, bcdefg12N6RestLF0, bcdefg12N6RestLF1, bcdefg12N6RestLF2, bcdefg12N6RestLF3, bcdefg12N6RestL0, bcdefg12N6RestL1, bcdefg12N6RestL2, bcdefg12N6RestL3, bcdefg12N6RestL4, bcdefg12N6RestL5, bcdefg12N6RestL6, bcdefg12N6RestBeta0, bcdefg12N6RestBeta1, bcdefg12N6RestBeta2, bcdefg12N6RestBeta3, bcdefg12N6RestGamma0, bcdefg12N6RestGamma1, bcdefg12N6RestDelta0, bcdefg12N6RestDelta1, bcdefg12N6RestDelta2, bcdefg12N6RestEpsilon0, bcdefg12N6RestEpsilon1, bcdefg12N6RestZeta0, bcdefg12N6RestZeta1, bcdefg12N6RestEta0, bcdefg12N6RestTheta0, bcdefg12N6RestTheta1]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Strict load bands put the whole remainder below the face. -/
theorem bcdefg12N6Rest_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbL : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbBeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbDelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbZeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbTheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree) :
    (bcdefg12N6Rest l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
  have hb0 := bcdefg12N6RestLF0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb1 := bcdefg12N6RestLF1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb2 := bcdefg12N6RestLF2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb3 := bcdefg12N6RestLF3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb4 := bcdefg12N6RestL0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb5 := bcdefg12N6RestL1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb6 := bcdefg12N6RestL2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb7 := bcdefg12N6RestL3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb8 := bcdefg12N6RestL4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb9 := bcdefg12N6RestL5_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb10 := bcdefg12N6RestL6_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL
  have hb11 := bcdefg12N6RestBeta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb12 := bcdefg12N6RestBeta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb13 := bcdefg12N6RestBeta2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb14 := bcdefg12N6RestBeta3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbBeta
  have hb15 := bcdefg12N6RestGamma0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb16 := bcdefg12N6RestGamma1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb17 := bcdefg12N6RestDelta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbDelta
  have hb18 := bcdefg12N6RestDelta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbDelta
  have hb19 := bcdefg12N6RestDelta2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbDelta
  have hb20 := bcdefg12N6RestEpsilon0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb21 := bcdefg12N6RestEpsilon1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb22 := bcdefg12N6RestZeta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbZeta
  have hb23 := bcdefg12N6RestZeta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbZeta
  have hb24 := bcdefg12N6RestEta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc
  have hb25 := bcdefg12N6RestTheta0_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbTheta
  have hb26 := bcdefg12N6RestTheta1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbTheta
  unfold bcdefg12N6Rest
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hb0 hb1) hb2) hb3) hb4) hb5) hb6) hb7) hb8) hb9) hb10) hb11) hb12) hb13) hb14) hb15) hb16) hb17) hb18) hb19) hb20) hb21) hb22) hb23) hb24) hb25) hb26)

set_option maxHeartbeats 64000000 in
/-- Coefficient of the homogeneous polynomial face. -/
theorem bcdefg12N6Face_coeff
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) :
    (bcdefg12N6Face A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) =
      (5 / 12288 : k) * A.leadingCoeff * n6QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have hApos := hcone.1
  have hA : A ≠ 0 := by intro hz; simp [hz] at hApos
  have hd0 : (A ^ 2 * B ^ 3 * C).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 3 hB)) hC, natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 3 hB)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf0 : (A ^ 2 * B ^ 3 * C).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (A ^ 2 * B ^ 2 * F).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)) hF, natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf1 : (A ^ 2 * B ^ 2 * F).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (A ^ 2 * B * D ^ 2).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) hB) (pow_ne_zero 2 hD), natDegree_mul (pow_ne_zero 2 hA) hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf2 : (A ^ 2 * B * D ^ 2).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (A * B * C ^ 3).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA hB) (pow_ne_zero 3 hC), natDegree_mul hA hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf3 : (A * B * C ^ 3).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hd3, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (A * B * C * G).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hA hB) hC) hG, natDegree_mul (mul_ne_zero hA hB) hC, natDegree_mul hA hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf4 : (A * B * C * G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : (A * B * E ^ 2).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA hB) (pow_ne_zero 2 hE), natDegree_mul hA hB] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf5 : (A * B * E ^ 2).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd6 : (A * C * D * E).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hA hC) hD) hE, natDegree_mul (mul_ne_zero hA hC) hD, natDegree_mul hA hC] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf6 : (A * C * D * E).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd6, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd7 : (A * F * G).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA hF) hG, natDegree_mul hA hF] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf7 : (A * F * G).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * F.leadingCoeff * G.leadingCoeff := by
    rw [← hd7, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd8 : (A * C ^ 2 * F).natDegree = 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hC)) hF, natDegree_mul hA (pow_ne_zero 2 hC)] <;> (try simp only [natDegree_pow]) <;> omega
  have hcf8 : (A * C ^ 2 * F).coeff (2 * A.natDegree + 3 * B.natDegree + C.natDegree) = A.leadingCoeff * C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hd8, coeff_natDegree] <;> simp only [leadingCoeff_mul, leadingCoeff_pow]
  simp only [bcdefg12N6Face, n6QuarticOpenIIFace810, coeff_add, coeff_smul, smul_eq_mul, hcf0, hcf1, hcf2, hcf3, hcf4, hcf5, hcf6, hcf7, hcf8]
  ring

set_option maxHeartbeats 64000000 in
/-- Vanishing of the scalar N6 face under the strict load bands. -/
theorem bcdefg12N6Face_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG12810 A B C D E F G)
    (hbL : l = 0 ∨ 11 * A.natDegree < 8 * B.natDegree)
    (hbBeta : beta = 0 ∨ 9 * A.natDegree < 8 * B.natDegree)
    (hbDelta : delta = 0 ∨ 7 * A.natDegree < 8 * B.natDegree)
    (hbZeta : zeta = 0 ∨ 5 * A.natDegree < 8 * B.natDegree)
    (hbTheta : theta = 0 ∨ 3 * A.natDegree < 8 * B.natDegree)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    n6QuarticOpenIIFace810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hrest := bcdefg12N6Rest_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hc hbL hbBeta hbDelta hbZeta hbTheta
  have hface := bcdefg12N6Face_coeff A B C D E F G hc
  have hApos := hc.1.1
  have hcarrier := degreeZeroN6TowerQuartic810_natDegree_le l beta gamma delta epsilon zeta eta theta A B C D E F G hApos hprim homi hnu
  have htop : 2 * A.natDegree < 2 * A.natDegree + 3 * B.natDegree + C.natDegree := by
    rcases hc with ⟨hcone, hB, hC, hD, hE, hF, hG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    have hApos := hcone.1
    omega
  have hz := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hcarrier htop)
  rw [bcdefg12N6_split, coeff_add, coeff_eq_zero_of_natDegree_lt hrest, add_zero, hface] at hz
  have hA : A ≠ 0 := by intro hz; simp [hz] at hApos
  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (by norm_num : (5 / 12288 : k) ≠ 0) (leadingCoeff_ne_zero.mpr hA))

set_option maxHeartbeats 64000000 in
/-- The maximal-tie BCDEFG12 residual chamber is impossible. The auxiliary
`N₇ + (1/4)ACκ` supplies strict load bands, and the six resulting scalar
faces satisfy the tracked Open-II certificate. -/
theorem quarticUnownedCell_rBCDEFG12_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) = Polynomial.C (j / t))
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hc : QuarticChamberBCDEFG12810 A B C D E F G) : False := by
  have hprim := natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticBCDEFG12_loadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hc hprim homi hnu hkap
  have hk := bcdefg12KappaFace_zero810 l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hkap
  have hm := bcdefg12MuFace_zero810 l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hmu
  have hx := bcdefg12XiFace_zero810 l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hxi
  have hp := bcdefg12PiFace_zero810 l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hpi
  have hn2 := bcdefg12N2Face_zero l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hnu hkap
  have hn6 := bcdefg12N6Face_zero l beta gamma delta epsilon zeta eta theta
    A B C D E F G hc hbl hbbeta hbdelta hbzeta hbtheta hprim homi hnu
  have hAne : A ≠ 0 := by intro hz; have ha := hcone.1; simp [hz] at ha
  exact quarticOpenChamberII810_impossible
    A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff
    hk hm hx hp hn2 hn6
    (leadingCoeff_ne_zero.mpr hAne)
    (leadingCoeff_ne_zero.mpr hc.2.1)
    (leadingCoeff_ne_zero.mpr hc.2.2.1)
    (leadingCoeff_ne_zero.mpr hc.2.2.2.1)
    (leadingCoeff_ne_zero.mpr hc.2.2.2.2.1)
    (leadingCoeff_ne_zero.mpr hc.2.2.2.2.2.1)
    (leadingCoeff_ne_zero.mpr hc.2.2.2.2.2.2.1)

end Max11DegreeRoutes

#print axioms Max11DegreeRoutes.quarticUnownedCell_rBCDEFG12_impossible
