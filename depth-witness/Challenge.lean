/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), OpenAI Codex (definitions)
-/
import Mathlib

/-!
# Challenge: depth-window witnesses for the residue-A phase-2 chart

This is the definition-only statement layer for the Palomar phase-2
certificate at the campaign degree pair `(72,108)` and total defect `6`.
It defines the residue-A orbit data, constructs the two normalized chart jets
by finite Cauchy products, and states the Jacobian rows structurally.  Thus the
depth parameter has its literal engine meaning: depth `D` imposes rows `k < D`.

In particular, depth 21 imposes rows 0 through 20, depth 23 adds rows 21 and
22, and depth 25 adds rows 23 and 24.  No expanded CORE2, Row_22, or Row_24
polynomial list occurs here.  The eventual witness theorem is represented by
the proposition `HasDepthWitness D`; no nonemptiness theorem is asserted in
this phase.

The coefficient field is the fixed split prime `ZMod 105337`, with the
campaign embedding `sqrt(3) = 795`, primitive 42nd root `2779`, and B-root
`24069`.  The 36 radical fibers remain unsplit: `alpha1`, `alpha2`, and the
two `HW/W` signs are fields of `RadicalPoint`, subject to their defining
equations and chart-unit witnesses.
-/

namespace JC72108.DepthWitness

open scoped BigOperators

/-! ## Campaign and coefficient data -/

/-- The campaign degree-pair label.  This is metadata, not the pair of
chart polynomial degrees `(168,252)`. -/
def newtonDegreePair : ℕ × ℕ := (72, 108)

/-- Total defect of the distinguished two-pole template. -/
def totalDefect : ℕ := 6

/-- Global template type `(alpha,beta)`. -/
def templateType : ℕ × ℕ := (2, 3)

/-- Global exponent pair `(k_f,l_f)`. -/
def fExponentPair : ℕ × ℕ := (126, 42)

/-- Global exponent pair `(k_g,l_g)`. -/
def gExponentPair : ℕ × ℕ := (189, 63)

def degreeFMinusA : ℕ := 168
def degreeG : ℕ := 252

/-- The two pole charges whose sum is `totalDefect`. -/
def poleCharges : ℕ × ℕ := (3, 3)

/-- Common denominator of the residue-A chart. -/
def commonRamification : ℕ := 42

/-- The split prime used by the phase-2 certificate. -/
def windowPrime : ℕ := 105337

/-- Coefficient field of the modular certificate. -/
abbrev Coeff := ZMod windowPrime

theorem windowPrime_prime : Nat.Prime windowPrime := by
  norm_num [windowPrime]

instance windowPrimeFact : Fact (Nat.Prime windowPrime) := ⟨windowPrime_prime⟩

/-- The fixed square-root embedding `sqrt(3) = 795 (mod 105337)`. -/
def sqrtThree : Coeff := 795

/-- The fixed primitive 42nd root used by the orbit action. -/
def zeta42 : Coeff := 2779

/-- The fixed B-side seventh root, satisfying `2 * etaB^7 = 3`. -/
def etaB : Coeff := 24069

/-- Transported leading coefficient of the normalized `f` jet. -/
def fLead : Coeff := 51107

/-- Transported leading coefficient of the normalized `g` jet. -/
def gLead : Coeff := 33066

theorem sqrtThree_sq : sqrtThree ^ 2 = (3 : Coeff) := by
  decide

theorem zeta42_pow : zeta42 ^ 42 = (1 : Coeff) := by
  decide

theorem zeta42_primitive :
    zeta42 ^ 6 ≠ (1 : Coeff) ∧ zeta42 ^ 14 ≠ (1 : Coeff) ∧
      zeta42 ^ 21 ≠ (1 : Coeff) := by
  decide

theorem etaB_seventh : 2 * etaB ^ 7 = (3 : Coeff) := by
  decide

theorem fLead_value : fLead * (2 : Coeff) ^ 6 = (7 : Coeff) ^ 12 := by
  decide

theorem gLead_value : gLead * (2 : Coeff) ^ 9 = -(7 : Coeff) ^ 18 := by
  decide

theorem lead_tower_relation : gLead ^ 2 = fLead ^ 3 := by
  decide

/-! ## Exponent ladder and approximate-root recurrence -/

inductive TemplateVertex
  | root | suffix | merge | pole1 | pole2
  deriving DecidableEq, Repr

/-- The five entries of `Q(F) = (D_F, deg p_F, nu_F, M_F, kappaBar_F)`.
`multiplicity = none` records the source's unresolved `M_R`. -/
structure QDatum where
  Df : ℕ
  patternDegree : ℕ
  nu : ℕ
  multiplicity : Option ℕ
  kappaBar : ℕ
  deriving DecidableEq, Repr

/-- Exponent-ladder data at one vertex.  `exactTowerDepth = none` at the
root means only the lower bound is pinned. -/
structure LadderDatum where
  pi : ℚ
  kappa : ℕ
  dF : ℚ
  dG : ℚ
  dH1 : ℚ
  dH2 : ℚ
  Dg : ℕ
  towerDepthLower : ℕ
  exactTowerDepth : Option ℕ
  q : QDatum
  deriving DecidableEq, Repr

/-- The chain `P_i -> G_m -> F_s -> R`, oriented toward the root. -/
def towardRoot : TemplateVertex → Option TemplateVertex
  | .pole1 | .pole2 => some .merge
  | .merge => some .suffix
  | .suffix => some .root
  | .root => none

/-- The complete pinned table from the template's exponent ladder. -/
def ladderDatum : TemplateVertex → LadderDatum
  | .root =>
      { pi := 0, kappa := 1, dF := 42, dG := 63, dH1 := 56, dH2 := 138
        Dg := 63
        towerDepthLower := 3, exactTowerDepth := none
        q := ⟨42, 126, 1, none, 1⟩ }
  | .suffix =>
      { pi := 2 / 7, kappa := 7, dF := 6, dG := 9, dH1 := 8, dH2 := 138 / 7
        Dg := 63
        towerDepthLower := 2, exactTowerDepth := some 2
        q := ⟨42, 126, 7, some 3, 5⟩ }
  | .merge =>
      { pi := 16 / 21, kappa := 21, dF := 2 / 7, dG := 3 / 7
        dH1 := 8 / 21, dH2 := 8 / 7
        Dg := 9
        towerDepthLower := 1, exactTowerDepth := some 1
        q := ⟨6, 12, 3, some 2, 5⟩ }
  | .pole1 | .pole2 =>
      { pi := 37 / 42, kappa := 42, dF := 1 / 21, dG := 1 / 14
        dH1 := 1 / 7, dH2 := 3 / 7
        Dg := 3
        towerDepthLower := 0, exactTowerDepth := some 0
        q := ⟨2, 2, 2, some 1, 5⟩ }

/-- One approximate-root step `h_next = h^k - s * (f-a)^l`. -/
structure TowerStep (R : Type*) where
  k : ℕ
  l : ℕ
  s : R

/-- Structural recurrence for the approximate-root tower, with `h_0 = g`. -/
def towerTerm {R : Type*} [CommRing R] (fMinusA g : R)
    (step : ℕ → TowerStep R) : ℕ → R
  | 0 => g
  | n + 1 => (towerTerm fMinusA g step n) ^ (step n).k -
      (step n).s * fMinusA ^ (step n).l

/-- Pinned exponent pairs `(k_j,l_j)` for the known prefix of the tower. -/
def knownTowerExponents : ℕ → Option (ℕ × ℕ)
  | 0 => some (2, 3)
  | 1 => some (3, 4)
  | 2 => some (7, 23)
  | _ => none

/-! ## Residue-A orbit data -/

/-- The nine orbit types in the exact residue-A registry. -/
inductive Orbit
  | p1 | p2 | b | gp1 | gp2 | g0p1 | g0p2 | gb42 | gb21
  deriving DecidableEq, Repr

def orbitSize : Orbit → ℕ
  | .p1 | .p2 | .b | .gp1 | .gp2 | .gb42 => 42
  | .g0p1 | .g0p2 | .gb21 => 21

def fOrbits : List Orbit := [.p1, .p2, .b]

def gOrbits : List Orbit := [.gp1, .gp2, .g0p1, .g0p2, .gb42, .gb21]

/-- Orbits whose level-12 coefficient is one and whose `k=0` directions
pass through the distinguished direction. -/
def isAside : Orbit → Bool
  | .p1 | .p2 | .gp1 | .gp2 | .g0p1 | .g0p2 => true
  | .b | .gb42 | .gb21 => false

/-- The radical and localization coordinates left symbolic across all 36
fibers of the fixed split-prime embedding. -/
structure RadicalPoint where
  alpha1 : Coeff
  alpha2 : Coeff
  W1 : Coeff
  HW1 : Coeff
  W2 : Coeff
  HW2 : Coeff
  uW1 : Coeff
  uW2 : Coeff
  uA : Coeff
  deriving DecidableEq, Repr

/-- The seven radical/chart equations appended to the 38 CORE2 residuals. -/
def RadicalPoint.Valid (r : RadicalPoint) : Prop :=
  r.alpha1 ^ 3 = 3 + sqrtThree ∧
  r.alpha2 ^ 3 = 3 - sqrtThree ∧
  2 * r.HW1 ^ 2 = 3 * r.W1 ^ 2 ∧
  2 * r.HW2 ^ 2 = 3 * r.W2 ^ 2 ∧
  r.uW1 * r.W1 = 1 ∧
  r.uW2 * r.W2 = 1 ∧
  r.uA * (r.alpha1 - r.alpha2) = 1

/-- A point of the infinite residue-A coefficient space.  The construction
below reads only finitely many fields at any fixed depth. -/
structure ResidueAData where
  radical : RadicalPoint
  uf18 : Coeff
  uf24 : Coeff
  uf30 : Coeff
  vf1_34 : Coeff
  vf1_36 : Coeff
  vf2_34 : Coeff
  vf2_36 : Coeff
  tail : Orbit → ℕ → Coeff

/-- The B, GB42, and GB21 representative tails are frozen on this chart. -/
def BFrozen (x : ResidueAData) : Prop :=
  ∀ o, (o = .b ∨ o = .gb42 ∨ o = .gb21) → ∀ level, x.tail o level = 0

/-- The six live no-log pins at absolute level 42. -/
def NoLogPins (x : ResidueAData) : Prop :=
  x.tail .p1 42 = 0 ∧ x.tail .p2 42 = 0 ∧
  x.tail .gp1 42 = 0 ∧ x.tail .gp2 42 = 0 ∧
  x.tail .g0p1 42 = 0 ∧ x.tail .g0p2 42 = 0

/-- The common prefix arc `t^12 + uf18*t^18 + uf24*t^24 + uf30*t^30`. -/
def prefixCoefficient (x : ResidueAData) (level : ℕ) : Coeff :=
  if level = 12 then 1 else
  if level = 18 then x.uf18 else
  if level = 24 then x.uf24 else
  if level = 30 then x.uf30 else 0

/-- Coefficients of the nine representative branch series.  The B-side is
frozen, odd tails of 21-orbits vanish, and the six live level-42 tails are
zero by construction (the no-log/PIN42 conditions). -/
def orbitCoefficient (x : ResidueAData) (o : Orbit) (level : ℕ) : Coeff :=
  match o with
  | .b | .gb42 | .gb21 => if level = 12 then etaB else 0
  | .p1 | .gp1 | .g0p1 =>
      if level = 12 then 1 else
      if level = 18 then x.uf18 else
      if level = 24 then x.uf24 else
      if level = 30 then x.uf30 else
      if level = 32 then x.radical.alpha1 else
      if level = 34 then x.vf1_34 else
      if level = 36 then x.vf1_36 else
      if level = 37 then
        match o with
        | .p1 => x.radical.W1
        | .gp1 => x.radical.HW1
        | _ => 0
      else if 38 ≤ level ∧ level ≠ 42 ∧
          (o ≠ .g0p1 ∨ level % 2 = 0) then x.tail o level else 0
  | .p2 | .gp2 | .g0p2 =>
      if level = 12 then 1 else
      if level = 18 then x.uf18 else
      if level = 24 then x.uf24 else
      if level = 30 then x.uf30 else
      if level = 32 then x.radical.alpha2 else
      if level = 34 then x.vf2_34 else
      if level = 36 then x.vf2_36 else
      if level = 37 then
        match o with
        | .p2 => x.radical.W2
        | .gp2 => x.radical.HW2
        | _ => 0
      else if 38 ≤ level ∧ level ≠ 42 ∧
          (o ≠ .g0p2 ∨ level % 2 = 0) then x.tail o level else 0

/-! ## Structural jet construction -/

/-- A `t`-jet whose coefficient at each slot is a polynomial in `eta`. -/
abbrev Jet (R : Type*) [Semiring R] := ℕ → Polynomial R

noncomputable def jetOne {R : Type*} [Semiring R] : Jet R :=
  fun k => if k = 0 then 1 else 0

/-- Cauchy multiplication of jets, stated coefficientwise. -/
noncomputable def jetMul {R : Type*} [Semiring R] (a b : Jet R) : Jet R :=
  fun k => ∑ i ∈ Finset.range (k + 1), a i * b (k - i)

/-- Finite Cauchy product.  This is the compact substitute for all expanded
window polynomials. -/
noncomputable def jetProduct {R : Type*} [Semiring R] : List (Jet R) → Jet R
  | [] => jetOne
  | a :: as => jetMul a (jetProduct as)

def twistedCoefficient (x : ResidueAData) (o : Orbit) (phase level : ℕ) : Coeff :=
  zeta42 ^ (phase * level) * orbitCoefficient x o level

/-- A factor through the distinguished direction, normalized at level 32. -/
noncomputable def throughFactor (x : ResidueAData) (o : Orbit) (phase : ℕ) : Jet Coeff :=
  fun slot : ℕ =>
    (if slot = 0 then Polynomial.X else 0) -
      Polynomial.C (twistedCoefficient x o phase (32 + slot))

/-- Any other factor: the phase difference from the prefix arc, with the
`eta*t^20` term at the resonance slot. -/
noncomputable def offFactor (x : ResidueAData) (o : Orbit) (phase : ℕ) : Jet Coeff :=
  fun slot : ℕ =>
    Polynomial.C (prefixCoefficient x (12 + slot) -
      twistedCoefficient x o phase (12 + slot)) +
      if slot = 20 then Polynomial.X else 0

/-- The `7 * (orbitSize/7)` factors of one orbit.  Writing
`phase = k + 7*j` matches the source registry exactly. -/
noncomputable def orbitFactors (x : ResidueAData) (o : Orbit) : List (Jet Coeff) :=
  (List.range 7).flatMap fun k =>
    (List.range (orbitSize o / 7)).map fun j =>
      let phase := k + 7 * j
      if isAside o = true ∧ k = 0 then throughFactor x o phase
      else offFactor x o phase

noncomputable def orbitJet (x : ResidueAData) (o : Orbit) : Jet Coeff :=
  jetProduct (orbitFactors x o)

/-- The normalized `Phi` jet of `f-a`. -/
noncomputable def phi (x : ResidueAData) : Jet Coeff :=
  jetProduct (fOrbits.map (orbitJet x))

/-- The normalized `Gamma` jet of `g`. -/
noncomputable def gamma (x : ResidueAData) : Jet Coeff :=
  jetProduct (gOrbits.map (orbitJet x))

/-- `P(eta) = (eta^3-a1)(eta^3-a2)` in the merge chart. -/
noncomputable def mergePolynomial : Polynomial Coeff :=
  (Polynomial.X ^ 3 - Polynomial.C (3 + sqrtThree)) *
    (Polynomial.X ^ 3 - Polynomial.C (3 - sqrtThree))

noncomputable def expectedPhi0 : Polynomial Coeff :=
  Polynomial.C fLead * mergePolynomial ^ 2

noncomputable def expectedGamma0 : Polynomial Coeff :=
  Polynomial.C gLead * mergePolynomial ^ 3

/-- The four promoted slot-zero gates. -/
def TopConditions (x : ResidueAData) : Prop :=
  phi x 0 = expectedPhi0 ∧
  gamma x 0 = expectedGamma0 ∧
  gamma x 0 ^ 2 = phi x 0 ^ 3 ∧
  (-12 : Polynomial Coeff) * phi x 0 * Polynomial.derivative (gamma x 0) +
      18 * gamma x 0 * Polynomial.derivative (phi x 0) = 0

/-! ## Depth rows, extensions, and the existence template -/

/-- The coefficient of `t^k` in
`(t Phi_t-12 Phi) Gamma_eta - Phi_eta (t Gamma_t-18 Gamma)`. -/
noncomputable def jacobianRow (x : ResidueAData) (k : ℕ) : Polynomial Coeff :=
  ∑ i ∈ Finset.range (k + 1),
    (Polynomial.C ((((i : ℤ) - 12 : ℤ) : Coeff)) *
        phi x i * Polynomial.derivative (gamma x (k - i)) -
      Polynomial.C (((((k - i : ℕ) : ℤ) - 18 : ℤ) : Coeff)) *
        gamma x (k - i) * Polynomial.derivative (phi x i))

/-- Homogeneous rows except for the gauged Jacobian inhomogeneity at slot 20. -/
noncomputable def rowTarget (k : ℕ) : Polynomial Coeff :=
  if k = 20 then Polynomial.C (-42) else 0

/-- The engine convention: a depth-`D` point satisfies precisely the rows
with `k < D`, together with the fixed chart and top data. -/
def WindowConditions (D : ℕ) (x : ResidueAData) : Prop :=
  x.radical.Valid ∧ BFrozen x ∧ NoLogPins x ∧ TopConditions x ∧
    ∀ k < D, jacobianRow x k = rowTarget k

/-- Campaign depth indices are odd and start at the D21 base window. -/
def IsCampaignDepth (D : ℕ) : Prop := 21 ≤ D ∧ D ≤ 42 ∧ Odd D

/-- Statement template for modular depth-window survival.  A final Solution
will instantiate this at depth 25 if a rational witness is extracted, or
prove its negation at depth 25 if the family is empty. -/
def HasDepthWitness (D : ℕ) : Prop :=
  ∃ x : ResidueAData, IsCampaignDepth D ∧ WindowConditions D x

/-- Equality of the source coefficients that can affect the smaller window. -/
def TruncatesTo (lower : ℕ) (small large : ResidueAData) : Prop :=
  small.radical = large.radical ∧
    ∀ o level, level < 32 + lower →
      orbitCoefficient small o level = orbitCoefficient large o level

/-- Structural extension in the depth ladder. -/
def DepthExtension (lower upper : ℕ) (small large : ResidueAData) : Prop :=
  IsCampaignDepth lower ∧ IsCampaignDepth upper ∧ lower ≤ upper ∧
    WindowConditions lower small ∧ WindowConditions upper large ∧
    TruncatesTo lower small large

/-- D21 conditions followed by the two new D23 rows. -/
def D23Extension : ResidueAData → ResidueAData → Prop := DepthExtension 21 23

/-- D23 conditions followed by the two new D25 rows. -/
def D25Extension : ResidueAData → ResidueAData → Prop := DepthExtension 23 25

/-! ## CORE2 and frontier metadata (no expanded equation lists) -/

structure RowCell where
  row : ℕ
  etaDegree : ℕ
  deriving DecidableEq, Repr

def rowCellFamily (row start count : ℕ) : List RowCell :=
  (List.range count).map fun j => ⟨row, start + 3 * j⟩

/-- The 77 raw D21 coefficient cells before PIN42 removes `(10,28)`. -/
def d21RawCells : List RowCell :=
  rowCellFamily 6 2 9 ++ rowCellFamily 8 0 10 ++
  rowCellFamily 10 1 10 ++ rowCellFamily 12 2 9 ++
  rowCellFamily 14 0 10 ++ rowCellFamily 16 1 10 ++
  rowCellFamily 18 2 9 ++ rowCellFamily 20 0 10

/-- The 38 post-pivot CORE2 residual labels.  These are labels only, not
the expanded pseudo-division polynomials. -/
def core2ResidualCells : List RowCell :=
  rowCellFamily 10 1 9 ++ rowCellFamily 12 11 6 ++
  rowCellFamily 14 12 6 ++ rowCellFamily 16 13 6 ++
  rowCellFamily 18 14 5 ++ rowCellFamily 20 12 6

inductive CoreCoordinate
  | tf2_38 | tg1_38 | tg1_39 | tg1_40 | tg1_41
  | tg2_38 | tg2_39 | tg2_40 | tg2_41
  | tg01_38 | tg01_40 | tg02_38 | tg02_40
  | uf18 | vf1_34 | vf1_36 | vf2_34 | vf2_36
  deriving DecidableEq, Repr

def coreCoordinateValue (x : ResidueAData) : CoreCoordinate → Coeff
  | .tf2_38 => x.tail .p2 38
  | .tg1_38 => x.tail .gp1 38
  | .tg1_39 => x.tail .gp1 39
  | .tg1_40 => x.tail .gp1 40
  | .tg1_41 => x.tail .gp1 41
  | .tg2_38 => x.tail .gp2 38
  | .tg2_39 => x.tail .gp2 39
  | .tg2_40 => x.tail .gp2 40
  | .tg2_41 => x.tail .gp2 41
  | .tg01_38 => x.tail .g0p1 38
  | .tg01_40 => x.tail .g0p1 40
  | .tg02_38 => x.tail .g0p2 38
  | .tg02_40 => x.tail .g0p2 40
  | .uf18 => x.uf18
  | .vf1_34 => x.vf1_34
  | .vf1_36 => x.vf1_36
  | .vf2_34 => x.vf2_34
  | .vf2_36 => x.vf2_36

/-- The 22 pivot coordinates, ordered as 16 high then six low. -/
inductive PivotCoordinate
  | tf1_44 | tf2_44 | tf1_46 | tf2_46 | tf1_43 | tf1_48 | tf2_43 | tf2_48
  | tf1_45 | tf1_50 | tf2_45 | tf2_50 | tf1_47 | tf1_52 | tf2_47 | tf2_52
  | tf1_38 | tf1_40 | tf2_40 | tf1_39 | tf1_41 | tf2_41
  deriving DecidableEq, Repr

def pivotCell : PivotCoordinate → RowCell
  | .tf1_44 => ⟨12, 2⟩ | .tf2_44 => ⟨12, 5⟩
  | .tf1_46 => ⟨14, 0⟩ | .tf2_46 => ⟨14, 3⟩
  | .tf1_43 => ⟨16, 1⟩ | .tf1_48 => ⟨16, 4⟩
  | .tf2_43 => ⟨16, 7⟩ | .tf2_48 => ⟨16, 10⟩
  | .tf1_45 => ⟨18, 2⟩ | .tf1_50 => ⟨18, 5⟩
  | .tf2_45 => ⟨18, 8⟩ | .tf2_50 => ⟨18, 11⟩
  | .tf1_47 => ⟨20, 0⟩ | .tf1_52 => ⟨20, 3⟩
  | .tf2_47 => ⟨20, 6⟩ | .tf2_52 => ⟨20, 9⟩
  | .tf1_38 => ⟨6, 2⟩ | .tf1_40 => ⟨8, 0⟩
  | .tf2_40 => ⟨8, 3⟩ | .tf1_39 => ⟨12, 8⟩
  | .tf1_41 => ⟨14, 6⟩ | .tf2_41 => ⟨14, 9⟩

def core2VariableCount : ℕ := 27
def core2EquationCount : ℕ := 45
def core2PivotCount : ℕ := 22
def core2ResidualCount : ℕ := 38
def core2TemplateCoordinateCount : ℕ := 18

/-- Ten new tail coordinates on which Row_22 is affine. -/
inductive D23Tail
  | tg02_54 | tg01_54 | tg2_49 | tg1_49 | tg1_54
  | tg2_54 | tf1_54 | tf2_54 | tf1_49 | tf2_49
  deriving DecidableEq, Repr

def d23EtaSupport : List ℕ := (List.range 10).map fun j => 1 + 3 * j

/-- Ten frontier coordinates on which Row_24 is affine before the rank-four
Schur solve. -/
inductive D25Frontier
  | tf1_51 | tf1_56 | tf2_51 | tf2_56 | tg1_51
  | tg1_56 | tg2_51 | tg2_56 | tg01_56 | tg02_56
  deriving DecidableEq, Repr

def d25EtaSupport : List ℕ := (List.range 9).map fun j => 2 + 3 * j

end JC72108.DepthWitness
