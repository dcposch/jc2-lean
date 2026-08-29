import LowScale68ScaleTwoRhoOneTransverse

/-! # Algebraic component split of the full `rho = 1` residual

After normalizing a nonzero branch parameter `z`, the two exact top rows are
two polynomials in `(T,V) = (t/z³,v/z²)`.  Their common zero set has exactly
the rational cubic-core point and one degree-ten component over `ℚ`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RhoOneComponentSplit68

variable {k : Type*} [Field k] [CharZero k]

def rhoOneResidualFour68 (t v z : k) : k :=
  topRowFour68 (rhoOneInitialA68 v z) (rhoOneInitialB68 t v z)
    (rhoOneInitialC68 t v z) (rhoOneInitialD68 t v z)
    (rhoOneInitialE68 t v z)

def rhoOneResidualThree68 (t v z : k) : k :=
  topRowThree68 (rhoOneInitialA68 v z) (rhoOneInitialB68 t v z)
    (rhoOneInitialC68 t v z) (rhoOneInitialD68 t v z)
    (rhoOneInitialE68 t v z)

def rhoOneAffineFour68 (T V : k) : k := rhoOneResidualFour68 T V 1
def rhoOneAffineThree68 (T V : k) : k := rhoOneResidualThree68 T V 1

/-- The irreducible degree-ten `V`-polynomial of the non-cubic component. -/
def rhoOneNoncubicVPolynomial68 (V : k) : k :=
  44098668 * V ^ 10 - 61024590 * V ^ 9 + 5212350 * V ^ 8 +
    39856212 * V ^ 7 - 37561590 * V ^ 6 + 18860985 * V ^ 5 -
    6400779 * V ^ 4 + 1550615 * V ^ 3 - 265353 * V ^ 2 +
    30855 * V - 2057

private def rhoOneSplitMultiplierFour68 (T V : k) : k :=
  (5093861985 * V ^ 6 - 3276333765 * V ^ 5 - 2893696245 * V ^ 4 +
      3318849045 * V ^ 3 - 1393261155 * V ^ 2 + 342956592 * V -
      42869574) * T ^ 2 +
    (8489769975 * V ^ 8 - 22926364740 * V ^ 7 + 11431295910 * V ^ 6 +
      12307110678 * V ^ 5 - 16631741340 * V ^ 4 + 8637097230 * V ^ 3 -
      2620962036 * V ^ 2 + 486432540 * V - 42725232) * T +
    (-9790737543 * V ^ 9 + 20897500149 * V ^ 8 - 9909189837 * V ^ 7 -
      10101295917 * V ^ 6 + 15270176376 * V ^ 5 - 9068334264 * V ^ 4 +
      3211649595 * V ^ 3 - 737943129 * V ^ 2 + 103666959 * V - 6690519)

private def rhoOneSplitMultiplierThree68 (T V : k) : k :=
  (-565984665 * V ^ 6 + 364037085 * V ^ 5 + 321521805 * V ^ 4 -
      368761005 * V ^ 3 + 154806795 * V ^ 2 - 38106288 * V + 4763286) *
      T ^ 2 +
    (2569517235 * V ^ 7 - 2839371165 * V ^ 6 - 705615867 * V ^ 5 +
      2356940835 * V ^ 4 - 1477908990 * V ^ 3 + 497627064 * V ^ 2 -
      101680920 * V + 10039788) * T +
    (892998027 * V ^ 9 - 3143709711 * V ^ 8 + 2595223233 * V ^ 7 +
      914994873 * V ^ 6 - 2627229249 * V ^ 5 + 1831331106 * V ^ 4 -
      710612595 * V ^ 3 + 175676985 * V ^ 2 - 26626347 * V + 1862487)

set_option maxHeartbeats 3000000 in
/-- Exact resultant certificate.  It is replayed by `ring`; no CAS result is
trusted by this theorem. -/
theorem rhoOne_affine_component_certificate68 (T V : k) :
    rhoOneNoncubicVPolynomial68 V * (3 * V - 1) ^ 4 =
      rhoOneSplitMultiplierFour68 T V * rhoOneAffineFour68 T V +
      rhoOneSplitMultiplierThree68 T V * rhoOneAffineThree68 T V := by
  simp only [rhoOneNoncubicVPolynomial68, rhoOneSplitMultiplierFour68,
    rhoOneSplitMultiplierThree68, rhoOneAffineFour68, rhoOneAffineThree68,
    rhoOneResidualFour68, rhoOneResidualThree68, rhoOneInitialA68,
    rhoOneInitialB68, rhoOneInitialC68, rhoOneInitialD68, rhoOneInitialE68,
    topRowFour68, topRowThree68]
  ring

theorem rhoOneAffineFour68_at_cubicV (T : k) :
    rhoOneAffineFour68 T (1 / 3) =
      -(1 / 6561 : k) * (27 * T + 17) * (27 * T - 1) ^ 2 := by
  simp only [rhoOneAffineFour68, rhoOneResidualFour68, rhoOneInitialA68,
    rhoOneInitialB68, rhoOneInitialC68, rhoOneInitialD68, rhoOneInitialE68,
    topRowFour68]
  ring

theorem rhoOneAffineThree68_at_cubicV (T : k) :
    rhoOneAffineThree68 T (1 / 3) =
      -(1 / 729 : k) * (27 * T + 2) * (27 * T - 1) ^ 2 := by
  simp only [rhoOneAffineThree68, rhoOneResidualThree68, rhoOneInitialA68,
    rhoOneInitialB68, rhoOneInitialC68, rhoOneInitialD68, rhoOneInitialE68,
    topRowThree68]
  ring

/-- Set-theoretic component classification of the two affine residuals. -/
theorem rhoOne_affine_component_split68 (T V : k)
    (h4 : rhoOneAffineFour68 T V = 0)
    (h3 : rhoOneAffineThree68 T V = 0) :
    (V = 1 / 3 ∧ T = 1 / 27) ∨ rhoOneNoncubicVPolynomial68 V = 0 := by
  have hcert := rhoOne_affine_component_certificate68 T V
  rw [h4, h3] at hcert
  simp only [mul_zero, add_zero] at hcert
  rcases mul_eq_zero.mp hcert with hP | hcore
  · exact Or.inr hP
  · left
    have hVlin : 3 * V - 1 = 0 := eq_zero_of_pow_eq_zero hcore
    have hV : V = 1 / 3 := by linear_combination (1 / 3 : k) * hVlin
    refine ⟨hV, ?_⟩
    rw [hV, rhoOneAffineFour68_at_cubicV] at h4
    rw [hV, rhoOneAffineThree68_at_cubicV] at h3
    have hsquare : (27 * T - 1) ^ 2 = 0 := by
      linear_combination (-(6561 / 15 : k)) * h4 + (729 / 15 : k) * h3
    have hTlin : 27 * T - 1 = 0 := eq_zero_of_pow_eq_zero hsquare
    linear_combination (1 / 27 : k) * hTlin

theorem rhoOneNoncubicVPolynomial68_ne_at_cubic :
    rhoOneNoncubicVPolynomial68 (1 / 3 : k) = -90 := by
  simp only [rhoOneNoncubicVPolynomial68]
  ring

theorem rhoOneResidualFour68_normalize (t v z : k) (hz : z ≠ 0) :
    rhoOneResidualFour68 t v z =
      z ^ 9 * rhoOneAffineFour68 (t / z ^ 3) (v / z ^ 2) := by
  simp only [rhoOneResidualFour68, rhoOneAffineFour68, rhoOneInitialA68,
    rhoOneInitialB68, rhoOneInitialC68, rhoOneInitialD68, rhoOneInitialE68,
    topRowFour68]
  field_simp [hz]

theorem rhoOneResidualThree68_normalize (t v z : k) (hz : z ≠ 0) :
    rhoOneResidualThree68 t v z =
      z ^ 10 * rhoOneAffineThree68 (t / z ^ 3) (v / z ^ 2) := by
  simp only [rhoOneResidualThree68, rhoOneAffineThree68, rhoOneInitialA68,
    rhoOneInitialB68, rhoOneInitialC68, rhoOneInitialD68, rhoOneInitialE68,
    topRowThree68]
  field_simp [hz]

theorem rhoOne_residual_at_z_zero68 (t v : k)
    (h4 : rhoOneResidualFour68 t v 0 = 0)
    (h3 : rhoOneResidualThree68 t v 0 = 0) : t = 0 ∧ v = 0 := by
  have h4' : t * (5 * v ^ 3 - 3 * t ^ 2) = 0 := by
    have h4raw : 5 * v ^ 3 * t - 3 * t ^ 3 = 0 := by
      simpa [rhoOneResidualFour68, rhoOneInitialA68, rhoOneInitialB68,
        rhoOneInitialC68, rhoOneInitialD68, rhoOneInitialE68, topRowFour68]
        using h4
    linear_combination h4raw
  have h3' : v ^ 2 * (4 * v ^ 3 - 45 * t ^ 2) = 0 := by
    have h3raw : 4 * v ^ 5 - 45 * v ^ 2 * t ^ 2 = 0 := by
      simpa [rhoOneResidualThree68, rhoOneInitialA68, rhoOneInitialB68,
        rhoOneInitialC68, rhoOneInitialD68, rhoOneInitialE68, topRowThree68]
        using h3
    linear_combination h3raw
  by_cases ht : t = 0
  · subst t
    have hv5 : v ^ 5 = 0 := by
      simpa using h3'
    exact ⟨rfl, eq_zero_of_pow_eq_zero hv5⟩
  · have hrel4 : 5 * v ^ 3 - 3 * t ^ 2 = 0 :=
      (mul_eq_zero.mp h4').resolve_left ht
    have hv : v ≠ 0 := by
      intro hv0
      rw [hv0] at hrel4
      have ht2 : t ^ 2 = 0 := by linear_combination (-(1 / 3 : k)) * hrel4
      exact ht (eq_zero_of_pow_eq_zero ht2)
    have hrel3 : 4 * v ^ 3 - 45 * t ^ 2 = 0 :=
      (mul_eq_zero.mp h3').resolve_left (pow_ne_zero 2 hv)
    have ht2 : t ^ 2 = 0 := by
      linear_combination (4 / 213 : k) * hrel4 - (5 / 213 : k) * hrel3
    exact (ht (eq_zero_of_pow_eq_zero ht2)).elim

theorem SquareConstantLIntegratedLocalRootData68.rhoOne_residual_with_scale_single
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    ∃ c t v z : k, c ≠ 0 ∧
      ratFuncAtHahn46 T.root (algebraMap k[X] (RatFunc k) h0) =
        HahnSeries.single (1 : ℚ) c ∧
      t = (c ^ 3)⁻¹ * (p.coeff 3).eval T.root ∧
      v = (c ^ 2)⁻¹ * u.eval T.root ∧
      z = c⁻¹ * g.eval T.root ∧
      rhoOneResidualFour68 t v z = 0 ∧ rhoOneResidualThree68 t v z = 0 := by
  obtain ⟨c, hc, hsingle⟩ := ratFuncAtHahn68_linearRoot_eq_single
    h0 T.root T.scale_degree T.root_eq
  obtain ⟨hAclear, hBclear, hCclear, hDclear, hEclear⟩ :=
    T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero hH hp6 hp5 hp4
  have hAco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedA68RhoOne g u) T.source.A 2 hc hsingle hAclear
  have hBco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedB68RhoOne g u (p.coeff 3)) T.source.B 3 hc hsingle hBclear
  have hCco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)) T.source.C0 4
    hc hsingle hCclear
  have hDco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1))
    T.source.D 5 hc hsingle hDclear
  have hEco := localHahn_coeff_neg_of_cleared T.root c h0
    (localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2) (p.coeff 1)
      (p.coeff 0)) T.source.E 6 hc hsingle hEclear
  norm_num at hAco hBco hCco hDco hEco
  let t : k := (c ^ 3)⁻¹ * (p.coeff 3).eval T.root
  let v : k := (c ^ 2)⁻¹ * u.eval T.root
  let z : k := c⁻¹ * g.eval T.root
  have hAroot : (localClearedA68RhoOne g u).eval T.root =
      u.eval T.root - (5 / 12 : k) * g.eval T.root ^ 2 := by
    simp [localClearedA68RhoOne]
  have hBroot : (localClearedB68RhoOne g u (p.coeff 3)).eval T.root =
      (p.coeff 3).eval T.root - (2 / 3 : k) * u.eval T.root *
        g.eval T.root + (5 / 27 : k) * g.eval T.root ^ 3 := by
    simp [localClearedB68RhoOne]
  have hCroot :
      (localClearedC68RhoOne h0 g u (p.coeff 3) (p.coeff 2)).eval T.root =
        -(1 / 2 : k) * (p.coeff 3).eval T.root * g.eval T.root +
          (1 / 6 : k) * u.eval T.root * g.eval T.root ^ 2 -
          (5 / 144 : k) * g.eval T.root ^ 4 := by
    simp [localClearedC68RhoOne, T.root_eq]
  have hDroot :
      (localClearedD68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
        (p.coeff 1)).eval T.root =
        (1 / 12 : k) * (p.coeff 3).eval T.root * g.eval T.root ^ 2 -
          (1 / 54 : k) * u.eval T.root * g.eval T.root ^ 3 +
          (1 / 324 : k) * g.eval T.root ^ 5 := by
    simp [localClearedD68RhoOne, T.root_eq]
  have hEroot :
      (localClearedE68RhoOne h0 g u (p.coeff 3) (p.coeff 2)
        (p.coeff 1) (p.coeff 0)).eval T.root =
        -(1 / 216 : k) * (p.coeff 3).eval T.root * g.eval T.root ^ 3 +
          (1 / 1296 : k) * u.eval T.root * g.eval T.root ^ 4 -
          (5 / 46656 : k) * g.eval T.root ^ 6 := by
    simp [localClearedE68RhoOne, T.root_eq]
  have hAform : (ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ) =
      rhoOneInitialA68 v z := by
    rw [hAco, hAroot]
    simp only [rhoOneInitialA68, v, z]
    field_simp [hc]
  have hBform : (ratFuncAtHahn46 T.root T.source.B).coeff (-3 : ℚ) =
      rhoOneInitialB68 t v z := by
    rw [hBco, hBroot]
    simp only [rhoOneInitialB68, t, v, z]
    field_simp [hc]
  have hCform : (ratFuncAtHahn46 T.root T.source.C0).coeff (-4 : ℚ) =
      rhoOneInitialC68 t v z := by
    rw [hCco, hCroot]
    simp only [rhoOneInitialC68, t, v, z]
    field_simp [hc]
  have hDform : (ratFuncAtHahn46 T.root T.source.D).coeff (-5 : ℚ) =
      rhoOneInitialD68 t v z := by
    rw [hDco, hDroot]
    simp only [rhoOneInitialD68, t, v, z]
    field_simp [hc]
  have hEform : (ratFuncAtHahn46 T.root T.source.E).coeff (-6 : ℚ) =
      rhoOneInitialE68 t v z := by
    rw [hEco, hEroot]
    simp only [rhoOneInitialE68, t, v, z]
    field_simp [hc]
  have htop4 := T.topRowFourRhoOne_zero hp hH hp6 hp5 hp4
  have htop3 := T.topRowThreeRhoOne_zero hp hH hp6 hp5 hp4
  rw [hAform, hBform, hCform, hDform, hEform] at htop4 htop3
  exact ⟨c, t, v, z, hc, hsingle, rfl, rfl, rfl, htop4, htop3⟩

def RhoOneNoncubicSourcePacket68
    {p q : k[X][X]} {j l : k} {h0 : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (g u : k[X]) : Prop :=
  ∃ c t v z : k, c ≠ 0 ∧
    ratFuncAtHahn46 T.root (algebraMap k[X] (RatFunc k) h0) =
      HahnSeries.single (1 : ℚ) c ∧
    t = (c ^ 3)⁻¹ * (p.coeff 3).eval T.root ∧
    v = (c ^ 2)⁻¹ * u.eval T.root ∧
    z = c⁻¹ * g.eval T.root ∧ z ≠ 0 ∧
    rhoOneNoncubicVPolynomial68 (v / z ^ 2) = 0 ∧
    rhoOneAffineFour68 (t / z ^ 3) (v / z ^ 2) = 0 ∧
    rhoOneAffineThree68 (t / z ^ 3) (v / z ^ 2) = 0

/-- Global set-theoretic split: the rational cubic component receives the
transverse descent, leaving only the explicit degree-ten component. -/
theorem SquareConstantLIntegratedLocalRootData68.rhoOne_component_split_or_descend
    {p q : k[X][X]} {j l : k} {h0 H g u : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    (h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
      RhoOneNoncubicSourcePacket68 T g u := by
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, h4, h3⟩ :=
    T.rhoOne_residual_with_scale_single hp hH hp6 hp5 hp4
  by_cases hz : z = 0
  · obtain ⟨ht0, hv0⟩ := rhoOne_residual_at_z_zero68 t v (by simpa [hz] using h4)
      (by simpa [hz] using h3)
    have hbranch : RhoOneSourceCubicBranch68 T g u := by
      refine ⟨c, hc, hsingle, ?_, ?_⟩
      · rw [← hv, ← hzdef, hv0, hz]
        norm_num
      · rw [← ht, ← hzdef, ht0, hz]
        norm_num
    left
    exact T.rhoOne_cubicBranch_next_divisibilities hp hH hp6 hp5 hp4 hbranch
  · have h4aff : rhoOneAffineFour68 (t / z ^ 3) (v / z ^ 2) = 0 := by
      rw [rhoOneResidualFour68_normalize t v z hz] at h4
      exact (mul_eq_zero.mp h4).resolve_left (pow_ne_zero 9 hz)
    have h3aff : rhoOneAffineThree68 (t / z ^ 3) (v / z ^ 2) = 0 := by
      rw [rhoOneResidualThree68_normalize t v z hz] at h3
      exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 10 hz)
    rcases rhoOne_affine_component_split68 (t / z ^ 3) (v / z ^ 2)
      h4aff h3aff with hcore | hnon
    · have hvcore : v = z ^ 2 / 3 := by
        calc
          v = (v / z ^ 2) * z ^ 2 := by field_simp [hz]
          _ = (1 / 3) * z ^ 2 := by rw [hcore.1]
          _ = z ^ 2 / 3 := by ring
      have htcore : t = z ^ 3 / 27 := by
        calc
          t = (t / z ^ 3) * z ^ 3 := by field_simp [hz]
          _ = (1 / 27) * z ^ 3 := by rw [hcore.2]
          _ = z ^ 3 / 27 := by ring
      have hbranch : RhoOneSourceCubicBranch68 T g u := by
        refine ⟨c, hc, hsingle, ?_, ?_⟩
        · rw [← hv, ← hzdef, hvcore]
        · rw [← ht, ← hzdef, htcore]
      left
      exact T.rhoOne_cubicBranch_next_divisibilities hp hH hp6 hp5 hp4 hbranch
    · right
      exact ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hnon, h4aff, h3aff⟩

end RhoOneComponentSplit68

#print axioms rhoOne_affine_component_certificate68
#print axioms rhoOne_affine_component_split68
#print axioms SquareConstantLIntegratedLocalRootData68.rhoOne_component_split_or_descend

end Max11DegreeRoutes
