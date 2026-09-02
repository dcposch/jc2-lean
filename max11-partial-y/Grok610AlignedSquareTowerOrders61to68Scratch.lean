import Grok610AlignedSquareSourceWrapperScratch
import Grok610PoleCeilingLemmaScratch

/-! # Orders `61` through `68` of the aligned-square `(6,10)` bounded tower

Untracked working note.  No tracked file was edited.

`Grok610AlignedSquareSourceWrapperScratch` established the aligned-face
wrapper of the weight-fifteen primitive: native clearing `5 · 15 = 75`,
MixedPair remaining pole `21`, and the `w₁ = 0` child with base order
`61` (remaining pole `14`).  Orders `61` through `75` exhaust the tower
before the cancel-and-expose endgame.  This file is the analog of the
committed `Grok610DegreeZeroOrder72`-`75` chain, batched through order
`68`.  It does not close either limb.

The two live MixedPair limbs, honoring NinthLoads / MixedPair / M1M2:

* **`w₁ = 0`.**  The linear scale upgrades `w₁ = h₀ w₁n`.  The MixedPair
  jet then starts at `h⁷` (order `61`).  The complementary child after
  `e₁ = h₀ e₁b`, `e₃ = h₀ e₃b`, `a₂ = h₀ a₂b` (the `a₂b = 0` collision
  is already empty) has identically vanishing orders `61`–`63` and first
  surviving coefficient at order `64`.  The residual `6 p₁ = a₂b w₁n` is
  not inserted as a polynomial identity.
* **`μ = 0`.**  Endgame gives `e₁ = h₀ e₁n` with `w₁(a) ≠ 0`.  The
  order-`21` obstruction forces `q₈(a) = 0`, upgraded to `b₈ = h₀ b₈n`.
  The mixed jet then starts at `h¹` (order `55`); this batch extracts
  the mixed coefficients of orders `61` through `68`.

Each order `k` is the `h^(k-54)` coefficient of the MixedPair jet, or
the same coefficient after the limb substitution.  Vanishing is recorded
in the `h₀`-divisibility shape the ceiling lemma consumes.  The next
unused compact-numerator order is `69`.  Residual remaining pole after
this batch is `6` on the `w₁ = 0` peel (`21 - 15`).  No chamber is
closed.

CAS: `derive_610_aligned_square_tower_orders61to68.py` (job
`20260902T031400Z-aligned-square-tower-61to68-32890`).  No `sorry`, no new axioms, no finite-root shortcut, no
closure overclaim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 1600000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Bookkeeping: base order `61`, remaining pole `14` -/

/-- First surviving order of the `w₁ = 0` MixedPair jet. -/
def alignedSquareTowerBaseOrder610 : ℕ := 61

/-- Remaining pole of `ρ` after the `w₁ = 0` peel: `75 - 61 = 14`. -/
def alignedSquareW1ZeroRemainingPole610 : ℕ := 14

/-- Last order extracted in this batch. -/
def alignedSquareTowerBatchLastOrder610 : ℕ := 68

/-- Next unused compact-numerator order after this batch. -/
def alignedSquareTowerNextUnusedOrder610 : ℕ := 69

/-- Vanishing multiplicity of the MixedPair jet recorded by this batch
on the `w₁ = 0` peel: orders `54` through `68`. -/
def alignedSquareTowerBatchDivisibility610 : ℕ := 15

theorem alignedSquareTowerBaseOrder610_eq :
    alignedSquareTowerBaseOrder610 = 61 :=
  rfl

theorem alignedSquareW1ZeroRemainingPole610_eq :
    alignedSquareW1ZeroRemainingPole610 = 14 :=
  rfl

theorem alignedSquareTowerBatchLastOrder610_eq :
    alignedSquareTowerBatchLastOrder610 = 68 :=
  rfl

theorem alignedSquareTowerNextUnusedOrder610_eq :
    alignedSquareTowerNextUnusedOrder610 = 69 :=
  rfl

theorem alignedSquareTowerBatchDivisibility610_eq :
    alignedSquareTowerBatchDivisibility610 = 15 :=
  rfl

theorem alignedSquareW1ZeroRemainingPole610_eq_sub :
    alignedSquareW1ZeroRemainingPole610 =
      alignedSquareTowerCeiling610 - alignedSquareTowerBaseOrder610 :=
  rfl

theorem alignedSquareTowerBaseOrder610_eq_mixedPair_add :
    alignedSquareTowerBaseOrder610 = alignedSquareBaseOrder610 + 7 :=
  rfl

theorem alignedSquareTowerNextUnusedOrder610_succ :
    alignedSquareTowerNextUnusedOrder610 =
      alignedSquareTowerBatchLastOrder610 + 1 :=
  rfl

theorem alignedSquareTowerBatchDivisibility610_eq_add :
    alignedSquareTowerBatchDivisibility610 =
      alignedSquareTowerBatchLastOrder610 - alignedSquareBaseOrder610 +
        1 :=
  rfl

theorem alignedSquareW1ZeroRemainingPole610_ne_six :
    alignedSquareW1ZeroRemainingPole610 ≠ 6 := by
  decide

theorem alignedSquareTowerBatchLastOrder610_lt_ceiling :
    alignedSquareTowerBatchLastOrder610 <
      alignedSquareTowerCeiling610 := by
  decide

#print axioms alignedSquareW1ZeroRemainingPole610_eq_sub
#print axioms alignedSquareTowerBaseOrder610_eq_mixedPair_add
#print axioms alignedSquareW1ZeroRemainingPole610_ne_six
/-! ## Linear divisibility and clearing cancellation -/

section AlignedSquareTowerDvd610

variable {k : Type*} [Field k]

/-- A degree-one polynomial divides every polynomial vanishing at its
unique root. -/
theorem alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610
    (h0 f : k[X]) (a : k) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hf : f.eval a = 0) : h0 ∣ f := by
  have hlinearRoot : X - C a ∣ f := Polynomial.dvd_iff_isRoot.mpr hf
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by simpa [← hlinear] using hroot
  have hd : d = -(c * a) := by linear_combination hca
  have hfactor : h0 = C c * (X - C a) := by
    calc
      h0 = C c * X + C d := hlinear.symm
      _ = C c * X - C (c * a) := by rw [hd, map_neg]; ring
      _ = C c * (X - C a) := by rw [mul_sub, ← map_mul]
  have hscaleDvd : h0 ∣ X - C a := by
    refine ⟨C c⁻¹, ?_⟩
    rw [hfactor]
    calc
      X - C a = 1 * (X - C a) := by rw [one_mul]
      _ = (C c * C c⁻¹) * (X - C a) := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]
      _ = C c * (X - C a) * C c⁻¹ := by ring
  exact hscaleDvd.trans hlinearRoot

/-- Cancel `m` polynomial powers from a pole-`(m+n)` clearing. -/
theorem alignedSquare_algebraMap_cancel_pow610
    (h0 Q : k[X]) (rho : RatFunc k) (m n : ℕ) (hh0 : h0 ≠ 0)
    (hclear :
      algebraMap k[X] (RatFunc k) (h0 ^ m * Q) =
        (algebraMap k[X] (RatFunc k) h0) ^ (m + n) * rho) :
    algebraMap k[X] (RatFunc k) Q =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero m hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ m * Q) =
        hRF ^ m * algebraMap k[X] (RatFunc k) Q := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ m * algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k) (h0 ^ m * Q) := hmapPow.symm
    _ = hRF ^ (m + n) * rho := hclear
    _ = hRF ^ m * (hRF ^ n * rho) := by
      rw [pow_add]
      ring

/-- Cancel one polynomial power of a linear clearing. -/
theorem alignedSquare_algebraMap_cancel_one_clearing610
    (h0 old new : k[X]) (rho : RatFunc k) (r : ℕ) (hh0 : h0 ≠ 0)
    (hfact : old = h0 * new)
    (hclear : algebraMap k[X] (RatFunc k) old =
      (algebraMap k[X] (RatFunc k) h0) ^ (r + 1) * rho) :
    algebraMap k[X] (RatFunc k) new =
      (algebraMap k[X] (RatFunc k) h0) ^ r * rho :=
  alignedSquare_algebraMap_cancel_pow610 h0 new rho 1 r hh0
    (by
      have hclear' :
          algebraMap k[X] (RatFunc k) (h0 * new) =
            (algebraMap k[X] (RatFunc k) h0) ^ (1 + r) * rho := by
        simpa [hfact, add_comm r 1] using hclear
      simpa [pow_one] using hclear')

#print axioms alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610
#print axioms alignedSquare_algebraMap_cancel_pow610
#print axioms alignedSquare_algebraMap_cancel_one_clearing610

/-- Evaluation of a remaining numerator `c₀ + h₀ · rest` at a root of
the linear scale is the head `c₀`. -/
theorem alignedSquare_eval_head_of_linear_factor610
    (h0 c0 rest : k[X]) (a : k) (hroot : h0.eval a = 0) :
    (c0 + h0 * rest).eval a = c0.eval a := by
  simp [Polynomial.eval_add, Polynomial.eval_mul, hroot, zero_mul,
    add_zero]

#print axioms alignedSquare_eval_head_of_linear_factor610

end AlignedSquareTowerDvd610

/-! ## Remaining-pole `14` head obstruction on the `w₁ = 0` peel -/

section AlignedSquarePoleFourteen610

variable {k : Type*} [Field k] [CharZero k]

/-- Order-`14` specialisation matching the `w₁ = 0` remaining pole. -/
theorem alignedSquare_poleFourteen_head_eval_zero610
    (a j : k) (h0 A0 : k[X]) (rho : RatFunc k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^
          alignedSquareW1ZeroRemainingPole610 *
        rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    A0.eval a = 0 :=
  alignedSquare_localLinearPole_head_eval_zero610
    alignedSquareW1ZeroRemainingPole610 (by decide) a j h0 A0 rho
    hdegree hroot hclear hderiv

#print axioms alignedSquare_poleFourteen_head_eval_zero610

end AlignedSquarePoleFourteen610
/-! ## Order `61` (MixedPair `h^7`) -/
set_option maxHeartbeats 1600000000 in
/-- Frozen order-`61` coefficient of the MixedPair jet (`h^7` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder61610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) : R :=
    (69754744080 : R) * w1 ^ 13 * e1
    + (2918248819200 : R) * w1 ^ 8 * e1 * b5
    - (49389740015616 : R) * w1 ^ 6 * e1 * e3 * b6
    - (597166856552448 : R) * w1 ^ 5 * e1 ^ 3 * b6
    + (2823931017363456 : R) * w1 ^ 5 * e1 * a2 * b6
    + (3294586186924032 : R) * w1 ^ 5 * e1 * a1 * b7
    + (3765241356484608 : R) * w1 ^ 5 * e1 * a0 * b8
    + (36862151639040 : R) * w1 ^ 4 * e1 * e3 ^ 2 * b7
    + (279285007712256 : R) * w1 ^ 3 * e1 ^ 3 * e3 * b7
    - (2514386764431360 : R) * w1 ^ 3 * e1 * e3 * a2 * b7
    - (2873584873635840 : R) * w1 ^ 3 * e1 * e3 * a1 * b8
    + (175637310750720 : R) * w1 ^ 2 * e1 ^ 5 * b7
    - (5901413641224192 : R) * w1 ^ 2 * e1 ^ 3 * a2 * b7
    - (6744472732827648 : R) * w1 ^ 2 * e1 ^ 3 * a1 * b8
    - (3083892424704 : R) * w1 ^ 2 * e1 * e3 ^ 3 * b8
    + (35940940220989440 : R) * w1 ^ 2 * e1 * a2 ^ 2 * b7
    + (82150720505118720 : R) * w1 ^ 2 * e1 * a2 * a1 * b8
    - (11013901516800 : R) * w1 * e1 ^ 3 * e3 ^ 2 * b8
    + (142740163657728 : R) * w1 * e1 * e3 ^ 2 * a2 * b8
    - (3304170455040 : R) * e1 ^ 5 * e3 * b8
    + (142740163657728 : R) * e1 ^ 3 * e3 * a2 * b8
    - (1217047711186944 : R) * e1 * e3 * a2 ^ 2 * b8
/-- Order-`61` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder61610 {R : Type*} [CommRing R] (e1 e3 a2 b8 : R) : R :=
    - (3304170455040 : R) * e1 ^ 5 * e3 * b8
    + (142740163657728 : R) * e1 ^ 3 * e3 * a2 * b8
    - (1217047711186944 : R) * e1 * e3 * a2 ^ 2 * b8
/-- Order-`61` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder61610 {R : Type*} [CommRing R] (w1n e1 e3 a2 b8 : R) : R :=
    (25607321026560 : R) * w1n * e1 ^ 6 * b8
    - (1338189034291200 : R) * w1n * e1 ^ 4 * a2 * b8
    + (17342929884413952 : R) * w1n * e1 ^ 2 * a2 ^ 2 * b8
    - (32860288202047488 : R) * w1n * a2 ^ 3 * b8
    - (3304170455040 : R) * e1 ^ 5 * e3 * b8
    + (142740163657728 : R) * e1 ^ 3 * e3 * a2 * b8
    - (1217047711186944 : R) * e1 * e3 * a2 ^ 2 * b8
/-- Order-`61` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder61610 {R : Type*} [CommRing R] (w1n : R) : R :=
    0
set_option maxHeartbeats 1600000000 in
/-- Order-`61` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order61610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b8n : R) : R :=
    - (302796245606400 : R) * w1 ^ 7 * e1n ^ 3 * b8n
    - (44824301862912 : R) * w1 ^ 7 * a0 * b8n
    + (169565897539584 : R) * w1 ^ 6 * e1n ^ 2 * e3 * b8n
    - (1778030640562176 : R) * w1 ^ 6 * e1n * a1 * b8n
    - (7166002278629376 : R) * w1 ^ 5 * e1n ^ 2 * a2 * b8n
    - (29489721311232 : R) * w1 ^ 5 * e1n * e3 ^ 2 * b8n
    + (418360150720512 : R) * w1 ^ 5 * e3 * a1 * b8n
    + (2274921358295040 : R) * w1 ^ 4 * e1n * e3 * a2 * b8n
    + (1560302714880 : R) * w1 ^ 4 * e3 ^ 3 * b8n
    - (22591448138907648 : R) * w1 ^ 4 * a2 * a1 * b8n
    - (38793395794083840 : R) * w1 ^ 3 * e1n * a2 ^ 2 * b8n
    - (159643604090880 : R) * w1 ^ 3 * e3 ^ 2 * a2 * b8n
    + (4563928916951040 : R) * w1 ^ 2 * e3 * a2 ^ 2 * b8n
    - (32860288202047488 : R) * w1 * a2 ^ 3 * b8n
/-! ## Order `62` (MixedPair `h^8`) -/
set_option maxHeartbeats 1600000000 in
/-- Frozen order-`62` coefficient of the MixedPair jet (`h^8` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder62610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : R) : R :=
    - (24284496600 : R) * w1 ^ 12 * e3
    - (14193574012800 : R) * w1 ^ 11 * e1 ^ 2
    + (2062916968320 : R) * w1 ^ 11 * a2
    + (11972302848 : R) * w1 ^ 9 * b4
    - (1037599580160 : R) * w1 ^ 7 * e3 * b5
    - (185211525058560 : R) * w1 ^ 6 * e1 ^ 2 * b5
    + (90510609530880 : R) * w1 ^ 6 * a2 * b5
    + (108612731437056 : R) * w1 ^ 6 * a1 * b6
    + (126714853343232 : R) * w1 ^ 6 * a0 * b7
    + (5810557648896 : R) * w1 ^ 5 * e3 ^ 2 * b6
    + (284365169786880 : R) * w1 ^ 4 * e1 ^ 2 * e3 * b6
    - (627540226080768 : R) * w1 ^ 4 * e3 * a2 * b6
    - (732130263760896 : R) * w1 ^ 4 * e3 * a1 * b7
    - (836720301441024 : R) * w1 ^ 4 * e3 * a0 * b8
    + (538621086302208 : R) * w1 ^ 3 * e1 ^ 4 * b6
    - (9698348948520960 : R) * w1 ^ 3 * e1 ^ 2 * a2 * b6
    - (11314740439941120 : R) * w1 ^ 3 * e1 ^ 2 * a1 * b7
    - (12931131931361280 : R) * w1 ^ 3 * e1 ^ 2 * a0 * b8
    - (1724545105920 : R) * w1 ^ 3 * e3 ^ 3 * b7
    + (15640233326936064 : R) * w1 ^ 3 * a2 ^ 2 * b6
    + (36493877762850816 : R) * w1 ^ 3 * a2 * a1 * b7
    + (41707288871829504 : R) * w1 ^ 3 * a2 * a0 * b8
    + (20853644435914752 : R) * w1 ^ 3 * a1 ^ 2 * b8
    - (36428479266816 : R) * w1 ^ 2 * e1 ^ 2 * e3 ^ 2 * b7
    + (147905103790080 : R) * w1 ^ 2 * e3 ^ 2 * a2 * b7
    + (169034404331520 : R) * w1 ^ 2 * e3 ^ 2 * a1 * b8
    - (43367237222400 : R) * w1 * e1 ^ 4 * e3 * b7
    + (1124078788804608 : R) * w1 * e1 ^ 2 * e3 * a2 * b7
    + (1284661472919552 : R) * w1 * e1 ^ 2 * e3 * a1 * b8
    + (48950673408 : R) * w1 * e3 ^ 4 * b8
    - (3194750241865728 : R) * w1 * e3 * a2 ^ 2 * b7
    - (7302286267121664 : R) * w1 * e3 * a2 * a1 * b8
    - (4336723722240 : R) * e1 ^ 6 * b7
    + (281019697201152 : R) * e1 ^ 4 * a2 * b7
    + (321165368229888 : R) * e1 ^ 4 * a1 * b8
    + (293704040448 : R) * e1 ^ 2 * e3 ^ 3 * b8
    - (4792125362798592 : R) * e1 ^ 2 * a2 ^ 2 * b7
    - (10953429400682496 : R) * e1 ^ 2 * a2 * a1 * b8
    - (1669475598336 : R) * e3 ^ 3 * a2 * b8
    + (13270501004673024 : R) * a2 ^ 3 * b7
    + (45498860587450368 : R) * a2 ^ 2 * a1 * b8
/-- Order-`62` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder62610 {R : Type*} [CommRing R] (e1 e3 a2 a1 b8 b7 : R) : R :=
    - (4336723722240 : R) * e1 ^ 6 * b7
    + (281019697201152 : R) * e1 ^ 4 * a2 * b7
    + (321165368229888 : R) * e1 ^ 4 * a1 * b8
    + (293704040448 : R) * e1 ^ 2 * e3 ^ 3 * b8
    - (4792125362798592 : R) * e1 ^ 2 * a2 ^ 2 * b7
    - (10953429400682496 : R) * e1 ^ 2 * a2 * a1 * b8
    - (1669475598336 : R) * e3 ^ 3 * a2 * b8
    + (13270501004673024 : R) * a2 ^ 3 * b7
    + (45498860587450368 : R) * a2 ^ 2 * a1 * b8
set_option maxHeartbeats 1600000000 in
/-- Order-`62` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder62610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 b8 b7 : R) : R :=
    - (323395683287040 : R) * w1n ^ 3 * e1 ^ 5 * b8
    + (8617937380835328 : R) * w1n ^ 3 * e1 ^ 3 * a2 * b8
    - (38793395794083840 : R) * w1n ^ 3 * e1 * a2 ^ 2 * b8
    + (111515752857600 : R) * w1n ^ 2 * e1 ^ 4 * e3 * b8
    - (2248157577609216 : R) * w1n ^ 2 * e1 ^ 2 * e3 * a2 * b8
    + (4563928916951040 : R) * w1n ^ 2 * e3 * a2 ^ 2 * b8
    - (11013901516800 : R) * w1n * e1 ^ 3 * e3 ^ 2 * b8
    + (142740163657728 : R) * w1n * e1 * e3 ^ 2 * a2 * b8
    - (4336723722240 : R) * e1 ^ 6 * b7
    + (281019697201152 : R) * e1 ^ 4 * a2 * b7
    + (321165368229888 : R) * e1 ^ 4 * a1 * b8
    + (293704040448 : R) * e1 ^ 2 * e3 ^ 3 * b8
    - (4792125362798592 : R) * e1 ^ 2 * a2 ^ 2 * b7
    - (10953429400682496 : R) * e1 ^ 2 * a2 * a1 * b8
    - (1669475598336 : R) * e3 ^ 3 * a2 * b8
    + (13270501004673024 : R) * a2 ^ 3 * b7
    + (45498860587450368 : R) * a2 ^ 2 * a1 * b8
/-- Order-`62` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder62610 {R : Type*} [CommRing R] (w1n : R) : R :=
    0
set_option maxHeartbeats 1600000000 in
/-- Order-`62` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order62610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 : R) : R :=
    (69754744080 : R) * w1 ^ 13 * e1n
    - (24284496600 : R) * w1 ^ 12 * e3
    + (2062916968320 : R) * w1 ^ 11 * a2
    + (11972302848 : R) * w1 ^ 9 * b4
    + (2918248819200 : R) * w1 ^ 8 * e1n * b5
    + (100543399317504 : R) * w1 ^ 7 * e1n ^ 2 * b6
    - (1037599580160 : R) * w1 ^ 7 * e3 * b5
    + (445110481041408 : R) * w1 ^ 6 * e1n ^ 3 * b7
    - (49389740015616 : R) * w1 ^ 6 * e1n * e3 * b6
    + (90510609530880 : R) * w1 ^ 6 * a2 * b5
    + (108612731437056 : R) * w1 ^ 6 * a1 * b6
    + (126714853343232 : R) * w1 ^ 6 * a0 * b7
    - (232231555325952 : R) * w1 ^ 5 * e1n ^ 2 * e3 * b7
    + (2823931017363456 : R) * w1 ^ 5 * e1n * a2 * b6
    + (3294586186924032 : R) * w1 ^ 5 * e1n * a1 * b7
    + (5810557648896 : R) * w1 ^ 5 * e3 ^ 2 * b6
    + (8957502848286720 : R) * w1 ^ 4 * e1n ^ 2 * a2 * b7
    + (36862151639040 : R) * w1 ^ 4 * e1n * e3 ^ 2 * b7
    - (627540226080768 : R) * w1 ^ 4 * e3 * a2 * b6
    - (732130263760896 : R) * w1 ^ 4 * e3 * a1 * b7
    - (2514386764431360 : R) * w1 ^ 3 * e1n * e3 * a2 * b7
    - (1724545105920 : R) * w1 ^ 3 * e3 ^ 3 * b7
    + (15640233326936064 : R) * w1 ^ 3 * a2 ^ 2 * b6
    + (36493877762850816 : R) * w1 ^ 3 * a2 * a1 * b7
    + (35940940220989440 : R) * w1 ^ 2 * e1n * a2 ^ 2 * b7
    + (147905103790080 : R) * w1 ^ 2 * e3 ^ 2 * a2 * b7
    - (3194750241865728 : R) * w1 * e3 * a2 ^ 2 * b7
    + (13270501004673024 : R) * a2 ^ 3 * b7
/-! ## Order `63` (MixedPair `h^9`) -/
set_option maxHeartbeats 1600000000 in
/-- Frozen order-`63` coefficient of the MixedPair jet (`h^9` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder63610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : R) : R :=
    (7517337347520 : R) * w1 ^ 10 * e1 * e3
    + (205018291296000 : R) * w1 ^ 9 * e1 ^ 3
    - (472460881052160 : R) * w1 ^ 9 * e1 * a2
    - (7470716977152 : R) * w1 ^ 7 * e1 * b4
    + (87158364733440 : R) * w1 ^ 5 * e1 * e3 * b5
    + (710912924467200 : R) * w1 ^ 4 * e1 ^ 3 * b5
    - (4706551695605760 : R) * w1 ^ 4 * e1 * a2 * b5
    - (5647862034726912 : R) * w1 ^ 4 * e1 * a1 * b6
    - (6589172373848064 : R) * w1 ^ 4 * e1 * a0 * b7
    - (39910901022720 : R) * w1 ^ 3 * e1 * e3 ^ 2 * b6
    - (187346464800768 : R) * w1 ^ 2 * e1 ^ 3 * e3 * b6
    + (2281964458475520 : R) * w1 ^ 2 * e1 * e3 * a2 * b6
    + (2662291868221440 : R) * w1 ^ 2 * e1 * e3 * a1 * b7
    + (3042619277967360 : R) * w1 ^ 2 * e1 * e3 * a0 * b8
    - (66909451714560 : R) * w1 * e1 ^ 5 * b6
    + (2890488314068992 : R) * w1 * e1 ^ 3 * a2 * b6
    + (3372236366413824 : R) * w1 * e1 ^ 3 * a1 * b7
    + (3853984418758656 : R) * w1 * e1 ^ 3 * a0 * b8
    + (1541946212352 : R) * w1 * e1 * e3 ^ 3 * b7
    - (24645216151535616 : R) * w1 * e1 * a2 ^ 2 * b6
    - (57505504353583104 : R) * w1 * e1 * a2 * a1 * b7
    - (65720576404094976 : R) * w1 * e1 * a2 * a0 * b8
    - (32860288202047488 : R) * w1 * e1 * a1 ^ 2 * b8
    + (2312919318528 : R) * e1 ^ 3 * e3 ^ 2 * b7
    - (39441361010688 : R) * e1 * e3 ^ 2 * a2 * b7
    - (45075841155072 : R) * e1 * e3 ^ 2 * a1 * b8
/-- Order-`63` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder63610 {R : Type*} [CommRing R] (e1 e3 a2 a1 b8 b7 : R) : R :=
    (2312919318528 : R) * e1 ^ 3 * e3 ^ 2 * b7
    - (39441361010688 : R) * e1 * e3 ^ 2 * a2 * b7
    - (45075841155072 : R) * e1 * e3 ^ 2 * a1 * b8
set_option maxHeartbeats 1600000000 in
/-- Order-`63` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder63610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 b8 b7 : R) : R :=
    (673276357877760 : R) * w1n ^ 5 * e1 ^ 4 * b8
    - (7166002278629376 : R) * w1n ^ 5 * e1 ^ 2 * a2 * b8
    + (5647862034726912 : R) * w1n ^ 5 * a2 ^ 2 * b8
    - (332482152038400 : R) * w1n ^ 4 * e1 ^ 3 * e3 * b8
    + (2274921358295040 : R) * w1n ^ 4 * e1 * e3 * a2 * b8
    + (53197144326144 : R) * w1n ^ 3 * e1 ^ 2 * e3 ^ 2 * b8
    - (159643604090880 : R) * w1n ^ 3 * e3 ^ 2 * a2 * b8
    + (175637310750720 : R) * w1n ^ 2 * e1 ^ 5 * b7
    - (5901413641224192 : R) * w1n ^ 2 * e1 ^ 3 * a2 * b7
    - (6744472732827648 : R) * w1n ^ 2 * e1 ^ 3 * a1 * b8
    - (3083892424704 : R) * w1n ^ 2 * e1 * e3 ^ 3 * b8
    + (35940940220989440 : R) * w1n ^ 2 * e1 * a2 ^ 2 * b7
    + (82150720505118720 : R) * w1n ^ 2 * e1 * a2 * a1 * b8
    - (43367237222400 : R) * w1n * e1 ^ 4 * e3 * b7
    + (1124078788804608 : R) * w1n * e1 ^ 2 * e3 * a2 * b7
    + (1284661472919552 : R) * w1n * e1 ^ 2 * e3 * a1 * b8
    + (48950673408 : R) * w1n * e3 ^ 4 * b8
    - (3194750241865728 : R) * w1n * e3 * a2 ^ 2 * b7
    - (7302286267121664 : R) * w1n * e3 * a2 * a1 * b8
    + (2312919318528 : R) * e1 ^ 3 * e3 ^ 2 * b7
    - (39441361010688 : R) * e1 * e3 ^ 2 * a2 * b7
    - (45075841155072 : R) * e1 * e3 ^ 2 * a1 * b8
/-- Order-`63` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder63610 {R : Type*} [CommRing R] (w1n : R) : R :=
    0
set_option maxHeartbeats 1600000000 in
/-- Order-`63` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order63610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b8n : R) : R :=
    (673276357877760 : R) * w1 ^ 5 * e1n ^ 4 * b8n
    + (3765241356484608 : R) * w1 ^ 5 * e1n * a0 * b8n
    - (332482152038400 : R) * w1 ^ 4 * e1n ^ 3 * e3 * b8n
    + (10237146112327680 : R) * w1 ^ 4 * e1n ^ 2 * a1 * b8n
    - (836720301441024 : R) * w1 ^ 4 * e3 * a0 * b8n
    + (8617937380835328 : R) * w1 ^ 3 * e1n ^ 3 * a2 * b8n
    + (53197144326144 : R) * w1 ^ 3 * e1n ^ 2 * e3 ^ 2 * b8n
    - (2873584873635840 : R) * w1 ^ 3 * e1n * e3 * a1 * b8n
    + (41707288871829504 : R) * w1 ^ 3 * a2 * a0 * b8n
    + (20853644435914752 : R) * w1 ^ 3 * a1 ^ 2 * b8n
    - (2248157577609216 : R) * w1 ^ 2 * e1n ^ 2 * e3 * a2 * b8n
    - (3083892424704 : R) * w1 ^ 2 * e1n * e3 ^ 3 * b8n
    + (82150720505118720 : R) * w1 ^ 2 * e1n * a2 * a1 * b8n
    + (169034404331520 : R) * w1 ^ 2 * e3 ^ 2 * a1 * b8n
    + (17342929884413952 : R) * w1 * e1n ^ 2 * a2 ^ 2 * b8n
    + (142740163657728 : R) * w1 * e1n * e3 ^ 2 * a2 * b8n
    + (48950673408 : R) * w1 * e3 ^ 4 * b8n
    - (7302286267121664 : R) * w1 * e3 * a2 * a1 * b8n
    - (1217047711186944 : R) * e1n * e3 * a2 ^ 2 * b8n
    - (1669475598336 : R) * e3 ^ 3 * a2 * b8n
    + (45498860587450368 : R) * a2 ^ 2 * a1 * b8n
/-! ## Order `64` (MixedPair `h^10`) -/
set_option maxHeartbeats 1600000000 in
/-- Frozen order-`64` coefficient of the MixedPair jet (`h^10` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder64610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 : R) : R :=
    - (6522826527360 : R) * w1 ^ 10 * a1
    - (972141730560 : R) * w1 ^ 9 * e3 ^ 2
    - (118279783440000 : R) * w1 ^ 8 * e1 ^ 2 * e3
    + (118697068638720 : R) * w1 ^ 8 * e3 * a2
    - (44079842304 : R) * w1 ^ 8 * b3
    - (516534771916800 : R) * w1 ^ 7 * e1 ^ 4
    + (5177815799869440 : R) * w1 ^ 7 * e1 ^ 2 * a2
    - (3492560186818560 : R) * w1 ^ 7 * a2 ^ 2
    + (2681795837952 : R) * w1 ^ 6 * e3 * b4
    + (313770113040384 : R) * w1 ^ 5 * e1 ^ 2 * b4
    - (236973232226304 : R) * w1 ^ 5 * a2 * b4
    - (296216540282880 : R) * w1 ^ 5 * a1 * b5
    - (355459848339456 : R) * w1 ^ 5 * a0 * b6
    - (9684262748160 : R) * w1 ^ 4 * e3 ^ 2 * b5
    - (299331757670400 : R) * w1 ^ 3 * e1 ^ 2 * e3 * b5
    + (965446501662720 : R) * w1 ^ 3 * e3 * a2 * b5
    + (1158535801995264 : R) * w1 ^ 3 * e3 * a1 * b6
    + (1351625102327808 : R) * w1 ^ 3 * e3 * a0 * b7
    - (351274621501440 : R) * w1 ^ 2 * e1 ^ 4 * b5
    + (8557366719283200 : R) * w1 ^ 2 * e1 ^ 2 * a2 * b5
    + (10268840063139840 : R) * w1 ^ 2 * e1 ^ 2 * a1 * b6
    + (11980313406996480 : R) * w1 ^ 2 * e1 ^ 2 * a0 * b7
    + (1565133373440 : R) * w1 ^ 2 * e3 ^ 3 * b6
    - (21327590900367360 : R) * w1 ^ 2 * a2 ^ 2 * b5
    - (51186218160881664 : R) * w1 ^ 2 * a2 * a1 * b6
    - (59717254521028608 : R) * w1 ^ 2 * a2 * a0 * b7
    - (29858627260514304 : R) * w1 ^ 2 * a1 ^ 2 * b7
    - (68248290881175552 : R) * w1 ^ 2 * a1 * a0 * b8
    + (17842520457216 : R) * w1 * e1 ^ 2 * e3 ^ 2 * b6
    - (101420642598912 : R) * w1 * e3 ^ 2 * a2 * b6
    - (118324083032064 : R) * w1 * e3 ^ 2 * a1 * b7
    - (135227523465216 : R) * w1 * e3 ^ 2 * a0 * b8
    + (8921260228608 : R) * e1 ^ 4 * e3 * b6
    - (304261927796736 : R) * e1 ^ 2 * e3 * a2 * b6
    - (354972249096192 : R) * e1 ^ 2 * e3 * a1 * b7
    - (405682570395648 : R) * e1 ^ 2 * e3 * a0 * b8
    - (13525843968 : R) * e3 ^ 4 * b7
    + (1263857238540288 : R) * e3 * a2 ^ 2 * b6
    + (2949000223260672 : R) * e3 * a2 * a1 * b7
    + (3370285969440768 : R) * e3 * a2 * a0 * b8
    + (1685142984720384 : R) * e3 * a1 ^ 2 * b8
/-- Order-`64` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder64610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b8 b7 b6 : R) : R :=
    (8921260228608 : R) * e1 ^ 4 * e3 * b6
    - (304261927796736 : R) * e1 ^ 2 * e3 * a2 * b6
    - (354972249096192 : R) * e1 ^ 2 * e3 * a1 * b7
    - (405682570395648 : R) * e1 ^ 2 * e3 * a0 * b8
    - (13525843968 : R) * e3 ^ 4 * b7
    + (1263857238540288 : R) * e3 * a2 ^ 2 * b6
    + (2949000223260672 : R) * e3 * a2 * a1 * b7
    + (3370285969440768 : R) * e3 * a2 * a0 * b8
    + (1685142984720384 : R) * e3 * a1 ^ 2 * b8
set_option maxHeartbeats 1600000000 in
/-- Order-`64` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder64610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b8 b7 b6 : R) : R :=
    - (302796245606400 : R) * w1n ^ 7 * e1 ^ 3 * b8
    + (804347194540032 : R) * w1n ^ 7 * e1 * a2 * b8
    + (169565897539584 : R) * w1n ^ 6 * e1 ^ 2 * e3 * b8
    - (197558960062464 : R) * w1n ^ 6 * e3 * a2 * b8
    - (29489721311232 : R) * w1n ^ 5 * e1 * e3 ^ 2 * b8
    - (654574236825600 : R) * w1n ^ 4 * e1 ^ 4 * b7
    + (8957502848286720 : R) * w1n ^ 4 * e1 ^ 2 * a2 * b7
    + (10237146112327680 : R) * w1n ^ 4 * e1 ^ 2 * a1 * b8
    + (1560302714880 : R) * w1n ^ 4 * e3 ^ 3 * b8
    - (9883758560772096 : R) * w1n ^ 4 * a2 ^ 2 * b7
    - (22591448138907648 : R) * w1n ^ 4 * a2 * a1 * b8
    + (279285007712256 : R) * w1n ^ 3 * e1 ^ 3 * e3 * b7
    - (2514386764431360 : R) * w1n ^ 3 * e1 * e3 * a2 * b7
    - (2873584873635840 : R) * w1n ^ 3 * e1 * e3 * a1 * b8
    - (36428479266816 : R) * w1n ^ 2 * e1 ^ 2 * e3 ^ 2 * b7
    + (147905103790080 : R) * w1n ^ 2 * e3 ^ 2 * a2 * b7
    + (169034404331520 : R) * w1n ^ 2 * e3 ^ 2 * a1 * b8
    - (66909451714560 : R) * w1n * e1 ^ 5 * b6
    + (2890488314068992 : R) * w1n * e1 ^ 3 * a2 * b6
    + (3372236366413824 : R) * w1n * e1 ^ 3 * a1 * b7
    + (3853984418758656 : R) * w1n * e1 ^ 3 * a0 * b8
    + (1541946212352 : R) * w1n * e1 * e3 ^ 3 * b7
    - (24645216151535616 : R) * w1n * e1 * a2 ^ 2 * b6
    - (57505504353583104 : R) * w1n * e1 * a2 * a1 * b7
    - (65720576404094976 : R) * w1n * e1 * a2 * a0 * b8
    - (32860288202047488 : R) * w1n * e1 * a1 ^ 2 * b8
    + (8921260228608 : R) * e1 ^ 4 * e3 * b6
    - (304261927796736 : R) * e1 ^ 2 * e3 * a2 * b6
    - (354972249096192 : R) * e1 ^ 2 * e3 * a1 * b7
    - (405682570395648 : R) * e1 ^ 2 * e3 * a0 * b8
    - (13525843968 : R) * e3 ^ 4 * b7
    + (1263857238540288 : R) * e3 * a2 ^ 2 * b6
    + (2949000223260672 : R) * e3 * a2 * a1 * b7
    + (3370285969440768 : R) * e3 * a2 * a0 * b8
    + (1685142984720384 : R) * e3 * a1 ^ 2 * b8
/-- Order-`64` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder64610 {R : Type*} [CommRing R] (w1n a2b a1 b8 : R) : R :=
    - (32860288202047488 : R) * w1n * a2b ^ 3 * b8
    + (45498860587450368 : R) * a2b ^ 2 * a1 * b8
set_option maxHeartbeats 1600000000 in
/-- Order-`64` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order64610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 : R) : R :=
    - (14193574012800 : R) * w1 ^ 11 * e1n ^ 2
    + (7517337347520 : R) * w1 ^ 10 * e1n * e3
    - (6522826527360 : R) * w1 ^ 10 * a1
    - (472460881052160 : R) * w1 ^ 9 * e1n * a2
    - (972141730560 : R) * w1 ^ 9 * e3 ^ 2
    + (118697068638720 : R) * w1 ^ 8 * e3 * a2
    - (44079842304 : R) * w1 ^ 8 * b3
    - (7470716977152 : R) * w1 ^ 7 * e1n * b4
    - (3492560186818560 : R) * w1 ^ 7 * a2 ^ 2
    - (185211525058560 : R) * w1 ^ 6 * e1n ^ 2 * b5
    + (2681795837952 : R) * w1 ^ 6 * e3 * b4
    - (597166856552448 : R) * w1 ^ 5 * e1n ^ 3 * b6
    + (87158364733440 : R) * w1 ^ 5 * e1n * e3 * b5
    - (236973232226304 : R) * w1 ^ 5 * a2 * b4
    - (296216540282880 : R) * w1 ^ 5 * a1 * b5
    - (355459848339456 : R) * w1 ^ 5 * a0 * b6
    - (654574236825600 : R) * w1 ^ 4 * e1n ^ 4 * b7
    + (284365169786880 : R) * w1 ^ 4 * e1n ^ 2 * e3 * b6
    - (4706551695605760 : R) * w1 ^ 4 * e1n * a2 * b5
    - (5647862034726912 : R) * w1 ^ 4 * e1n * a1 * b6
    - (6589172373848064 : R) * w1 ^ 4 * e1n * a0 * b7
    - (9684262748160 : R) * w1 ^ 4 * e3 ^ 2 * b5
    + (279285007712256 : R) * w1 ^ 3 * e1n ^ 3 * e3 * b7
    - (9698348948520960 : R) * w1 ^ 3 * e1n ^ 2 * a2 * b6
    - (11314740439941120 : R) * w1 ^ 3 * e1n ^ 2 * a1 * b7
    - (39910901022720 : R) * w1 ^ 3 * e1n * e3 ^ 2 * b6
    + (965446501662720 : R) * w1 ^ 3 * e3 * a2 * b5
    + (1158535801995264 : R) * w1 ^ 3 * e3 * a1 * b6
    + (1351625102327808 : R) * w1 ^ 3 * e3 * a0 * b7
    - (5901413641224192 : R) * w1 ^ 2 * e1n ^ 3 * a2 * b7
    - (36428479266816 : R) * w1 ^ 2 * e1n ^ 2 * e3 ^ 2 * b7
    + (2281964458475520 : R) * w1 ^ 2 * e1n * e3 * a2 * b6
    + (2662291868221440 : R) * w1 ^ 2 * e1n * e3 * a1 * b7
    + (1565133373440 : R) * w1 ^ 2 * e3 ^ 3 * b6
    - (21327590900367360 : R) * w1 ^ 2 * a2 ^ 2 * b5
    - (51186218160881664 : R) * w1 ^ 2 * a2 * a1 * b6
    - (59717254521028608 : R) * w1 ^ 2 * a2 * a0 * b7
    - (29858627260514304 : R) * w1 ^ 2 * a1 ^ 2 * b7
    + (1124078788804608 : R) * w1 * e1n ^ 2 * e3 * a2 * b7
    + (1541946212352 : R) * w1 * e1n * e3 ^ 3 * b7
    - (24645216151535616 : R) * w1 * e1n * a2 ^ 2 * b6
    - (57505504353583104 : R) * w1 * e1n * a2 * a1 * b7
    - (101420642598912 : R) * w1 * e3 ^ 2 * a2 * b6
    - (118324083032064 : R) * w1 * e3 ^ 2 * a1 * b7
    - (4792125362798592 : R) * e1n ^ 2 * a2 ^ 2 * b7
    - (39441361010688 : R) * e1n * e3 ^ 2 * a2 * b7
    - (13525843968 : R) * e3 ^ 4 * b7
    + (1263857238540288 : R) * e3 * a2 ^ 2 * b6
    + (2949000223260672 : R) * e3 * a2 * a1 * b7
/-! ## Order `65` (MixedPair `h^11`) -/
set_option maxHeartbeats 1600000000 in
/-- Frozen order-`65` coefficient of the MixedPair jet (`h^11` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder65610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 : R) : R :=
    (1068273617748480 : R) * w1 ^ 8 * e1 * a1
    + (21307883950080 : R) * w1 ^ 7 * e1 * e3 ^ 2
    + (259751681280000 : R) * w1 ^ 6 * e1 ^ 3 * e3
    - (1714090051215360 : R) * w1 ^ 6 * e1 * e3 * a2
    + (18102121906176 : R) * w1 ^ 6 * e1 * b3
    + (208859712122880 : R) * w1 ^ 5 * e1 ^ 5
    - (6732763578777600 : R) * w1 ^ 5 * e1 ^ 3 * a2
    + (30711438336983040 : R) * w1 ^ 5 * e1 * a2 ^ 2
    - (139453383573504 : R) * w1 ^ 4 * e1 * e3 * b4
    - (718396218408960 : R) * w1 ^ 3 * e1 ^ 3 * b4
    + (6951214811971584 : R) * w1 ^ 3 * e1 * a2 * b4
    + (8689018514964480 : R) * w1 ^ 3 * e1 * a1 * b5
    + (10426822217957376 : R) * w1 ^ 3 * e1 * a0 * b6
    + (35215500902400 : R) * w1 ^ 2 * e1 * e3 ^ 2 * b5
    + (89212602286080 : R) * w1 * e1 ^ 3 * e3 * b5
    - (1521309638983680 : R) * w1 * e1 * e3 * a2 * b5
    - (1825571566780416 : R) * w1 * e1 * e3 * a1 * b6
    - (2129833494577152 : R) * w1 * e1 * e3 * a0 * b7
    + (13381890342912 : R) * e1 ^ 5 * b5
    - (760654819491840 : R) * e1 ^ 3 * a2 * b5
    - (912785783390208 : R) * e1 ^ 3 * a1 * b6
    - (1064916747288576 : R) * e1 ^ 3 * a0 * b7
    - (417368899584 : R) * e1 * e3 ^ 3 * b6
    + (9478929289052160 : R) * e1 * a2 ^ 2 * b5
    + (22749430293725184 : R) * e1 * a2 * a1 * b6
    + (26541002009346048 : R) * e1 * a2 * a0 * b7
    + (13270501004673024 : R) * e1 * a1 ^ 2 * b7
    + (30332573724966912 : R) * e1 * a1 * a0 * b8
set_option maxHeartbeats 1600000000 in
/-- Order-`65` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder65610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) : R :=
    (13381890342912 : R) * e1 ^ 5 * b5
    - (760654819491840 : R) * e1 ^ 3 * a2 * b5
    - (912785783390208 : R) * e1 ^ 3 * a1 * b6
    - (1064916747288576 : R) * e1 ^ 3 * a0 * b7
    - (417368899584 : R) * e1 * e3 ^ 3 * b6
    + (9478929289052160 : R) * e1 * a2 ^ 2 * b5
    + (22749430293725184 : R) * e1 * a2 * a1 * b6
    + (26541002009346048 : R) * e1 * a2 * a0 * b7
    + (13270501004673024 : R) * e1 * a1 ^ 2 * b7
    + (30332573724966912 : R) * e1 * a1 * a0 * b8
set_option maxHeartbeats 1600000000 in
/-- Order-`65` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder65610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) : R :=
    (24980690262528 : R) * w1n ^ 9 * e1 ^ 2 * b8
    - (4409798215680 : R) * w1n ^ 9 * a2 * b8
    - (13033403615232 : R) * w1n ^ 8 * e1 * e3 * b8
    + (1655035379712 : R) * w1n ^ 7 * e3 ^ 2 * b8
    + (445110481041408 : R) * w1n ^ 6 * e1 ^ 3 * b7
    - (1555776810491904 : R) * w1n ^ 6 * e1 * a2 * b7
    - (1778030640562176 : R) * w1n ^ 6 * e1 * a1 * b8
    - (232231555325952 : R) * w1n ^ 5 * e1 ^ 2 * e3 * b7
    + (366065131880448 : R) * w1n ^ 5 * e3 * a2 * b7
    + (418360150720512 : R) * w1n ^ 5 * e3 * a1 * b8
    + (36862151639040 : R) * w1n ^ 4 * e1 * e3 ^ 2 * b7
    + (538621086302208 : R) * w1n ^ 3 * e1 ^ 4 * b6
    - (9698348948520960 : R) * w1n ^ 3 * e1 ^ 2 * a2 * b6
    - (11314740439941120 : R) * w1n ^ 3 * e1 ^ 2 * a1 * b7
    - (12931131931361280 : R) * w1n ^ 3 * e1 ^ 2 * a0 * b8
    - (1724545105920 : R) * w1n ^ 3 * e3 ^ 3 * b7
    + (15640233326936064 : R) * w1n ^ 3 * a2 ^ 2 * b6
    + (36493877762850816 : R) * w1n ^ 3 * a2 * a1 * b7
    + (41707288871829504 : R) * w1n ^ 3 * a2 * a0 * b8
    + (20853644435914752 : R) * w1n ^ 3 * a1 ^ 2 * b8
    - (187346464800768 : R) * w1n ^ 2 * e1 ^ 3 * e3 * b6
    + (2281964458475520 : R) * w1n ^ 2 * e1 * e3 * a2 * b6
    + (2662291868221440 : R) * w1n ^ 2 * e1 * e3 * a1 * b7
    + (3042619277967360 : R) * w1n ^ 2 * e1 * e3 * a0 * b8
    + (17842520457216 : R) * w1n * e1 ^ 2 * e3 ^ 2 * b6
    - (101420642598912 : R) * w1n * e3 ^ 2 * a2 * b6
    - (118324083032064 : R) * w1n * e3 ^ 2 * a1 * b7
    - (135227523465216 : R) * w1n * e3 ^ 2 * a0 * b8
    + (13381890342912 : R) * e1 ^ 5 * b5
    - (760654819491840 : R) * e1 ^ 3 * a2 * b5
    - (912785783390208 : R) * e1 ^ 3 * a1 * b6
    - (1064916747288576 : R) * e1 ^ 3 * a0 * b7
    - (417368899584 : R) * e1 * e3 ^ 3 * b6
    + (9478929289052160 : R) * e1 * a2 ^ 2 * b5
    + (22749430293725184 : R) * e1 * a2 * a1 * b6
    + (26541002009346048 : R) * e1 * a2 * a0 * b7
    + (13270501004673024 : R) * e1 * a1 ^ 2 * b7
    + (30332573724966912 : R) * e1 * a1 * a0 * b8
set_option maxHeartbeats 1600000000 in
/-- Order-`65` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder65610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 b8 b7 : R) : R :=
    (5647862034726912 : R) * w1n ^ 5 * a2b ^ 2 * b8
    - (22591448138907648 : R) * w1n ^ 4 * a2b * a1 * b8
    - (38793395794083840 : R) * w1n ^ 3 * e1b * a2b ^ 2 * b8
    + (20853644435914752 : R) * w1n ^ 3 * a1 ^ 2 * b8
    + (82150720505118720 : R) * w1n ^ 2 * e1b * a2b * a1 * b8
    + (4563928916951040 : R) * w1n ^ 2 * e3b * a2b ^ 2 * b8
    + (17342929884413952 : R) * w1n * e1b ^ 2 * a2b ^ 2 * b8
    - (32860288202047488 : R) * w1n * e1b * a1 ^ 2 * b8
    - (7302286267121664 : R) * w1n * e3b * a2b * a1 * b8
    - (10953429400682496 : R) * e1b ^ 2 * a2b * a1 * b8
    - (1217047711186944 : R) * e1b * e3b * a2b ^ 2 * b8
    + (1685142984720384 : R) * e3b * a1 ^ 2 * b8
    + (13270501004673024 : R) * a2b ^ 3 * b7
set_option maxHeartbeats 1600000000 in
/-- Order-`65` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order65610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b8n : R) : R :=
    - (323395683287040 : R) * w1 ^ 3 * e1n ^ 5 * b8n
    - (12931131931361280 : R) * w1 ^ 3 * e1n ^ 2 * a0 * b8n
    + (111515752857600 : R) * w1 ^ 2 * e1n ^ 4 * e3 * b8n
    - (6744472732827648 : R) * w1 ^ 2 * e1n ^ 3 * a1 * b8n
    + (3042619277967360 : R) * w1 ^ 2 * e1n * e3 * a0 * b8n
    - (68248290881175552 : R) * w1 ^ 2 * a1 * a0 * b8n
    - (1338189034291200 : R) * w1 * e1n ^ 4 * a2 * b8n
    - (11013901516800 : R) * w1 * e1n ^ 3 * e3 ^ 2 * b8n
    + (1284661472919552 : R) * w1 * e1n ^ 2 * e3 * a1 * b8n
    - (65720576404094976 : R) * w1 * e1n * a2 * a0 * b8n
    - (32860288202047488 : R) * w1 * e1n * a1 ^ 2 * b8n
    - (135227523465216 : R) * w1 * e3 ^ 2 * a0 * b8n
    + (142740163657728 : R) * e1n ^ 3 * e3 * a2 * b8n
    + (293704040448 : R) * e1n ^ 2 * e3 ^ 3 * b8n
    - (10953429400682496 : R) * e1n ^ 2 * a2 * a1 * b8n
    - (45075841155072 : R) * e1n * e3 ^ 2 * a1 * b8n
    + (3370285969440768 : R) * e3 * a2 * a0 * b8n
    + (1685142984720384 : R) * e3 * a1 ^ 2 * b8n
/-! ## Order `66` (MixedPair `h^12`) -/
set_option maxHeartbeats 1600000000 in
/-- Frozen order-`66` coefficient of the MixedPair jet (`h^12` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder66610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 : R) : R :=
    (20751991603200 : R) * w1 ^ 9 * a0
    - (258708161986560 : R) * w1 ^ 7 * e3 * a1
    + (156728328192 : R) * w1 ^ 7 * b2
    - (7713405230469120 : R) * w1 ^ 6 * e1 ^ 2 * a1
    - (1175644753920 : R) * w1 ^ 6 * e3 ^ 3
    + (14511867728117760 : R) * w1 ^ 6 * a2 * a1
    - (41560269004800 : R) * w1 ^ 5 * e1 ^ 2 * e3 ^ 2
    + (126384519905280 : R) * w1 ^ 5 * e3 ^ 2 * a2
    - (6582589784064 : R) * w1 ^ 5 * e3 * b3
    - (46787569920000 : R) * w1 ^ 4 * e1 ^ 4 * e3
    + (1645786652590080 : R) * w1 ^ 4 * e1 ^ 2 * e3 * a2
    - (470655169560576 : R) * w1 ^ 4 * e1 ^ 2 * b3
    - (3816479910297600 : R) * w1 ^ 4 * e3 * a2 ^ 2
    + (592433080565760 : R) * w1 ^ 4 * a2 * b3
    + (789910774087680 : R) * w1 ^ 4 * a1 * b4
    + (987388467609600 : R) * w1 ^ 4 * a0 * b5
    + (39122296012800 : R) * w1 ^ 3 * e1 ^ 6
    - (418184073216000 : R) * w1 ^ 3 * e1 ^ 4 * a2
    - (8430590916034560 : R) * w1 ^ 3 * e1 ^ 2 * a2 ^ 2
    + (14302911135744 : R) * w1 ^ 3 * e3 ^ 2 * b4
    + (28524555730944000 : R) * w1 ^ 3 * a2 ^ 3
    + (253551606497280 : R) * w1 ^ 2 * e1 ^ 2 * e3 * b4
    - (1263857238540288 : R) * w1 ^ 2 * e3 * a2 * b4
    - (1579821548175360 : R) * w1 ^ 2 * e3 * a1 * b5
    - (1895785857810432 : R) * w1 ^ 2 * e3 * a0 * b6
    + (160582684114944 : R) * w1 * e1 ^ 4 * b4
    - (5476714700341248 : R) * w1 * e1 ^ 2 * a2 * b4
    - (6845893375426560 : R) * w1 * e1 ^ 2 * a1 * b5
    - (8215072050511872 : R) * w1 * e1 ^ 2 * a0 * b6
    - (1043422248960 : R) * w1 * e3 ^ 3 * b5
    + (22749430293725184 : R) * w1 * a2 ^ 2 * b4
    + (56873575734312960 : R) * w1 * a2 * a1 * b5
    + (68248290881175552 : R) * w1 * a2 * a0 * b6
    + (34124145440587776 : R) * w1 * a1 ^ 2 * b6
    + (79623006028038144 : R) * w1 * a1 * a0 * b7
    + (45498860587450368 : R) * w1 * a0 ^ 2 * b8
    - (4695400120320 : R) * e1 ^ 2 * e3 ^ 2 * b5
    + (39007939461120 : R) * e3 ^ 2 * a2 * b5
    + (46809527353344 : R) * e3 ^ 2 * a1 * b6
    + (54611115245568 : R) * e3 ^ 2 * a0 * b7
/-- Order-`66` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder66610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b7 b6 b5 : R) : R :=
    - (4695400120320 : R) * e1 ^ 2 * e3 ^ 2 * b5
    + (39007939461120 : R) * e3 ^ 2 * a2 * b5
    + (46809527353344 : R) * e3 ^ 2 * a1 * b6
    + (54611115245568 : R) * e3 ^ 2 * a0 * b7
set_option maxHeartbeats 1600000000 in
/-- Order-`66` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder66610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) : R :=
    - (148106859264 : R) * w1n ^ 11 * e1 * b8
    + (51719855616 : R) * w1n ^ 10 * e3 * b8
    - (51319026734976 : R) * w1n ^ 8 * e1 ^ 2 * b7
    + (12256645040640 : R) * w1n ^ 8 * a2 * b7
    + (14007594332160 : R) * w1n ^ 8 * a1 * b8
    + (26066807230464 : R) * w1n ^ 7 * e1 * e3 * b7
    - (3201186852864 : R) * w1n ^ 6 * e3 ^ 2 * b7
    - (597166856552448 : R) * w1n ^ 5 * e1 ^ 3 * b6
    + (2823931017363456 : R) * w1n ^ 5 * e1 * a2 * b6
    + (3294586186924032 : R) * w1n ^ 5 * e1 * a1 * b7
    + (3765241356484608 : R) * w1n ^ 5 * e1 * a0 * b8
    + (284365169786880 : R) * w1n ^ 4 * e1 ^ 2 * e3 * b6
    - (627540226080768 : R) * w1n ^ 4 * e3 * a2 * b6
    - (732130263760896 : R) * w1n ^ 4 * e3 * a1 * b7
    - (836720301441024 : R) * w1n ^ 4 * e3 * a0 * b8
    - (39910901022720 : R) * w1n ^ 3 * e1 * e3 ^ 2 * b6
    - (351274621501440 : R) * w1n ^ 2 * e1 ^ 4 * b5
    + (8557366719283200 : R) * w1n ^ 2 * e1 ^ 2 * a2 * b5
    + (10268840063139840 : R) * w1n ^ 2 * e1 ^ 2 * a1 * b6
    + (11980313406996480 : R) * w1n ^ 2 * e1 ^ 2 * a0 * b7
    + (1565133373440 : R) * w1n ^ 2 * e3 ^ 3 * b6
    - (21327590900367360 : R) * w1n ^ 2 * a2 ^ 2 * b5
    - (51186218160881664 : R) * w1n ^ 2 * a2 * a1 * b6
    - (59717254521028608 : R) * w1n ^ 2 * a2 * a0 * b7
    - (29858627260514304 : R) * w1n ^ 2 * a1 ^ 2 * b7
    - (68248290881175552 : R) * w1n ^ 2 * a1 * a0 * b8
    + (89212602286080 : R) * w1n * e1 ^ 3 * e3 * b5
    - (1521309638983680 : R) * w1n * e1 * e3 * a2 * b5
    - (1825571566780416 : R) * w1n * e1 * e3 * a1 * b6
    - (2129833494577152 : R) * w1n * e1 * e3 * a0 * b7
    - (4695400120320 : R) * e1 ^ 2 * e3 ^ 2 * b5
    + (39007939461120 : R) * e3 ^ 2 * a2 * b5
    + (46809527353344 : R) * e3 ^ 2 * a1 * b6
    + (54611115245568 : R) * e3 ^ 2 * a0 * b7
set_option maxHeartbeats 1600000000 in
/-- Order-`66` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder66610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b8 b7 : R) : R :=
    - (4409798215680 : R) * w1n ^ 9 * a2b * b8
    + (14007594332160 : R) * w1n ^ 8 * a1 * b8
    + (804347194540032 : R) * w1n ^ 7 * e1b * a2b * b8
    - (1778030640562176 : R) * w1n ^ 6 * e1b * a1 * b8
    - (197558960062464 : R) * w1n ^ 6 * e3b * a2b * b8
    - (7166002278629376 : R) * w1n ^ 5 * e1b ^ 2 * a2b * b8
    + (418360150720512 : R) * w1n ^ 5 * e3b * a1 * b8
    + (10237146112327680 : R) * w1n ^ 4 * e1b ^ 2 * a1 * b8
    + (2274921358295040 : R) * w1n ^ 4 * e1b * e3b * a2b * b8
    - (9883758560772096 : R) * w1n ^ 4 * a2b ^ 2 * b7
    + (8617937380835328 : R) * w1n ^ 3 * e1b ^ 3 * a2b * b8
    - (2873584873635840 : R) * w1n ^ 3 * e1b * e3b * a1 * b8
    - (159643604090880 : R) * w1n ^ 3 * e3b ^ 2 * a2b * b8
    + (36493877762850816 : R) * w1n ^ 3 * a2b * a1 * b7
    + (41707288871829504 : R) * w1n ^ 3 * a2b * a0 * b8
    - (6744472732827648 : R) * w1n ^ 2 * e1b ^ 3 * a1 * b8
    - (2248157577609216 : R) * w1n ^ 2 * e1b ^ 2 * e3b * a2b * b8
    + (35940940220989440 : R) * w1n ^ 2 * e1b * a2b ^ 2 * b7
    + (169034404331520 : R) * w1n ^ 2 * e3b ^ 2 * a1 * b8
    - (29858627260514304 : R) * w1n ^ 2 * a1 ^ 2 * b7
    - (68248290881175552 : R) * w1n ^ 2 * a1 * a0 * b8
    - (1338189034291200 : R) * w1n * e1b ^ 4 * a2b * b8
    + (1284661472919552 : R) * w1n * e1b ^ 2 * e3b * a1 * b8
    + (142740163657728 : R) * w1n * e1b * e3b ^ 2 * a2b * b8
    - (57505504353583104 : R) * w1n * e1b * a2b * a1 * b7
    - (65720576404094976 : R) * w1n * e1b * a2b * a0 * b8
    - (3194750241865728 : R) * w1n * e3b * a2b ^ 2 * b7
    + (321165368229888 : R) * e1b ^ 4 * a1 * b8
    + (142740163657728 : R) * e1b ^ 3 * e3b * a2b * b8
    - (4792125362798592 : R) * e1b ^ 2 * a2b ^ 2 * b7
    - (45075841155072 : R) * e1b * e3b ^ 2 * a1 * b8
    + (13270501004673024 : R) * e1b * a1 ^ 2 * b7
    + (30332573724966912 : R) * e1b * a1 * a0 * b8
    - (1669475598336 : R) * e3b ^ 3 * a2b * b8
    + (2949000223260672 : R) * e3b * a2b * a1 * b7
    + (3370285969440768 : R) * e3b * a2b * a0 * b8
set_option maxHeartbeats 1600000000 in
/-- Order-`66` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order66610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 : R) : R :=
    (205018291296000 : R) * w1 ^ 9 * e1n ^ 3
    + (20751991603200 : R) * w1 ^ 9 * a0
    - (118279783440000 : R) * w1 ^ 8 * e1n ^ 2 * e3
    + (1068273617748480 : R) * w1 ^ 8 * e1n * a1
    + (5177815799869440 : R) * w1 ^ 7 * e1n ^ 2 * a2
    + (21307883950080 : R) * w1 ^ 7 * e1n * e3 ^ 2
    - (258708161986560 : R) * w1 ^ 7 * e3 * a1
    + (156728328192 : R) * w1 ^ 7 * b2
    - (1714090051215360 : R) * w1 ^ 6 * e1n * e3 * a2
    + (18102121906176 : R) * w1 ^ 6 * e1n * b3
    - (1175644753920 : R) * w1 ^ 6 * e3 ^ 3
    + (14511867728117760 : R) * w1 ^ 6 * a2 * a1
    + (313770113040384 : R) * w1 ^ 5 * e1n ^ 2 * b4
    + (30711438336983040 : R) * w1 ^ 5 * e1n * a2 ^ 2
    + (126384519905280 : R) * w1 ^ 5 * e3 ^ 2 * a2
    - (6582589784064 : R) * w1 ^ 5 * e3 * b3
    + (710912924467200 : R) * w1 ^ 4 * e1n ^ 3 * b5
    - (139453383573504 : R) * w1 ^ 4 * e1n * e3 * b4
    - (3816479910297600 : R) * w1 ^ 4 * e3 * a2 ^ 2
    + (592433080565760 : R) * w1 ^ 4 * a2 * b3
    + (789910774087680 : R) * w1 ^ 4 * a1 * b4
    + (987388467609600 : R) * w1 ^ 4 * a0 * b5
    + (538621086302208 : R) * w1 ^ 3 * e1n ^ 4 * b6
    - (299331757670400 : R) * w1 ^ 3 * e1n ^ 2 * e3 * b5
    + (6951214811971584 : R) * w1 ^ 3 * e1n * a2 * b4
    + (8689018514964480 : R) * w1 ^ 3 * e1n * a1 * b5
    + (10426822217957376 : R) * w1 ^ 3 * e1n * a0 * b6
    + (14302911135744 : R) * w1 ^ 3 * e3 ^ 2 * b4
    + (28524555730944000 : R) * w1 ^ 3 * a2 ^ 3
    + (175637310750720 : R) * w1 ^ 2 * e1n ^ 5 * b7
    - (187346464800768 : R) * w1 ^ 2 * e1n ^ 3 * e3 * b6
    + (8557366719283200 : R) * w1 ^ 2 * e1n ^ 2 * a2 * b5
    + (10268840063139840 : R) * w1 ^ 2 * e1n ^ 2 * a1 * b6
    + (11980313406996480 : R) * w1 ^ 2 * e1n ^ 2 * a0 * b7
    + (35215500902400 : R) * w1 ^ 2 * e1n * e3 ^ 2 * b5
    - (1263857238540288 : R) * w1 ^ 2 * e3 * a2 * b4
    - (1579821548175360 : R) * w1 ^ 2 * e3 * a1 * b5
    - (1895785857810432 : R) * w1 ^ 2 * e3 * a0 * b6
    - (43367237222400 : R) * w1 * e1n ^ 4 * e3 * b7
    + (2890488314068992 : R) * w1 * e1n ^ 3 * a2 * b6
    + (3372236366413824 : R) * w1 * e1n ^ 3 * a1 * b7
    + (17842520457216 : R) * w1 * e1n ^ 2 * e3 ^ 2 * b6
    - (1521309638983680 : R) * w1 * e1n * e3 * a2 * b5
    - (1825571566780416 : R) * w1 * e1n * e3 * a1 * b6
    - (2129833494577152 : R) * w1 * e1n * e3 * a0 * b7
    - (1043422248960 : R) * w1 * e3 ^ 3 * b5
    + (22749430293725184 : R) * w1 * a2 ^ 2 * b4
    + (56873575734312960 : R) * w1 * a2 * a1 * b5
    + (68248290881175552 : R) * w1 * a2 * a0 * b6
    + (34124145440587776 : R) * w1 * a1 ^ 2 * b6
    + (79623006028038144 : R) * w1 * a1 * a0 * b7
    + (281019697201152 : R) * e1n ^ 4 * a2 * b7
    + (2312919318528 : R) * e1n ^ 3 * e3 ^ 2 * b7
    - (304261927796736 : R) * e1n ^ 2 * e3 * a2 * b6
    - (354972249096192 : R) * e1n ^ 2 * e3 * a1 * b7
    - (417368899584 : R) * e1n * e3 ^ 3 * b6
    + (9478929289052160 : R) * e1n * a2 ^ 2 * b5
    + (22749430293725184 : R) * e1n * a2 * a1 * b6
    + (26541002009346048 : R) * e1n * a2 * a0 * b7
    + (13270501004673024 : R) * e1n * a1 ^ 2 * b7
    + (39007939461120 : R) * e3 ^ 2 * a2 * b5
    + (46809527353344 : R) * e3 ^ 2 * a1 * b6
    + (54611115245568 : R) * e3 ^ 2 * a0 * b7
/-! ## Order `67` (MixedPair `h^13`) -/
set_option maxHeartbeats 1600000000 in
/-- Frozen order-`67` coefficient of the MixedPair jet (`h^13` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder67610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 : R) : R :=
    - (2328373457879040 : R) * w1 ^ 7 * e1 * a0
    + (2274921358295040 : R) * w1 ^ 5 * e1 * e3 * a1
    - (39495538704384 : R) * w1 ^ 5 * e1 * b2
    + (4937359957770240 : R) * w1 ^ 4 * e1 ^ 3 * a1
    + (2257594859520 : R) * w1 ^ 4 * e1 * e3 ^ 3
    - (68696638385356800 : R) * w1 ^ 4 * e1 * a2 * a1
    - (3441844224000 : R) * w1 ^ 3 * e1 ^ 3 * e3 ^ 2
    - (69387579555840 : R) * w1 ^ 3 * e1 * e3 ^ 2 * a2
    + (193089300332544 : R) * w1 ^ 3 * e1 * e3 * b3
    - (26674292736000 : R) * w1 ^ 2 * e1 ^ 5 * e3
    + (557578764288000 : R) * w1 ^ 2 * e1 ^ 3 * e3 * a2
    + (570491114618880 : R) * w1 ^ 2 * e1 ^ 3 * b3
    - (1204370130862080 : R) * w1 ^ 2 * e1 * e3 * a2 ^ 2
    - (8531036360146944 : R) * w1 ^ 2 * e1 * a2 * b3
    - (11374715146862592 : R) * w1 ^ 2 * e1 * a1 * b4
    - (14218393933578240 : R) * w1 ^ 2 * e1 * a0 * b5
    - (7113144729600 : R) * w1 * e1 ^ 7
    + (408891093811200 : R) * w1 * e1 ^ 5 * a2
    - (6423307364597760 : R) * w1 * e1 ^ 3 * a2 ^ 2
    - (22537920577536 : R) * w1 * e1 * e3 ^ 2 * b4
    + (22819644584755200 : R) * w1 * e1 * a2 ^ 3
    - (22537920577536 : R) * e1 ^ 3 * e3 * b4
    + (561714328240128 : R) * e1 * e3 * a2 * b4
    + (702142910300160 : R) * e1 * e3 * a1 * b5
    + (842571492360192 : R) * e1 * e3 * a0 * b6
/-- Order-`67` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder67610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b6 b5 b4 : R) : R :=
    - (22537920577536 : R) * e1 ^ 3 * e3 * b4
    + (561714328240128 : R) * e1 * e3 * a2 * b4
    + (702142910300160 : R) * e1 * e3 * a1 * b5
    + (842571492360192 : R) * e1 * e3 * a0 * b6
set_option maxHeartbeats 1600000000 in
/-- Order-`67` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder67610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : R) : R :=
    (67814496 : R) * w1n ^ 13 * b8
    + (407293862976 : R) * w1n ^ 10 * e1 * b7
    - (142910127360 : R) * w1n ^ 9 * e3 * b7
    + (100543399317504 : R) * w1n ^ 7 * e1 ^ 2 * b6
    - (33618226397184 : R) * w1n ^ 7 * a2 * b6
    - (39221264130048 : R) * w1n ^ 7 * a1 * b7
    - (44824301862912 : R) * w1n ^ 7 * a0 * b8
    - (49389740015616 : R) * w1n ^ 6 * e1 * e3 * b6
    + (5810557648896 : R) * w1n ^ 5 * e3 ^ 2 * b6
    + (710912924467200 : R) * w1n ^ 4 * e1 ^ 3 * b5
    - (4706551695605760 : R) * w1n ^ 4 * e1 * a2 * b5
    - (5647862034726912 : R) * w1n ^ 4 * e1 * a1 * b6
    - (6589172373848064 : R) * w1n ^ 4 * e1 * a0 * b7
    - (299331757670400 : R) * w1n ^ 3 * e1 ^ 2 * e3 * b5
    + (965446501662720 : R) * w1n ^ 3 * e3 * a2 * b5
    + (1158535801995264 : R) * w1n ^ 3 * e3 * a1 * b6
    + (1351625102327808 : R) * w1n ^ 3 * e3 * a0 * b7
    + (35215500902400 : R) * w1n ^ 2 * e1 * e3 ^ 2 * b5
    + (160582684114944 : R) * w1n * e1 ^ 4 * b4
    - (5476714700341248 : R) * w1n * e1 ^ 2 * a2 * b4
    - (6845893375426560 : R) * w1n * e1 ^ 2 * a1 * b5
    - (8215072050511872 : R) * w1n * e1 ^ 2 * a0 * b6
    - (1043422248960 : R) * w1n * e3 ^ 3 * b5
    + (22749430293725184 : R) * w1n * a2 ^ 2 * b4
    + (56873575734312960 : R) * w1n * a2 * a1 * b5
    + (68248290881175552 : R) * w1n * a2 * a0 * b6
    + (34124145440587776 : R) * w1n * a1 ^ 2 * b6
    + (79623006028038144 : R) * w1n * a1 * a0 * b7
    + (45498860587450368 : R) * w1n * a0 ^ 2 * b8
    - (22537920577536 : R) * e1 ^ 3 * e3 * b4
    + (561714328240128 : R) * e1 * e3 * a2 * b4
    + (702142910300160 : R) * e1 * e3 * a1 * b5
    + (842571492360192 : R) * e1 * e3 * a0 * b6
set_option maxHeartbeats 1600000000 in
/-- Order-`67` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder67610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b8 b7 b6 : R) : R :=
    (67814496 : R) * w1n ^ 13 * b8
    - (148106859264 : R) * w1n ^ 11 * e1b * b8
    + (51719855616 : R) * w1n ^ 10 * e3b * b8
    + (24980690262528 : R) * w1n ^ 9 * e1b ^ 2 * b8
    - (13033403615232 : R) * w1n ^ 8 * e1b * e3b * b8
    + (12256645040640 : R) * w1n ^ 8 * a2b * b7
    - (302796245606400 : R) * w1n ^ 7 * e1b ^ 3 * b8
    + (1655035379712 : R) * w1n ^ 7 * e3b ^ 2 * b8
    - (39221264130048 : R) * w1n ^ 7 * a1 * b7
    - (44824301862912 : R) * w1n ^ 7 * a0 * b8
    + (169565897539584 : R) * w1n ^ 6 * e1b ^ 2 * e3b * b8
    - (1555776810491904 : R) * w1n ^ 6 * e1b * a2b * b7
    + (673276357877760 : R) * w1n ^ 5 * e1b ^ 4 * b8
    - (29489721311232 : R) * w1n ^ 5 * e1b * e3b ^ 2 * b8
    + (3294586186924032 : R) * w1n ^ 5 * e1b * a1 * b7
    + (3765241356484608 : R) * w1n ^ 5 * e1b * a0 * b8
    + (366065131880448 : R) * w1n ^ 5 * e3b * a2b * b7
    - (332482152038400 : R) * w1n ^ 4 * e1b ^ 3 * e3b * b8
    + (8957502848286720 : R) * w1n ^ 4 * e1b ^ 2 * a2b * b7
    + (1560302714880 : R) * w1n ^ 4 * e3b ^ 3 * b8
    - (732130263760896 : R) * w1n ^ 4 * e3b * a1 * b7
    - (836720301441024 : R) * w1n ^ 4 * e3b * a0 * b8
    - (323395683287040 : R) * w1n ^ 3 * e1b ^ 5 * b8
    + (53197144326144 : R) * w1n ^ 3 * e1b ^ 2 * e3b ^ 2 * b8
    - (11314740439941120 : R) * w1n ^ 3 * e1b ^ 2 * a1 * b7
    - (12931131931361280 : R) * w1n ^ 3 * e1b ^ 2 * a0 * b8
    - (2514386764431360 : R) * w1n ^ 3 * e1b * e3b * a2b * b7
    + (15640233326936064 : R) * w1n ^ 3 * a2b ^ 2 * b6
    + (111515752857600 : R) * w1n ^ 2 * e1b ^ 4 * e3b * b8
    - (5901413641224192 : R) * w1n ^ 2 * e1b ^ 3 * a2b * b7
    - (3083892424704 : R) * w1n ^ 2 * e1b * e3b ^ 3 * b8
    + (2662291868221440 : R) * w1n ^ 2 * e1b * e3b * a1 * b7
    + (3042619277967360 : R) * w1n ^ 2 * e1b * e3b * a0 * b8
    + (147905103790080 : R) * w1n ^ 2 * e3b ^ 2 * a2b * b7
    - (51186218160881664 : R) * w1n ^ 2 * a2b * a1 * b6
    - (59717254521028608 : R) * w1n ^ 2 * a2b * a0 * b7
    + (25607321026560 : R) * w1n * e1b ^ 6 * b8
    - (11013901516800 : R) * w1n * e1b ^ 3 * e3b ^ 2 * b8
    + (3372236366413824 : R) * w1n * e1b ^ 3 * a1 * b7
    + (3853984418758656 : R) * w1n * e1b ^ 3 * a0 * b8
    + (1124078788804608 : R) * w1n * e1b ^ 2 * e3b * a2b * b7
    - (24645216151535616 : R) * w1n * e1b * a2b ^ 2 * b6
    + (48950673408 : R) * w1n * e3b ^ 4 * b8
    - (118324083032064 : R) * w1n * e3b ^ 2 * a1 * b7
    - (135227523465216 : R) * w1n * e3b ^ 2 * a0 * b8
    + (34124145440587776 : R) * w1n * a1 ^ 2 * b6
    + (79623006028038144 : R) * w1n * a1 * a0 * b7
    + (45498860587450368 : R) * w1n * a0 ^ 2 * b8
    - (3304170455040 : R) * e1b ^ 5 * e3b * b8
    + (281019697201152 : R) * e1b ^ 4 * a2b * b7
    + (293704040448 : R) * e1b ^ 2 * e3b ^ 3 * b8
    - (354972249096192 : R) * e1b ^ 2 * e3b * a1 * b7
    - (405682570395648 : R) * e1b ^ 2 * e3b * a0 * b8
    - (39441361010688 : R) * e1b * e3b ^ 2 * a2b * b7
    + (22749430293725184 : R) * e1b * a2b * a1 * b6
    + (26541002009346048 : R) * e1b * a2b * a0 * b7
    + (1263857238540288 : R) * e3b * a2b ^ 2 * b6
/-- Order-`67` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order67610 {R : Type*} [CommRing R] (w1 e1n e3 a1 a0 b8n : R) : R :=
    (25607321026560 : R) * w1 * e1n ^ 6 * b8n
    + (3853984418758656 : R) * w1 * e1n ^ 3 * a0 * b8n
    + (45498860587450368 : R) * w1 * a0 ^ 2 * b8n
    - (3304170455040 : R) * e1n ^ 5 * e3 * b8n
    + (321165368229888 : R) * e1n ^ 4 * a1 * b8n
    - (405682570395648 : R) * e1n ^ 2 * e3 * a0 * b8n
    + (30332573724966912 : R) * e1n * a1 * a0 * b8n
/-! ## Order `68` (MixedPair `h^14`) -/
set_option maxHeartbeats 1600000000 in
/-- Frozen order-`68` coefficient of the MixedPair jet (`h^14` of `alignedSquareJetQuotient610`). -/
def alignedSquareMixedPairOrder68610 {R : Type*} [CommRing R] (w1 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    (537476582522880 : R) * w1 ^ 6 * e3 * a0
    - (470184984576 : R) * w1 ^ 6 * b1
    + (10237146112327680 : R) * w1 ^ 5 * e1 ^ 2 * a0
    - (28239310173634560 : R) * w1 ^ 5 * a2 * a0
    - (14119655086817280 : R) * w1 ^ 5 * a1 ^ 2
    - (141351107788800 : R) * w1 ^ 4 * e3 ^ 2 * a1
    + (14627977297920 : R) * w1 ^ 4 * e3 * b2
    - (624488216002560 : R) * w1 ^ 3 * e1 ^ 2 * e3 * a1
    + (579267900997632 : R) * w1 ^ 3 * e1 ^ 2 * b2
    - (23795466240 : R) * w1 ^ 3 * e3 ^ 4
    + (6338790162432000 : R) * w1 ^ 3 * e3 * a2 * a1
    - (1354132755578880 : R) * w1 ^ 3 * a2 * b2
    - (2031199133368320 : R) * w1 ^ 3 * a1 * b3
    - (2708265511157760 : R) * w1 ^ 3 * a0 * b4
    + (1254552219648000 : R) * w1 ^ 2 * e1 ^ 4 * a1
    + (1147281408000 : R) * w1 ^ 2 * e1 ^ 2 * e3 ^ 3
    - (10839331177758720 : R) * w1 ^ 2 * e1 ^ 2 * a2 * a1
    - (1652085227520 : R) * w1 ^ 2 * e3 ^ 3 * a2
    - (17553572757504 : R) * w1 ^ 2 * e3 ^ 2 * b3
    - (30806520189419520 : R) * w1 ^ 2 * a2 ^ 2 * a1
    + (4206698496000 : R) * w1 * e1 ^ 4 * e3 ^ 2
    - (79300090920960 : R) * w1 * e1 ^ 2 * e3 ^ 2 * a2
    - (152130963898368 : R) * w1 * e1 ^ 2 * e3 * b3
    + (140862003609600 : R) * w1 * e3 ^ 2 * a2 ^ 2
    + (1263857238540288 : R) * w1 * e3 * a2 * b3
    + (1685142984720384 : R) * w1 * e3 * a1 * b4
    + (2106428730900480 : R) * w1 * e3 * a0 * b5
    + (1185524121600 : R) * e1 ^ 6 * e3
    - (61953196032000 : R) * e1 ^ 4 * e3 * a2
    - (38032740974592 : R) * e1 ^ 4 * b3
    + (802913420574720 : R) * e1 ^ 2 * e3 * a2 ^ 2
    + (1895785857810432 : R) * e1 ^ 2 * a2 * b3
    + (2527714477080576 : R) * e1 ^ 2 * a1 * b4
    + (3159643096350720 : R) * e1 ^ 2 * a0 * b5
    + (385263599616 : R) * e3 ^ 3 * b4
    - (1521309638983680 : R) * e3 * a2 ^ 3
    - (14624633760251904 : R) * a2 ^ 2 * b3
    - (38999023360671744 : R) * a2 * a1 * b4
    - (48748779200839680 : R) * a2 * a0 * b5
    - (24374389600419840 : R) * a1 ^ 2 * b5
    - (58498535041007616 : R) * a1 * a0 * b6
    - (34124145440587776 : R) * a0 ^ 2 * b7
set_option maxHeartbeats 1600000000 in
/-- Order-`68` coefficient of the MixedPair jet on `w₁ = 0` (frozen, no Taylor of `w₁`). -/
def alignedSquareW1ZeroOrder68610 {R : Type*} [CommRing R] (e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 : R) : R :=
    (1185524121600 : R) * e1 ^ 6 * e3
    - (61953196032000 : R) * e1 ^ 4 * e3 * a2
    - (38032740974592 : R) * e1 ^ 4 * b3
    + (802913420574720 : R) * e1 ^ 2 * e3 * a2 ^ 2
    + (1895785857810432 : R) * e1 ^ 2 * a2 * b3
    + (2527714477080576 : R) * e1 ^ 2 * a1 * b4
    + (3159643096350720 : R) * e1 ^ 2 * a0 * b5
    + (385263599616 : R) * e3 ^ 3 * b4
    - (1521309638983680 : R) * e3 * a2 ^ 3
    - (14624633760251904 : R) * a2 ^ 2 * b3
    - (38999023360671744 : R) * a2 * a1 * b4
    - (48748779200839680 : R) * a2 * a0 * b5
    - (24374389600419840 : R) * a1 ^ 2 * b5
    - (58498535041007616 : R) * a1 * a0 * b6
    - (34124145440587776 : R) * a0 ^ 2 * b7
set_option maxHeartbeats 1600000000 in
/-- Order-`68` mixed coefficient after `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder68610 {R : Type*} [CommRing R] (w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 : R) : R :=
    - (243596808 : R) * w1n ^ 12 * b7
    - (1102449553920 : R) * w1n ^ 9 * e1 * b6
    + (389099842560 : R) * w1n ^ 8 * e3 * b6
    - (185211525058560 : R) * w1n ^ 6 * e1 ^ 2 * b5
    + (90510609530880 : R) * w1n ^ 6 * a2 * b5
    + (108612731437056 : R) * w1n ^ 6 * a1 * b6
    + (126714853343232 : R) * w1n ^ 6 * a0 * b7
    + (87158364733440 : R) * w1n ^ 5 * e1 * e3 * b5
    - (9684262748160 : R) * w1n ^ 4 * e3 ^ 2 * b5
    - (718396218408960 : R) * w1n ^ 3 * e1 ^ 3 * b4
    + (6951214811971584 : R) * w1n ^ 3 * e1 * a2 * b4
    + (8689018514964480 : R) * w1n ^ 3 * e1 * a1 * b5
    + (10426822217957376 : R) * w1n ^ 3 * e1 * a0 * b6
    + (253551606497280 : R) * w1n ^ 2 * e1 ^ 2 * e3 * b4
    - (1263857238540288 : R) * w1n ^ 2 * e3 * a2 * b4
    - (1579821548175360 : R) * w1n ^ 2 * e3 * a1 * b5
    - (1895785857810432 : R) * w1n ^ 2 * e3 * a0 * b6
    - (7113144729600 : R) * w1n * e1 ^ 7
    + (408891093811200 : R) * w1n * e1 ^ 5 * a2
    - (6423307364597760 : R) * w1n * e1 ^ 3 * a2 ^ 2
    - (22537920577536 : R) * w1n * e1 * e3 ^ 2 * b4
    + (22819644584755200 : R) * w1n * e1 * a2 ^ 3
    + (1185524121600 : R) * e1 ^ 6 * e3
    - (61953196032000 : R) * e1 ^ 4 * e3 * a2
    - (38032740974592 : R) * e1 ^ 4 * b3
    + (802913420574720 : R) * e1 ^ 2 * e3 * a2 ^ 2
    + (1895785857810432 : R) * e1 ^ 2 * a2 * b3
    + (2527714477080576 : R) * e1 ^ 2 * a1 * b4
    + (3159643096350720 : R) * e1 ^ 2 * a0 * b5
    + (385263599616 : R) * e3 ^ 3 * b4
    - (1521309638983680 : R) * e3 * a2 ^ 3
    - (14624633760251904 : R) * a2 ^ 2 * b3
    - (38999023360671744 : R) * a2 * a1 * b4
    - (48748779200839680 : R) * a2 * a0 * b5
    - (24374389600419840 : R) * a1 ^ 2 * b5
    - (58498535041007616 : R) * a1 * a0 * b6
    - (34124145440587776 : R) * a0 ^ 2 * b7
set_option maxHeartbeats 1600000000 in
/-- Order-`68` coefficient on the `w₁ = 0` complement peel `w₁ = h w₁n`, `e₁ = h e₁b`, `e₃ = h e₃b`, `a₂ = h a₂b`. -/
def alignedSquareW1ComplementOrder68610 {R : Type*} [CommRing R] (w1n e1b e3b a2b a1 a0 b7 b6 b5 : R) : R :=
    - (243596808 : R) * w1n ^ 12 * b7
    + (407293862976 : R) * w1n ^ 10 * e1b * b7
    - (142910127360 : R) * w1n ^ 9 * e3b * b7
    - (51319026734976 : R) * w1n ^ 8 * e1b ^ 2 * b7
    + (26066807230464 : R) * w1n ^ 7 * e1b * e3b * b7
    - (33618226397184 : R) * w1n ^ 7 * a2b * b6
    + (445110481041408 : R) * w1n ^ 6 * e1b ^ 3 * b7
    - (3201186852864 : R) * w1n ^ 6 * e3b ^ 2 * b7
    + (108612731437056 : R) * w1n ^ 6 * a1 * b6
    + (126714853343232 : R) * w1n ^ 6 * a0 * b7
    - (232231555325952 : R) * w1n ^ 5 * e1b ^ 2 * e3b * b7
    + (2823931017363456 : R) * w1n ^ 5 * e1b * a2b * b6
    - (654574236825600 : R) * w1n ^ 4 * e1b ^ 4 * b7
    + (36862151639040 : R) * w1n ^ 4 * e1b * e3b ^ 2 * b7
    - (5647862034726912 : R) * w1n ^ 4 * e1b * a1 * b6
    - (6589172373848064 : R) * w1n ^ 4 * e1b * a0 * b7
    - (627540226080768 : R) * w1n ^ 4 * e3b * a2b * b6
    + (279285007712256 : R) * w1n ^ 3 * e1b ^ 3 * e3b * b7
    - (9698348948520960 : R) * w1n ^ 3 * e1b ^ 2 * a2b * b6
    - (1724545105920 : R) * w1n ^ 3 * e3b ^ 3 * b7
    + (1158535801995264 : R) * w1n ^ 3 * e3b * a1 * b6
    + (1351625102327808 : R) * w1n ^ 3 * e3b * a0 * b7
    + (175637310750720 : R) * w1n ^ 2 * e1b ^ 5 * b7
    - (36428479266816 : R) * w1n ^ 2 * e1b ^ 2 * e3b ^ 2 * b7
    + (10268840063139840 : R) * w1n ^ 2 * e1b ^ 2 * a1 * b6
    + (11980313406996480 : R) * w1n ^ 2 * e1b ^ 2 * a0 * b7
    + (2281964458475520 : R) * w1n ^ 2 * e1b * e3b * a2b * b6
    - (21327590900367360 : R) * w1n ^ 2 * a2b ^ 2 * b5
    - (43367237222400 : R) * w1n * e1b ^ 4 * e3b * b7
    + (2890488314068992 : R) * w1n * e1b ^ 3 * a2b * b6
    + (1541946212352 : R) * w1n * e1b * e3b ^ 3 * b7
    - (1825571566780416 : R) * w1n * e1b * e3b * a1 * b6
    - (2129833494577152 : R) * w1n * e1b * e3b * a0 * b7
    - (101420642598912 : R) * w1n * e3b ^ 2 * a2b * b6
    + (56873575734312960 : R) * w1n * a2b * a1 * b5
    + (68248290881175552 : R) * w1n * a2b * a0 * b6
    - (4336723722240 : R) * e1b ^ 6 * b7
    + (2312919318528 : R) * e1b ^ 3 * e3b ^ 2 * b7
    - (912785783390208 : R) * e1b ^ 3 * a1 * b6
    - (1064916747288576 : R) * e1b ^ 3 * a0 * b7
    - (304261927796736 : R) * e1b ^ 2 * e3b * a2b * b6
    + (9478929289052160 : R) * e1b * a2b ^ 2 * b5
    - (13525843968 : R) * e3b ^ 4 * b7
    + (46809527353344 : R) * e3b ^ 2 * a1 * b6
    + (54611115245568 : R) * e3b ^ 2 * a0 * b7
    - (24374389600419840 : R) * a1 ^ 2 * b5
    - (58498535041007616 : R) * a1 * a0 * b6
    - (34124145440587776 : R) * a0 ^ 2 * b7
set_option maxHeartbeats 1600000000 in
/-- Order-`68` mixed coefficient on `μ = 0` after the pole-`21` `q₈` peel: `e₁ = h e₁n`, `b₈ = h b₈n`. -/
def alignedSquareMuZeroQ8Order68610 {R : Type*} [CommRing R] (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (516534771916800 : R) * w1 ^ 7 * e1n ^ 4
    - (2328373457879040 : R) * w1 ^ 7 * e1n * a0
    + (259751681280000 : R) * w1 ^ 6 * e1n ^ 3 * e3
    - (7713405230469120 : R) * w1 ^ 6 * e1n ^ 2 * a1
    + (537476582522880 : R) * w1 ^ 6 * e3 * a0
    - (470184984576 : R) * w1 ^ 6 * b1
    - (6732763578777600 : R) * w1 ^ 5 * e1n ^ 3 * a2
    - (41560269004800 : R) * w1 ^ 5 * e1n ^ 2 * e3 ^ 2
    + (2274921358295040 : R) * w1 ^ 5 * e1n * e3 * a1
    - (39495538704384 : R) * w1 ^ 5 * e1n * b2
    - (28239310173634560 : R) * w1 ^ 5 * a2 * a0
    - (14119655086817280 : R) * w1 ^ 5 * a1 ^ 2
    + (1645786652590080 : R) * w1 ^ 4 * e1n ^ 2 * e3 * a2
    - (470655169560576 : R) * w1 ^ 4 * e1n ^ 2 * b3
    + (2257594859520 : R) * w1 ^ 4 * e1n * e3 ^ 3
    - (68696638385356800 : R) * w1 ^ 4 * e1n * a2 * a1
    - (141351107788800 : R) * w1 ^ 4 * e3 ^ 2 * a1
    + (14627977297920 : R) * w1 ^ 4 * e3 * b2
    - (718396218408960 : R) * w1 ^ 3 * e1n ^ 3 * b4
    - (8430590916034560 : R) * w1 ^ 3 * e1n ^ 2 * a2 ^ 2
    - (69387579555840 : R) * w1 ^ 3 * e1n * e3 ^ 2 * a2
    + (193089300332544 : R) * w1 ^ 3 * e1n * e3 * b3
    - (23795466240 : R) * w1 ^ 3 * e3 ^ 4
    + (6338790162432000 : R) * w1 ^ 3 * e3 * a2 * a1
    - (1354132755578880 : R) * w1 ^ 3 * a2 * b2
    - (2031199133368320 : R) * w1 ^ 3 * a1 * b3
    - (2708265511157760 : R) * w1 ^ 3 * a0 * b4
    - (351274621501440 : R) * w1 ^ 2 * e1n ^ 4 * b5
    + (253551606497280 : R) * w1 ^ 2 * e1n ^ 2 * e3 * b4
    - (1204370130862080 : R) * w1 ^ 2 * e1n * e3 * a2 ^ 2
    - (8531036360146944 : R) * w1 ^ 2 * e1n * a2 * b3
    - (11374715146862592 : R) * w1 ^ 2 * e1n * a1 * b4
    - (14218393933578240 : R) * w1 ^ 2 * e1n * a0 * b5
    - (1652085227520 : R) * w1 ^ 2 * e3 ^ 3 * a2
    - (17553572757504 : R) * w1 ^ 2 * e3 ^ 2 * b3
    - (30806520189419520 : R) * w1 ^ 2 * a2 ^ 2 * a1
    - (66909451714560 : R) * w1 * e1n ^ 5 * b6
    + (89212602286080 : R) * w1 * e1n ^ 3 * e3 * b5
    - (5476714700341248 : R) * w1 * e1n ^ 2 * a2 * b4
    - (6845893375426560 : R) * w1 * e1n ^ 2 * a1 * b5
    - (8215072050511872 : R) * w1 * e1n ^ 2 * a0 * b6
    - (22537920577536 : R) * w1 * e1n * e3 ^ 2 * b4
    + (22819644584755200 : R) * w1 * e1n * a2 ^ 3
    + (140862003609600 : R) * w1 * e3 ^ 2 * a2 ^ 2
    + (1263857238540288 : R) * w1 * e3 * a2 * b3
    + (1685142984720384 : R) * w1 * e3 * a1 * b4
    + (2106428730900480 : R) * w1 * e3 * a0 * b5
    - (4336723722240 : R) * e1n ^ 6 * b7
    + (8921260228608 : R) * e1n ^ 4 * e3 * b6
    - (760654819491840 : R) * e1n ^ 3 * a2 * b5
    - (912785783390208 : R) * e1n ^ 3 * a1 * b6
    - (1064916747288576 : R) * e1n ^ 3 * a0 * b7
    - (4695400120320 : R) * e1n ^ 2 * e3 ^ 2 * b5
    + (561714328240128 : R) * e1n * e3 * a2 * b4
    + (702142910300160 : R) * e1n * e3 * a1 * b5
    + (842571492360192 : R) * e1n * e3 * a0 * b6
    + (385263599616 : R) * e3 ^ 3 * b4
    - (1521309638983680 : R) * e3 * a2 ^ 3
    - (14624633760251904 : R) * a2 ^ 2 * b3
    - (38999023360671744 : R) * a2 * a1 * b4
    - (48748779200839680 : R) * a2 * a0 * b5
    - (24374389600419840 : R) * a1 ^ 2 * b5
    - (58498535041007616 : R) * a1 * a0 * b6
    - (34124145440587776 : R) * a0 ^ 2 * b7
/-! ## Order-`68` Plus remainders -/
set_option maxHeartbeats 1600000000 in
/-- Remaining factor after order `68` on `w₁ = 0` (frozen). -/
def alignedSquareW1ZeroOrder68Plus610 {R : Type*} [CommRing R] (h e1 e3 a2 a1 a0 b4 b3 b2 b1 : R) : R :=
    (2106428730900480 : R) * h ^ 5 * e3 * a0 ^ 2
    + (58498535041007616 : R) * h ^ 5 * a0 * b1
    - (13691786750853120 : R) * h ^ 3 * e1 ^ 2 * a1 * a0
    - (2086844497920 : R) * h ^ 3 * e3 ^ 3 * a0
    - (6687075336192 : R) * h ^ 3 * e3 ^ 2 * b1
    + (113747151468625920 : R) * h ^ 3 * a2 * a1 * a0
    + (18957858578104320 : R) * h ^ 3 * a1 ^ 3
    + (178425204572160 : R) * h ^ 2 * e1 ^ 3 * e3 * a0
    + (70214291030016 : R) * h ^ 2 * e1 ^ 3 * b1
    - (3042619277967360 : R) * h ^ 2 * e1 * e3 * a2 * a0
    - (1521309638983680 : R) * h ^ 2 * e1 * e3 * a1 ^ 2
    - (3249918613389312 : R) * h ^ 2 * e1 * a2 * b1
    - (6499837226778624 : R) * h ^ 2 * e1 * a1 * b2
    - (9749755840167936 : R) * h ^ 2 * e1 * a0 * b3
    + (29737534095360 : R) * h * e1 ^ 2 * e3 ^ 2 * a1
    + (46809527353344 : R) * h * e1 ^ 2 * e3 * b2
    + (453246976 : R) * h * e3 ^ 5
    - (169034404331520 : R) * h * e3 ^ 2 * a2 * a1
    - (722204136308736 : R) * h * e3 * a2 * b2
    - (1083306204463104 : R) * h * e3 * a1 * b3
    - (1444408272617472 : R) * h * e3 * a0 * b4
    - (111515752857600 : R) * e1 ^ 5 * a1
    - (169967616000 : R) * e1 ^ 3 * e3 ^ 3
    + (4817480523448320 : R) * e1 ^ 3 * a2 * a1
    + (2202780303360 : R) * e1 * e3 ^ 3 * a2
    + (7801587892224 : R) * e1 * e3 ^ 2 * b3
    - (41075360252559360 : R) * e1 * a2 ^ 2 * a1
set_option maxHeartbeats 1600000000 in
/-- Remaining factor after order `68` on `w₁ = h w₁n`. -/
def alignedSquareW1PeelOrder68Plus610 {R : Type*} [CommRing R] (h w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (26372304 : R) * h ^ 6 * w1n ^ 15
    + (20751991603200 : R) * h ^ 6 * w1n ^ 9 * a0
    - (37915717156208640 : R) * h ^ 6 * w1n ^ 3 * a0 ^ 2
    + (69754744080 : R) * h ^ 5 * w1n ^ 13 * e1
    - (24284496600 : R) * h ^ 5 * w1n ^ 12 * e3
    - (6522826527360 : R) * h ^ 5 * w1n ^ 10 * a1
    - (2328373457879040 : R) * h ^ 5 * w1n ^ 7 * e1 * a0
    + (537476582522880 : R) * h ^ 5 * w1n ^ 6 * e3 * a0
    - (470184984576 : R) * h ^ 5 * w1n ^ 6 * b1
    + (49961856461045760 : R) * h ^ 5 * w1n ^ 4 * a1 * a0
    - (12638572385402880 : R) * h ^ 5 * w1n * e1 * a0 ^ 2
    + (2106428730900480 : R) * h ^ 5 * e3 * a0 ^ 2
    + (58498535041007616 : R) * h ^ 5 * a0 * b1
    - (14193574012800 : R) * h ^ 4 * w1n ^ 11 * e1 ^ 2
    + (2062916968320 : R) * h ^ 4 * w1n ^ 11 * a2
    + (7517337347520 : R) * h ^ 4 * w1n ^ 10 * e1 * e3
    - (972141730560 : R) * h ^ 4 * w1n ^ 9 * e3 ^ 2
    + (1068273617748480 : R) * h ^ 4 * w1n ^ 8 * e1 * a1
    - (258708161986560 : R) * h ^ 4 * w1n ^ 7 * e3 * a1
    + (156728328192 : R) * h ^ 4 * w1n ^ 7 * b2
    + (10237146112327680 : R) * h ^ 4 * w1n ^ 5 * e1 ^ 2 * a0
    - (28239310173634560 : R) * h ^ 4 * w1n ^ 5 * a2 * a0
    - (14119655086817280 : R) * h ^ 4 * w1n ^ 5 * a1 ^ 2
    - (2544319940198400 : R) * h ^ 4 * w1n ^ 4 * e1 * e3 * a0
    + (65825897840640 : R) * h ^ 4 * w1n ^ 4 * e1 * b1
    + (117385003008000 : R) * h ^ 4 * w1n ^ 3 * e3 ^ 2 * a0
    - (25076532510720 : R) * h ^ 4 * w1n ^ 3 * e3 * b1
    - (20537680126279680 : R) * h ^ 4 * w1n ^ 2 * e1 * a1 * a0
    - (2808571641200640 : R) * h ^ 4 * w1n * e3 * a1 * a0
    - (9749755840167936 : R) * h ^ 4 * w1n * a1 * b1
    - (19499511680335872 : R) * h ^ 4 * w1n * a0 * b2
    + (205018291296000 : R) * h ^ 3 * w1n ^ 9 * e1 ^ 3
    - (472460881052160 : R) * h ^ 3 * w1n ^ 9 * e1 * a2
    - (118279783440000 : R) * h ^ 3 * w1n ^ 8 * e1 ^ 2 * e3
    + (118697068638720 : R) * h ^ 3 * w1n ^ 8 * e3 * a2
    - (44079842304 : R) * h ^ 3 * w1n ^ 8 * b3
    + (21307883950080 : R) * h ^ 3 * w1n ^ 7 * e1 * e3 ^ 2
    - (7713405230469120 : R) * h ^ 3 * w1n ^ 6 * e1 ^ 2 * a1
    - (1175644753920 : R) * h ^ 3 * w1n ^ 6 * e3 ^ 3
    + (14511867728117760 : R) * h ^ 3 * w1n ^ 6 * a2 * a1
    + (2274921358295040 : R) * h ^ 3 * w1n ^ 5 * e1 * e3 * a1
    - (39495538704384 : R) * h ^ 3 * w1n ^ 5 * e1 * b2
    - (141351107788800 : R) * h ^ 3 * w1n ^ 4 * e3 ^ 2 * a1
    + (14627977297920 : R) * h ^ 3 * w1n ^ 4 * e3 * b2
    - (1873464648007680 : R) * h ^ 3 * w1n ^ 3 * e1 ^ 3 * a0
    + (57049111461888000 : R) * h ^ 3 * w1n ^ 3 * e1 * a2 * a0
    + (28524555730944000 : R) * h ^ 3 * w1n ^ 3 * e1 * a1 ^ 2
    - (401456710287360 : R) * h ^ 3 * w1n ^ 2 * e1 ^ 2 * e3 * a0
    - (473946464452608 : R) * h ^ 3 * w1n ^ 2 * e1 ^ 2 * b1
    - (2281964458475520 : R) * h ^ 3 * w1n ^ 2 * e3 * a2 * a0
    - (1140982229237760 : R) * h ^ 3 * w1n ^ 2 * e3 * a1 ^ 2
    + (2437438960041984 : R) * h ^ 3 * w1n ^ 2 * a2 * b1
    + (4874877920083968 : R) * h ^ 3 * w1n ^ 2 * a1 * b2
    + (7312316880125952 : R) * h ^ 3 * w1n ^ 2 * a0 * b3
    + (93908002406400 : R) * h ^ 3 * w1n * e1 * e3 ^ 2 * a0
    + (140428582060032 : R) * h ^ 3 * w1n * e1 * e3 * b1
    - (13691786750853120 : R) * h ^ 3 * e1 ^ 2 * a1 * a0
    - (2086844497920 : R) * h ^ 3 * e3 ^ 3 * a0
    - (6687075336192 : R) * h ^ 3 * e3 ^ 2 * b1
    + (113747151468625920 : R) * h ^ 3 * a2 * a1 * a0
    + (18957858578104320 : R) * h ^ 3 * a1 ^ 3
    + (11972302848 : R) * h ^ 2 * w1n ^ 9 * b4
    - (516534771916800 : R) * h ^ 2 * w1n ^ 7 * e1 ^ 4
    + (5177815799869440 : R) * h ^ 2 * w1n ^ 7 * e1 ^ 2 * a2
    - (3492560186818560 : R) * h ^ 2 * w1n ^ 7 * a2 ^ 2
    + (259751681280000 : R) * h ^ 2 * w1n ^ 6 * e1 ^ 3 * e3
    - (1714090051215360 : R) * h ^ 2 * w1n ^ 6 * e1 * e3 * a2
    + (18102121906176 : R) * h ^ 2 * w1n ^ 6 * e1 * b3
    - (41560269004800 : R) * h ^ 2 * w1n ^ 5 * e1 ^ 2 * e3 ^ 2
    + (126384519905280 : R) * h ^ 2 * w1n ^ 5 * e3 ^ 2 * a2
    - (6582589784064 : R) * h ^ 2 * w1n ^ 5 * e3 * b3
    + (4937359957770240 : R) * h ^ 2 * w1n ^ 4 * e1 ^ 3 * a1
    + (2257594859520 : R) * h ^ 2 * w1n ^ 4 * e1 * e3 ^ 3
    - (68696638385356800 : R) * h ^ 2 * w1n ^ 4 * e1 * a2 * a1
    - (624488216002560 : R) * h ^ 2 * w1n ^ 3 * e1 ^ 2 * e3 * a1
    + (579267900997632 : R) * h ^ 2 * w1n ^ 3 * e1 ^ 2 * b2
    - (23795466240 : R) * h ^ 2 * w1n ^ 3 * e3 ^ 4
    + (6338790162432000 : R) * h ^ 2 * w1n ^ 3 * e3 * a2 * a1
    - (1354132755578880 : R) * h ^ 2 * w1n ^ 3 * a2 * b2
    - (2031199133368320 : R) * h ^ 2 * w1n ^ 3 * a1 * b3
    - (2708265511157760 : R) * h ^ 2 * w1n ^ 3 * a0 * b4
    - (44606301143040 : R) * h ^ 2 * w1n ^ 2 * e1 * e3 ^ 2 * a1
    - (210642873090048 : R) * h ^ 2 * w1n ^ 2 * e1 * e3 * b2
    - (1070551227432960 : R) * h ^ 2 * w1n * e1 ^ 4 * a0
    + (22819644584755200 : R) * h ^ 2 * w1n * e1 ^ 2 * a2 * a0
    + (11409822292377600 : R) * h ^ 2 * w1n * e1 ^ 2 * a1 ^ 2
    + (3478074163200 : R) * h ^ 2 * w1n * e3 ^ 3 * a1
    + (15603175784448 : R) * h ^ 2 * w1n * e3 ^ 2 * b2
    - (37915717156208640 : R) * h ^ 2 * w1n * a2 ^ 2 * a0
    - (37915717156208640 : R) * h ^ 2 * w1n * a2 * a1 ^ 2
    + (178425204572160 : R) * h ^ 2 * e1 ^ 3 * e3 * a0
    + (70214291030016 : R) * h ^ 2 * e1 ^ 3 * b1
    - (3042619277967360 : R) * h ^ 2 * e1 * e3 * a2 * a0
    - (1521309638983680 : R) * h ^ 2 * e1 * e3 * a1 ^ 2
    - (3249918613389312 : R) * h ^ 2 * e1 * a2 * b1
    - (6499837226778624 : R) * h ^ 2 * e1 * a1 * b2
    - (9749755840167936 : R) * h ^ 2 * e1 * a0 * b3
    - (3242498688 : R) * h * w1n ^ 10 * b5
    - (7470716977152 : R) * h * w1n ^ 7 * e1 * b4
    + (2681795837952 : R) * h * w1n ^ 6 * e3 * b4
    + (208859712122880 : R) * h * w1n ^ 5 * e1 ^ 5
    - (6732763578777600 : R) * h * w1n ^ 5 * e1 ^ 3 * a2
    + (30711438336983040 : R) * h * w1n ^ 5 * e1 * a2 ^ 2
    - (46787569920000 : R) * h * w1n ^ 4 * e1 ^ 4 * e3
    + (1645786652590080 : R) * h * w1n ^ 4 * e1 ^ 2 * e3 * a2
    - (470655169560576 : R) * h * w1n ^ 4 * e1 ^ 2 * b3
    - (3816479910297600 : R) * h * w1n ^ 4 * e3 * a2 ^ 2
    + (592433080565760 : R) * h * w1n ^ 4 * a2 * b3
    + (789910774087680 : R) * h * w1n ^ 4 * a1 * b4
    + (987388467609600 : R) * h * w1n ^ 4 * a0 * b5
    - (3441844224000 : R) * h * w1n ^ 3 * e1 ^ 3 * e3 ^ 2
    - (69387579555840 : R) * h * w1n ^ 3 * e1 * e3 ^ 2 * a2
    + (193089300332544 : R) * h * w1n ^ 3 * e1 * e3 * b3
    + (1254552219648000 : R) * h * w1n ^ 2 * e1 ^ 4 * a1
    + (1147281408000 : R) * h * w1n ^ 2 * e1 ^ 2 * e3 ^ 3
    - (10839331177758720 : R) * h * w1n ^ 2 * e1 ^ 2 * a2 * a1
    - (1652085227520 : R) * h * w1n ^ 2 * e3 ^ 3 * a2
    - (17553572757504 : R) * h * w1n ^ 2 * e3 ^ 2 * b3
    - (30806520189419520 : R) * h * w1n ^ 2 * a2 ^ 2 * a1
    - (475800545525760 : R) * h * w1n * e1 ^ 3 * e3 * a1
    - (304261927796736 : R) * h * w1n * e1 ^ 3 * b2
    - (54389637120 : R) * h * w1n * e1 * e3 ^ 4
    + (5071032129945600 : R) * h * w1n * e1 * e3 * a2 * a1
    + (7583143431241728 : R) * h * w1n * e1 * a2 * b2
    + (11374715146862592 : R) * h * w1n * e1 * a1 * b3
    + (15166286862483456 : R) * h * w1n * e1 * a0 * b4
    + (29737534095360 : R) * h * e1 ^ 2 * e3 ^ 2 * a1
    + (46809527353344 : R) * h * e1 ^ 2 * e3 * b2
    + (453246976 : R) * h * e3 ^ 5
    - (169034404331520 : R) * h * e3 ^ 2 * a2 * a1
    - (722204136308736 : R) * h * e3 * a2 * b2
    - (1083306204463104 : R) * h * e3 * a1 * b3
    - (1444408272617472 : R) * h * e3 * a0 * b4
    + (884317824 : R) * w1n ^ 11 * b6
    + (2918248819200 : R) * w1n ^ 8 * e1 * b5
    - (1037599580160 : R) * w1n ^ 7 * e3 * b5
    + (313770113040384 : R) * w1n ^ 5 * e1 ^ 2 * b4
    - (236973232226304 : R) * w1n ^ 5 * a2 * b4
    - (296216540282880 : R) * w1n ^ 5 * a1 * b5
    - (355459848339456 : R) * w1n ^ 5 * a0 * b6
    - (139453383573504 : R) * w1n ^ 4 * e1 * e3 * b4
    + (39122296012800 : R) * w1n ^ 3 * e1 ^ 6
    - (418184073216000 : R) * w1n ^ 3 * e1 ^ 4 * a2
    - (8430590916034560 : R) * w1n ^ 3 * e1 ^ 2 * a2 ^ 2
    + (14302911135744 : R) * w1n ^ 3 * e3 ^ 2 * b4
    + (28524555730944000 : R) * w1n ^ 3 * a2 ^ 3
    - (26674292736000 : R) * w1n ^ 2 * e1 ^ 5 * e3
    + (557578764288000 : R) * w1n ^ 2 * e1 ^ 3 * e3 * a2
    + (570491114618880 : R) * w1n ^ 2 * e1 ^ 3 * b3
    - (1204370130862080 : R) * w1n ^ 2 * e1 * e3 * a2 ^ 2
    - (8531036360146944 : R) * w1n ^ 2 * e1 * a2 * b3
    - (11374715146862592 : R) * w1n ^ 2 * e1 * a1 * b4
    - (14218393933578240 : R) * w1n ^ 2 * e1 * a0 * b5
    + (4206698496000 : R) * w1n * e1 ^ 4 * e3 ^ 2
    - (79300090920960 : R) * w1n * e1 ^ 2 * e3 ^ 2 * a2
    - (152130963898368 : R) * w1n * e1 ^ 2 * e3 * b3
    + (140862003609600 : R) * w1n * e3 ^ 2 * a2 ^ 2
    + (1263857238540288 : R) * w1n * e3 * a2 * b3
    + (1685142984720384 : R) * w1n * e3 * a1 * b4
    + (2106428730900480 : R) * w1n * e3 * a0 * b5
    - (111515752857600 : R) * e1 ^ 5 * a1
    - (169967616000 : R) * e1 ^ 3 * e3 ^ 3
    + (4817480523448320 : R) * e1 ^ 3 * a2 * a1
    + (2202780303360 : R) * e1 * e3 ^ 3 * a2
    + (7801587892224 : R) * e1 * e3 ^ 2 * b3
    - (41075360252559360 : R) * e1 * a2 ^ 2 * a1
set_option maxHeartbeats 1600000000 in
/-- Remaining factor after order `68` on the `w₁ = 0` complement. -/
def alignedSquareW1ComplementOrder68Plus610 {R : Type*} [CommRing R] (h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (26372304 : R) * h ^ 6 * w1n ^ 15
    + (69754744080 : R) * h ^ 6 * w1n ^ 13 * e1b
    - (24284496600 : R) * h ^ 6 * w1n ^ 12 * e3b
    - (14193574012800 : R) * h ^ 6 * w1n ^ 11 * e1b ^ 2
    + (7517337347520 : R) * h ^ 6 * w1n ^ 10 * e1b * e3b
    + (205018291296000 : R) * h ^ 6 * w1n ^ 9 * e1b ^ 3
    - (972141730560 : R) * h ^ 6 * w1n ^ 9 * e3b ^ 2
    + (20751991603200 : R) * h ^ 6 * w1n ^ 9 * a0
    - (118279783440000 : R) * h ^ 6 * w1n ^ 8 * e1b ^ 2 * e3b
    - (516534771916800 : R) * h ^ 6 * w1n ^ 7 * e1b ^ 4
    + (21307883950080 : R) * h ^ 6 * w1n ^ 7 * e1b * e3b ^ 2
    - (2328373457879040 : R) * h ^ 6 * w1n ^ 7 * e1b * a0
    + (259751681280000 : R) * h ^ 6 * w1n ^ 6 * e1b ^ 3 * e3b
    - (1175644753920 : R) * h ^ 6 * w1n ^ 6 * e3b ^ 3
    + (537476582522880 : R) * h ^ 6 * w1n ^ 6 * e3b * a0
    + (208859712122880 : R) * h ^ 6 * w1n ^ 5 * e1b ^ 5
    - (41560269004800 : R) * h ^ 6 * w1n ^ 5 * e1b ^ 2 * e3b ^ 2
    + (10237146112327680 : R) * h ^ 6 * w1n ^ 5 * e1b ^ 2 * a0
    - (46787569920000 : R) * h ^ 6 * w1n ^ 4 * e1b ^ 4 * e3b
    + (2257594859520 : R) * h ^ 6 * w1n ^ 4 * e1b * e3b ^ 3
    - (2544319940198400 : R) * h ^ 6 * w1n ^ 4 * e1b * e3b * a0
    + (39122296012800 : R) * h ^ 6 * w1n ^ 3 * e1b ^ 6
    - (3441844224000 : R) * h ^ 6 * w1n ^ 3 * e1b ^ 3 * e3b ^ 2
    - (1873464648007680 : R) * h ^ 6 * w1n ^ 3 * e1b ^ 3 * a0
    - (23795466240 : R) * h ^ 6 * w1n ^ 3 * e3b ^ 4
    + (117385003008000 : R) * h ^ 6 * w1n ^ 3 * e3b ^ 2 * a0
    - (37915717156208640 : R) * h ^ 6 * w1n ^ 3 * a0 ^ 2
    - (26674292736000 : R) * h ^ 6 * w1n ^ 2 * e1b ^ 5 * e3b
    + (1147281408000 : R) * h ^ 6 * w1n ^ 2 * e1b ^ 2 * e3b ^ 3
    - (401456710287360 : R) * h ^ 6 * w1n ^ 2 * e1b ^ 2 * e3b * a0
    - (7113144729600 : R) * h ^ 6 * w1n * e1b ^ 7
    + (4206698496000 : R) * h ^ 6 * w1n * e1b ^ 4 * e3b ^ 2
    - (1070551227432960 : R) * h ^ 6 * w1n * e1b ^ 4 * a0
    - (54389637120 : R) * h ^ 6 * w1n * e1b * e3b ^ 4
    + (93908002406400 : R) * h ^ 6 * w1n * e1b * e3b ^ 2 * a0
    - (12638572385402880 : R) * h ^ 6 * w1n * e1b * a0 ^ 2
    + (1185524121600 : R) * h ^ 6 * e1b ^ 6 * e3b
    - (169967616000 : R) * h ^ 6 * e1b ^ 3 * e3b ^ 3
    + (178425204572160 : R) * h ^ 6 * e1b ^ 3 * e3b * a0
    + (453246976 : R) * h ^ 6 * e3b ^ 5
    - (2086844497920 : R) * h ^ 6 * e3b ^ 3 * a0
    + (2106428730900480 : R) * h ^ 6 * e3b * a0 ^ 2
    + (2062916968320 : R) * h ^ 5 * w1n ^ 11 * a2b
    - (6522826527360 : R) * h ^ 5 * w1n ^ 10 * a1
    - (472460881052160 : R) * h ^ 5 * w1n ^ 9 * e1b * a2b
    + (1068273617748480 : R) * h ^ 5 * w1n ^ 8 * e1b * a1
    + (118697068638720 : R) * h ^ 5 * w1n ^ 8 * e3b * a2b
    + (5177815799869440 : R) * h ^ 5 * w1n ^ 7 * e1b ^ 2 * a2b
    - (258708161986560 : R) * h ^ 5 * w1n ^ 7 * e3b * a1
    - (7713405230469120 : R) * h ^ 5 * w1n ^ 6 * e1b ^ 2 * a1
    - (1714090051215360 : R) * h ^ 5 * w1n ^ 6 * e1b * e3b * a2b
    - (470184984576 : R) * h ^ 5 * w1n ^ 6 * b1
    - (6732763578777600 : R) * h ^ 5 * w1n ^ 5 * e1b ^ 3 * a2b
    + (2274921358295040 : R) * h ^ 5 * w1n ^ 5 * e1b * e3b * a1
    + (126384519905280 : R) * h ^ 5 * w1n ^ 5 * e3b ^ 2 * a2b
    - (28239310173634560 : R) * h ^ 5 * w1n ^ 5 * a2b * a0
    + (4937359957770240 : R) * h ^ 5 * w1n ^ 4 * e1b ^ 3 * a1
    + (1645786652590080 : R) * h ^ 5 * w1n ^ 4 * e1b ^ 2 * e3b * a2b
    + (65825897840640 : R) * h ^ 5 * w1n ^ 4 * e1b * b1
    - (141351107788800 : R) * h ^ 5 * w1n ^ 4 * e3b ^ 2 * a1
    + (49961856461045760 : R) * h ^ 5 * w1n ^ 4 * a1 * a0
    - (418184073216000 : R) * h ^ 5 * w1n ^ 3 * e1b ^ 4 * a2b
    - (624488216002560 : R) * h ^ 5 * w1n ^ 3 * e1b ^ 2 * e3b * a1
    - (69387579555840 : R) * h ^ 5 * w1n ^ 3 * e1b * e3b ^ 2 * a2b
    + (57049111461888000 : R) * h ^ 5 * w1n ^ 3 * e1b * a2b * a0
    - (25076532510720 : R) * h ^ 5 * w1n ^ 3 * e3b * b1
    + (1254552219648000 : R) * h ^ 5 * w1n ^ 2 * e1b ^ 4 * a1
    + (557578764288000 : R) * h ^ 5 * w1n ^ 2 * e1b ^ 3 * e3b * a2b
    - (473946464452608 : R) * h ^ 5 * w1n ^ 2 * e1b ^ 2 * b1
    - (44606301143040 : R) * h ^ 5 * w1n ^ 2 * e1b * e3b ^ 2 * a1
    - (20537680126279680 : R) * h ^ 5 * w1n ^ 2 * e1b * a1 * a0
    - (1652085227520 : R) * h ^ 5 * w1n ^ 2 * e3b ^ 3 * a2b
    - (2281964458475520 : R) * h ^ 5 * w1n ^ 2 * e3b * a2b * a0
    + (408891093811200 : R) * h ^ 5 * w1n * e1b ^ 5 * a2b
    - (475800545525760 : R) * h ^ 5 * w1n * e1b ^ 3 * e3b * a1
    - (79300090920960 : R) * h ^ 5 * w1n * e1b ^ 2 * e3b ^ 2 * a2b
    + (22819644584755200 : R) * h ^ 5 * w1n * e1b ^ 2 * a2b * a0
    + (140428582060032 : R) * h ^ 5 * w1n * e1b * e3b * b1
    + (3478074163200 : R) * h ^ 5 * w1n * e3b ^ 3 * a1
    - (2808571641200640 : R) * h ^ 5 * w1n * e3b * a1 * a0
    - (111515752857600 : R) * h ^ 5 * e1b ^ 5 * a1
    - (61953196032000 : R) * h ^ 5 * e1b ^ 4 * e3b * a2b
    + (70214291030016 : R) * h ^ 5 * e1b ^ 3 * b1
    + (29737534095360 : R) * h ^ 5 * e1b ^ 2 * e3b ^ 2 * a1
    - (13691786750853120 : R) * h ^ 5 * e1b ^ 2 * a1 * a0
    + (2202780303360 : R) * h ^ 5 * e1b * e3b ^ 3 * a2b
    - (3042619277967360 : R) * h ^ 5 * e1b * e3b * a2b * a0
    - (6687075336192 : R) * h ^ 5 * e3b ^ 2 * b1
    + (58498535041007616 : R) * h ^ 5 * a0 * b1
    - (3492560186818560 : R) * h ^ 4 * w1n ^ 7 * a2b ^ 2
    + (156728328192 : R) * h ^ 4 * w1n ^ 7 * b2
    + (14511867728117760 : R) * h ^ 4 * w1n ^ 6 * a2b * a1
    + (30711438336983040 : R) * h ^ 4 * w1n ^ 5 * e1b * a2b ^ 2
    - (39495538704384 : R) * h ^ 4 * w1n ^ 5 * e1b * b2
    - (14119655086817280 : R) * h ^ 4 * w1n ^ 5 * a1 ^ 2
    - (68696638385356800 : R) * h ^ 4 * w1n ^ 4 * e1b * a2b * a1
    - (3816479910297600 : R) * h ^ 4 * w1n ^ 4 * e3b * a2b ^ 2
    + (14627977297920 : R) * h ^ 4 * w1n ^ 4 * e3b * b2
    - (8430590916034560 : R) * h ^ 4 * w1n ^ 3 * e1b ^ 2 * a2b ^ 2
    + (579267900997632 : R) * h ^ 4 * w1n ^ 3 * e1b ^ 2 * b2
    + (28524555730944000 : R) * h ^ 4 * w1n ^ 3 * e1b * a1 ^ 2
    + (6338790162432000 : R) * h ^ 4 * w1n ^ 3 * e3b * a2b * a1
    - (10839331177758720 : R) * h ^ 4 * w1n ^ 2 * e1b ^ 2 * a2b * a1
    - (1204370130862080 : R) * h ^ 4 * w1n ^ 2 * e1b * e3b * a2b ^ 2
    - (210642873090048 : R) * h ^ 4 * w1n ^ 2 * e1b * e3b * b2
    - (1140982229237760 : R) * h ^ 4 * w1n ^ 2 * e3b * a1 ^ 2
    + (2437438960041984 : R) * h ^ 4 * w1n ^ 2 * a2b * b1
    - (6423307364597760 : R) * h ^ 4 * w1n * e1b ^ 3 * a2b ^ 2
    - (304261927796736 : R) * h ^ 4 * w1n * e1b ^ 3 * b2
    + (11409822292377600 : R) * h ^ 4 * w1n * e1b ^ 2 * a1 ^ 2
    + (5071032129945600 : R) * h ^ 4 * w1n * e1b * e3b * a2b * a1
    + (140862003609600 : R) * h ^ 4 * w1n * e3b ^ 2 * a2b ^ 2
    + (15603175784448 : R) * h ^ 4 * w1n * e3b ^ 2 * b2
    - (37915717156208640 : R) * h ^ 4 * w1n * a2b ^ 2 * a0
    - (9749755840167936 : R) * h ^ 4 * w1n * a1 * b1
    - (19499511680335872 : R) * h ^ 4 * w1n * a0 * b2
    + (4817480523448320 : R) * h ^ 4 * e1b ^ 3 * a2b * a1
    + (802913420574720 : R) * h ^ 4 * e1b ^ 2 * e3b * a2b ^ 2
    + (46809527353344 : R) * h ^ 4 * e1b ^ 2 * e3b * b2
    - (1521309638983680 : R) * h ^ 4 * e1b * e3b * a1 ^ 2
    - (3249918613389312 : R) * h ^ 4 * e1b * a2b * b1
    - (169034404331520 : R) * h ^ 4 * e3b ^ 2 * a2b * a1
    + (113747151468625920 : R) * h ^ 4 * a2b * a1 * a0
    - (44079842304 : R) * h ^ 3 * w1n ^ 8 * b3
    + (18102121906176 : R) * h ^ 3 * w1n ^ 6 * e1b * b3
    - (6582589784064 : R) * h ^ 3 * w1n ^ 5 * e3b * b3
    - (470655169560576 : R) * h ^ 3 * w1n ^ 4 * e1b ^ 2 * b3
    + (193089300332544 : R) * h ^ 3 * w1n ^ 3 * e1b * e3b * b3
    + (28524555730944000 : R) * h ^ 3 * w1n ^ 3 * a2b ^ 3
    - (1354132755578880 : R) * h ^ 3 * w1n ^ 3 * a2b * b2
    + (570491114618880 : R) * h ^ 3 * w1n ^ 2 * e1b ^ 3 * b3
    - (17553572757504 : R) * h ^ 3 * w1n ^ 2 * e3b ^ 2 * b3
    - (30806520189419520 : R) * h ^ 3 * w1n ^ 2 * a2b ^ 2 * a1
    + (4874877920083968 : R) * h ^ 3 * w1n ^ 2 * a1 * b2
    + (7312316880125952 : R) * h ^ 3 * w1n ^ 2 * a0 * b3
    - (152130963898368 : R) * h ^ 3 * w1n * e1b ^ 2 * e3b * b3
    + (22819644584755200 : R) * h ^ 3 * w1n * e1b * a2b ^ 3
    + (7583143431241728 : R) * h ^ 3 * w1n * e1b * a2b * b2
    - (37915717156208640 : R) * h ^ 3 * w1n * a2b * a1 ^ 2
    - (38032740974592 : R) * h ^ 3 * e1b ^ 4 * b3
    + (7801587892224 : R) * h ^ 3 * e1b * e3b ^ 2 * b3
    - (41075360252559360 : R) * h ^ 3 * e1b * a2b ^ 2 * a1
    - (6499837226778624 : R) * h ^ 3 * e1b * a1 * b2
    - (9749755840167936 : R) * h ^ 3 * e1b * a0 * b3
    - (1521309638983680 : R) * h ^ 3 * e3b * a2b ^ 3
    - (722204136308736 : R) * h ^ 3 * e3b * a2b * b2
    + (18957858578104320 : R) * h ^ 3 * a1 ^ 3
    + (11972302848 : R) * h ^ 2 * w1n ^ 9 * b4
    - (7470716977152 : R) * h ^ 2 * w1n ^ 7 * e1b * b4
    + (2681795837952 : R) * h ^ 2 * w1n ^ 6 * e3b * b4
    + (313770113040384 : R) * h ^ 2 * w1n ^ 5 * e1b ^ 2 * b4
    - (139453383573504 : R) * h ^ 2 * w1n ^ 4 * e1b * e3b * b4
    + (592433080565760 : R) * h ^ 2 * w1n ^ 4 * a2b * b3
    - (718396218408960 : R) * h ^ 2 * w1n ^ 3 * e1b ^ 3 * b4
    + (14302911135744 : R) * h ^ 2 * w1n ^ 3 * e3b ^ 2 * b4
    - (2031199133368320 : R) * h ^ 2 * w1n ^ 3 * a1 * b3
    - (2708265511157760 : R) * h ^ 2 * w1n ^ 3 * a0 * b4
    + (253551606497280 : R) * h ^ 2 * w1n ^ 2 * e1b ^ 2 * e3b * b4
    - (8531036360146944 : R) * h ^ 2 * w1n ^ 2 * e1b * a2b * b3
    + (160582684114944 : R) * h ^ 2 * w1n * e1b ^ 4 * b4
    - (22537920577536 : R) * h ^ 2 * w1n * e1b * e3b ^ 2 * b4
    + (11374715146862592 : R) * h ^ 2 * w1n * e1b * a1 * b3
    + (15166286862483456 : R) * h ^ 2 * w1n * e1b * a0 * b4
    + (1263857238540288 : R) * h ^ 2 * w1n * e3b * a2b * b3
    - (22537920577536 : R) * h ^ 2 * e1b ^ 3 * e3b * b4
    + (1895785857810432 : R) * h ^ 2 * e1b ^ 2 * a2b * b3
    + (385263599616 : R) * h ^ 2 * e3b ^ 3 * b4
    - (1083306204463104 : R) * h ^ 2 * e3b * a1 * b3
    - (1444408272617472 : R) * h ^ 2 * e3b * a0 * b4
    - (3242498688 : R) * h * w1n ^ 10 * b5
    + (2918248819200 : R) * h * w1n ^ 8 * e1b * b5
    - (1037599580160 : R) * h * w1n ^ 7 * e3b * b5
    - (185211525058560 : R) * h * w1n ^ 6 * e1b ^ 2 * b5
    + (87158364733440 : R) * h * w1n ^ 5 * e1b * e3b * b5
    - (236973232226304 : R) * h * w1n ^ 5 * a2b * b4
    + (710912924467200 : R) * h * w1n ^ 4 * e1b ^ 3 * b5
    - (9684262748160 : R) * h * w1n ^ 4 * e3b ^ 2 * b5
    + (789910774087680 : R) * h * w1n ^ 4 * a1 * b4
    + (987388467609600 : R) * h * w1n ^ 4 * a0 * b5
    - (299331757670400 : R) * h * w1n ^ 3 * e1b ^ 2 * e3b * b5
    + (6951214811971584 : R) * h * w1n ^ 3 * e1b * a2b * b4
    - (351274621501440 : R) * h * w1n ^ 2 * e1b ^ 4 * b5
    + (35215500902400 : R) * h * w1n ^ 2 * e1b * e3b ^ 2 * b5
    - (11374715146862592 : R) * h * w1n ^ 2 * e1b * a1 * b4
    - (14218393933578240 : R) * h * w1n ^ 2 * e1b * a0 * b5
    - (1263857238540288 : R) * h * w1n ^ 2 * e3b * a2b * b4
    + (89212602286080 : R) * h * w1n * e1b ^ 3 * e3b * b5
    - (5476714700341248 : R) * h * w1n * e1b ^ 2 * a2b * b4
    - (1043422248960 : R) * h * w1n * e3b ^ 3 * b5
    + (1685142984720384 : R) * h * w1n * e3b * a1 * b4
    + (2106428730900480 : R) * h * w1n * e3b * a0 * b5
    + (13381890342912 : R) * h * e1b ^ 5 * b5
    - (4695400120320 : R) * h * e1b ^ 2 * e3b ^ 2 * b5
    + (2527714477080576 : R) * h * e1b ^ 2 * a1 * b4
    + (3159643096350720 : R) * h * e1b ^ 2 * a0 * b5
    + (561714328240128 : R) * h * e1b * e3b * a2b * b4
    - (14624633760251904 : R) * h * a2b ^ 2 * b3
    + (884317824 : R) * w1n ^ 11 * b6
    - (1102449553920 : R) * w1n ^ 9 * e1b * b6
    + (389099842560 : R) * w1n ^ 8 * e3b * b6
    + (100543399317504 : R) * w1n ^ 7 * e1b ^ 2 * b6
    - (49389740015616 : R) * w1n ^ 6 * e1b * e3b * b6
    + (90510609530880 : R) * w1n ^ 6 * a2b * b5
    - (597166856552448 : R) * w1n ^ 5 * e1b ^ 3 * b6
    + (5810557648896 : R) * w1n ^ 5 * e3b ^ 2 * b6
    - (296216540282880 : R) * w1n ^ 5 * a1 * b5
    - (355459848339456 : R) * w1n ^ 5 * a0 * b6
    + (284365169786880 : R) * w1n ^ 4 * e1b ^ 2 * e3b * b6
    - (4706551695605760 : R) * w1n ^ 4 * e1b * a2b * b5
    + (538621086302208 : R) * w1n ^ 3 * e1b ^ 4 * b6
    - (39910901022720 : R) * w1n ^ 3 * e1b * e3b ^ 2 * b6
    + (8689018514964480 : R) * w1n ^ 3 * e1b * a1 * b5
    + (10426822217957376 : R) * w1n ^ 3 * e1b * a0 * b6
    + (965446501662720 : R) * w1n ^ 3 * e3b * a2b * b5
    - (187346464800768 : R) * w1n ^ 2 * e1b ^ 3 * e3b * b6
    + (8557366719283200 : R) * w1n ^ 2 * e1b ^ 2 * a2b * b5
    + (1565133373440 : R) * w1n ^ 2 * e3b ^ 3 * b6
    - (1579821548175360 : R) * w1n ^ 2 * e3b * a1 * b5
    - (1895785857810432 : R) * w1n ^ 2 * e3b * a0 * b6
    - (66909451714560 : R) * w1n * e1b ^ 5 * b6
    + (17842520457216 : R) * w1n * e1b ^ 2 * e3b ^ 2 * b6
    - (6845893375426560 : R) * w1n * e1b ^ 2 * a1 * b5
    - (8215072050511872 : R) * w1n * e1b ^ 2 * a0 * b6
    - (1521309638983680 : R) * w1n * e1b * e3b * a2b * b5
    + (22749430293725184 : R) * w1n * a2b ^ 2 * b4
    + (8921260228608 : R) * e1b ^ 4 * e3b * b6
    - (760654819491840 : R) * e1b ^ 3 * a2b * b5
    - (417368899584 : R) * e1b * e3b ^ 3 * b6
    + (702142910300160 : R) * e1b * e3b * a1 * b5
    + (842571492360192 : R) * e1b * e3b * a0 * b6
    + (39007939461120 : R) * e3b ^ 2 * a2b * b5
    - (38999023360671744 : R) * a2b * a1 * b4
    - (48748779200839680 : R) * a2b * a0 * b5
set_option maxHeartbeats 1600000000 in
/-- Remaining factor after order `68` on `μ = 0` after the `q₈` peel. -/
def alignedSquareMuZeroQ8Order68Plus610 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1 : R) : R :=
    - (7113144729600 : R) * h ^ 5 * w1 * e1n ^ 7
    - (1070551227432960 : R) * h ^ 5 * w1 * e1n ^ 4 * a0
    - (12638572385402880 : R) * h ^ 5 * w1 * e1n * a0 ^ 2
    + (1185524121600 : R) * h ^ 5 * e1n ^ 6 * e3
    - (111515752857600 : R) * h ^ 5 * e1n ^ 5 * a1
    + (178425204572160 : R) * h ^ 5 * e1n ^ 3 * e3 * a0
    + (70214291030016 : R) * h ^ 5 * e1n ^ 3 * b1
    - (13691786750853120 : R) * h ^ 5 * e1n ^ 2 * a1 * a0
    + (2106428730900480 : R) * h ^ 5 * e3 * a0 ^ 2
    + (58498535041007616 : R) * h ^ 5 * a0 * b1
    + (39122296012800 : R) * h ^ 3 * w1 ^ 3 * e1n ^ 6
    - (1873464648007680 : R) * h ^ 3 * w1 ^ 3 * e1n ^ 3 * a0
    - (37915717156208640 : R) * h ^ 3 * w1 ^ 3 * a0 ^ 2
    - (26674292736000 : R) * h ^ 3 * w1 ^ 2 * e1n ^ 5 * e3
    + (1254552219648000 : R) * h ^ 3 * w1 ^ 2 * e1n ^ 4 * a1
    - (401456710287360 : R) * h ^ 3 * w1 ^ 2 * e1n ^ 2 * e3 * a0
    - (473946464452608 : R) * h ^ 3 * w1 ^ 2 * e1n ^ 2 * b1
    - (20537680126279680 : R) * h ^ 3 * w1 ^ 2 * e1n * a1 * a0
    + (408891093811200 : R) * h ^ 3 * w1 * e1n ^ 5 * a2
    + (4206698496000 : R) * h ^ 3 * w1 * e1n ^ 4 * e3 ^ 2
    - (475800545525760 : R) * h ^ 3 * w1 * e1n ^ 3 * e3 * a1
    - (304261927796736 : R) * h ^ 3 * w1 * e1n ^ 3 * b2
    + (22819644584755200 : R) * h ^ 3 * w1 * e1n ^ 2 * a2 * a0
    + (11409822292377600 : R) * h ^ 3 * w1 * e1n ^ 2 * a1 ^ 2
    + (93908002406400 : R) * h ^ 3 * w1 * e1n * e3 ^ 2 * a0
    + (140428582060032 : R) * h ^ 3 * w1 * e1n * e3 * b1
    - (2808571641200640 : R) * h ^ 3 * w1 * e3 * a1 * a0
    - (9749755840167936 : R) * h ^ 3 * w1 * a1 * b1
    - (19499511680335872 : R) * h ^ 3 * w1 * a0 * b2
    - (61953196032000 : R) * h ^ 3 * e1n ^ 4 * e3 * a2
    - (38032740974592 : R) * h ^ 3 * e1n ^ 4 * b3
    - (169967616000 : R) * h ^ 3 * e1n ^ 3 * e3 ^ 3
    + (4817480523448320 : R) * h ^ 3 * e1n ^ 3 * a2 * a1
    + (29737534095360 : R) * h ^ 3 * e1n ^ 2 * e3 ^ 2 * a1
    + (46809527353344 : R) * h ^ 3 * e1n ^ 2 * e3 * b2
    - (3042619277967360 : R) * h ^ 3 * e1n * e3 * a2 * a0
    - (1521309638983680 : R) * h ^ 3 * e1n * e3 * a1 ^ 2
    - (3249918613389312 : R) * h ^ 3 * e1n * a2 * b1
    - (6499837226778624 : R) * h ^ 3 * e1n * a1 * b2
    - (9749755840167936 : R) * h ^ 3 * e1n * a0 * b3
    - (2086844497920 : R) * h ^ 3 * e3 ^ 3 * a0
    - (6687075336192 : R) * h ^ 3 * e3 ^ 2 * b1
    + (113747151468625920 : R) * h ^ 3 * a2 * a1 * a0
    + (18957858578104320 : R) * h ^ 3 * a1 ^ 3
    + (208859712122880 : R) * h * w1 ^ 5 * e1n ^ 5
    + (10237146112327680 : R) * h * w1 ^ 5 * e1n ^ 2 * a0
    - (46787569920000 : R) * h * w1 ^ 4 * e1n ^ 4 * e3
    + (4937359957770240 : R) * h * w1 ^ 4 * e1n ^ 3 * a1
    - (2544319940198400 : R) * h * w1 ^ 4 * e1n * e3 * a0
    + (65825897840640 : R) * h * w1 ^ 4 * e1n * b1
    + (49961856461045760 : R) * h * w1 ^ 4 * a1 * a0
    - (418184073216000 : R) * h * w1 ^ 3 * e1n ^ 4 * a2
    - (3441844224000 : R) * h * w1 ^ 3 * e1n ^ 3 * e3 ^ 2
    - (624488216002560 : R) * h * w1 ^ 3 * e1n ^ 2 * e3 * a1
    + (579267900997632 : R) * h * w1 ^ 3 * e1n ^ 2 * b2
    + (57049111461888000 : R) * h * w1 ^ 3 * e1n * a2 * a0
    + (28524555730944000 : R) * h * w1 ^ 3 * e1n * a1 ^ 2
    + (117385003008000 : R) * h * w1 ^ 3 * e3 ^ 2 * a0
    - (25076532510720 : R) * h * w1 ^ 3 * e3 * b1
    + (557578764288000 : R) * h * w1 ^ 2 * e1n ^ 3 * e3 * a2
    + (570491114618880 : R) * h * w1 ^ 2 * e1n ^ 3 * b3
    + (1147281408000 : R) * h * w1 ^ 2 * e1n ^ 2 * e3 ^ 3
    - (10839331177758720 : R) * h * w1 ^ 2 * e1n ^ 2 * a2 * a1
    - (44606301143040 : R) * h * w1 ^ 2 * e1n * e3 ^ 2 * a1
    - (210642873090048 : R) * h * w1 ^ 2 * e1n * e3 * b2
    - (2281964458475520 : R) * h * w1 ^ 2 * e3 * a2 * a0
    - (1140982229237760 : R) * h * w1 ^ 2 * e3 * a1 ^ 2
    + (2437438960041984 : R) * h * w1 ^ 2 * a2 * b1
    + (4874877920083968 : R) * h * w1 ^ 2 * a1 * b2
    + (7312316880125952 : R) * h * w1 ^ 2 * a0 * b3
    + (160582684114944 : R) * h * w1 * e1n ^ 4 * b4
    - (6423307364597760 : R) * h * w1 * e1n ^ 3 * a2 ^ 2
    - (79300090920960 : R) * h * w1 * e1n ^ 2 * e3 ^ 2 * a2
    - (152130963898368 : R) * h * w1 * e1n ^ 2 * e3 * b3
    - (54389637120 : R) * h * w1 * e1n * e3 ^ 4
    + (5071032129945600 : R) * h * w1 * e1n * e3 * a2 * a1
    + (7583143431241728 : R) * h * w1 * e1n * a2 * b2
    + (11374715146862592 : R) * h * w1 * e1n * a1 * b3
    + (15166286862483456 : R) * h * w1 * e1n * a0 * b4
    + (3478074163200 : R) * h * w1 * e3 ^ 3 * a1
    + (15603175784448 : R) * h * w1 * e3 ^ 2 * b2
    - (37915717156208640 : R) * h * w1 * a2 ^ 2 * a0
    - (37915717156208640 : R) * h * w1 * a2 * a1 ^ 2
    + (13381890342912 : R) * h * e1n ^ 5 * b5
    - (22537920577536 : R) * h * e1n ^ 3 * e3 * b4
    + (802913420574720 : R) * h * e1n ^ 2 * e3 * a2 ^ 2
    + (1895785857810432 : R) * h * e1n ^ 2 * a2 * b3
    + (2527714477080576 : R) * h * e1n ^ 2 * a1 * b4
    + (3159643096350720 : R) * h * e1n ^ 2 * a0 * b5
    + (2202780303360 : R) * h * e1n * e3 ^ 3 * a2
    + (7801587892224 : R) * h * e1n * e3 ^ 2 * b3
    - (41075360252559360 : R) * h * e1n * a2 ^ 2 * a1
    + (453246976 : R) * h * e3 ^ 5
    - (169034404331520 : R) * h * e3 ^ 2 * a2 * a1
    - (722204136308736 : R) * h * e3 * a2 * b2
    - (1083306204463104 : R) * h * e3 * a1 * b3
    - (1444408272617472 : R) * h * e3 * a0 * b4
/-! ## Ring maps and evaluation -/
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder61610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) :
    phi (alignedSquareMixedPairOrder61610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5) =
      alignedSquareMixedPairOrder61610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) (phi b5) := by
  simp only [alignedSquareMixedPairOrder61610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder61610
theorem alignedSquareMixedPairOrder61610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder61610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5).eval a =
      alignedSquareMixedPairOrder61610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) :=
  map_alignedSquareMixedPairOrder61610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b8 b7 b6 b5

#print axioms alignedSquareMixedPairOrder61610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder61610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 b8 : R) :
    phi (alignedSquareW1ZeroOrder61610 e1 e3 a2 b8) =
      alignedSquareW1ZeroOrder61610 (phi e1) (phi e3) (phi a2) (phi b8) := by
  simp only [alignedSquareW1ZeroOrder61610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder61610
theorem alignedSquareW1ZeroOrder61610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 b8 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder61610 e1 e3 a2 b8).eval a =
      alignedSquareW1ZeroOrder61610 (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a) :=
  map_alignedSquareW1ZeroOrder61610 (Polynomial.evalRingHom a) e1 e3 a2 b8

#print axioms alignedSquareW1ZeroOrder61610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder61610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 b8 : R) :
    phi (alignedSquareW1PeelOrder61610 w1n e1 e3 a2 b8) =
      alignedSquareW1PeelOrder61610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi b8) := by
  simp only [alignedSquareW1PeelOrder61610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder61610
theorem alignedSquareW1PeelOrder61610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 b8 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder61610 w1n e1 e3 a2 b8).eval a =
      alignedSquareW1PeelOrder61610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a) :=
  map_alignedSquareW1PeelOrder61610 (Polynomial.evalRingHom a) w1n e1 e3 a2 b8

#print axioms alignedSquareW1PeelOrder61610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder61610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n : R) :
    phi (alignedSquareW1ComplementOrder61610 w1n) =
      alignedSquareW1ComplementOrder61610 (phi w1n) := by
  simp only [alignedSquareW1ComplementOrder61610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder61610
theorem alignedSquareW1ComplementOrder61610_eval
    {k : Type*} [CommRing k]
    (w1n : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder61610 w1n).eval a =
      alignedSquareW1ComplementOrder61610 (w1n.eval a) :=
  map_alignedSquareW1ComplementOrder61610 (Polynomial.evalRingHom a) w1n

#print axioms alignedSquareW1ComplementOrder61610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order61610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a2 a1 a0 b8n : R) :
    phi (alignedSquareMuZeroQ8Order61610 w1 e1n e3 a2 a1 a0 b8n) =
      alignedSquareMuZeroQ8Order61610 (phi w1) (phi e1n) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8n) := by
  simp only [alignedSquareMuZeroQ8Order61610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order61610
theorem alignedSquareMuZeroQ8Order61610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a2 a1 a0 b8n : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order61610 w1 e1n e3 a2 a1 a0 b8n).eval a =
      alignedSquareMuZeroQ8Order61610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a) :=
  map_alignedSquareMuZeroQ8Order61610 (Polynomial.evalRingHom a) w1 e1n e3 a2 a1 a0 b8n

#print axioms alignedSquareMuZeroQ8Order61610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder62610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : R) :
    phi (alignedSquareMixedPairOrder62610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4) =
      alignedSquareMixedPairOrder62610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) (phi b5) (phi b4) := by
  simp only [alignedSquareMixedPairOrder62610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder62610
theorem alignedSquareMixedPairOrder62610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder62610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4).eval a =
      alignedSquareMixedPairOrder62610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) :=
  map_alignedSquareMixedPairOrder62610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4

#print axioms alignedSquareMixedPairOrder62610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder62610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 b8 b7 : R) :
    phi (alignedSquareW1ZeroOrder62610 e1 e3 a2 a1 b8 b7) =
      alignedSquareW1ZeroOrder62610 (phi e1) (phi e3) (phi a2) (phi a1) (phi b8) (phi b7) := by
  simp only [alignedSquareW1ZeroOrder62610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder62610
theorem alignedSquareW1ZeroOrder62610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 a1 b8 b7 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder62610 e1 e3 a2 a1 b8 b7).eval a =
      alignedSquareW1ZeroOrder62610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a) :=
  map_alignedSquareW1ZeroOrder62610 (Polynomial.evalRingHom a) e1 e3 a2 a1 b8 b7

#print axioms alignedSquareW1ZeroOrder62610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder62610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 b8 b7 : R) :
    phi (alignedSquareW1PeelOrder62610 w1n e1 e3 a2 a1 b8 b7) =
      alignedSquareW1PeelOrder62610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi b8) (phi b7) := by
  simp only [alignedSquareW1PeelOrder62610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder62610
theorem alignedSquareW1PeelOrder62610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 b8 b7 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder62610 w1n e1 e3 a2 a1 b8 b7).eval a =
      alignedSquareW1PeelOrder62610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a) :=
  map_alignedSquareW1PeelOrder62610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 b8 b7

#print axioms alignedSquareW1PeelOrder62610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder62610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n : R) :
    phi (alignedSquareW1ComplementOrder62610 w1n) =
      alignedSquareW1ComplementOrder62610 (phi w1n) := by
  simp only [alignedSquareW1ComplementOrder62610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder62610
theorem alignedSquareW1ComplementOrder62610_eval
    {k : Type*} [CommRing k]
    (w1n : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder62610 w1n).eval a =
      alignedSquareW1ComplementOrder62610 (w1n.eval a) :=
  map_alignedSquareW1ComplementOrder62610 (Polynomial.evalRingHom a) w1n

#print axioms alignedSquareW1ComplementOrder62610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order62610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 : R) :
    phi (alignedSquareMuZeroQ8Order62610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4) =
      alignedSquareMuZeroQ8Order62610 (phi w1) (phi e1n) (phi e3) (phi a2) (phi a1) (phi a0) (phi b7) (phi b6) (phi b5) (phi b4) := by
  simp only [alignedSquareMuZeroQ8Order62610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order62610
theorem alignedSquareMuZeroQ8Order62610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order62610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4).eval a =
      alignedSquareMuZeroQ8Order62610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) :=
  map_alignedSquareMuZeroQ8Order62610 (Polynomial.evalRingHom a) w1 e1n e3 a2 a1 a0 b7 b6 b5 b4

#print axioms alignedSquareMuZeroQ8Order62610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder63610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : R) :
    phi (alignedSquareMixedPairOrder63610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4) =
      alignedSquareMixedPairOrder63610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) (phi b5) (phi b4) := by
  simp only [alignedSquareMixedPairOrder63610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder63610
theorem alignedSquareMixedPairOrder63610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder63610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4).eval a =
      alignedSquareMixedPairOrder63610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) :=
  map_alignedSquareMixedPairOrder63610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4

#print axioms alignedSquareMixedPairOrder63610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder63610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 b8 b7 : R) :
    phi (alignedSquareW1ZeroOrder63610 e1 e3 a2 a1 b8 b7) =
      alignedSquareW1ZeroOrder63610 (phi e1) (phi e3) (phi a2) (phi a1) (phi b8) (phi b7) := by
  simp only [alignedSquareW1ZeroOrder63610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder63610
theorem alignedSquareW1ZeroOrder63610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 a1 b8 b7 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder63610 e1 e3 a2 a1 b8 b7).eval a =
      alignedSquareW1ZeroOrder63610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a) :=
  map_alignedSquareW1ZeroOrder63610 (Polynomial.evalRingHom a) e1 e3 a2 a1 b8 b7

#print axioms alignedSquareW1ZeroOrder63610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder63610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 b8 b7 : R) :
    phi (alignedSquareW1PeelOrder63610 w1n e1 e3 a2 a1 b8 b7) =
      alignedSquareW1PeelOrder63610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi b8) (phi b7) := by
  simp only [alignedSquareW1PeelOrder63610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder63610
theorem alignedSquareW1PeelOrder63610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 b8 b7 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder63610 w1n e1 e3 a2 a1 b8 b7).eval a =
      alignedSquareW1PeelOrder63610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a) :=
  map_alignedSquareW1PeelOrder63610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 b8 b7

#print axioms alignedSquareW1PeelOrder63610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder63610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n : R) :
    phi (alignedSquareW1ComplementOrder63610 w1n) =
      alignedSquareW1ComplementOrder63610 (phi w1n) := by
  simp only [alignedSquareW1ComplementOrder63610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder63610
theorem alignedSquareW1ComplementOrder63610_eval
    {k : Type*} [CommRing k]
    (w1n : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder63610 w1n).eval a =
      alignedSquareW1ComplementOrder63610 (w1n.eval a) :=
  map_alignedSquareW1ComplementOrder63610 (Polynomial.evalRingHom a) w1n

#print axioms alignedSquareW1ComplementOrder63610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order63610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a2 a1 a0 b8n : R) :
    phi (alignedSquareMuZeroQ8Order63610 w1 e1n e3 a2 a1 a0 b8n) =
      alignedSquareMuZeroQ8Order63610 (phi w1) (phi e1n) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8n) := by
  simp only [alignedSquareMuZeroQ8Order63610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order63610
theorem alignedSquareMuZeroQ8Order63610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a2 a1 a0 b8n : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order63610 w1 e1n e3 a2 a1 a0 b8n).eval a =
      alignedSquareMuZeroQ8Order63610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a) :=
  map_alignedSquareMuZeroQ8Order63610 (Polynomial.evalRingHom a) w1 e1n e3 a2 a1 a0 b8n

#print axioms alignedSquareMuZeroQ8Order63610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder64610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 : R) :
    phi (alignedSquareMixedPairOrder64610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3) =
      alignedSquareMixedPairOrder64610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) (phi b5) (phi b4) (phi b3) := by
  simp only [alignedSquareMixedPairOrder64610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder64610
theorem alignedSquareMixedPairOrder64610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder64610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3).eval a =
      alignedSquareMixedPairOrder64610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) :=
  map_alignedSquareMixedPairOrder64610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3

#print axioms alignedSquareMixedPairOrder64610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder64610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 a0 b8 b7 b6 : R) :
    phi (alignedSquareW1ZeroOrder64610 e1 e3 a2 a1 a0 b8 b7 b6) =
      alignedSquareW1ZeroOrder64610 (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) := by
  simp only [alignedSquareW1ZeroOrder64610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder64610
theorem alignedSquareW1ZeroOrder64610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 a1 a0 b8 b7 b6 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder64610 e1 e3 a2 a1 a0 b8 b7 b6).eval a =
      alignedSquareW1ZeroOrder64610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) :=
  map_alignedSquareW1ZeroOrder64610 (Polynomial.evalRingHom a) e1 e3 a2 a1 a0 b8 b7 b6

#print axioms alignedSquareW1ZeroOrder64610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder64610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 a0 b8 b7 b6 : R) :
    phi (alignedSquareW1PeelOrder64610 w1n e1 e3 a2 a1 a0 b8 b7 b6) =
      alignedSquareW1PeelOrder64610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) := by
  simp only [alignedSquareW1PeelOrder64610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder64610
theorem alignedSquareW1PeelOrder64610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 a0 b8 b7 b6 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder64610 w1n e1 e3 a2 a1 a0 b8 b7 b6).eval a =
      alignedSquareW1PeelOrder64610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) :=
  map_alignedSquareW1PeelOrder64610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 a0 b8 b7 b6

#print axioms alignedSquareW1PeelOrder64610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder64610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n a2b a1 b8 : R) :
    phi (alignedSquareW1ComplementOrder64610 w1n a2b a1 b8) =
      alignedSquareW1ComplementOrder64610 (phi w1n) (phi a2b) (phi a1) (phi b8) := by
  simp only [alignedSquareW1ComplementOrder64610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder64610
theorem alignedSquareW1ComplementOrder64610_eval
    {k : Type*} [CommRing k]
    (w1n a2b a1 b8 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder64610 w1n a2b a1 b8).eval a =
      alignedSquareW1ComplementOrder64610 (w1n.eval a) (a2b.eval a) (a1.eval a) (b8.eval a) :=
  map_alignedSquareW1ComplementOrder64610 (Polynomial.evalRingHom a) w1n a2b a1 b8

#print axioms alignedSquareW1ComplementOrder64610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order64610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 : R) :
    phi (alignedSquareMuZeroQ8Order64610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3) =
      alignedSquareMuZeroQ8Order64610 (phi w1) (phi e1n) (phi e3) (phi a2) (phi a1) (phi a0) (phi b7) (phi b6) (phi b5) (phi b4) (phi b3) := by
  simp only [alignedSquareMuZeroQ8Order64610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order64610
theorem alignedSquareMuZeroQ8Order64610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order64610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3).eval a =
      alignedSquareMuZeroQ8Order64610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) :=
  map_alignedSquareMuZeroQ8Order64610 (Polynomial.evalRingHom a) w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3

#print axioms alignedSquareMuZeroQ8Order64610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder65610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 : R) :
    phi (alignedSquareMixedPairOrder65610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3) =
      alignedSquareMixedPairOrder65610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) (phi b5) (phi b4) (phi b3) := by
  simp only [alignedSquareMixedPairOrder65610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder65610
theorem alignedSquareMixedPairOrder65610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder65610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3).eval a =
      alignedSquareMixedPairOrder65610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) :=
  map_alignedSquareMixedPairOrder65610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3

#print axioms alignedSquareMixedPairOrder65610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder65610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) :
    phi (alignedSquareW1ZeroOrder65610 e1 e3 a2 a1 a0 b8 b7 b6 b5) =
      alignedSquareW1ZeroOrder65610 (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) (phi b5) := by
  simp only [alignedSquareW1ZeroOrder65610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder65610
theorem alignedSquareW1ZeroOrder65610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 a1 a0 b8 b7 b6 b5 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder65610 e1 e3 a2 a1 a0 b8 b7 b6 b5).eval a =
      alignedSquareW1ZeroOrder65610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) :=
  map_alignedSquareW1ZeroOrder65610 (Polynomial.evalRingHom a) e1 e3 a2 a1 a0 b8 b7 b6 b5

#print axioms alignedSquareW1ZeroOrder65610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder65610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) :
    phi (alignedSquareW1PeelOrder65610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5) =
      alignedSquareW1PeelOrder65610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) (phi b5) := by
  simp only [alignedSquareW1PeelOrder65610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder65610
theorem alignedSquareW1PeelOrder65610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder65610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5).eval a =
      alignedSquareW1PeelOrder65610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) :=
  map_alignedSquareW1PeelOrder65610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 a0 b8 b7 b6 b5

#print axioms alignedSquareW1PeelOrder65610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder65610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a2b a1 b8 b7 : R) :
    phi (alignedSquareW1ComplementOrder65610 w1n e1b e3b a2b a1 b8 b7) =
      alignedSquareW1ComplementOrder65610 (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi b8) (phi b7) := by
  simp only [alignedSquareW1ComplementOrder65610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder65610
theorem alignedSquareW1ComplementOrder65610_eval
    {k : Type*} [CommRing k]
    (w1n e1b e3b a2b a1 b8 b7 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder65610 w1n e1b e3b a2b a1 b8 b7).eval a =
      alignedSquareW1ComplementOrder65610 (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (b8.eval a) (b7.eval a) :=
  map_alignedSquareW1ComplementOrder65610 (Polynomial.evalRingHom a) w1n e1b e3b a2b a1 b8 b7

#print axioms alignedSquareW1ComplementOrder65610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order65610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a2 a1 a0 b8n : R) :
    phi (alignedSquareMuZeroQ8Order65610 w1 e1n e3 a2 a1 a0 b8n) =
      alignedSquareMuZeroQ8Order65610 (phi w1) (phi e1n) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8n) := by
  simp only [alignedSquareMuZeroQ8Order65610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order65610
theorem alignedSquareMuZeroQ8Order65610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a2 a1 a0 b8n : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order65610 w1 e1n e3 a2 a1 a0 b8n).eval a =
      alignedSquareMuZeroQ8Order65610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a) :=
  map_alignedSquareMuZeroQ8Order65610 (Polynomial.evalRingHom a) w1 e1n e3 a2 a1 a0 b8n

#print axioms alignedSquareMuZeroQ8Order65610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder66610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 : R) :
    phi (alignedSquareMixedPairOrder66610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2) =
      alignedSquareMixedPairOrder66610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) (phi b5) (phi b4) (phi b3) (phi b2) := by
  simp only [alignedSquareMixedPairOrder66610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder66610
theorem alignedSquareMixedPairOrder66610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder66610 w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2).eval a =
      alignedSquareMixedPairOrder66610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) :=
  map_alignedSquareMixedPairOrder66610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2

#print axioms alignedSquareMixedPairOrder66610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder66610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 a0 b7 b6 b5 : R) :
    phi (alignedSquareW1ZeroOrder66610 e1 e3 a2 a1 a0 b7 b6 b5) =
      alignedSquareW1ZeroOrder66610 (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b7) (phi b6) (phi b5) := by
  simp only [alignedSquareW1ZeroOrder66610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder66610
theorem alignedSquareW1ZeroOrder66610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 a1 a0 b7 b6 b5 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder66610 e1 e3 a2 a1 a0 b7 b6 b5).eval a =
      alignedSquareW1ZeroOrder66610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) :=
  map_alignedSquareW1ZeroOrder66610 (Polynomial.evalRingHom a) e1 e3 a2 a1 a0 b7 b6 b5

#print axioms alignedSquareW1ZeroOrder66610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder66610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 : R) :
    phi (alignedSquareW1PeelOrder66610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5) =
      alignedSquareW1PeelOrder66610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) (phi b5) := by
  simp only [alignedSquareW1PeelOrder66610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder66610
theorem alignedSquareW1PeelOrder66610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder66610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5).eval a =
      alignedSquareW1PeelOrder66610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) :=
  map_alignedSquareW1PeelOrder66610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 a0 b8 b7 b6 b5

#print axioms alignedSquareW1PeelOrder66610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder66610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a2b a1 a0 b8 b7 : R) :
    phi (alignedSquareW1ComplementOrder66610 w1n e1b e3b a2b a1 a0 b8 b7) =
      alignedSquareW1ComplementOrder66610 (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi a0) (phi b8) (phi b7) := by
  simp only [alignedSquareW1ComplementOrder66610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder66610
theorem alignedSquareW1ComplementOrder66610_eval
    {k : Type*} [CommRing k]
    (w1n e1b e3b a2b a1 a0 b8 b7 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder66610 w1n e1b e3b a2b a1 a0 b8 b7).eval a =
      alignedSquareW1ComplementOrder66610 (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) :=
  map_alignedSquareW1ComplementOrder66610 (Polynomial.evalRingHom a) w1n e1b e3b a2b a1 a0 b8 b7

#print axioms alignedSquareW1ComplementOrder66610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order66610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 : R) :
    phi (alignedSquareMuZeroQ8Order66610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2) =
      alignedSquareMuZeroQ8Order66610 (phi w1) (phi e1n) (phi e3) (phi a2) (phi a1) (phi a0) (phi b7) (phi b6) (phi b5) (phi b4) (phi b3) (phi b2) := by
  simp only [alignedSquareMuZeroQ8Order66610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order66610
theorem alignedSquareMuZeroQ8Order66610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order66610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2).eval a =
      alignedSquareMuZeroQ8Order66610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) :=
  map_alignedSquareMuZeroQ8Order66610 (Polynomial.evalRingHom a) w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2

#print axioms alignedSquareMuZeroQ8Order66610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder67610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 : R) :
    phi (alignedSquareMixedPairOrder67610 w1 e1 e3 a2 a1 a0 b6 b5 b4 b3 b2) =
      alignedSquareMixedPairOrder67610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b6) (phi b5) (phi b4) (phi b3) (phi b2) := by
  simp only [alignedSquareMixedPairOrder67610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder67610
theorem alignedSquareMixedPairOrder67610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder67610 w1 e1 e3 a2 a1 a0 b6 b5 b4 b3 b2).eval a =
      alignedSquareMixedPairOrder67610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) :=
  map_alignedSquareMixedPairOrder67610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b6 b5 b4 b3 b2

#print axioms alignedSquareMixedPairOrder67610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder67610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 a0 b6 b5 b4 : R) :
    phi (alignedSquareW1ZeroOrder67610 e1 e3 a2 a1 a0 b6 b5 b4) =
      alignedSquareW1ZeroOrder67610 (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b6) (phi b5) (phi b4) := by
  simp only [alignedSquareW1ZeroOrder67610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder67610
theorem alignedSquareW1ZeroOrder67610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 a1 a0 b6 b5 b4 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder67610 e1 e3 a2 a1 a0 b6 b5 b4).eval a =
      alignedSquareW1ZeroOrder67610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a) :=
  map_alignedSquareW1ZeroOrder67610 (Polynomial.evalRingHom a) e1 e3 a2 a1 a0 b6 b5 b4

#print axioms alignedSquareW1ZeroOrder67610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder67610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : R) :
    phi (alignedSquareW1PeelOrder67610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4) =
      alignedSquareW1PeelOrder67610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) (phi b5) (phi b4) := by
  simp only [alignedSquareW1PeelOrder67610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder67610
theorem alignedSquareW1PeelOrder67610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder67610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4).eval a =
      alignedSquareW1PeelOrder67610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) :=
  map_alignedSquareW1PeelOrder67610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4

#print axioms alignedSquareW1PeelOrder67610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder67610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a2b a1 a0 b8 b7 b6 : R) :
    phi (alignedSquareW1ComplementOrder67610 w1n e1b e3b a2b a1 a0 b8 b7 b6) =
      alignedSquareW1ComplementOrder67610 (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) := by
  simp only [alignedSquareW1ComplementOrder67610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder67610
theorem alignedSquareW1ComplementOrder67610_eval
    {k : Type*} [CommRing k]
    (w1n e1b e3b a2b a1 a0 b8 b7 b6 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder67610 w1n e1b e3b a2b a1 a0 b8 b7 b6).eval a =
      alignedSquareW1ComplementOrder67610 (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) :=
  map_alignedSquareW1ComplementOrder67610 (Polynomial.evalRingHom a) w1n e1b e3b a2b a1 a0 b8 b7 b6

#print axioms alignedSquareW1ComplementOrder67610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order67610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a1 a0 b8n : R) :
    phi (alignedSquareMuZeroQ8Order67610 w1 e1n e3 a1 a0 b8n) =
      alignedSquareMuZeroQ8Order67610 (phi w1) (phi e1n) (phi e3) (phi a1) (phi a0) (phi b8n) := by
  simp only [alignedSquareMuZeroQ8Order67610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order67610
theorem alignedSquareMuZeroQ8Order67610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a1 a0 b8n : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order67610 w1 e1n e3 a1 a0 b8n).eval a =
      alignedSquareMuZeroQ8Order67610 (w1.eval a) (e1n.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b8n.eval a) :=
  map_alignedSquareMuZeroQ8Order67610 (Polynomial.evalRingHom a) w1 e1n e3 a1 a0 b8n

#print axioms alignedSquareMuZeroQ8Order67610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMixedPairOrder68610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 : R) :
    phi (alignedSquareMixedPairOrder68610 w1 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1) =
      alignedSquareMixedPairOrder68610 (phi w1) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b7) (phi b6) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareMixedPairOrder68610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMixedPairOrder68610
theorem alignedSquareMixedPairOrder68610_eval
    {k : Type*} [CommRing k]
    (w1 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareMixedPairOrder68610 w1 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1).eval a =
      alignedSquareMixedPairOrder68610 (w1.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareMixedPairOrder68610 (Polynomial.evalRingHom a) w1 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1

#print axioms alignedSquareMixedPairOrder68610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder68610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 : R) :
    phi (alignedSquareW1ZeroOrder68610 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3) =
      alignedSquareW1ZeroOrder68610 (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b7) (phi b6) (phi b5) (phi b4) (phi b3) := by
  simp only [alignedSquareW1ZeroOrder68610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder68610
theorem alignedSquareW1ZeroOrder68610_eval
    {k : Type*} [CommRing k]
    (e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder68610 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3).eval a =
      alignedSquareW1ZeroOrder68610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) :=
  map_alignedSquareW1ZeroOrder68610 (Polynomial.evalRingHom a) e1 e3 a2 a1 a0 b7 b6 b5 b4 b3

#print axioms alignedSquareW1ZeroOrder68610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder68610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 : R) :
    phi (alignedSquareW1PeelOrder68610 w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3) =
      alignedSquareW1PeelOrder68610 (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b7) (phi b6) (phi b5) (phi b4) (phi b3) := by
  simp only [alignedSquareW1PeelOrder68610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder68610
theorem alignedSquareW1PeelOrder68610_eval
    {k : Type*} [CommRing k]
    (w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder68610 w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3).eval a =
      alignedSquareW1PeelOrder68610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) :=
  map_alignedSquareW1PeelOrder68610 (Polynomial.evalRingHom a) w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3

#print axioms alignedSquareW1PeelOrder68610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder68610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1n e1b e3b a2b a1 a0 b7 b6 b5 : R) :
    phi (alignedSquareW1ComplementOrder68610 w1n e1b e3b a2b a1 a0 b7 b6 b5) =
      alignedSquareW1ComplementOrder68610 (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi a0) (phi b7) (phi b6) (phi b5) := by
  simp only [alignedSquareW1ComplementOrder68610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder68610
theorem alignedSquareW1ComplementOrder68610_eval
    {k : Type*} [CommRing k]
    (w1n e1b e3b a2b a1 a0 b7 b6 b5 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder68610 w1n e1b e3b a2b a1 a0 b7 b6 b5).eval a =
      alignedSquareW1ComplementOrder68610 (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) :=
  map_alignedSquareW1ComplementOrder68610 (Polynomial.evalRingHom a) w1n e1b e3b a2b a1 a0 b7 b6 b5

#print axioms alignedSquareW1ComplementOrder68610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order68610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 : R) :
    phi (alignedSquareMuZeroQ8Order68610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1) =
      alignedSquareMuZeroQ8Order68610 (phi w1) (phi e1n) (phi e3) (phi a2) (phi a1) (phi a0) (phi b7) (phi b6) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareMuZeroQ8Order68610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order68610
theorem alignedSquareMuZeroQ8Order68610_eval
    {k : Type*} [CommRing k]
    (w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order68610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1).eval a =
      alignedSquareMuZeroQ8Order68610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareMuZeroQ8Order68610 (Polynomial.evalRingHom a) w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1

#print axioms alignedSquareMuZeroQ8Order68610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ZeroOrder68Plus610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (h e1 e3 a2 a1 a0 b4 b3 b2 b1 : R) :
    phi (alignedSquareW1ZeroOrder68Plus610 h e1 e3 a2 a1 a0 b4 b3 b2 b1) =
      alignedSquareW1ZeroOrder68Plus610 (phi h) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b4) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareW1ZeroOrder68Plus610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ZeroOrder68Plus610
theorem alignedSquareW1ZeroOrder68Plus610_eval
    {k : Type*} [CommRing k]
    (h e1 e3 a2 a1 a0 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareW1ZeroOrder68Plus610 h e1 e3 a2 a1 a0 b4 b3 b2 b1).eval a =
      alignedSquareW1ZeroOrder68Plus610 (h.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareW1ZeroOrder68Plus610 (Polynomial.evalRingHom a) h e1 e3 a2 a1 a0 b4 b3 b2 b1

#print axioms alignedSquareW1ZeroOrder68Plus610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1PeelOrder68Plus610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (h w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1 : R) :
    phi (alignedSquareW1PeelOrder68Plus610 h w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1) =
      alignedSquareW1PeelOrder68Plus610 (phi h) (phi w1n) (phi e1) (phi e3) (phi a2) (phi a1) (phi a0) (phi b6) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareW1PeelOrder68Plus610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1PeelOrder68Plus610
theorem alignedSquareW1PeelOrder68Plus610_eval
    {k : Type*} [CommRing k]
    (h w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareW1PeelOrder68Plus610 h w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1).eval a =
      alignedSquareW1PeelOrder68Plus610 (h.eval a) (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareW1PeelOrder68Plus610 (Polynomial.evalRingHom a) h w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1

#print axioms alignedSquareW1PeelOrder68Plus610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareW1ComplementOrder68Plus610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1 : R) :
    phi (alignedSquareW1ComplementOrder68Plus610 h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1) =
      alignedSquareW1ComplementOrder68Plus610 (phi h) (phi w1n) (phi e1b) (phi e3b) (phi a2b) (phi a1) (phi a0) (phi b6) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareW1ComplementOrder68Plus610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareW1ComplementOrder68Plus610
theorem alignedSquareW1ComplementOrder68Plus610_eval
    {k : Type*} [CommRing k]
    (h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareW1ComplementOrder68Plus610 h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1).eval a =
      alignedSquareW1ComplementOrder68Plus610 (h.eval a) (w1n.eval a) (e1b.eval a) (e3b.eval a) (a2b.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareW1ComplementOrder68Plus610 (Polynomial.evalRingHom a) h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1

#print axioms alignedSquareW1ComplementOrder68Plus610_eval
set_option maxHeartbeats 800000000 in
theorem map_alignedSquareMuZeroQ8Order68Plus610 {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1 : R) :
    phi (alignedSquareMuZeroQ8Order68Plus610 h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1) =
      alignedSquareMuZeroQ8Order68Plus610 (phi h) (phi w1) (phi e1n) (phi e3) (phi a2) (phi a1) (phi a0) (phi b5) (phi b4) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedSquareMuZeroQ8Order68Plus610, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_zero]

#print axioms map_alignedSquareMuZeroQ8Order68Plus610
theorem alignedSquareMuZeroQ8Order68Plus610_eval
    {k : Type*} [CommRing k]
    (h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1 : k[X]) (a : k) :
    (alignedSquareMuZeroQ8Order68Plus610 h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1).eval a =
      alignedSquareMuZeroQ8Order68Plus610 (h.eval a) (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) :=
  map_alignedSquareMuZeroQ8Order68Plus610 (Polynomial.evalRingHom a) h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1

#print axioms alignedSquareMuZeroQ8Order68Plus610_eval
/-! ## Identically vanishing complement orders `61`–`63` -/
theorem alignedSquareW1ComplementOrder61610_eq_zero {R : Type*} [CommRing R]
    (w1n : R) :
    alignedSquareW1ComplementOrder61610 w1n = 0 :=
  rfl

#print axioms alignedSquareW1ComplementOrder61610_eq_zero
theorem alignedSquareW1ComplementOrder62610_eq_zero {R : Type*} [CommRing R]
    (w1n : R) :
    alignedSquareW1ComplementOrder62610 w1n = 0 :=
  rfl

#print axioms alignedSquareW1ComplementOrder62610_eq_zero
theorem alignedSquareW1ComplementOrder63610_eq_zero {R : Type*} [CommRing R]
    (w1n : R) :
    alignedSquareW1ComplementOrder63610 w1n = 0 :=
  rfl

#print axioms alignedSquareW1ComplementOrder63610_eq_zero
/-! ## Scale identities -/

section AlignedSquareTowerScale610

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 1600000000 in
/-- On `w₁ = 0` the MixedPair jet is `h⁷` times the order-`61`
tower (remaining pole `14`). -/
theorem alignedSquareJetQuotient610_w1Zero_scale
    (h e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 h 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
        b4 b3 b2 b1 =
      h ^ 7 * (
          alignedSquareW1ZeroOrder61610 e1 e3 a2 b8
        + h * alignedSquareW1ZeroOrder62610 e1 e3 a2 a1 b8 b7
        + h ^ 2 * alignedSquareW1ZeroOrder63610 e1 e3 a2 a1 b8 b7
        + h ^ 3 * alignedSquareW1ZeroOrder64610 e1 e3 a2 a1 a0 b8 b7 b6
        + h ^ 4 * alignedSquareW1ZeroOrder65610 e1 e3 a2 a1 a0 b8 b7 b6 b5
        + h ^ 5 * alignedSquareW1ZeroOrder66610 e1 e3 a2 a1 a0 b7 b6 b5
        + h ^ 6 * alignedSquareW1ZeroOrder67610 e1 e3 a2 a1 a0 b6 b5 b4
        + h ^ 7 * alignedSquareW1ZeroOrder68610 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
        + h ^ 8 * alignedSquareW1ZeroOrder68Plus610 h e1 e3 a2 a1 a0 b4 b3 b2 b1) := by
  simp only [alignedSquareJetQuotient610, alignedSquareW1ZeroOrder61610, alignedSquareW1ZeroOrder62610, alignedSquareW1ZeroOrder63610, alignedSquareW1ZeroOrder64610, alignedSquareW1ZeroOrder65610, alignedSquareW1ZeroOrder66610, alignedSquareW1ZeroOrder67610, alignedSquareW1ZeroOrder68610, alignedSquareW1ZeroOrder68Plus610]
  ring

#print axioms alignedSquareJetQuotient610_w1Zero_scale
set_option maxHeartbeats 1600000000 in
/-- After `w₁ = h w₁n` the MixedPair jet is `h⁷` times the
order-`61` mixed tower. -/
theorem alignedSquareJetQuotient610_w1Peel_scale
    (h w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 h (h * w1n) e1 e3 a2 a1 a0 b8 b7
        b6 b5 b4 b3 b2 b1 =
      h ^ 7 * (
          alignedSquareW1PeelOrder61610 w1n e1 e3 a2 b8
        + h * alignedSquareW1PeelOrder62610 w1n e1 e3 a2 a1 b8 b7
        + h ^ 2 * alignedSquareW1PeelOrder63610 w1n e1 e3 a2 a1 b8 b7
        + h ^ 3 * alignedSquareW1PeelOrder64610 w1n e1 e3 a2 a1 a0 b8 b7 b6
        + h ^ 4 * alignedSquareW1PeelOrder65610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5
        + h ^ 5 * alignedSquareW1PeelOrder66610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5
        + h ^ 6 * alignedSquareW1PeelOrder67610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4
        + h ^ 7 * alignedSquareW1PeelOrder68610 w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
        + h ^ 8 * alignedSquareW1PeelOrder68Plus610 h w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1) := by
  simp only [alignedSquareJetQuotient610, alignedSquareW1PeelOrder61610, alignedSquareW1PeelOrder62610, alignedSquareW1PeelOrder63610, alignedSquareW1PeelOrder64610, alignedSquareW1PeelOrder65610, alignedSquareW1PeelOrder66610, alignedSquareW1PeelOrder67610, alignedSquareW1PeelOrder68610, alignedSquareW1PeelOrder68Plus610]
  ring

#print axioms alignedSquareJetQuotient610_w1Peel_scale
set_option maxHeartbeats 1600000000 in
/-- On the `w₁ = 0` complement peel the MixedPair jet is `h¹⁰`
times the order-`64` tower.  Orders `61`–`63` vanish identically. -/
theorem alignedSquareJetQuotient610_w1Complement_scale
    (h w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 h (h * w1n) (h * e1b) (h * e3b)
        (h * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
      h ^ 10 * (
          alignedSquareW1ComplementOrder64610 w1n a2b a1 b8
        + h * alignedSquareW1ComplementOrder65610 w1n e1b e3b a2b a1 b8 b7
        + h ^ 2 * alignedSquareW1ComplementOrder66610 w1n e1b e3b a2b a1 a0 b8 b7
        + h ^ 3 * alignedSquareW1ComplementOrder67610 w1n e1b e3b a2b a1 a0 b8 b7 b6
        + h ^ 4 * alignedSquareW1ComplementOrder68610 w1n e1b e3b a2b a1 a0 b7 b6 b5
        + h ^ 5 * alignedSquareW1ComplementOrder68Plus610 h w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1) := by
  simp only [alignedSquareJetQuotient610, alignedSquareW1ComplementOrder64610, alignedSquareW1ComplementOrder65610, alignedSquareW1ComplementOrder66610, alignedSquareW1ComplementOrder67610, alignedSquareW1ComplementOrder68610, alignedSquareW1ComplementOrder68Plus610]
  ring

#print axioms alignedSquareJetQuotient610_w1Complement_scale
set_option maxHeartbeats 1600000000 in
/-- Mixed orders `55` through `60` of the `μ = 0` `q₈`-peeled jet (the `h¹` through `h⁶` terms).  Not extracted as named frozen heads in this batch; recorded so the order-`61` identity is exact. -/
def alignedSquareMuZeroQ8Prefix5560610 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 b8n b7 b6 b5 : R) : R :=
    - (26372304 : R) * h ^ 6 * w1 ^ 15
    - (3242498688 : R) * h ^ 6 * w1 ^ 10 * b5
    - (1102449553920 : R) * h ^ 6 * w1 ^ 9 * e1n * b6
    - (51319026734976 : R) * h ^ 6 * w1 ^ 8 * e1n ^ 2 * b7
    + (389099842560 : R) * h ^ 6 * w1 ^ 8 * e3 * b6
    + (26066807230464 : R) * h ^ 6 * w1 ^ 7 * e1n * e3 * b7
    - (33618226397184 : R) * h ^ 6 * w1 ^ 7 * a2 * b6
    - (39221264130048 : R) * h ^ 6 * w1 ^ 7 * a1 * b7
    - (1555776810491904 : R) * h ^ 6 * w1 ^ 6 * e1n * a2 * b7
    - (3201186852864 : R) * h ^ 6 * w1 ^ 6 * e3 ^ 2 * b7
    + (366065131880448 : R) * h ^ 6 * w1 ^ 5 * e3 * a2 * b7
    - (9883758560772096 : R) * h ^ 6 * w1 ^ 4 * a2 ^ 2 * b7
    + (24980690262528 : R) * h ^ 5 * w1 ^ 9 * e1n ^ 2 * b8n
    - (13033403615232 : R) * h ^ 5 * w1 ^ 8 * e1n * e3 * b8n
    + (14007594332160 : R) * h ^ 5 * w1 ^ 8 * a1 * b8n
    + (804347194540032 : R) * h ^ 5 * w1 ^ 7 * e1n * a2 * b8n
    + (1655035379712 : R) * h ^ 5 * w1 ^ 7 * e3 ^ 2 * b8n
    - (197558960062464 : R) * h ^ 5 * w1 ^ 6 * e3 * a2 * b8n
    + (5647862034726912 : R) * h ^ 5 * w1 ^ 5 * a2 ^ 2 * b8n
    + (884317824 : R) * h ^ 4 * w1 ^ 11 * b6
    + (407293862976 : R) * h ^ 4 * w1 ^ 10 * e1n * b7
    - (142910127360 : R) * h ^ 4 * w1 ^ 9 * e3 * b7
    + (12256645040640 : R) * h ^ 4 * w1 ^ 8 * a2 * b7
    - (148106859264 : R) * h ^ 3 * w1 ^ 11 * e1n * b8n
    + (51719855616 : R) * h ^ 3 * w1 ^ 10 * e3 * b8n
    - (4409798215680 : R) * h ^ 3 * w1 ^ 9 * a2 * b8n
    - (243596808 : R) * h ^ 2 * w1 ^ 12 * b7
    + (67814496 : R) * h * w1 ^ 13 * b8n
set_option maxHeartbeats 1600000000 in
/-- On `μ = 0` after the `q₈` peel, the substituted jet splits as
the order-`55`–`60` prefix plus `h⁷` times the order-`61` tower. -/
theorem alignedSquareJetQuotient610_muZeroQ8_scale
    (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 h w1 (h * e1n) e3 a2 a1 a0
        (h * b8n) b7 b6 b5 b4 b3 b2 b1 =
      alignedSquareMuZeroQ8Prefix5560610 h w1 e1n e3 a2 a1 b8n b7 b6 b5 +
        h ^ 7 * (
          alignedSquareMuZeroQ8Order61610 w1 e1n e3 a2 a1 a0 b8n
        + h * alignedSquareMuZeroQ8Order62610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4
        + h ^ 2 * alignedSquareMuZeroQ8Order63610 w1 e1n e3 a2 a1 a0 b8n
        + h ^ 3 * alignedSquareMuZeroQ8Order64610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3
        + h ^ 4 * alignedSquareMuZeroQ8Order65610 w1 e1n e3 a2 a1 a0 b8n
        + h ^ 5 * alignedSquareMuZeroQ8Order66610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2
        + h ^ 6 * alignedSquareMuZeroQ8Order67610 w1 e1n e3 a1 a0 b8n
        + h ^ 7 * alignedSquareMuZeroQ8Order68610 w1 e1n e3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1
        + h ^ 8 * alignedSquareMuZeroQ8Order68Plus610 h w1 e1n e3 a2 a1 a0 b5 b4 b3 b2 b1) := by
  simp only [alignedSquareJetQuotient610, alignedSquareMuZeroQ8Order61610, alignedSquareMuZeroQ8Order62610, alignedSquareMuZeroQ8Order63610, alignedSquareMuZeroQ8Order64610, alignedSquareMuZeroQ8Order65610, alignedSquareMuZeroQ8Order66610, alignedSquareMuZeroQ8Order67610, alignedSquareMuZeroQ8Order68610, alignedSquareMuZeroQ8Order68Plus610, alignedSquareMuZeroQ8Prefix5560610]
  ring

#print axioms alignedSquareJetQuotient610_muZeroQ8_scale
end AlignedSquareTowerScale610
/-! ## Pole obstruction and `h₀`-divisibility

Each limb theorem assumes the MixedPair jet is the remaining pole-`21`
numerator of a rational function with simple-pole derivative, matching
`alignedSquare_poleTwentyOne_head_eval_zero610`.  The source-primitive
clearing identity is not re-proved here.  Successive vanishings are
recorded as `h₀`-divisibility of the remaining numerator, which is the
shape `Grok610PoleCeilingLemmaScratch` consumes.  Neither limb is False.
The square chamber is not claimed empty.
-/

section AlignedSquareTowerHeads610

variable {k : Type*} [Field k] [CharZero k]

/-- Polynomial `h₀⁷`-divisibility of the MixedPair jet after `w₁ = h₀ w₁n`.
This is the `w₁ = 0` base-order `61` upgrade; no pole obstruction is used. -/
theorem alignedSquareJetQuotient610_w1Peel_pow_dvd
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X]) :
    h0 ^ 7 ∣
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
        b5 b4 b3 b2 b1 :=
  ⟨_, alignedSquareJetQuotient610_w1Peel_scale h0 w1n e1 e3 a2 a1 a0 b8
      b7 b6 b5 b4 b3 b2 b1⟩

#print axioms alignedSquareJetQuotient610_w1Peel_pow_dvd

/-- Frozen `w₁ = 0` likewise yields `h₀⁷ ∣` the MixedPair jet. -/
theorem alignedSquareJetQuotient610_w1Zero_pow_dvd
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X]) :
    h0 ^ 7 ∣
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 b1 :=
  ⟨_, alignedSquareJetQuotient610_w1Zero_scale h0 e1 e3 a2 a1 a0 b8 b7
      b6 b5 b4 b3 b2 b1⟩

#print axioms alignedSquareJetQuotient610_w1Zero_pow_dvd

/-- Complement peels yield `h₀¹⁰ ∣` the MixedPair jet.  Orders `61`–`63`
vanish identically in that quotient. -/
theorem alignedSquareJetQuotient610_w1Complement_pow_dvd
    (h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X]) :
    h0 ^ 10 ∣
      alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b)
        (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 :=
  ⟨_, alignedSquareJetQuotient610_w1Complement_scale h0 w1n e1b e3b a2b
      a1 a0 b8 b7 b6 b5 b4 b3 b2 b1⟩

#print axioms alignedSquareJetQuotient610_w1Complement_pow_dvd
set_option maxHeartbeats 1600000000 in
/-- On `w₁ = h₀ w₁n`, cancel the polynomial `h₀⁷` from the pole-`21`
clearing and apply the remaining pole-`14` obstruction.  The order-`61`
mixed head vanishes at the linear root. -/
theorem alignedSquareW1PeelOrder61610_zero_of_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder61610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a) = 0 := by
  let Q61 : k[X] :=
    alignedSquareW1PeelOrder61610 w1n e1 e3 a2 b8
      + h0 * alignedSquareW1PeelOrder62610 w1n e1 e3 a2 a1 b8 b7
      + h0 ^ 2 * alignedSquareW1PeelOrder63610 w1n e1 e3 a2 a1 b8 b7
      + h0 ^ 3 * alignedSquareW1PeelOrder64610 w1n e1 e3 a2 a1 a0 b8 b7 b6
      + h0 ^ 4 * alignedSquareW1PeelOrder65610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1PeelOrder66610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 6 * alignedSquareW1PeelOrder67610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4
      + h0 ^ 7 * alignedSquareW1PeelOrder68610 w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
      + h0 ^ 8 * alignedSquareW1PeelOrder68Plus610 h0 w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1
  have hscale := alignedSquareJetQuotient610_w1Peel_scale h0 w1n e1 e3 a2
    a1 a0 b8 b7 b6 b5 b4 b3 b2 b1
  have hjet : alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0
      b8 b7 b6 b5 b4 b3 b2 b1 = h0 ^ 7 * Q61 := by
    simpa [Q61] using hscale
  have hclear14 :
      algebraMap k[X] (RatFunc k) Q61 =
        (algebraMap k[X] (RatFunc k) h0) ^
            alignedSquareW1ZeroRemainingPole610 * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q61 rho 7 14 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  have hQ0 : Q61.eval a = 0 :=
    alignedSquare_poleFourteen_head_eval_zero610 a j h0 Q61 rho hdegree
      hroot hclear14 hderiv
  let Head : k[X] := alignedSquareW1PeelOrder61610 w1n e1 e3 a2 b8
  let Rest : k[X] :=
    alignedSquareW1PeelOrder62610 w1n e1 e3 a2 a1 b8 b7
      + h0 * alignedSquareW1PeelOrder63610 w1n e1 e3 a2 a1 b8 b7
      + h0 ^ 2 * alignedSquareW1PeelOrder64610 w1n e1 e3 a2 a1 a0 b8 b7 b6
      + h0 ^ 3 * alignedSquareW1PeelOrder65610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 4 * alignedSquareW1PeelOrder66610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1PeelOrder67610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4
      + h0 ^ 6 * alignedSquareW1PeelOrder68610 w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
      + h0 ^ 7 * alignedSquareW1PeelOrder68Plus610 h0 w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1
  have hshape : Q61 = Head + h0 * Rest := by
    simp only [Q61, Head, Rest]
    ring
  have hO : Q61.eval a =
      alignedSquareW1PeelOrder61610 (w1n.eval a) (e1.eval a) (e3.eval a)
        (a2.eval a) (b8.eval a) := by
    rw [hshape,
      alignedSquare_eval_head_of_linear_factor610 h0 Head Rest a hroot]
    simp only [Head, alignedSquareW1PeelOrder61610_eval]
  exact hO.symm.trans hQ0

#print axioms alignedSquareW1PeelOrder61610_zero_of_pole
set_option maxHeartbeats 1600000000 in
/-- Frozen `w₁ = 0`: the same pole-`14` obstruction forces the frozen
order-`61` head to vanish at `a`. -/
theorem alignedSquareW1ZeroOrder61610_zero_of_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder61610 (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a) = 0 := by
  let Q61 : k[X] :=
    alignedSquareW1ZeroOrder61610 e1 e3 a2 b8
      + h0 * alignedSquareW1ZeroOrder62610 e1 e3 a2 a1 b8 b7
      + h0 ^ 2 * alignedSquareW1ZeroOrder63610 e1 e3 a2 a1 b8 b7
      + h0 ^ 3 * alignedSquareW1ZeroOrder64610 e1 e3 a2 a1 a0 b8 b7 b6
      + h0 ^ 4 * alignedSquareW1ZeroOrder65610 e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1ZeroOrder66610 e1 e3 a2 a1 a0 b7 b6 b5
      + h0 ^ 6 * alignedSquareW1ZeroOrder67610 e1 e3 a2 a1 a0 b6 b5 b4
      + h0 ^ 7 * alignedSquareW1ZeroOrder68610 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
      + h0 ^ 8 * alignedSquareW1ZeroOrder68Plus610 h0 e1 e3 a2 a1 a0 b4 b3 b2 b1
  have hscale := alignedSquareJetQuotient610_w1Zero_scale h0 e1 e3 a2 a1
    a0 b8 b7 b6 b5 b4 b3 b2 b1
  have hjet : alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1 = h0 ^ 7 * Q61 := by
    simpa [Q61] using hscale
  have hclear14 :
      algebraMap k[X] (RatFunc k) Q61 =
        (algebraMap k[X] (RatFunc k) h0) ^
            alignedSquareW1ZeroRemainingPole610 * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q61 rho 7 14 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  have hQ0 : Q61.eval a = 0 :=
    alignedSquare_poleFourteen_head_eval_zero610 a j h0 Q61 rho hdegree
      hroot hclear14 hderiv
  let Head : k[X] := alignedSquareW1ZeroOrder61610 e1 e3 a2 b8
  let Rest : k[X] :=
    alignedSquareW1ZeroOrder62610 e1 e3 a2 a1 b8 b7
      + h0 * alignedSquareW1ZeroOrder63610 e1 e3 a2 a1 b8 b7
      + h0 ^ 2 * alignedSquareW1ZeroOrder64610 e1 e3 a2 a1 a0 b8 b7 b6
      + h0 ^ 3 * alignedSquareW1ZeroOrder65610 e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 4 * alignedSquareW1ZeroOrder66610 e1 e3 a2 a1 a0 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1ZeroOrder67610 e1 e3 a2 a1 a0 b6 b5 b4
      + h0 ^ 6 * alignedSquareW1ZeroOrder68610 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
      + h0 ^ 7 * alignedSquareW1ZeroOrder68Plus610 h0 e1 e3 a2 a1 a0 b4 b3 b2 b1
  have hshape : Q61 = Head + h0 * Rest := by
    simp only [Q61, Head, Rest]
    ring
  have hO : Q61.eval a =
      alignedSquareW1ZeroOrder61610 (e1.eval a) (e3.eval a) (a2.eval a)
        (b8.eval a) := by
    rw [hshape,
      alignedSquare_eval_head_of_linear_factor610 h0 Head Rest a hroot]
    simp only [Head, alignedSquareW1ZeroOrder61610_eval]
  exact hO.symm.trans hQ0

#print axioms alignedSquareW1ZeroOrder61610_zero_of_pole
set_option maxHeartbeats 1600000000 in
/-- On the `w₁ = 0` complement, cancel the polynomial `h₀¹⁰` from the
pole-`21` clearing.  The remaining pole-`11` obstruction forces the
first surviving coefficient, order `64`, to vanish at `a`.  Orders
`61`–`63` are identically zero. -/
theorem alignedSquareW1ComplementOrder64610_zero_of_pole
    (h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b)
            (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ComplementOrder64610 (w1n.eval a) (a2b.eval a) (a1.eval a) (b8.eval a) = 0 := by
  let Q64 : k[X] :=
    alignedSquareW1ComplementOrder64610 w1n a2b a1 b8
      + h0 * alignedSquareW1ComplementOrder65610 w1n e1b e3b a2b a1 b8 b7
      + h0 ^ 2 * alignedSquareW1ComplementOrder66610 w1n e1b e3b a2b a1 a0 b8 b7
      + h0 ^ 3 * alignedSquareW1ComplementOrder67610 w1n e1b e3b a2b a1 a0 b8 b7 b6
      + h0 ^ 4 * alignedSquareW1ComplementOrder68610 w1n e1b e3b a2b a1 a0 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1ComplementOrder68Plus610 h0 w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1
  have hscale := alignedSquareJetQuotient610_w1Complement_scale h0 w1n
    e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1
  have hjet : alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b)
      (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
      h0 ^ 10 * Q64 := by
    simpa [Q64] using hscale
  have hclear11 :
      algebraMap k[X] (RatFunc k) Q64 =
        (algebraMap k[X] (RatFunc k) h0) ^ 11 * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q64 rho 10 11 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 10 + 11 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  have hQ0 : Q64.eval a = 0 :=
    alignedSquare_localLinearPole_head_eval_zero610 11 (by decide) a j
      h0 Q64 rho hdegree hroot hclear11 hderiv
  let Head : k[X] := alignedSquareW1ComplementOrder64610 w1n a2b a1 b8
  let Rest : k[X] :=
    alignedSquareW1ComplementOrder65610 w1n e1b e3b a2b a1 b8 b7
      + h0 * alignedSquareW1ComplementOrder66610 w1n e1b e3b a2b a1 a0 b8 b7
      + h0 ^ 2 * alignedSquareW1ComplementOrder67610 w1n e1b e3b a2b a1 a0 b8 b7 b6
      + h0 ^ 3 * alignedSquareW1ComplementOrder68610 w1n e1b e3b a2b a1 a0 b7 b6 b5
      + h0 ^ 4 * alignedSquareW1ComplementOrder68Plus610 h0 w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1
  have hshape : Q64 = Head + h0 * Rest := by
    simp only [Q64, Head, Rest]
    ring
  have hO : Q64.eval a =
      alignedSquareW1ComplementOrder64610 (w1n.eval a) (a2b.eval a)
        (a1.eval a) (b8.eval a) := by
    rw [hshape,
      alignedSquare_eval_head_of_linear_factor610 h0 Head Rest a hroot]
    simp only [Head, alignedSquareW1ComplementOrder64610_eval]
  exact hO.symm.trans hQ0

#print axioms alignedSquareW1ComplementOrder64610_zero_of_pole
set_option maxHeartbeats 1600000000 in
/-- The `μ = 0` `q₈`-peeled jet after cancelling the leading `h`. -/
def alignedSquareMuZeroQ8QuotOne610 {R : Type*} [CommRing R] (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) : R :=
    - (7113144729600 : R) * h ^ 19 * w1 * e1n ^ 7
    - (1070551227432960 : R) * h ^ 19 * w1 * e1n ^ 4 * a0
    - (12638572385402880 : R) * h ^ 19 * w1 * e1n * a0 ^ 2
    + (1185524121600 : R) * h ^ 19 * e1n ^ 6 * e3
    - (111515752857600 : R) * h ^ 19 * e1n ^ 5 * a1
    + (178425204572160 : R) * h ^ 19 * e1n ^ 3 * e3 * a0
    + (70214291030016 : R) * h ^ 19 * e1n ^ 3 * b1
    - (13691786750853120 : R) * h ^ 19 * e1n ^ 2 * a1 * a0
    + (2106428730900480 : R) * h ^ 19 * e3 * a0 ^ 2
    + (58498535041007616 : R) * h ^ 19 * a0 * b1
    + (39122296012800 : R) * h ^ 17 * w1 ^ 3 * e1n ^ 6
    - (1873464648007680 : R) * h ^ 17 * w1 ^ 3 * e1n ^ 3 * a0
    - (37915717156208640 : R) * h ^ 17 * w1 ^ 3 * a0 ^ 2
    - (26674292736000 : R) * h ^ 17 * w1 ^ 2 * e1n ^ 5 * e3
    + (1254552219648000 : R) * h ^ 17 * w1 ^ 2 * e1n ^ 4 * a1
    - (401456710287360 : R) * h ^ 17 * w1 ^ 2 * e1n ^ 2 * e3 * a0
    - (473946464452608 : R) * h ^ 17 * w1 ^ 2 * e1n ^ 2 * b1
    - (20537680126279680 : R) * h ^ 17 * w1 ^ 2 * e1n * a1 * a0
    + (408891093811200 : R) * h ^ 17 * w1 * e1n ^ 5 * a2
    + (4206698496000 : R) * h ^ 17 * w1 * e1n ^ 4 * e3 ^ 2
    - (475800545525760 : R) * h ^ 17 * w1 * e1n ^ 3 * e3 * a1
    - (304261927796736 : R) * h ^ 17 * w1 * e1n ^ 3 * b2
    + (22819644584755200 : R) * h ^ 17 * w1 * e1n ^ 2 * a2 * a0
    + (11409822292377600 : R) * h ^ 17 * w1 * e1n ^ 2 * a1 ^ 2
    + (93908002406400 : R) * h ^ 17 * w1 * e1n * e3 ^ 2 * a0
    + (140428582060032 : R) * h ^ 17 * w1 * e1n * e3 * b1
    - (2808571641200640 : R) * h ^ 17 * w1 * e3 * a1 * a0
    - (9749755840167936 : R) * h ^ 17 * w1 * a1 * b1
    - (19499511680335872 : R) * h ^ 17 * w1 * a0 * b2
    - (61953196032000 : R) * h ^ 17 * e1n ^ 4 * e3 * a2
    - (38032740974592 : R) * h ^ 17 * e1n ^ 4 * b3
    - (169967616000 : R) * h ^ 17 * e1n ^ 3 * e3 ^ 3
    + (4817480523448320 : R) * h ^ 17 * e1n ^ 3 * a2 * a1
    + (29737534095360 : R) * h ^ 17 * e1n ^ 2 * e3 ^ 2 * a1
    + (46809527353344 : R) * h ^ 17 * e1n ^ 2 * e3 * b2
    - (3042619277967360 : R) * h ^ 17 * e1n * e3 * a2 * a0
    - (1521309638983680 : R) * h ^ 17 * e1n * e3 * a1 ^ 2
    - (3249918613389312 : R) * h ^ 17 * e1n * a2 * b1
    - (6499837226778624 : R) * h ^ 17 * e1n * a1 * b2
    - (9749755840167936 : R) * h ^ 17 * e1n * a0 * b3
    - (2086844497920 : R) * h ^ 17 * e3 ^ 3 * a0
    - (6687075336192 : R) * h ^ 17 * e3 ^ 2 * b1
    + (113747151468625920 : R) * h ^ 17 * a2 * a1 * a0
    + (18957858578104320 : R) * h ^ 17 * a1 ^ 3
    + (208859712122880 : R) * h ^ 15 * w1 ^ 5 * e1n ^ 5
    + (10237146112327680 : R) * h ^ 15 * w1 ^ 5 * e1n ^ 2 * a0
    - (46787569920000 : R) * h ^ 15 * w1 ^ 4 * e1n ^ 4 * e3
    + (4937359957770240 : R) * h ^ 15 * w1 ^ 4 * e1n ^ 3 * a1
    - (2544319940198400 : R) * h ^ 15 * w1 ^ 4 * e1n * e3 * a0
    + (65825897840640 : R) * h ^ 15 * w1 ^ 4 * e1n * b1
    + (49961856461045760 : R) * h ^ 15 * w1 ^ 4 * a1 * a0
    - (418184073216000 : R) * h ^ 15 * w1 ^ 3 * e1n ^ 4 * a2
    - (3441844224000 : R) * h ^ 15 * w1 ^ 3 * e1n ^ 3 * e3 ^ 2
    - (624488216002560 : R) * h ^ 15 * w1 ^ 3 * e1n ^ 2 * e3 * a1
    + (579267900997632 : R) * h ^ 15 * w1 ^ 3 * e1n ^ 2 * b2
    + (57049111461888000 : R) * h ^ 15 * w1 ^ 3 * e1n * a2 * a0
    + (28524555730944000 : R) * h ^ 15 * w1 ^ 3 * e1n * a1 ^ 2
    + (117385003008000 : R) * h ^ 15 * w1 ^ 3 * e3 ^ 2 * a0
    - (25076532510720 : R) * h ^ 15 * w1 ^ 3 * e3 * b1
    + (557578764288000 : R) * h ^ 15 * w1 ^ 2 * e1n ^ 3 * e3 * a2
    + (570491114618880 : R) * h ^ 15 * w1 ^ 2 * e1n ^ 3 * b3
    + (1147281408000 : R) * h ^ 15 * w1 ^ 2 * e1n ^ 2 * e3 ^ 3
    - (10839331177758720 : R) * h ^ 15 * w1 ^ 2 * e1n ^ 2 * a2 * a1
    - (44606301143040 : R) * h ^ 15 * w1 ^ 2 * e1n * e3 ^ 2 * a1
    - (210642873090048 : R) * h ^ 15 * w1 ^ 2 * e1n * e3 * b2
    - (2281964458475520 : R) * h ^ 15 * w1 ^ 2 * e3 * a2 * a0
    - (1140982229237760 : R) * h ^ 15 * w1 ^ 2 * e3 * a1 ^ 2
    + (2437438960041984 : R) * h ^ 15 * w1 ^ 2 * a2 * b1
    + (4874877920083968 : R) * h ^ 15 * w1 ^ 2 * a1 * b2
    + (7312316880125952 : R) * h ^ 15 * w1 ^ 2 * a0 * b3
    + (160582684114944 : R) * h ^ 15 * w1 * e1n ^ 4 * b4
    - (6423307364597760 : R) * h ^ 15 * w1 * e1n ^ 3 * a2 ^ 2
    - (79300090920960 : R) * h ^ 15 * w1 * e1n ^ 2 * e3 ^ 2 * a2
    - (152130963898368 : R) * h ^ 15 * w1 * e1n ^ 2 * e3 * b3
    - (54389637120 : R) * h ^ 15 * w1 * e1n * e3 ^ 4
    + (5071032129945600 : R) * h ^ 15 * w1 * e1n * e3 * a2 * a1
    + (7583143431241728 : R) * h ^ 15 * w1 * e1n * a2 * b2
    + (11374715146862592 : R) * h ^ 15 * w1 * e1n * a1 * b3
    + (15166286862483456 : R) * h ^ 15 * w1 * e1n * a0 * b4
    + (3478074163200 : R) * h ^ 15 * w1 * e3 ^ 3 * a1
    + (15603175784448 : R) * h ^ 15 * w1 * e3 ^ 2 * b2
    - (37915717156208640 : R) * h ^ 15 * w1 * a2 ^ 2 * a0
    - (37915717156208640 : R) * h ^ 15 * w1 * a2 * a1 ^ 2
    + (13381890342912 : R) * h ^ 15 * e1n ^ 5 * b5
    - (22537920577536 : R) * h ^ 15 * e1n ^ 3 * e3 * b4
    + (802913420574720 : R) * h ^ 15 * e1n ^ 2 * e3 * a2 ^ 2
    + (1895785857810432 : R) * h ^ 15 * e1n ^ 2 * a2 * b3
    + (2527714477080576 : R) * h ^ 15 * e1n ^ 2 * a1 * b4
    + (3159643096350720 : R) * h ^ 15 * e1n ^ 2 * a0 * b5
    + (2202780303360 : R) * h ^ 15 * e1n * e3 ^ 3 * a2
    + (7801587892224 : R) * h ^ 15 * e1n * e3 ^ 2 * b3
    - (41075360252559360 : R) * h ^ 15 * e1n * a2 ^ 2 * a1
    + (453246976 : R) * h ^ 15 * e3 ^ 5
    - (169034404331520 : R) * h ^ 15 * e3 ^ 2 * a2 * a1
    - (722204136308736 : R) * h ^ 15 * e3 * a2 * b2
    - (1083306204463104 : R) * h ^ 15 * e3 * a1 * b3
    - (1444408272617472 : R) * h ^ 15 * e3 * a0 * b4
    - (516534771916800 : R) * h ^ 13 * w1 ^ 7 * e1n ^ 4
    - (2328373457879040 : R) * h ^ 13 * w1 ^ 7 * e1n * a0
    + (259751681280000 : R) * h ^ 13 * w1 ^ 6 * e1n ^ 3 * e3
    - (7713405230469120 : R) * h ^ 13 * w1 ^ 6 * e1n ^ 2 * a1
    + (537476582522880 : R) * h ^ 13 * w1 ^ 6 * e3 * a0
    - (470184984576 : R) * h ^ 13 * w1 ^ 6 * b1
    - (6732763578777600 : R) * h ^ 13 * w1 ^ 5 * e1n ^ 3 * a2
    - (41560269004800 : R) * h ^ 13 * w1 ^ 5 * e1n ^ 2 * e3 ^ 2
    + (2274921358295040 : R) * h ^ 13 * w1 ^ 5 * e1n * e3 * a1
    - (39495538704384 : R) * h ^ 13 * w1 ^ 5 * e1n * b2
    - (28239310173634560 : R) * h ^ 13 * w1 ^ 5 * a2 * a0
    - (14119655086817280 : R) * h ^ 13 * w1 ^ 5 * a1 ^ 2
    + (1645786652590080 : R) * h ^ 13 * w1 ^ 4 * e1n ^ 2 * e3 * a2
    - (470655169560576 : R) * h ^ 13 * w1 ^ 4 * e1n ^ 2 * b3
    + (2257594859520 : R) * h ^ 13 * w1 ^ 4 * e1n * e3 ^ 3
    - (68696638385356800 : R) * h ^ 13 * w1 ^ 4 * e1n * a2 * a1
    - (141351107788800 : R) * h ^ 13 * w1 ^ 4 * e3 ^ 2 * a1
    + (14627977297920 : R) * h ^ 13 * w1 ^ 4 * e3 * b2
    - (718396218408960 : R) * h ^ 13 * w1 ^ 3 * e1n ^ 3 * b4
    - (8430590916034560 : R) * h ^ 13 * w1 ^ 3 * e1n ^ 2 * a2 ^ 2
    - (69387579555840 : R) * h ^ 13 * w1 ^ 3 * e1n * e3 ^ 2 * a2
    + (193089300332544 : R) * h ^ 13 * w1 ^ 3 * e1n * e3 * b3
    - (23795466240 : R) * h ^ 13 * w1 ^ 3 * e3 ^ 4
    + (6338790162432000 : R) * h ^ 13 * w1 ^ 3 * e3 * a2 * a1
    - (1354132755578880 : R) * h ^ 13 * w1 ^ 3 * a2 * b2
    - (2031199133368320 : R) * h ^ 13 * w1 ^ 3 * a1 * b3
    - (2708265511157760 : R) * h ^ 13 * w1 ^ 3 * a0 * b4
    - (351274621501440 : R) * h ^ 13 * w1 ^ 2 * e1n ^ 4 * b5
    + (253551606497280 : R) * h ^ 13 * w1 ^ 2 * e1n ^ 2 * e3 * b4
    - (1204370130862080 : R) * h ^ 13 * w1 ^ 2 * e1n * e3 * a2 ^ 2
    - (8531036360146944 : R) * h ^ 13 * w1 ^ 2 * e1n * a2 * b3
    - (11374715146862592 : R) * h ^ 13 * w1 ^ 2 * e1n * a1 * b4
    - (14218393933578240 : R) * h ^ 13 * w1 ^ 2 * e1n * a0 * b5
    - (1652085227520 : R) * h ^ 13 * w1 ^ 2 * e3 ^ 3 * a2
    - (17553572757504 : R) * h ^ 13 * w1 ^ 2 * e3 ^ 2 * b3
    - (30806520189419520 : R) * h ^ 13 * w1 ^ 2 * a2 ^ 2 * a1
    - (66909451714560 : R) * h ^ 13 * w1 * e1n ^ 5 * b6
    + (89212602286080 : R) * h ^ 13 * w1 * e1n ^ 3 * e3 * b5
    - (5476714700341248 : R) * h ^ 13 * w1 * e1n ^ 2 * a2 * b4
    - (6845893375426560 : R) * h ^ 13 * w1 * e1n ^ 2 * a1 * b5
    - (8215072050511872 : R) * h ^ 13 * w1 * e1n ^ 2 * a0 * b6
    - (22537920577536 : R) * h ^ 13 * w1 * e1n * e3 ^ 2 * b4
    + (22819644584755200 : R) * h ^ 13 * w1 * e1n * a2 ^ 3
    + (140862003609600 : R) * h ^ 13 * w1 * e3 ^ 2 * a2 ^ 2
    + (1263857238540288 : R) * h ^ 13 * w1 * e3 * a2 * b3
    + (1685142984720384 : R) * h ^ 13 * w1 * e3 * a1 * b4
    + (2106428730900480 : R) * h ^ 13 * w1 * e3 * a0 * b5
    - (4336723722240 : R) * h ^ 13 * e1n ^ 6 * b7
    + (8921260228608 : R) * h ^ 13 * e1n ^ 4 * e3 * b6
    - (760654819491840 : R) * h ^ 13 * e1n ^ 3 * a2 * b5
    - (912785783390208 : R) * h ^ 13 * e1n ^ 3 * a1 * b6
    - (1064916747288576 : R) * h ^ 13 * e1n ^ 3 * a0 * b7
    - (4695400120320 : R) * h ^ 13 * e1n ^ 2 * e3 ^ 2 * b5
    + (561714328240128 : R) * h ^ 13 * e1n * e3 * a2 * b4
    + (702142910300160 : R) * h ^ 13 * e1n * e3 * a1 * b5
    + (842571492360192 : R) * h ^ 13 * e1n * e3 * a0 * b6
    + (385263599616 : R) * h ^ 13 * e3 ^ 3 * b4
    - (1521309638983680 : R) * h ^ 13 * e3 * a2 ^ 3
    - (14624633760251904 : R) * h ^ 13 * a2 ^ 2 * b3
    - (38999023360671744 : R) * h ^ 13 * a2 * a1 * b4
    - (48748779200839680 : R) * h ^ 13 * a2 * a0 * b5
    - (24374389600419840 : R) * h ^ 13 * a1 ^ 2 * b5
    - (58498535041007616 : R) * h ^ 13 * a1 * a0 * b6
    - (34124145440587776 : R) * h ^ 13 * a0 ^ 2 * b7
    + (25607321026560 : R) * h ^ 12 * w1 * e1n ^ 6 * b8n
    + (3853984418758656 : R) * h ^ 12 * w1 * e1n ^ 3 * a0 * b8n
    + (45498860587450368 : R) * h ^ 12 * w1 * a0 ^ 2 * b8n
    - (3304170455040 : R) * h ^ 12 * e1n ^ 5 * e3 * b8n
    + (321165368229888 : R) * h ^ 12 * e1n ^ 4 * a1 * b8n
    - (405682570395648 : R) * h ^ 12 * e1n ^ 2 * e3 * a0 * b8n
    + (30332573724966912 : R) * h ^ 12 * e1n * a1 * a0 * b8n
    + (205018291296000 : R) * h ^ 11 * w1 ^ 9 * e1n ^ 3
    + (20751991603200 : R) * h ^ 11 * w1 ^ 9 * a0
    - (118279783440000 : R) * h ^ 11 * w1 ^ 8 * e1n ^ 2 * e3
    + (1068273617748480 : R) * h ^ 11 * w1 ^ 8 * e1n * a1
    + (5177815799869440 : R) * h ^ 11 * w1 ^ 7 * e1n ^ 2 * a2
    + (21307883950080 : R) * h ^ 11 * w1 ^ 7 * e1n * e3 ^ 2
    - (258708161986560 : R) * h ^ 11 * w1 ^ 7 * e3 * a1
    + (156728328192 : R) * h ^ 11 * w1 ^ 7 * b2
    - (1714090051215360 : R) * h ^ 11 * w1 ^ 6 * e1n * e3 * a2
    + (18102121906176 : R) * h ^ 11 * w1 ^ 6 * e1n * b3
    - (1175644753920 : R) * h ^ 11 * w1 ^ 6 * e3 ^ 3
    + (14511867728117760 : R) * h ^ 11 * w1 ^ 6 * a2 * a1
    + (313770113040384 : R) * h ^ 11 * w1 ^ 5 * e1n ^ 2 * b4
    + (30711438336983040 : R) * h ^ 11 * w1 ^ 5 * e1n * a2 ^ 2
    + (126384519905280 : R) * h ^ 11 * w1 ^ 5 * e3 ^ 2 * a2
    - (6582589784064 : R) * h ^ 11 * w1 ^ 5 * e3 * b3
    + (710912924467200 : R) * h ^ 11 * w1 ^ 4 * e1n ^ 3 * b5
    - (139453383573504 : R) * h ^ 11 * w1 ^ 4 * e1n * e3 * b4
    - (3816479910297600 : R) * h ^ 11 * w1 ^ 4 * e3 * a2 ^ 2
    + (592433080565760 : R) * h ^ 11 * w1 ^ 4 * a2 * b3
    + (789910774087680 : R) * h ^ 11 * w1 ^ 4 * a1 * b4
    + (987388467609600 : R) * h ^ 11 * w1 ^ 4 * a0 * b5
    + (538621086302208 : R) * h ^ 11 * w1 ^ 3 * e1n ^ 4 * b6
    - (299331757670400 : R) * h ^ 11 * w1 ^ 3 * e1n ^ 2 * e3 * b5
    + (6951214811971584 : R) * h ^ 11 * w1 ^ 3 * e1n * a2 * b4
    + (8689018514964480 : R) * h ^ 11 * w1 ^ 3 * e1n * a1 * b5
    + (10426822217957376 : R) * h ^ 11 * w1 ^ 3 * e1n * a0 * b6
    + (14302911135744 : R) * h ^ 11 * w1 ^ 3 * e3 ^ 2 * b4
    + (28524555730944000 : R) * h ^ 11 * w1 ^ 3 * a2 ^ 3
    + (175637310750720 : R) * h ^ 11 * w1 ^ 2 * e1n ^ 5 * b7
    - (187346464800768 : R) * h ^ 11 * w1 ^ 2 * e1n ^ 3 * e3 * b6
    + (8557366719283200 : R) * h ^ 11 * w1 ^ 2 * e1n ^ 2 * a2 * b5
    + (10268840063139840 : R) * h ^ 11 * w1 ^ 2 * e1n ^ 2 * a1 * b6
    + (11980313406996480 : R) * h ^ 11 * w1 ^ 2 * e1n ^ 2 * a0 * b7
    + (35215500902400 : R) * h ^ 11 * w1 ^ 2 * e1n * e3 ^ 2 * b5
    - (1263857238540288 : R) * h ^ 11 * w1 ^ 2 * e3 * a2 * b4
    - (1579821548175360 : R) * h ^ 11 * w1 ^ 2 * e3 * a1 * b5
    - (1895785857810432 : R) * h ^ 11 * w1 ^ 2 * e3 * a0 * b6
    - (43367237222400 : R) * h ^ 11 * w1 * e1n ^ 4 * e3 * b7
    + (2890488314068992 : R) * h ^ 11 * w1 * e1n ^ 3 * a2 * b6
    + (3372236366413824 : R) * h ^ 11 * w1 * e1n ^ 3 * a1 * b7
    + (17842520457216 : R) * h ^ 11 * w1 * e1n ^ 2 * e3 ^ 2 * b6
    - (1521309638983680 : R) * h ^ 11 * w1 * e1n * e3 * a2 * b5
    - (1825571566780416 : R) * h ^ 11 * w1 * e1n * e3 * a1 * b6
    - (2129833494577152 : R) * h ^ 11 * w1 * e1n * e3 * a0 * b7
    - (1043422248960 : R) * h ^ 11 * w1 * e3 ^ 3 * b5
    + (22749430293725184 : R) * h ^ 11 * w1 * a2 ^ 2 * b4
    + (56873575734312960 : R) * h ^ 11 * w1 * a2 * a1 * b5
    + (68248290881175552 : R) * h ^ 11 * w1 * a2 * a0 * b6
    + (34124145440587776 : R) * h ^ 11 * w1 * a1 ^ 2 * b6
    + (79623006028038144 : R) * h ^ 11 * w1 * a1 * a0 * b7
    + (281019697201152 : R) * h ^ 11 * e1n ^ 4 * a2 * b7
    + (2312919318528 : R) * h ^ 11 * e1n ^ 3 * e3 ^ 2 * b7
    - (304261927796736 : R) * h ^ 11 * e1n ^ 2 * e3 * a2 * b6
    - (354972249096192 : R) * h ^ 11 * e1n ^ 2 * e3 * a1 * b7
    - (417368899584 : R) * h ^ 11 * e1n * e3 ^ 3 * b6
    + (9478929289052160 : R) * h ^ 11 * e1n * a2 ^ 2 * b5
    + (22749430293725184 : R) * h ^ 11 * e1n * a2 * a1 * b6
    + (26541002009346048 : R) * h ^ 11 * e1n * a2 * a0 * b7
    + (13270501004673024 : R) * h ^ 11 * e1n * a1 ^ 2 * b7
    + (39007939461120 : R) * h ^ 11 * e3 ^ 2 * a2 * b5
    + (46809527353344 : R) * h ^ 11 * e3 ^ 2 * a1 * b6
    + (54611115245568 : R) * h ^ 11 * e3 ^ 2 * a0 * b7
    - (323395683287040 : R) * h ^ 10 * w1 ^ 3 * e1n ^ 5 * b8n
    - (12931131931361280 : R) * h ^ 10 * w1 ^ 3 * e1n ^ 2 * a0 * b8n
    + (111515752857600 : R) * h ^ 10 * w1 ^ 2 * e1n ^ 4 * e3 * b8n
    - (6744472732827648 : R) * h ^ 10 * w1 ^ 2 * e1n ^ 3 * a1 * b8n
    + (3042619277967360 : R) * h ^ 10 * w1 ^ 2 * e1n * e3 * a0 * b8n
    - (68248290881175552 : R) * h ^ 10 * w1 ^ 2 * a1 * a0 * b8n
    - (1338189034291200 : R) * h ^ 10 * w1 * e1n ^ 4 * a2 * b8n
    - (11013901516800 : R) * h ^ 10 * w1 * e1n ^ 3 * e3 ^ 2 * b8n
    + (1284661472919552 : R) * h ^ 10 * w1 * e1n ^ 2 * e3 * a1 * b8n
    - (65720576404094976 : R) * h ^ 10 * w1 * e1n * a2 * a0 * b8n
    - (32860288202047488 : R) * h ^ 10 * w1 * e1n * a1 ^ 2 * b8n
    - (135227523465216 : R) * h ^ 10 * w1 * e3 ^ 2 * a0 * b8n
    + (142740163657728 : R) * h ^ 10 * e1n ^ 3 * e3 * a2 * b8n
    + (293704040448 : R) * h ^ 10 * e1n ^ 2 * e3 ^ 3 * b8n
    - (10953429400682496 : R) * h ^ 10 * e1n ^ 2 * a2 * a1 * b8n
    - (45075841155072 : R) * h ^ 10 * e1n * e3 ^ 2 * a1 * b8n
    + (3370285969440768 : R) * h ^ 10 * e3 * a2 * a0 * b8n
    + (1685142984720384 : R) * h ^ 10 * e3 * a1 ^ 2 * b8n
    - (14193574012800 : R) * h ^ 9 * w1 ^ 11 * e1n ^ 2
    + (7517337347520 : R) * h ^ 9 * w1 ^ 10 * e1n * e3
    - (6522826527360 : R) * h ^ 9 * w1 ^ 10 * a1
    - (472460881052160 : R) * h ^ 9 * w1 ^ 9 * e1n * a2
    - (972141730560 : R) * h ^ 9 * w1 ^ 9 * e3 ^ 2
    + (118697068638720 : R) * h ^ 9 * w1 ^ 8 * e3 * a2
    - (44079842304 : R) * h ^ 9 * w1 ^ 8 * b3
    - (7470716977152 : R) * h ^ 9 * w1 ^ 7 * e1n * b4
    - (3492560186818560 : R) * h ^ 9 * w1 ^ 7 * a2 ^ 2
    - (185211525058560 : R) * h ^ 9 * w1 ^ 6 * e1n ^ 2 * b5
    + (2681795837952 : R) * h ^ 9 * w1 ^ 6 * e3 * b4
    - (597166856552448 : R) * h ^ 9 * w1 ^ 5 * e1n ^ 3 * b6
    + (87158364733440 : R) * h ^ 9 * w1 ^ 5 * e1n * e3 * b5
    - (236973232226304 : R) * h ^ 9 * w1 ^ 5 * a2 * b4
    - (296216540282880 : R) * h ^ 9 * w1 ^ 5 * a1 * b5
    - (355459848339456 : R) * h ^ 9 * w1 ^ 5 * a0 * b6
    - (654574236825600 : R) * h ^ 9 * w1 ^ 4 * e1n ^ 4 * b7
    + (284365169786880 : R) * h ^ 9 * w1 ^ 4 * e1n ^ 2 * e3 * b6
    - (4706551695605760 : R) * h ^ 9 * w1 ^ 4 * e1n * a2 * b5
    - (5647862034726912 : R) * h ^ 9 * w1 ^ 4 * e1n * a1 * b6
    - (6589172373848064 : R) * h ^ 9 * w1 ^ 4 * e1n * a0 * b7
    - (9684262748160 : R) * h ^ 9 * w1 ^ 4 * e3 ^ 2 * b5
    + (279285007712256 : R) * h ^ 9 * w1 ^ 3 * e1n ^ 3 * e3 * b7
    - (9698348948520960 : R) * h ^ 9 * w1 ^ 3 * e1n ^ 2 * a2 * b6
    - (11314740439941120 : R) * h ^ 9 * w1 ^ 3 * e1n ^ 2 * a1 * b7
    - (39910901022720 : R) * h ^ 9 * w1 ^ 3 * e1n * e3 ^ 2 * b6
    + (965446501662720 : R) * h ^ 9 * w1 ^ 3 * e3 * a2 * b5
    + (1158535801995264 : R) * h ^ 9 * w1 ^ 3 * e3 * a1 * b6
    + (1351625102327808 : R) * h ^ 9 * w1 ^ 3 * e3 * a0 * b7
    - (5901413641224192 : R) * h ^ 9 * w1 ^ 2 * e1n ^ 3 * a2 * b7
    - (36428479266816 : R) * h ^ 9 * w1 ^ 2 * e1n ^ 2 * e3 ^ 2 * b7
    + (2281964458475520 : R) * h ^ 9 * w1 ^ 2 * e1n * e3 * a2 * b6
    + (2662291868221440 : R) * h ^ 9 * w1 ^ 2 * e1n * e3 * a1 * b7
    + (1565133373440 : R) * h ^ 9 * w1 ^ 2 * e3 ^ 3 * b6
    - (21327590900367360 : R) * h ^ 9 * w1 ^ 2 * a2 ^ 2 * b5
    - (51186218160881664 : R) * h ^ 9 * w1 ^ 2 * a2 * a1 * b6
    - (59717254521028608 : R) * h ^ 9 * w1 ^ 2 * a2 * a0 * b7
    - (29858627260514304 : R) * h ^ 9 * w1 ^ 2 * a1 ^ 2 * b7
    + (1124078788804608 : R) * h ^ 9 * w1 * e1n ^ 2 * e3 * a2 * b7
    + (1541946212352 : R) * h ^ 9 * w1 * e1n * e3 ^ 3 * b7
    - (24645216151535616 : R) * h ^ 9 * w1 * e1n * a2 ^ 2 * b6
    - (57505504353583104 : R) * h ^ 9 * w1 * e1n * a2 * a1 * b7
    - (101420642598912 : R) * h ^ 9 * w1 * e3 ^ 2 * a2 * b6
    - (118324083032064 : R) * h ^ 9 * w1 * e3 ^ 2 * a1 * b7
    - (4792125362798592 : R) * h ^ 9 * e1n ^ 2 * a2 ^ 2 * b7
    - (39441361010688 : R) * h ^ 9 * e1n * e3 ^ 2 * a2 * b7
    - (13525843968 : R) * h ^ 9 * e3 ^ 4 * b7
    + (1263857238540288 : R) * h ^ 9 * e3 * a2 ^ 2 * b6
    + (2949000223260672 : R) * h ^ 9 * e3 * a2 * a1 * b7
    + (673276357877760 : R) * h ^ 8 * w1 ^ 5 * e1n ^ 4 * b8n
    + (3765241356484608 : R) * h ^ 8 * w1 ^ 5 * e1n * a0 * b8n
    - (332482152038400 : R) * h ^ 8 * w1 ^ 4 * e1n ^ 3 * e3 * b8n
    + (10237146112327680 : R) * h ^ 8 * w1 ^ 4 * e1n ^ 2 * a1 * b8n
    - (836720301441024 : R) * h ^ 8 * w1 ^ 4 * e3 * a0 * b8n
    + (8617937380835328 : R) * h ^ 8 * w1 ^ 3 * e1n ^ 3 * a2 * b8n
    + (53197144326144 : R) * h ^ 8 * w1 ^ 3 * e1n ^ 2 * e3 ^ 2 * b8n
    - (2873584873635840 : R) * h ^ 8 * w1 ^ 3 * e1n * e3 * a1 * b8n
    + (41707288871829504 : R) * h ^ 8 * w1 ^ 3 * a2 * a0 * b8n
    + (20853644435914752 : R) * h ^ 8 * w1 ^ 3 * a1 ^ 2 * b8n
    - (2248157577609216 : R) * h ^ 8 * w1 ^ 2 * e1n ^ 2 * e3 * a2 * b8n
    - (3083892424704 : R) * h ^ 8 * w1 ^ 2 * e1n * e3 ^ 3 * b8n
    + (82150720505118720 : R) * h ^ 8 * w1 ^ 2 * e1n * a2 * a1 * b8n
    + (169034404331520 : R) * h ^ 8 * w1 ^ 2 * e3 ^ 2 * a1 * b8n
    + (17342929884413952 : R) * h ^ 8 * w1 * e1n ^ 2 * a2 ^ 2 * b8n
    + (142740163657728 : R) * h ^ 8 * w1 * e1n * e3 ^ 2 * a2 * b8n
    + (48950673408 : R) * h ^ 8 * w1 * e3 ^ 4 * b8n
    - (7302286267121664 : R) * h ^ 8 * w1 * e3 * a2 * a1 * b8n
    - (1217047711186944 : R) * h ^ 8 * e1n * e3 * a2 ^ 2 * b8n
    - (1669475598336 : R) * h ^ 8 * e3 ^ 3 * a2 * b8n
    + (45498860587450368 : R) * h ^ 8 * a2 ^ 2 * a1 * b8n
    + (69754744080 : R) * h ^ 7 * w1 ^ 13 * e1n
    - (24284496600 : R) * h ^ 7 * w1 ^ 12 * e3
    + (2062916968320 : R) * h ^ 7 * w1 ^ 11 * a2
    + (11972302848 : R) * h ^ 7 * w1 ^ 9 * b4
    + (2918248819200 : R) * h ^ 7 * w1 ^ 8 * e1n * b5
    + (100543399317504 : R) * h ^ 7 * w1 ^ 7 * e1n ^ 2 * b6
    - (1037599580160 : R) * h ^ 7 * w1 ^ 7 * e3 * b5
    + (445110481041408 : R) * h ^ 7 * w1 ^ 6 * e1n ^ 3 * b7
    - (49389740015616 : R) * h ^ 7 * w1 ^ 6 * e1n * e3 * b6
    + (90510609530880 : R) * h ^ 7 * w1 ^ 6 * a2 * b5
    + (108612731437056 : R) * h ^ 7 * w1 ^ 6 * a1 * b6
    + (126714853343232 : R) * h ^ 7 * w1 ^ 6 * a0 * b7
    - (232231555325952 : R) * h ^ 7 * w1 ^ 5 * e1n ^ 2 * e3 * b7
    + (2823931017363456 : R) * h ^ 7 * w1 ^ 5 * e1n * a2 * b6
    + (3294586186924032 : R) * h ^ 7 * w1 ^ 5 * e1n * a1 * b7
    + (5810557648896 : R) * h ^ 7 * w1 ^ 5 * e3 ^ 2 * b6
    + (8957502848286720 : R) * h ^ 7 * w1 ^ 4 * e1n ^ 2 * a2 * b7
    + (36862151639040 : R) * h ^ 7 * w1 ^ 4 * e1n * e3 ^ 2 * b7
    - (627540226080768 : R) * h ^ 7 * w1 ^ 4 * e3 * a2 * b6
    - (732130263760896 : R) * h ^ 7 * w1 ^ 4 * e3 * a1 * b7
    - (2514386764431360 : R) * h ^ 7 * w1 ^ 3 * e1n * e3 * a2 * b7
    - (1724545105920 : R) * h ^ 7 * w1 ^ 3 * e3 ^ 3 * b7
    + (15640233326936064 : R) * h ^ 7 * w1 ^ 3 * a2 ^ 2 * b6
    + (36493877762850816 : R) * h ^ 7 * w1 ^ 3 * a2 * a1 * b7
    + (35940940220989440 : R) * h ^ 7 * w1 ^ 2 * e1n * a2 ^ 2 * b7
    + (147905103790080 : R) * h ^ 7 * w1 ^ 2 * e3 ^ 2 * a2 * b7
    - (3194750241865728 : R) * h ^ 7 * w1 * e3 * a2 ^ 2 * b7
    + (13270501004673024 : R) * h ^ 7 * a2 ^ 3 * b7
    - (302796245606400 : R) * h ^ 6 * w1 ^ 7 * e1n ^ 3 * b8n
    - (44824301862912 : R) * h ^ 6 * w1 ^ 7 * a0 * b8n
    + (169565897539584 : R) * h ^ 6 * w1 ^ 6 * e1n ^ 2 * e3 * b8n
    - (1778030640562176 : R) * h ^ 6 * w1 ^ 6 * e1n * a1 * b8n
    - (7166002278629376 : R) * h ^ 6 * w1 ^ 5 * e1n ^ 2 * a2 * b8n
    - (29489721311232 : R) * h ^ 6 * w1 ^ 5 * e1n * e3 ^ 2 * b8n
    + (418360150720512 : R) * h ^ 6 * w1 ^ 5 * e3 * a1 * b8n
    + (2274921358295040 : R) * h ^ 6 * w1 ^ 4 * e1n * e3 * a2 * b8n
    + (1560302714880 : R) * h ^ 6 * w1 ^ 4 * e3 ^ 3 * b8n
    - (22591448138907648 : R) * h ^ 6 * w1 ^ 4 * a2 * a1 * b8n
    - (38793395794083840 : R) * h ^ 6 * w1 ^ 3 * e1n * a2 ^ 2 * b8n
    - (159643604090880 : R) * h ^ 6 * w1 ^ 3 * e3 ^ 2 * a2 * b8n
    + (4563928916951040 : R) * h ^ 6 * w1 ^ 2 * e3 * a2 ^ 2 * b8n
    - (32860288202047488 : R) * h ^ 6 * w1 * a2 ^ 3 * b8n
    - (26372304 : R) * h ^ 5 * w1 ^ 15
    - (3242498688 : R) * h ^ 5 * w1 ^ 10 * b5
    - (1102449553920 : R) * h ^ 5 * w1 ^ 9 * e1n * b6
    - (51319026734976 : R) * h ^ 5 * w1 ^ 8 * e1n ^ 2 * b7
    + (389099842560 : R) * h ^ 5 * w1 ^ 8 * e3 * b6
    + (26066807230464 : R) * h ^ 5 * w1 ^ 7 * e1n * e3 * b7
    - (33618226397184 : R) * h ^ 5 * w1 ^ 7 * a2 * b6
    - (39221264130048 : R) * h ^ 5 * w1 ^ 7 * a1 * b7
    - (1555776810491904 : R) * h ^ 5 * w1 ^ 6 * e1n * a2 * b7
    - (3201186852864 : R) * h ^ 5 * w1 ^ 6 * e3 ^ 2 * b7
    + (366065131880448 : R) * h ^ 5 * w1 ^ 5 * e3 * a2 * b7
    - (9883758560772096 : R) * h ^ 5 * w1 ^ 4 * a2 ^ 2 * b7
    + (24980690262528 : R) * h ^ 4 * w1 ^ 9 * e1n ^ 2 * b8n
    - (13033403615232 : R) * h ^ 4 * w1 ^ 8 * e1n * e3 * b8n
    + (14007594332160 : R) * h ^ 4 * w1 ^ 8 * a1 * b8n
    + (804347194540032 : R) * h ^ 4 * w1 ^ 7 * e1n * a2 * b8n
    + (1655035379712 : R) * h ^ 4 * w1 ^ 7 * e3 ^ 2 * b8n
    - (197558960062464 : R) * h ^ 4 * w1 ^ 6 * e3 * a2 * b8n
    + (5647862034726912 : R) * h ^ 4 * w1 ^ 5 * a2 ^ 2 * b8n
    + (884317824 : R) * h ^ 3 * w1 ^ 11 * b6
    + (407293862976 : R) * h ^ 3 * w1 ^ 10 * e1n * b7
    - (142910127360 : R) * h ^ 3 * w1 ^ 9 * e3 * b7
    + (12256645040640 : R) * h ^ 3 * w1 ^ 8 * a2 * b7
    - (148106859264 : R) * h ^ 2 * w1 ^ 11 * e1n * b8n
    + (51719855616 : R) * h ^ 2 * w1 ^ 10 * e3 * b8n
    - (4409798215680 : R) * h ^ 2 * w1 ^ 9 * a2 * b8n
    - (243596808 : R) * h * w1 ^ 12 * b7
    + (67814496 : R) * w1 ^ 13 * b8n
set_option maxHeartbeats 1600000000 in
theorem alignedSquareJetQuotient610_muZeroQ8_factor_one
    {R : Type*} [CommRing R]
    (h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : R) :
    alignedSquareJetQuotient610 h w1 (h * e1n) e3 a2 a1 a0 (h * b8n) b7
        b6 b5 b4 b3 b2 b1 =
      h * alignedSquareMuZeroQ8QuotOne610 h w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 := by
  simp only [alignedSquareJetQuotient610,
    alignedSquareMuZeroQ8QuotOne610]
  ring

#print axioms alignedSquareJetQuotient610_muZeroQ8_factor_one

theorem alignedSquareJetQuotient610_muZeroQ8_pow_one_dvd
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : k[X]) :
    h0 ∣
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
        (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 :=
  ⟨_, alignedSquareJetQuotient610_muZeroQ8_factor_one h0 w1 e1n e3 a2
      a1 a0 b8n b7 b6 b5 b4 b3 b2 b1⟩

#print axioms alignedSquareJetQuotient610_muZeroQ8_pow_one_dvd
set_option maxHeartbeats 1600000000 in
/-- Conditional order-`61` vanishing on `μ = 0` after the `q₈` peel.
If previous mixed orders have already supplied `h₀⁷ ∣` the substituted
jet — equivalently, if the order-`55`–`60` prefix has been peeled —
then cancelling those seven powers from the pole-`21` clearing leaves
a pole-`14` numerator whose head is the order-`61` mixed coefficient. -/
theorem alignedSquareMuZeroQ8Order61610_zero_of_pole_of_pow_seven
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q61 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 7 * Q61)
    (hhead :
      Q61.eval a =
        alignedSquareMuZeroQ8Order61610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order61610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a) = 0 := by
  have hclear14 :
      algebraMap k[X] (RatFunc k) Q61 =
        (algebraMap k[X] (RatFunc k) h0) ^
            alignedSquareW1ZeroRemainingPole610 * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q61 rho 7 14 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
        rw [hpow] at hclear
        simpa [hfact] using hclear)
  have hQ0 : Q61.eval a = 0 :=
    alignedSquare_poleFourteen_head_eval_zero610 a j h0 Q61 rho hdegree
      hroot hclear14 hderiv
  exact hhead.symm.trans hQ0

#print axioms alignedSquareMuZeroQ8Order61610_zero_of_pole_of_pow_seven

/-- After the order-`61` head vanishes at `a`, the remaining order-`61`
numerator is divisible by `h₀`.  This is one step of the `h₀^M`
divisibility the ceiling lemma consumes. -/
theorem alignedSquareW1Peel_order61_remaining_dvd
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q61 : k[X],
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 7 * Q61 ∧ Q61.eval a = 0 ∧ h0 ∣ Q61 := by
  let Q61 : k[X] :=
    alignedSquareW1PeelOrder61610 w1n e1 e3 a2 b8
      + h0 * alignedSquareW1PeelOrder62610 w1n e1 e3 a2 a1 b8 b7
      + h0 ^ 2 * alignedSquareW1PeelOrder63610 w1n e1 e3 a2 a1 b8 b7
      + h0 ^ 3 * alignedSquareW1PeelOrder64610 w1n e1 e3 a2 a1 a0 b8 b7 b6
      + h0 ^ 4 * alignedSquareW1PeelOrder65610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1PeelOrder66610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 6 * alignedSquareW1PeelOrder67610 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4
      + h0 ^ 7 * alignedSquareW1PeelOrder68610 w1n e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
      + h0 ^ 8 * alignedSquareW1PeelOrder68Plus610 h0 w1n e1 e3 a2 a1 a0 b6 b5 b4 b3 b2 b1
  have hjet :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 7 * Q61 := by
    simpa [Q61] using alignedSquareJetQuotient610_w1Peel_scale h0 w1n e1
      e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1
  have hclear14 :
      algebraMap k[X] (RatFunc k) Q61 =
        (algebraMap k[X] (RatFunc k) h0) ^
            alignedSquareW1ZeroRemainingPole610 * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q61 rho 7 14 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  have hQ0 : Q61.eval a = 0 :=
    alignedSquare_poleFourteen_head_eval_zero610 a j h0 Q61 rho hdegree
      hroot hclear14 hderiv
  exact ⟨Q61, hjet, hQ0,
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Q61 a
      hdegree hroot hQ0⟩

#print axioms alignedSquareW1Peel_order61_remaining_dvd

/-- Same `h₀`-divisibility step on the frozen `w₁ = 0` limb. -/
theorem alignedSquareW1Zero_order61_remaining_dvd
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q61 : k[X],
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 7 * Q61 ∧ Q61.eval a = 0 ∧ h0 ∣ Q61 := by
  let Q61 : k[X] :=
    alignedSquareW1ZeroOrder61610 e1 e3 a2 b8
      + h0 * alignedSquareW1ZeroOrder62610 e1 e3 a2 a1 b8 b7
      + h0 ^ 2 * alignedSquareW1ZeroOrder63610 e1 e3 a2 a1 b8 b7
      + h0 ^ 3 * alignedSquareW1ZeroOrder64610 e1 e3 a2 a1 a0 b8 b7 b6
      + h0 ^ 4 * alignedSquareW1ZeroOrder65610 e1 e3 a2 a1 a0 b8 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1ZeroOrder66610 e1 e3 a2 a1 a0 b7 b6 b5
      + h0 ^ 6 * alignedSquareW1ZeroOrder67610 e1 e3 a2 a1 a0 b6 b5 b4
      + h0 ^ 7 * alignedSquareW1ZeroOrder68610 e1 e3 a2 a1 a0 b7 b6 b5 b4 b3
      + h0 ^ 8 * alignedSquareW1ZeroOrder68Plus610 h0 e1 e3 a2 a1 a0 b4 b3 b2 b1
  have hjet :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 7 * Q61 := by
    simpa [Q61] using alignedSquareJetQuotient610_w1Zero_scale h0 e1 e3
      a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1
  have hclear14 :
      algebraMap k[X] (RatFunc k) Q61 =
        (algebraMap k[X] (RatFunc k) h0) ^
            alignedSquareW1ZeroRemainingPole610 * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q61 rho 7 14 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  have hQ0 : Q61.eval a = 0 :=
    alignedSquare_poleFourteen_head_eval_zero610 a j h0 Q61 rho hdegree
      hroot hclear14 hderiv
  exact ⟨Q61, hjet, hQ0,
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Q61 a
      hdegree hroot hQ0⟩

#print axioms alignedSquareW1Zero_order61_remaining_dvd

/-- Complement: `h₀¹⁰ ∣` the jet, and the order-`64` head vanishes, so
the remaining pole-`11` numerator is divisible by one more `h₀`. -/
theorem alignedSquareW1Complement_order64_remaining_dvd
    (h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b)
            (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q64 : k[X],
      alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b)
          (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 10 * Q64 ∧ Q64.eval a = 0 ∧ h0 ∣ Q64 := by
  let Q64 : k[X] :=
    alignedSquareW1ComplementOrder64610 w1n a2b a1 b8
      + h0 * alignedSquareW1ComplementOrder65610 w1n e1b e3b a2b a1 b8 b7
      + h0 ^ 2 * alignedSquareW1ComplementOrder66610 w1n e1b e3b a2b a1 a0 b8 b7
      + h0 ^ 3 * alignedSquareW1ComplementOrder67610 w1n e1b e3b a2b a1 a0 b8 b7 b6
      + h0 ^ 4 * alignedSquareW1ComplementOrder68610 w1n e1b e3b a2b a1 a0 b7 b6 b5
      + h0 ^ 5 * alignedSquareW1ComplementOrder68Plus610 h0 w1n e1b e3b a2b a1 a0 b6 b5 b4 b3 b2 b1
  have hjet :
      alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b)
          (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 10 * Q64 := by
    simpa [Q64] using alignedSquareJetQuotient610_w1Complement_scale h0
      w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1
  have hclear11 :
      algebraMap k[X] (RatFunc k) Q64 =
        (algebraMap k[X] (RatFunc k) h0) ^ 11 * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q64 rho 10 11 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 10 + 11 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  have hQ0 : Q64.eval a = 0 :=
    alignedSquare_localLinearPole_head_eval_zero610 11 (by decide) a j
      h0 Q64 rho hdegree hroot hclear11 hderiv
  exact ⟨Q64, hjet, hQ0,
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Q64 a
      hdegree hroot hQ0⟩

#print axioms alignedSquareW1Complement_order64_remaining_dvd

/-- Cancel `m` polynomial powers from a pole-`(m+n)` clearing and apply
the remaining pole-`n` obstruction.  The remaining numerator evaluates
to a recorded head, so that head vanishes.  Instantiating `m = 0` and
`n = 21` is `alignedSquare_poleTwentyOne_head_eval_zero610`. -/
theorem alignedSquare_remainingHead_eval_zero610
    (h0 A0 Q : k[X]) (rho : RatFunc k) (j a head : k) (m n : ℕ)
    (hn : n ≠ 0) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact : A0 = h0 ^ m * Q) (hhead : Q.eval a = head)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ (m + n) * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    head = 0 := by
  have hclearQ :
      algebraMap k[X] (RatFunc k) Q =
        (algebraMap k[X] (RatFunc k) h0) ^ n * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q rho m n hh0
      (by simpa [hfact] using hclear)
  have hQ0 : Q.eval a = 0 :=
    alignedSquare_localLinearPole_head_eval_zero610 n hn a j h0 Q rho
      hdegree hroot hclearQ hderiv
  exact hhead.symm.trans hQ0

#print axioms alignedSquare_remainingHead_eval_zero610

/-- If a remaining pole-`(r+1)` numerator vanishes at the linear root,
one more linear factor cancels and the pole-`r` obstruction forces the
new remaining numerator to vanish.  This is one step of the `h₀^M`
divisibility the ceiling lemma consumes. -/
theorem alignedSquare_remainingNumerator_succ_dvd610
    (h0 Qold : k[X]) (rho : RatFunc k) (j a : k) (r : ℕ)
    (hr : r ≠ 0) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hQold : Qold.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) Qold =
      (algebraMap k[X] (RatFunc k) h0) ^ (r + 1) * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Qnew : k[X],
      Qold = h0 * Qnew ∧
        algebraMap k[X] (RatFunc k) Qnew =
          (algebraMap k[X] (RatFunc k) h0) ^ r * rho ∧
        Qnew.eval a = 0 ∧ h0 ∣ Qnew := by
  obtain ⟨Qnew, hfact⟩ :=
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Qold a
      hdegree hroot hQold
  have hclear' :
      algebraMap k[X] (RatFunc k) Qnew =
        (algebraMap k[X] (RatFunc k) h0) ^ r * rho :=
    alignedSquare_algebraMap_cancel_one_clearing610 h0 Qold Qnew rho r
      hh0 hfact hclear
  have hzero : Qnew.eval a = 0 :=
    alignedSquare_localLinearPole_head_eval_zero610 r hr a j h0 Qnew rho
      hdegree hroot hclear' hderiv
  exact ⟨Qnew, hfact, hclear', hzero,
    alignedSquare_linearPolynomial_dvd_of_eval_eq_zero610 h0 Qnew a
      hdegree hroot hzero⟩

#print axioms alignedSquare_remainingNumerator_succ_dvd610

/-! ### Parent pole-`21` obstruction on each specialised jet -/

/-- `w₁ = h₀ w₁n`: the specialised MixedPair jet is still a pole-`21`
numerator, so the parent obstruction applies.  After the polynomial
`h₀⁷` factor this vanishing is automatic; the order-`61` head uses the
remaining pole-`14` obstruction. -/
theorem alignedSquareW1Peel_jet_eval_zero_of_poleTwentyOne610
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
        b5 b4 b3 b2 b1).eval a = 0 :=
  alignedSquare_poleTwentyOne_head_eval_zero610 a j h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1)
    rho hdegree hroot hclear hderiv

#print axioms alignedSquareW1Peel_jet_eval_zero_of_poleTwentyOne610

/-- Frozen `w₁ = 0`: parent pole-`21` obstruction on the specialised jet. -/
theorem alignedSquareW1Zero_jet_eval_zero_of_poleTwentyOne610
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 b1).eval a = 0 :=
  alignedSquare_poleTwentyOne_head_eval_zero610 a j h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
      b2 b1)
    rho hdegree hroot hclear hderiv

#print axioms alignedSquareW1Zero_jet_eval_zero_of_poleTwentyOne610

/-- `μ = 0` after the pole-`21` `q₈` peel: parent obstruction on the
specialised jet. -/
theorem alignedSquareMuZeroQ8_jet_eval_zero_of_poleTwentyOne610
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n)
        b7 b6 b5 b4 b3 b2 b1).eval a = 0 :=
  alignedSquare_poleTwentyOne_head_eval_zero610 a j h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n)
      b7 b6 b5 b4 b3 b2 b1)
    rho hdegree hroot hclear hderiv

#print axioms alignedSquareMuZeroQ8_jet_eval_zero_of_poleTwentyOne610

/-! ### Successive remaining-numerator peels, orders `61`–`68` -/

set_option maxHeartbeats 1600000000 in
/-- On `w₁ = h₀ w₁n`, cancel the polynomial `h₀⁷` and peel remaining
numerators of orders `61` through `68`.  Each step applies the
remaining-pole obstruction (the same lemma as
`alignedSquare_poleTwentyOne_head_eval_zero610`) and records one more
`h₀` factor.  After order `68` the jet is `h₀^{15}` times a pole-`6`
numerator.  This is not a closure. -/
theorem alignedSquareW1Peel_orders61to68_remaining_dvd
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q61 Q62 Q63 Q64 Q65 Q66 Q67 Q68 : k[X],
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 7 * Q61 ∧ Q61.eval a = 0 ∧
      Q61 = h0 * Q62 ∧ Q62.eval a = 0 ∧
      Q62 = h0 * Q63 ∧ Q63.eval a = 0 ∧
      Q63 = h0 * Q64 ∧ Q64.eval a = 0 ∧
      Q64 = h0 * Q65 ∧ Q65.eval a = 0 ∧
      Q65 = h0 * Q66 ∧ Q66.eval a = 0 ∧
      Q66 = h0 * Q67 ∧ Q67.eval a = 0 ∧
      Q67 = h0 * Q68 ∧ Q68.eval a = 0 ∧
      h0 ∣ Q68 := by
  obtain ⟨Q61, hjet, h61z, hdvd61⟩ :=
    alignedSquareW1Peel_order61_remaining_dvd h0 w1n e1 e3 a2 a1 a0 b8
      b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear hderiv
  have hclear14 :
      algebraMap k[X] (RatFunc k) Q61 =
        (algebraMap k[X] (RatFunc k) h0) ^ (13 + 1) * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q61 rho 7 14 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  obtain ⟨Q62, h62f, hclear13, h62z, _hdvd62⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q61 rho j a 13
      (by decide) hh0 hdegree hroot h61z hclear14 hderiv
  obtain ⟨Q63, h63f, hclear12, h63z, _hdvd63⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q62 rho j a 12
      (by decide) hh0 hdegree hroot h62z hclear13 hderiv
  obtain ⟨Q64, h64f, hclear11, h64z, _hdvd64⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q63 rho j a 11
      (by decide) hh0 hdegree hroot h63z hclear12 hderiv
  obtain ⟨Q65, h65f, hclear10, h65z, _hdvd65⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q64 rho j a 10
      (by decide) hh0 hdegree hroot h64z hclear11 hderiv
  obtain ⟨Q66, h66f, hclear9, h66z, _hdvd66⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q65 rho j a 9
      (by decide) hh0 hdegree hroot h65z hclear10 hderiv
  obtain ⟨Q67, h67f, hclear8, h67z, _hdvd67⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q66 rho j a 8
      (by decide) hh0 hdegree hroot h66z hclear9 hderiv
  obtain ⟨Q68, h68f, _hclear7, h68z, hdvd68⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q67 rho j a 7
      (by decide) hh0 hdegree hroot h67z hclear8 hderiv
  exact ⟨Q61, Q62, Q63, Q64, Q65, Q66, Q67, Q68, hjet, h61z, h62f, h62z,
    h63f, h63z, h64f, h64z, h65f, h65z, h66f, h66z, h67f, h67z, h68f,
    h68z, hdvd68⟩

#print axioms alignedSquareW1Peel_orders61to68_remaining_dvd

/-- Batch `h₀^{15}`-divisibility on the `w₁ = 0` peel through order
`68`.  Remaining pole `6`; next unused compact-numerator order `69`. -/
theorem alignedSquareW1Peel_orders61to68_pow_dvd
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ alignedSquareTowerBatchDivisibility610 ∣
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
        b5 b4 b3 b2 b1 := by
  obtain ⟨Q61, Q62, Q63, Q64, Q65, Q66, Q67, Q68, hjet, _h61z, h62f,
      _h62z, h63f, _h63z, h64f, _h64z, h65f, _h65z, h66f, _h66z, h67f,
      _h67z, h68f, _h68z, hdvd68⟩ :=
    alignedSquareW1Peel_orders61to68_remaining_dvd h0 w1n e1 e3 a2 a1 a0
      b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear hderiv
  obtain ⟨Q69, h69⟩ := hdvd68
  refine ⟨Q69, ?_⟩
  simp only [alignedSquareTowerBatchDivisibility610, hjet, h62f, h63f,
    h64f, h65f, h66f, h67f, h68f, h69]
  ring

#print axioms alignedSquareW1Peel_orders61to68_pow_dvd

set_option maxHeartbeats 1600000000 in
/-- Frozen `w₁ = 0`: the same remaining-numerator peel through order
`68`. -/
theorem alignedSquareW1Zero_orders61to68_remaining_dvd
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q61 Q62 Q63 Q64 Q65 Q66 Q67 Q68 : k[X],
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 7 * Q61 ∧ Q61.eval a = 0 ∧
      Q61 = h0 * Q62 ∧ Q62.eval a = 0 ∧
      Q62 = h0 * Q63 ∧ Q63.eval a = 0 ∧
      Q63 = h0 * Q64 ∧ Q64.eval a = 0 ∧
      Q64 = h0 * Q65 ∧ Q65.eval a = 0 ∧
      Q65 = h0 * Q66 ∧ Q66.eval a = 0 ∧
      Q66 = h0 * Q67 ∧ Q67.eval a = 0 ∧
      Q67 = h0 * Q68 ∧ Q68.eval a = 0 ∧
      h0 ∣ Q68 := by
  obtain ⟨Q61, hjet, h61z, hdvd61⟩ :=
    alignedSquareW1Zero_order61_remaining_dvd h0 e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear hderiv
  have hclear14 :
      algebraMap k[X] (RatFunc k) Q61 =
        (algebraMap k[X] (RatFunc k) h0) ^ (13 + 1) * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q61 rho 7 14 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  obtain ⟨Q62, h62f, hclear13, h62z, _hdvd62⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q61 rho j a 13
      (by decide) hh0 hdegree hroot h61z hclear14 hderiv
  obtain ⟨Q63, h63f, hclear12, h63z, _hdvd63⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q62 rho j a 12
      (by decide) hh0 hdegree hroot h62z hclear13 hderiv
  obtain ⟨Q64, h64f, hclear11, h64z, _hdvd64⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q63 rho j a 11
      (by decide) hh0 hdegree hroot h63z hclear12 hderiv
  obtain ⟨Q65, h65f, hclear10, h65z, _hdvd65⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q64 rho j a 10
      (by decide) hh0 hdegree hroot h64z hclear11 hderiv
  obtain ⟨Q66, h66f, hclear9, h66z, _hdvd66⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q65 rho j a 9
      (by decide) hh0 hdegree hroot h65z hclear10 hderiv
  obtain ⟨Q67, h67f, hclear8, h67z, _hdvd67⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q66 rho j a 8
      (by decide) hh0 hdegree hroot h66z hclear9 hderiv
  obtain ⟨Q68, h68f, _hclear7, h68z, hdvd68⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q67 rho j a 7
      (by decide) hh0 hdegree hroot h67z hclear8 hderiv
  exact ⟨Q61, Q62, Q63, Q64, Q65, Q66, Q67, Q68, hjet, h61z, h62f, h62z,
    h63f, h63z, h64f, h64z, h65f, h65z, h66f, h66z, h67f, h67z, h68f,
    h68z, hdvd68⟩

#print axioms alignedSquareW1Zero_orders61to68_remaining_dvd

theorem alignedSquareW1Zero_orders61to68_pow_dvd
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ alignedSquareTowerBatchDivisibility610 ∣
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 b1 := by
  obtain ⟨Q61, Q62, Q63, Q64, Q65, Q66, Q67, Q68, hjet, _h61z, h62f,
      _h62z, h63f, _h63z, h64f, _h64z, h65f, _h65z, h66f, _h66z, h67f,
      _h67z, h68f, _h68z, hdvd68⟩ :=
    alignedSquareW1Zero_orders61to68_remaining_dvd h0 e1 e3 a2 a1 a0 b8
      b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear hderiv
  obtain ⟨Q69, h69⟩ := hdvd68
  refine ⟨Q69, ?_⟩
  simp only [alignedSquareTowerBatchDivisibility610, hjet, h62f, h63f,
    h64f, h65f, h66f, h67f, h68f, h69]
  ring

#print axioms alignedSquareW1Zero_orders61to68_pow_dvd

set_option maxHeartbeats 1600000000 in
/-- Complement peel: orders `61`–`63` vanish identically, then remaining
numerators of orders `64` through `68` peel.  Same terminal
`h₀^{15}`-divisibility. -/
theorem alignedSquareW1Complement_orders64to68_remaining_dvd
    (h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b)
            (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q64 Q65 Q66 Q67 Q68 : k[X],
      alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b)
          (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 10 * Q64 ∧ Q64.eval a = 0 ∧
      Q64 = h0 * Q65 ∧ Q65.eval a = 0 ∧
      Q65 = h0 * Q66 ∧ Q66.eval a = 0 ∧
      Q66 = h0 * Q67 ∧ Q67.eval a = 0 ∧
      Q67 = h0 * Q68 ∧ Q68.eval a = 0 ∧
      h0 ∣ Q68 := by
  obtain ⟨Q64, hjet, h64z, hdvd64⟩ :=
    alignedSquareW1Complement_order64_remaining_dvd h0 w1n e1b e3b a2b a1
      a0 b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear hderiv
  have hclear11 :
      algebraMap k[X] (RatFunc k) Q64 =
        (algebraMap k[X] (RatFunc k) h0) ^ (10 + 1) * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q64 rho 10 11 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 10 + 11 := rfl
        rw [hpow] at hclear
        simpa [hjet] using hclear)
  obtain ⟨Q65, h65f, hclear10, h65z, _hdvd65⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q64 rho j a 10
      (by decide) hh0 hdegree hroot h64z hclear11 hderiv
  obtain ⟨Q66, h66f, hclear9, h66z, _hdvd66⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q65 rho j a 9
      (by decide) hh0 hdegree hroot h65z hclear10 hderiv
  obtain ⟨Q67, h67f, hclear8, h67z, _hdvd67⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q66 rho j a 8
      (by decide) hh0 hdegree hroot h66z hclear9 hderiv
  obtain ⟨Q68, h68f, _hclear7, h68z, hdvd68⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q67 rho j a 7
      (by decide) hh0 hdegree hroot h67z hclear8 hderiv
  exact ⟨Q64, Q65, Q66, Q67, Q68, hjet, h64z, h65f, h65z, h66f, h66z,
    h67f, h67z, h68f, h68z, hdvd68⟩

#print axioms alignedSquareW1Complement_orders64to68_remaining_dvd

theorem alignedSquareW1Complement_orders64to68_pow_dvd
    (h0 w1n e1b e3b a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b)
            (h0 * e3b) (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ alignedSquareTowerBatchDivisibility610 ∣
      alignedSquareJetQuotient610 h0 (h0 * w1n) (h0 * e1b) (h0 * e3b)
        (h0 * a2b) a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 := by
  obtain ⟨Q64, Q65, Q66, Q67, Q68, hjet, _h64z, h65f, _h65z, h66f, _h66z,
      h67f, _h67z, h68f, _h68z, hdvd68⟩ :=
    alignedSquareW1Complement_orders64to68_remaining_dvd h0 w1n e1b e3b
      a2b a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear
      hderiv
  obtain ⟨Q69, h69⟩ := hdvd68
  refine ⟨Q69, ?_⟩
  simp only [alignedSquareTowerBatchDivisibility610, hjet, h65f, h66f,
    h67f, h68f, h69]
  ring

#print axioms alignedSquareW1Complement_orders64to68_pow_dvd

set_option maxHeartbeats 1600000000 in
/-- `μ = 0` after the `q₈` peel: the specialised jet is `h₀` times
`alignedSquareMuZeroQ8QuotOne610`.  Cancelling that factor leaves a
pole-`20` numerator; remaining-numerator peels then run through the
order-`68` remaining numerator.  Named mixed coefficients of orders
`61`–`68` are the `h^{k-61}` terms of the order-`61` tower; their
vanishing as frozen heads is the mixin of previous quotients, recorded
conditionally below. -/
theorem alignedSquareMuZeroQ8_orders55to68_remaining_dvd
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q55 Q56 Q57 Q58 Q59 Q60 Q61 Q62 Q63 Q64 Q65 Q66 Q67 Q68 : k[X],
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 * Q55 ∧ Q55.eval a = 0 ∧
      Q55 = h0 * Q56 ∧ Q56.eval a = 0 ∧
      Q56 = h0 * Q57 ∧ Q57.eval a = 0 ∧
      Q57 = h0 * Q58 ∧ Q58.eval a = 0 ∧
      Q58 = h0 * Q59 ∧ Q59.eval a = 0 ∧
      Q59 = h0 * Q60 ∧ Q60.eval a = 0 ∧
      Q60 = h0 * Q61 ∧ Q61.eval a = 0 ∧
      Q61 = h0 * Q62 ∧ Q62.eval a = 0 ∧
      Q62 = h0 * Q63 ∧ Q63.eval a = 0 ∧
      Q63 = h0 * Q64 ∧ Q64.eval a = 0 ∧
      Q64 = h0 * Q65 ∧ Q65.eval a = 0 ∧
      Q65 = h0 * Q66 ∧ Q66.eval a = 0 ∧
      Q66 = h0 * Q67 ∧ Q67.eval a = 0 ∧
      Q67 = h0 * Q68 ∧ Q68.eval a = 0 ∧
      h0 ∣ Q68 := by
  let Q55 : k[X] :=
    alignedSquareMuZeroQ8QuotOne610 h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5
      b4 b3 b2 b1
  have hjet :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 * Q55 := by
    simpa [Q55] using
      alignedSquareJetQuotient610_muZeroQ8_factor_one h0 w1 e1n e3 a2 a1
        a0 b8n b7 b6 b5 b4 b3 b2 b1
  have hclear20 :
      algebraMap k[X] (RatFunc k) Q55 =
        (algebraMap k[X] (RatFunc k) h0) ^ (19 + 1) * rho :=
    alignedSquare_algebraMap_cancel_pow610 h0 Q55 rho 1 20 hh0
      (by
        have hpow : alignedSquareRemainingPole610 = 1 + 20 := rfl
        rw [hpow] at hclear
        have hjet1 :
            alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
                (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
              h0 ^ 1 * Q55 := by
          simpa [pow_one] using hjet
        simpa [hjet1] using hclear)
  have h55z : Q55.eval a = 0 :=
    alignedSquare_localLinearPole_head_eval_zero610 20 (by decide) a j
      h0 Q55 rho hdegree hroot hclear20 hderiv
  obtain ⟨Q56, h56f, hclear19, h56z, _hdvd56⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q55 rho j a 19
      (by decide) hh0 hdegree hroot h55z hclear20 hderiv
  obtain ⟨Q57, h57f, hclear18, h57z, _hdvd57⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q56 rho j a 18
      (by decide) hh0 hdegree hroot h56z hclear19 hderiv
  obtain ⟨Q58, h58f, hclear17, h58z, _hdvd58⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q57 rho j a 17
      (by decide) hh0 hdegree hroot h57z hclear18 hderiv
  obtain ⟨Q59, h59f, hclear16, h59z, _hdvd59⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q58 rho j a 16
      (by decide) hh0 hdegree hroot h58z hclear17 hderiv
  obtain ⟨Q60, h60f, hclear15, h60z, _hdvd60⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q59 rho j a 15
      (by decide) hh0 hdegree hroot h59z hclear16 hderiv
  obtain ⟨Q61, h61f, hclear14, h61z, _hdvd61⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q60 rho j a 14
      (by decide) hh0 hdegree hroot h60z hclear15 hderiv
  obtain ⟨Q62, h62f, hclear13, h62z, _hdvd62⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q61 rho j a 13
      (by decide) hh0 hdegree hroot h61z hclear14 hderiv
  obtain ⟨Q63, h63f, hclear12, h63z, _hdvd63⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q62 rho j a 12
      (by decide) hh0 hdegree hroot h62z hclear13 hderiv
  obtain ⟨Q64, h64f, hclear11, h64z, _hdvd64⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q63 rho j a 11
      (by decide) hh0 hdegree hroot h63z hclear12 hderiv
  obtain ⟨Q65, h65f, hclear10, h65z, _hdvd65⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q64 rho j a 10
      (by decide) hh0 hdegree hroot h64z hclear11 hderiv
  obtain ⟨Q66, h66f, hclear9, h66z, _hdvd66⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q65 rho j a 9
      (by decide) hh0 hdegree hroot h65z hclear10 hderiv
  obtain ⟨Q67, h67f, hclear8, h67z, _hdvd67⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q66 rho j a 8
      (by decide) hh0 hdegree hroot h66z hclear9 hderiv
  obtain ⟨Q68, h68f, _hclear7, h68z, hdvd68⟩ :=
    alignedSquare_remainingNumerator_succ_dvd610 h0 Q67 rho j a 7
      (by decide) hh0 hdegree hroot h67z hclear8 hderiv
  exact ⟨Q55, Q56, Q57, Q58, Q59, Q60, Q61, Q62, Q63, Q64, Q65, Q66, Q67,
    Q68, hjet, h55z, h56f, h56z, h57f, h57z, h58f, h58z, h59f, h59z,
    h60f, h60z, h61f, h61z, h62f, h62z, h63f, h63z, h64f, h64z, h65f,
    h65z, h66f, h66z, h67f, h67z, h68f, h68z, hdvd68⟩

#print axioms alignedSquareMuZeroQ8_orders55to68_remaining_dvd

theorem alignedSquareMuZeroQ8_orders61to68_pow_dvd
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ alignedSquareTowerBatchDivisibility610 ∣
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
        (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 := by
  obtain ⟨Q55, Q56, Q57, Q58, Q59, Q60, Q61, Q62, Q63, Q64, Q65, Q66, Q67,
      Q68, hjet, _h55z, h56f, _h56z, h57f, _h57z, h58f, _h58z, h59f,
      _h59z, h60f, _h60z, h61f, _h61z, h62f, _h62z, h63f, _h63z, h64f,
      _h64z, h65f, _h65z, h66f, _h66z, h67f, _h67z, h68f, _h68z,
      hdvd68⟩ :=
    alignedSquareMuZeroQ8_orders55to68_remaining_dvd h0 w1 e1n e3 a2 a1
      a0 b8n b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree hroot hclear hderiv
  obtain ⟨Q69, h69⟩ := hdvd68
  refine ⟨Q69, ?_⟩
  simp only [alignedSquareTowerBatchDivisibility610, hjet, h56f, h57f,
    h58f, h59f, h60f, h61f, h62f, h63f, h64f, h65f, h66f, h67f, h68f,
    h69]
  ring

#print axioms alignedSquareMuZeroQ8_orders61to68_pow_dvd

/-! ### Named `h^{k-61}` coefficients versus remaining-pole heads

Each named coefficient is the `h^{k-61}` term of the order-`61` tower
on that limb.  If the remaining numerator after cancelling `h₀^{k-54}`
evaluates to that named coefficient, the remaining-pole obstruction
forces it to vanish.  On the `w₁` peel this identification holds
unconditionally at order `61`; later orders mix in polynomial quotients
of previous heads.  On `μ = 0` the same identification at order `61`
requires the order-`55`–`60` prefix to have been peeled.
-/

/-- Named `h^0` coefficient on the `w₁` peel, forced if it is
the remaining pole-`14` head after cancelling `h₀^7`. -/
theorem alignedSquareW1PeelOrder61610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 7 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder61610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder61610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (7 + 14) * rho := by
    have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder61610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a)) 7 14 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder61610_zero_of_remaining_pole

/-- Named `h^1` coefficient on the `w₁` peel, forced if it is
the remaining pole-`13` head after cancelling `h₀^8`. -/
theorem alignedSquareW1PeelOrder62610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 8 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder62610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder62610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (8 + 13) * rho := by
    have hpow : alignedSquareRemainingPole610 = 8 + 13 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder62610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a)) 8 13 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder62610_zero_of_remaining_pole

/-- Named `h^2` coefficient on the `w₁` peel, forced if it is
the remaining pole-`12` head after cancelling `h₀^9`. -/
theorem alignedSquareW1PeelOrder63610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 9 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder63610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder63610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (9 + 12) * rho := by
    have hpow : alignedSquareRemainingPole610 = 9 + 12 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder63610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a)) 9 12 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder63610_zero_of_remaining_pole

/-- Named `h^3` coefficient on the `w₁` peel, forced if it is
the remaining pole-`11` head after cancelling `h₀^10`. -/
theorem alignedSquareW1PeelOrder64610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 10 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder64610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder64610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (10 + 11) * rho := by
    have hpow : alignedSquareRemainingPole610 = 10 + 11 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder64610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a)) 10 11 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder64610_zero_of_remaining_pole

/-- Named `h^4` coefficient on the `w₁` peel, forced if it is
the remaining pole-`10` head after cancelling `h₀^11`. -/
theorem alignedSquareW1PeelOrder65610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 11 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder65610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder65610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (11 + 10) * rho := by
    have hpow : alignedSquareRemainingPole610 = 11 + 10 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder65610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a)) 11 10 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder65610_zero_of_remaining_pole

/-- Named `h^5` coefficient on the `w₁` peel, forced if it is
the remaining pole-`9` head after cancelling `h₀^12`. -/
theorem alignedSquareW1PeelOrder66610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 12 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder66610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder66610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (12 + 9) * rho := by
    have hpow : alignedSquareRemainingPole610 = 12 + 9 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder66610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a)) 12 9 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder66610_zero_of_remaining_pole

/-- Named `h^6` coefficient on the `w₁` peel, forced if it is
the remaining pole-`8` head after cancelling `h₀^13`. -/
theorem alignedSquareW1PeelOrder67610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 13 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder67610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder67610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (13 + 8) * rho := by
    have hpow : alignedSquareRemainingPole610 = 13 + 8 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder67610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a)) 13 8 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder67610_zero_of_remaining_pole

/-- Named `h^7` coefficient on the `w₁` peel, forced if it is
the remaining pole-`7` head after cancelling `h₀^14`. -/
theorem alignedSquareW1PeelOrder68610_zero_of_remaining_pole
    (h0 w1n e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
          b5 b4 b3 b2 b1 =
        h0 ^ 14 * Q)
    (hhead : Q.eval a = alignedSquareW1PeelOrder68610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1PeelOrder68610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8
            b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (14 + 7) * rho := by
    have hpow : alignedSquareRemainingPole610 = 14 + 7 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 (h0 * w1n) e1 e3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareW1PeelOrder68610 (w1n.eval a) (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a)) 14 7 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1PeelOrder68610_zero_of_remaining_pole

theorem alignedSquareW1ZeroOrder61610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 7 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder61610 (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder61610 (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (7 + 14) * rho := by
    have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
      b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder61610 (e1.eval a) (e3.eval a) (a2.eval a) (b8.eval a)) 7 14 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder61610_zero_of_remaining_pole

theorem alignedSquareW1ZeroOrder62610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 8 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder62610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder62610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (8 + 13) * rho := by
    have hpow : alignedSquareRemainingPole610 = 8 + 13 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
      b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder62610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a)) 8 13 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder62610_zero_of_remaining_pole

theorem alignedSquareW1ZeroOrder63610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 9 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder63610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder63610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (9 + 12) * rho := by
    have hpow : alignedSquareRemainingPole610 = 9 + 12 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
      b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder63610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (b8.eval a) (b7.eval a)) 9 12 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder63610_zero_of_remaining_pole

theorem alignedSquareW1ZeroOrder64610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 10 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder64610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder64610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (10 + 11) * rho := by
    have hpow : alignedSquareRemainingPole610 = 10 + 11 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
      b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder64610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a)) 10 11 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder64610_zero_of_remaining_pole

theorem alignedSquareW1ZeroOrder65610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 11 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder65610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder65610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (11 + 10) * rho := by
    have hpow : alignedSquareRemainingPole610 = 11 + 10 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
      b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder65610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8.eval a) (b7.eval a) (b6.eval a) (b5.eval a)) 11 10 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder65610_zero_of_remaining_pole

theorem alignedSquareW1ZeroOrder66610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 12 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder66610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder66610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (12 + 9) * rho := by
    have hpow : alignedSquareRemainingPole610 = 12 + 9 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
      b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder66610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a)) 12 9 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder66610_zero_of_remaining_pole

theorem alignedSquareW1ZeroOrder67610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 13 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder67610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder67610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (13 + 8) * rho := by
    have hpow : alignedSquareRemainingPole610 = 13 + 8 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
      b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder67610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b6.eval a) (b5.eval a) (b4.eval a)) 13 8 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder67610_zero_of_remaining_pole

theorem alignedSquareW1ZeroOrder68610_zero_of_remaining_pole
    (h0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
          b2 b1 =
        h0 ^ 14 * Q)
    (hhead : Q.eval a = alignedSquareW1ZeroOrder68610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareW1ZeroOrder68610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5
            b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (14 + 7) * rho := by
    have hpow : alignedSquareRemainingPole610 = 14 + 7 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 0 e1 e3 a2 a1 a0 b8 b7 b6 b5 b4 b3
      b2 b1)
    Q rho j a (alignedSquareW1ZeroOrder68610 (e1.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a)) 14 7 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareW1ZeroOrder68610_zero_of_remaining_pole

theorem alignedSquareMuZeroQ8Order61610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 7 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order61610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order61610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (7 + 14) * rho := by
    have hpow : alignedSquareRemainingPole610 = 7 + 14 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n)
      b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order61610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a)) 7 14 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order61610_zero_of_remaining_pole

theorem alignedSquareMuZeroQ8Order62610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 8 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order62610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order62610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (8 + 13) * rho := by
    have hpow : alignedSquareRemainingPole610 = 8 + 13 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n)
      b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order62610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a)) 8 13 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order62610_zero_of_remaining_pole

theorem alignedSquareMuZeroQ8Order63610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 9 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order63610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order63610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (9 + 12) * rho := by
    have hpow : alignedSquareRemainingPole610 = 9 + 12 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n)
      b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order63610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a)) 9 12 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order63610_zero_of_remaining_pole

theorem alignedSquareMuZeroQ8Order64610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 10 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order64610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order64610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (10 + 11) * rho := by
    have hpow : alignedSquareRemainingPole610 = 10 + 11 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n)
      b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order64610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a)) 10 11 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order64610_zero_of_remaining_pole

theorem alignedSquareMuZeroQ8Order65610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 11 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order65610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order65610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (11 + 10) * rho := by
    have hpow : alignedSquareRemainingPole610 = 11 + 10 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n)
      b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order65610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b8n.eval a)) 11 10 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order65610_zero_of_remaining_pole

theorem alignedSquareMuZeroQ8Order66610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 12 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order66610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order66610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (12 + 9) * rho := by
    have hpow : alignedSquareRemainingPole610 = 12 + 9 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n)
      b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order66610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a)) 12 9 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order66610_zero_of_remaining_pole

theorem alignedSquareMuZeroQ8Order67610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 13 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order67610 (w1.eval a) (e1n.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b8n.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order67610 (w1.eval a) (e1n.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b8n.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (13 + 8) * rho := by
    have hpow : alignedSquareRemainingPole610 = 13 + 8 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n)
      b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order67610 (w1.eval a) (e1n.eval a) (e3.eval a) (a1.eval a) (a0.eval a) (b8n.eval a)) 13 8 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order67610_zero_of_remaining_pole

theorem alignedSquareMuZeroQ8Order68610_zero_of_remaining_pole
    (h0 w1 e1n e3 a2 a1 a0 b8n b7 b6 b5 b4 b3 b2 b1 Q : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact :
      alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
          (h0 * b8n) b7 b6 b5 b4 b3 b2 b1 =
        h0 ^ 14 * Q)
    (hhead : Q.eval a = alignedSquareMuZeroQ8Order68610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a))
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ alignedSquareRemainingPole610 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    alignedSquareMuZeroQ8Order68610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a) = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0
            (h0 * b8n) b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ (14 + 7) * rho := by
    have hpow : alignedSquareRemainingPole610 = 14 + 7 := rfl
    rwa [hpow] at hclear
  exact alignedSquare_remainingHead_eval_zero610 h0
    (alignedSquareJetQuotient610 h0 w1 (h0 * e1n) e3 a2 a1 a0 (h0 * b8n)
      b7 b6 b5 b4 b3 b2 b1)
    Q rho j a (alignedSquareMuZeroQ8Order68610 (w1.eval a) (e1n.eval a) (e3.eval a) (a2.eval a) (a1.eval a) (a0.eval a) (b7.eval a) (b6.eval a) (b5.eval a) (b4.eval a) (b3.eval a) (b2.eval a) (b1.eval a)) 14 7 (by decide) hh0 hdegree hroot hfact
    hhead hclear_mn hderiv

#print axioms alignedSquareMuZeroQ8Order68610_zero_of_remaining_pole

end AlignedSquareTowerHeads610

end Max11DegreeRoutes
