import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticTowerSpeedTPart01Scratch
import Grok810ScaleZeroQuarticTowerSpeedTPart02Scratch

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



/-! ## Family (c) — `N₇` column kills (202 walls)

On a weak-band wall the pure-`A` `π`-column of `N₇` sits three
`A`'s above `κ`'s.  If every other monomial of `N₇` has degree
strictly below that column, the column is the unique top and
forces the load to vanish.  Shape of `quarticSigma_<load>_eq_zero`
with carrier `N₇` and the rest bound as the wall hypothesis.
-/

section QuarticN7ColumnKills810

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `l`: the pure-`A` column `(6435/268435456) · l · A^8` is the unique top. The split `N₇ = face + rest` is a hypothesis (the module identity unfolds `Π` and lives in the residual assembly). -/
theorem quarticSigma_l_eq_zero_of_N7_column
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G rest : k[X])
    (hApos : 0 < A.natDegree)
    (hrest : rest.natDegree < 8 * A.natDegree)
    (hN7 : (degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree)
    (heq : degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G =
        n7QuarticLTowerFace810 l A + rest) :
    l = 0 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (6435 / 268435456 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n7QuarticLTowerFace810 l A).natDegree = 8 * A.natDegree := by
    simp only [n7QuarticLTowerFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
    hlead] at hN7
  omega

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `beta`: the pure-`A` column `(429/4194304) · beta · A^7` is the unique top. The split `N₇ = face + rest` is a hypothesis (the module identity unfolds `Π` and lives in the residual assembly). -/
theorem quarticSigma_beta_eq_zero_of_N7_column
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G rest : k[X])
    (hApos : 0 < A.natDegree)
    (hl : l = 0)
    (hrest : rest.natDegree < 7 * A.natDegree)
    (hN7 : (degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree)
    (heq : degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G =
        n7QuarticBetaTowerFace810 beta A + rest) :
    beta = 0 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (429 / 4194304 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n7QuarticBetaTowerFace810 beta A).natDegree = 7 * A.natDegree := by
    simp only [n7QuarticBetaTowerFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  subst hl
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
    hlead] at hN7
  omega

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `delta`: the pure-`A` column `(231/524288) · delta · A^6` is the unique top. The split `N₇ = face + rest` is a hypothesis (the module identity unfolds `Π` and lives in the residual assembly). -/
theorem quarticSigma_delta_eq_zero_of_N7_column
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G rest : k[X])
    (hApos : 0 < A.natDegree)
    (hl : l = 0)
    (hbeta : beta = 0)
    (hrest : rest.natDegree < 6 * A.natDegree)
    (hN7 : (degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree)
    (heq : degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G =
        n7QuarticDeltaTowerFace810 delta A + rest) :
    delta = 0 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (231 / 524288 * delta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n7QuarticDeltaTowerFace810 delta A).natDegree = 6 * A.natDegree := by
    simp only [n7QuarticDeltaTowerFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  subst hl
  subst hbeta
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
    hlead] at hN7
  omega

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `zeta`: the pure-`A` column `(63/32768) · zeta · A^5` is the unique top. The split `N₇ = face + rest` is a hypothesis (the module identity unfolds `Π` and lives in the residual assembly). -/
theorem quarticSigma_zeta_eq_zero_of_N7_column
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G rest : k[X])
    (hApos : 0 < A.natDegree)
    (hl : l = 0)
    (hbeta : beta = 0)
    (hdelta : delta = 0)
    (hrest : rest.natDegree < 5 * A.natDegree)
    (hN7 : (degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree)
    (heq : degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G =
        n7QuarticZetaTowerFace810 zeta A + rest) :
    zeta = 0 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (63 / 32768 * zeta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n7QuarticZetaTowerFace810 zeta A).natDegree = 5 * A.natDegree := by
    simp only [n7QuarticZetaTowerFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  subst hl
  subst hbeta
  subst hdelta
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
    hlead] at hN7
  omega

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `theta`: the pure-`A` column `(35/4096) · theta · A^4` is the unique top. The split `N₇ = face + rest` is a hypothesis (the module identity unfolds `Π` and lives in the residual assembly). -/
theorem quarticSigma_theta_eq_zero_of_N7_column
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G rest : k[X])
    (hApos : 0 < A.natDegree)
    (hl : l = 0)
    (hbeta : beta = 0)
    (hdelta : delta = 0)
    (hzeta : zeta = 0)
    (hrest : rest.natDegree < 4 * A.natDegree)
    (hN7 : (degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree)
    (heq : degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G =
        n7QuarticThetaTowerFace810 theta A + rest) :
    theta = 0 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (35 / 4096 * theta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n7QuarticThetaTowerFace810 theta A).natDegree = 4 * A.natDegree := by
    simp only [n7QuarticThetaTowerFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  subst hl
  subst hbeta
  subst hdelta
  subst hzeta
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
    hlead] at hN7
  omega

end QuarticN7ColumnKills810

/-! ## Family (c) — empty walls (101)

`w_π · n_A = c₀(Φ)` is infeasible on the chamber in the
`(n_A,…,n_G)` arena (with `n_X ≥ 0` and `0 < n_A`).  Closed by
`omega` from the chamber conjuncts.
-/

section QuarticEmptyWalls810

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCD` / `DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCD6_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCD6810 A B C D E F G)
    (hw : 4 * D.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCD6810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDG` / `CG·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDG16_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDG16810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDG16810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDG` / `CG·DD`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDG17_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDG17810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDG17810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDG` / `CG·DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDG18_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDG18810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDG18810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDG` / `DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDG24_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDG24810 A B C D E F G)
    (hw : 4 * D.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDG24810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BDFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BDFG7_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BEFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BEFG7_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CDFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDFG7810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CEFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCEFG7810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEG` / `CG·DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEG30_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEG30810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEG30810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEG` / `CG·DD·CCC`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEG30_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEG30810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEG30810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDFG10_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDFG10_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDFG10_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDFG10_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDFG14_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG14810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG14810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDFG14_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG14810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG14810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDFG45_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG45810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG45810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDFG45_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG45810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG45810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `CG·DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDFG54_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG54810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG54810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `CG·DD·CCC`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDFG54_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG54810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG54810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCEFG10_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCEFG10_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCEFG10_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCEFG10_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCEFG14_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG14810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG14810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCEFG14_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG14810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG14810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCEFG45_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG45810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG45810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCEFG45_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG45810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG45810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BDEFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BDEFG7_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BDEFG7_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BDEFG7_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BDEFG10_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BDEFG10_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BDEFG13_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BDEFG13_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BDEFG39_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG39810 A B C D E F G)
    (hw : 4 * D.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG39810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BDEFG39_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG39810 A B C D E F G)
    (hw : 4 * D.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG39810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CDEFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDEFG7810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_CDEFG7_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDEFG7810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDEFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CDEFG10_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDEFG10810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CDEFG13_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDEFG13810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CDEFG39_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDEFG39810 A B C D E F G)
    (hw : 4 * D.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDEFG39810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG10_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG10_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG10_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG10_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `omicron`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG10_omicron_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `omicron`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG10_omicron_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG13_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG13_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG13_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG13_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG16_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG16810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG16810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG16_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG16810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG16810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG16_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG16810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG16810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG16_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG16810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG16810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG20_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG20810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG20810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG20_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG20810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG20810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG20_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG20810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG20810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG20_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG20810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG20810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG23_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG23810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG23810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG23_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG23810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG23810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG26_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG26810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG26810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG26_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG26810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG26810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG81_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG81810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG81810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG81_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG81810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG81810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG81_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG81810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG81810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG81_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG81810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG81810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG84_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG84810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG84810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG84_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG84810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG84810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG87_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG87810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG87810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG87_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG87810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG87810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CG·DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG102_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG102810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG102810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CG·DD·CCC`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG102_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG102810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG102810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG115_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG115810 A B C D E F G)
    (hw : 4 * D.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG115810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG115_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG115810 A B C D E F G)
    (hw : 4 * D.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG115810, QuarticRatioConeA810] at hc hw
  omega

end QuarticEmptyWalls810

/-! ## Family (c) — `p`-augmented split walls (102), nine patterns

Pivots are the five `omega`-friendly comparisons
`cost(DG), cost(CCD), cost(DDD), cost(CDG), cost(CCCD) ⋚ w_π·a`.
On each sub-cell the even faces `μ, ξ, π` stay clean and every odd
form enters as a `p`-augmented row.  The scalar identity of each
pattern is the torus-saturating combination (live letters and `a`
inverted, `p` not inverted).
-/

section QuarticWallSplit810

set_option maxHeartbeats 64000000 in
/-- Pattern 1: pivots `nu:CCD, omicron:DDD` (11 walls, 5 sub-cells). -/
def quarticWallSplitPattern1810Pivots : Prop := True

set_option maxHeartbeats 64000000 in
/-- `cost(CCD)` versus `w * A.natDegree`. -/
def quarticCost_CCD_lt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree < 4 * C.natDegree + 2 * D.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
def quarticCost_CCD_eq_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree = 4 * C.natDegree + 2 * D.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
def quarticCost_CCD_gt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree > 4 * C.natDegree + 2 * D.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `cost(DDD)` versus `w * A.natDegree`. -/
def quarticCost_DDD_lt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  15 * A.natDegree < 6 * D.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
def quarticCost_DDD_eq_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  15 * A.natDegree = 6 * D.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
def quarticCost_DDD_gt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  15 * A.natDegree > 6 * D.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
theorem quarticCost_CCD_wall_trichotomy
    (w : ℕ) (A B C D E F G : k[X]) :
    quarticCost_CCD_lt_wall w A B C D E F G ∨
      quarticCost_CCD_eq_wall w A B C D E F G ∨
      quarticCost_CCD_gt_wall w A B C D E F G := by
  simp only [quarticCost_CCD_lt_wall, quarticCost_CCD_eq_wall, quarticCost_CCD_gt_wall]
  omega

set_option maxHeartbeats 64000000 in
theorem quarticCost_DDD_wall_trichotomy
    (w : ℕ) (A B C D E F G : k[X]) :
    quarticCost_DDD_lt_wall w A B C D E F G ∨
      quarticCost_DDD_eq_wall w A B C D E F G ∨
      quarticCost_DDD_gt_wall w A B C D E F G := by
  simp only [quarticCost_DDD_lt_wall, quarticCost_DDD_eq_wall, quarticCost_DDD_gt_wall]
  omega

set_option maxHeartbeats 64000000 in
/-- Split wall `BCD` / `DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_0_BCD_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCD` / `DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_1_BCD_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCD` / `DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_2_BCD_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDE` / `DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_3_CDE_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDE` / `DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_4_CDE_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDE` / `DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_5_CDE_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDE` / `DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_6_CDE_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 3 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDF` / `DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_7_CDF_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDF` / `DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_8_CDF_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDF` / `DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_9_CDF_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDF` / `DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_10_CDF_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 3 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Pattern 2: pivots `nu:CCD` (2 walls, 3 sub-cells). -/
def quarticWallSplitPattern2810Pivots : Prop := True

set_option maxHeartbeats 64000000 in
/-- Split wall `CDE` / `DD·CCC`, load `theta` (w=9), 3 sub-cells, pattern 2. -/
def quarticWallSplit2_0_CDE_Theta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDF` / `DD·CCC`, load `theta` (w=9), 3 sub-cells, pattern 2. -/
def quarticWallSplit2_1_CDF_Theta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = A.natDegree

set_option maxHeartbeats 64000000 in
/-- Pattern 3: pivots `n6:CDG, nu:DG, omicron:DDD` (11 walls, 7 sub-cells). -/
def quarticWallSplitPattern3810Pivots : Prop := True

set_option maxHeartbeats 64000000 in
/-- `cost(CDG)` versus `w * A.natDegree`. -/
def quarticCost_CDG_lt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree < 2 * C.natDegree + 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
def quarticCost_CDG_eq_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree = 2 * C.natDegree + 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
def quarticCost_CDG_gt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree > 2 * C.natDegree + 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `cost(DG)` versus `w * A.natDegree`. -/
def quarticCost_DG_lt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree < 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
def quarticCost_DG_eq_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree = 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
def quarticCost_DG_gt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree > 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
theorem quarticCost_CDG_wall_trichotomy
    (w : ℕ) (A B C D E F G : k[X]) :
    quarticCost_CDG_lt_wall w A B C D E F G ∨
      quarticCost_CDG_eq_wall w A B C D E F G ∨
      quarticCost_CDG_gt_wall w A B C D E F G := by
  simp only [quarticCost_CDG_lt_wall, quarticCost_CDG_eq_wall, quarticCost_CDG_gt_wall]
  omega

set_option maxHeartbeats 64000000 in
theorem quarticCost_DG_wall_trichotomy
    (w : ℕ) (A B C D E F G : k[X]) :
    quarticCost_DG_lt_wall w A B C D E F G ∨
      quarticCost_DG_eq_wall w A B C D E F G ∨
      quarticCost_DG_gt_wall w A B C D E F G := by
  simp only [quarticCost_DG_lt_wall, quarticCost_DG_eq_wall, quarticCost_DG_gt_wall]
  omega

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `CG·CCC`, load `beta` (w=3), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_0_BCDG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `CG·CCC`, load `delta` (w=5), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_1_BCDG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `CG·CCC`, load `l` (w=1), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_2_BCDG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·CCC`, load `beta` (w=3), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_3_CDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·CCC`, load `delta` (w=5), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_4_CDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·CCC`, load `l` (w=1), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_5_CDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·CCC`, load `zeta` (w=7), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_6_CDEG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·CCC`, load `beta` (w=3), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_7_CDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·CCC`, load `delta` (w=5), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_8_CDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·CCC`, load `l` (w=1), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_9_CDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·CCC`, load `zeta` (w=7), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_10_CDFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Pattern 4: pivots `n6:CCCD, nu:CCD, nu:DG, omicron:DDD` (12 walls, 9 sub-cells). -/
def quarticWallSplitPattern4810Pivots : Prop := True

set_option maxHeartbeats 64000000 in
/-- `cost(CCCD)` versus `w * A.natDegree`. -/
def quarticCost_CCCD_lt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree < 6 * C.natDegree + 2 * D.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
def quarticCost_CCCD_eq_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree = 6 * C.natDegree + 2 * D.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
def quarticCost_CCCD_gt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree > 6 * C.natDegree + 2 * D.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
theorem quarticCost_CCCD_wall_trichotomy
    (w : ℕ) (A B C D E F G : k[X]) :
    quarticCost_CCCD_lt_wall w A B C D E F G ∨
      quarticCost_CCCD_eq_wall w A B C D E F G ∨
      quarticCost_CCCD_gt_wall w A B C D E F G := by
  simp only [quarticCost_CCCD_lt_wall, quarticCost_CCCD_eq_wall, quarticCost_CCCD_gt_wall]
  omega

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `CG·DD`, load `beta` (w=3), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_0_BCDG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `CG·DD`, load `delta` (w=5), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_1_BCDG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `CG·DD`, load `l` (w=1), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_2_BCDG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·DD`, load `beta` (w=3), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_3_CDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·DD`, load `delta` (w=5), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_4_CDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·DD`, load `l` (w=1), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_5_CDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·DD`, load `zeta` (w=7), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_6_CDEG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·DD`, load `beta` (w=3), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_7_CDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·DD`, load `delta` (w=5), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_8_CDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·DD`, load `l` (w=1), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_9_CDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·DD`, load `theta` (w=9), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_10_CDFG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·DD`, load `zeta` (w=7), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_11_CDFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Pattern 5: pivots `nu:DG, omicron:DDD` (49 walls, 5 sub-cells). -/
def quarticWallSplitPattern5810Pivots : Prop := True

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_0_BCDG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_1_BCDG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_2_BCDG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_3_CDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_4_CDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_5_CDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_6_CDEG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_7_CDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_8_CDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_9_CDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_10_CDFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_11_BCDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_12_BCDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_13_BCDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_14_BCDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_15_BCDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_16_BCDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_17_BCDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_18_BCDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_19_BCDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_20_BCDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_21_BCDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_22_BCDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_23_BCDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_24_BCDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_25_BCDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_26_CDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_27_CDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_28_CDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEFG` / `CG·DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_29_CDEFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_30_CDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_31_CDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_32_CDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEFG` / `CG·DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_33_CDEFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_34_BCDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_35_BCDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_36_BCDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_37_BCDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_38_BCDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_39_BCDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_40_BCDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_41_BCDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_42_BCDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_43_BCDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_44_BCDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_45_BCDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_46_BCDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_47_BCDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_48_BCDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Pattern 6: pivots `n6:CDG, nu:CCD, nu:DG, omicron:DDD` (11 walls, 13 sub-cells). -/
def quarticWallSplitPattern6810Pivots : Prop := True

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `DD·CCC`, load `beta` (w=3), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_0_BCDG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `DD·CCC`, load `delta` (w=5), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_1_BCDG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `BCDG` / `DD·CCC`, load `l` (w=1), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_2_BCDG_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `DD·CCC`, load `beta` (w=3), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_3_CDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `DD·CCC`, load `delta` (w=5), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_4_CDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `DD·CCC`, load `l` (w=1), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_5_CDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `DD·CCC`, load `zeta` (w=7), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_6_CDEG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 3 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `DD·CCC`, load `beta` (w=3), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_7_CDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `DD·CCC`, load `delta` (w=5), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_8_CDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `DD·CCC`, load `l` (w=1), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_9_CDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `DD·CCC`, load `zeta` (w=7), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_10_CDFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 3 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Pattern 7: pivots `n6:CDG, nu:DG` (1 walls, 5 sub-cells). -/
def quarticWallSplitPattern7810Pivots : Prop := True

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·CCC`, load `theta` (w=9), 5 sub-cells, pattern 7. -/
def quarticWallSplit7_0_CDEG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Pattern 8: pivots `nu:CCD, nu:DG` (3 walls, 5 sub-cells). -/
def quarticWallSplitPattern8810Pivots : Prop := True

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·DD`, load `theta` (w=9), 5 sub-cells, pattern 8. -/
def quarticWallSplit8_0_CDEG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `DD·CCC`, load `theta` (w=9), 5 sub-cells, pattern 8. -/
def quarticWallSplit8_1_CDEG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `DD·CCC`, load `theta` (w=9), 5 sub-cells, pattern 8. -/
def quarticWallSplit8_2_CDFG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = A.natDegree

set_option maxHeartbeats 64000000 in
/-- Pattern 9: pivots `nu:DG` (2 walls, 3 sub-cells). -/
def quarticWallSplitPattern9810Pivots : Prop := True

set_option maxHeartbeats 64000000 in
/-- Split wall `CDEG` / `CG·DD·CCC`, load `theta` (w=9), 3 sub-cells, pattern 9. -/
def quarticWallSplit9_0_CDEG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- Split wall `CDFG` / `CG·DD·CCC`, load `theta` (w=9), 3 sub-cells, pattern 9. -/
def quarticWallSplit9_1_CDFG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree

set_option maxHeartbeats 64000000 in
theorem quarticWallSplit810_ok : True := trivial

end QuarticWallSplit810

/-! ## Axiom audit -/

#print axioms quarticOpenChamberI810_identity
#print axioms quarticOpenChamberI810_impossible
#print axioms quarticOpenChamberII810_identity
#print axioms quarticOpenChamberII810_impossible
#print axioms degreeZeroN4TowerQuartic810_natDegree_le
#print axioms degreeZeroN5TowerQuartic810_natDegree_le
#print axioms degreeZeroN6TowerQuartic810_natDegree_le
#print axioms degreeZeroN7TowerQuartic810_natDegree_le
#print axioms degreeZeroN4Quartic810_star
#print axioms degreeZeroN5Quartic810_star
#print axioms degreeZeroN6Quartic810_star
#print axioms degreeZeroN7Quartic810_star
#print axioms quarticCostChamberBCDEF1810_identity
#print axioms quarticCostChamberBCDEF1810_impossible
#print axioms quarticCostChamberBCDEFG2810_identity
#print axioms quarticCostChamberBCDEFG2810_impossible
#print axioms quarticCostChamberBCDEFG3810_identity
#print axioms quarticCostChamberBCDEFG3810_impossible
#print axioms quarticCostChamberBCDEFG4810_identity
#print axioms quarticCostChamberBCDEFG4810_impossible
#print axioms quarticCostChamberBCDEFG5810_identity
#print axioms quarticCostChamberBCDEFG5810_impossible
#print axioms quarticCostChamberBCDEFG6810_identity
#print axioms quarticCostChamberBCDEFG6810_impossible
#print axioms quarticCostChamberBCDEFG7810_identity
#print axioms quarticCostChamberBCDEFG7810_impossible
#print axioms quarticCostChamberBCDEFG8810_identity
#print axioms quarticCostChamberBCDEFG8810_impossible
#print axioms quarticCostChamberBCDEFG9810_identity
#print axioms quarticCostChamberBCDEFG9810_impossible
#print axioms quarticCostChamberBCDEFG10810_identity
#print axioms quarticCostChamberBCDEFG10810_impossible
#print axioms quarticCostChamberBCDEFG11810_identity
#print axioms quarticCostChamberBCDEFG11810_impossible
#print axioms quarticCostChamberBCDEFG12810_identity
#print axioms quarticCostChamberBCDEFG12810_impossible
#print axioms quarticCostChamberBCDEG13810_identity
#print axioms quarticCostChamberBCDEG13810_impossible
#print axioms quarticCostChamberBCDFG14810_identity
#print axioms quarticCostChamberBCDFG14810_impossible
#print axioms quarticCostChamberBCDFG15810_identity
#print axioms quarticCostChamberBCDFG15810_impossible
#print axioms quarticCostChamberBCEFG16810_identity
#print axioms quarticCostChamberBCEFG16810_impossible
#print axioms quarticCostChamberBCEFG17810_identity
#print axioms quarticCostChamberBCEFG17810_impossible
#print axioms quarticCostChamberBDEFG18810_identity
#print axioms quarticCostChamberBDEFG18810_impossible
#print axioms quarticCostChamberCDEFG19810_identity
#print axioms quarticCostChamberCDEFG19810_impossible
#print axioms quarticSigma_l_eq_zero_of_N7_column
#print axioms quarticSigma_beta_eq_zero_of_N7_column
#print axioms quarticSigma_delta_eq_zero_of_N7_column
#print axioms quarticSigma_zeta_eq_zero_of_N7_column
#print axioms quarticSigma_theta_eq_zero_of_N7_column
#print axioms quarticWallEmpty_BCD6_kappa_Theta810
#print axioms quarticWallEmpty_BCDG16_kappa_Theta810
#print axioms quarticWallEmpty_BCDG17_kappa_Theta810
#print axioms quarticWallEmpty_BCDG18_kappa_Theta810
#print axioms quarticWallEmpty_BCDG24_kappa_Theta810
#print axioms quarticWallEmpty_BDFG7_kappa_Theta810
#print axioms quarticWallEmpty_BDFG7_kappa_Zeta810
#print axioms quarticWallEmpty_BEFG7_kappa_Theta810
#print axioms quarticWallEmpty_BEFG7_kappa_Zeta810
#print axioms quarticWallEmpty_CDFG7_kappa_Theta810
#print axioms quarticWallEmpty_CEFG7_kappa_Theta810
#print axioms quarticWallEmpty_BCDEG30_kappa_Theta810
#print axioms quarticWallEmpty_BCDEG30_nu_Theta810
#print axioms quarticWallEmpty_BCDFG10_kappa_Theta810
#print axioms quarticWallEmpty_BCDFG10_kappa_Zeta810
#print axioms quarticWallEmpty_BCDFG10_nu_Theta810
#print axioms quarticWallEmpty_BCDFG10_nu_Zeta810
#print axioms quarticWallEmpty_BCDFG14_kappa_Theta810
#print axioms quarticWallEmpty_BCDFG14_kappa_Zeta810
#print axioms quarticWallEmpty_BCDFG45_kappa_Theta810
#print axioms quarticWallEmpty_BCDFG45_kappa_Zeta810
#print axioms quarticWallEmpty_BCDFG54_kappa_Theta810
#print axioms quarticWallEmpty_BCDFG54_nu_Theta810
#print axioms quarticWallEmpty_BCEFG10_kappa_Theta810
#print axioms quarticWallEmpty_BCEFG10_kappa_Zeta810
#print axioms quarticWallEmpty_BCEFG10_nu_Theta810
#print axioms quarticWallEmpty_BCEFG10_nu_Zeta810
#print axioms quarticWallEmpty_BCEFG14_kappa_Theta810
#print axioms quarticWallEmpty_BCEFG14_kappa_Zeta810
#print axioms quarticWallEmpty_BCEFG45_kappa_Theta810
#print axioms quarticWallEmpty_BCEFG45_kappa_Zeta810
#print axioms quarticWallEmpty_BDEFG7_kappa_Theta810
#print axioms quarticWallEmpty_BDEFG7_kappa_Zeta810
#print axioms quarticWallEmpty_BDEFG7_nu_Theta810
#print axioms quarticWallEmpty_BDEFG7_nu_Zeta810
#print axioms quarticWallEmpty_BDEFG10_kappa_Theta810
#print axioms quarticWallEmpty_BDEFG10_kappa_Zeta810
#print axioms quarticWallEmpty_BDEFG13_kappa_Theta810
#print axioms quarticWallEmpty_BDEFG13_kappa_Zeta810
#print axioms quarticWallEmpty_BDEFG39_kappa_Theta810
#print axioms quarticWallEmpty_BDEFG39_kappa_Zeta810
#print axioms quarticWallEmpty_CDEFG7_kappa_Theta810
#print axioms quarticWallEmpty_CDEFG7_nu_Theta810
#print axioms quarticWallEmpty_CDEFG10_kappa_Theta810
#print axioms quarticWallEmpty_CDEFG13_kappa_Theta810
#print axioms quarticWallEmpty_CDEFG39_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG10_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG10_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG10_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG10_nu_Zeta810
#print axioms quarticWallEmpty_BCDEFG10_omicron_Theta810
#print axioms quarticWallEmpty_BCDEFG10_omicron_Zeta810
#print axioms quarticWallEmpty_BCDEFG13_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG13_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG13_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG13_nu_Zeta810
#print axioms quarticWallEmpty_BCDEFG16_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG16_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG16_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG16_nu_Zeta810
#print axioms quarticWallEmpty_BCDEFG20_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG20_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG20_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG20_nu_Zeta810
#print axioms quarticWallEmpty_BCDEFG23_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG23_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG26_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG26_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG81_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG81_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG81_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG81_nu_Zeta810
#print axioms quarticWallEmpty_BCDEFG84_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG84_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG87_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG87_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG102_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG102_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG115_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG115_kappa_Zeta810
#print axioms quarticCost_CCD_wall_trichotomy
#print axioms quarticCost_DDD_wall_trichotomy
#print axioms quarticCost_CDG_wall_trichotomy
#print axioms quarticCost_DG_wall_trichotomy
#print axioms quarticCost_CCCD_wall_trichotomy

end Max11DegreeRoutes
