import Fable610ScaleTwoTerminalIntegralClosureScratch
import Fable610ScaleZeroTenthDefectScratch

/-! # Kappa integral bridge for the normalized `(6,10)` nonzero source

On the nonzero first face `H = h₀²` and `N = 5 p₅ H² - 3 q₉ = λ h₀⁹`
with `h₀.natDegree = 1`, the terminal integral closure spent the
degree-`5` first integral `ι`; the next genuinely unused integral row
is the degree-`4` first integral `κ`, whose construction needs the
degree-`6` `θ` tower.  The imported tenth-defect scratch states the
whole `κ` clearing on this exact ninth-power face:
`nonzeroFace610_eleventhDefectPowerRelation` proves the weight-`55`
numerator `localClearedEleventhDefect610` of `3761479876608 h⁵⁵ κ`
equal to `C kappaMu · h₀⁵⁵` from the same face and Keller hypotheses
this chain carries, so the `θ` data required on this scale-two chain
is exactly the imported one and none is restated.  The spent `ι`
packet is reused opaquely; its weight-`50` numerator is never
re-expanded.

On the fifteenth-face jet `p₅ = h₀⁵ w₁`, `p₄ = h₀³ a₄₁`,
`p₃ = h₀ p₃₁`, `q₈ = h₀⁷ s₁`, `q₇ = h₀⁵ u₁`, `q₆ = h₀⁴ b₆₂`,
`q₅ = h₀² q₅₂` the numerator factors exactly through `h₀⁴⁸`, seven
orders below the defect weight, with fully factored first head
`4837294080 p₃₁ (264 p₃₁² s₁ + 693 a₄₁ p₃₁ u₁ - 935 a₄₁ p₃₁²
- 432 a₄₁ q₄ - 270 p₃₁ q₅₂)`; the peel is
`head + h₀ · tail = C kappaMu · h₀⁷`, so the head vanishes at the
root, and modulo the tenth-face root laws alone it reduces,
chamber-free, to `a₄₁(a) p₃₁(a)³ = 0` — the honest split
`a₄₁(a) = 0 ∨ p₃₁(a) = 0`, a relation the `ι` heads never reached.

Combined with the four exact terminal-closure children: the two
`p₃₁(a) = 0` sibling children and the pinned `p₃₁(a) = 0` complement
child absorb the head through its overall `p₃₁` factor and are
retained unchanged.  On the `p₃₁(a) ≠ 0` child the split forces
`a₄₁(a) = 0`, the retained core `5 a₄₁² + 2 p₃₁ w₁ = 0` forces
`w₁(a) = 0`, and the remaining ground relations collapse to the pins
`80 p₂(a) = 9 λ p₃₁(a)`, `16 b₆₂(a) = -5 λ p₃₁(a)`, which subsume all
three original relations; the retained `ψ₂` value collapses to
`ψ₂(a) = -209952 λ p₁(a)`, under which the retained boundary
elimination reproduces exactly the inhomogeneous degree-`0` Keller row
`p₀'(a) q₁(a) - p₁(a) q₀'(a) = j`, the sole inhomogeneous constraint
left on that child.

No child is closed, because none is contradicted — the Keller boundary
relation lives on the fresh coordinates `p₀, p₁, q₀, q₁`.  The honest
residual is that single boundary relation with the preserved ground
constants `ζ, η, iotaK, kappaMu` and the open aligned face `N = 0`.
The next unused integral row is the degree-`3` first integral
(`lambdaResidual610`, eleventh-defect scratch); the next unused
aligned row on `N = 0` is the degree-`10` row.

No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

/-! ## Jet head and tail of the cleared `κ` defect -/

section BridgeKappaJet610

variable {R : Type*} [CommRing R]

/-- Order-`48` head of the jet-substituted cleared `κ` defect: the
coefficient of `h⁴⁸` after the fifteenth-face jet `p₅ = h⁵ w₁`,
`p₄ = h³ a₄₁`, `p₃ = h p₃₁`, `q₈ = h⁷ s₁`, `q₇ = h⁵ u₁`, `q₆ = h⁴ b₆₂`,
`q₅ = h² q₅₂` is substituted into `localClearedEleventhDefect610`,
kept in its fully factored form. -/
def bridgeKappaJetHead610 (a41 p31 s1 u1 q52 q4 : R) : R :=
  (4837294080 : R) * p31 *
    ((264 : R) * p31 ^ 2 * s1 + (693 : R) * a41 * p31 * u1 -
      (935 : R) * a41 * p31 ^ 2 - (432 : R) * a41 * q4 -
      (270 : R) * p31 * q52)

set_option maxHeartbeats 40000000 in
/-- Tail of the jet-substituted cleared `κ` defect above order `h⁴⁹`. -/
def bridgeKappaJetTail610
    (hh w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 lam : R) : R :=
    (1884529152000 : R) * w1 ^ 2 * p31 ^ 3
    - (4749013463040 : R) * w1 ^ 2 * p31 ^ 2 * u1
    + (1915568455680 : R) * w1 ^ 2 * p31 * q4
    + (15830044876800 : R) * w1 * a41 ^ 2 * p31 ^ 2
    - (9498026926080 : R) * w1 * a41 ^ 2 * p31 * u1
    + (1915568455680 : R) * w1 * a41 ^ 2 * q4
    - (10854887915520 : R) * w1 * a41 * p31 ^ 2 * s1
    + (4788921139200 : R) * w1 * a41 * p31 * q52
    + (2873352683520 : R) * w1 * p31 ^ 2 * b62
    - (6385228185600 : R) * w1 * p31 ^ 2 * p2
    + (6704489594880 : R) * w1 * p31 * u1 * p2
    - (2089711042560 : R) * w1 * p2 * q4
    + (4334417049600 : R) * a41 ^ 4 * p31
    - (791502243840 : R) * a41 ^ 4 * u1
    - (3618295971840 : R) * a41 ^ 3 * p31 * s1
    + (798153523200 : R) * a41 ^ 3 * q52
    + (2873352683520 : R) * a41 ^ 2 * p31 * b62
    - (13568609894400 : R) * a41 ^ 2 * p31 * p2
    + (3352244797440 : R) * a41 ^ 2 * u1 * p2
    + (7662273822720 : R) * a41 * p31 * s1 * p2
    - (2612138803200 : R) * a41 * q52 * p2
    - (3134566563840 : R) * p31 * b62 * p2
    + (4788921139200 : R) * p31 * p2 ^ 2
    - (1828497162240 : R) * u1 * p2 ^ 2
    + (1356860989440 : R) * lam * w1 * p31 ^ 3
    + (2035291484160 : R) * lam * a41 ^ 2 * p31 ^ 2
    - (1436676341760 : R) * lam * p31 ^ 2 * p2
    - (2889611366400 : R) * hh * w1 ^ 3 * a41 * p31 ^ 2
    + (12136367738880 : R) * hh * w1 ^ 3 * a41 * p31 * u1
    - (1809147985920 : R) * hh * w1 ^ 3 * a41 * q4
    + (6935067279360 : R) * hh * w1 ^ 3 * p31 ^ 2 * s1
    - (2261434982400 : R) * hh * w1 ^ 3 * p31 * q52
    - (15892862515200 : R) * hh * w1 ^ 2 * a41 ^ 3 * p31
    + (6068183869440 : R) * hh * w1 ^ 2 * a41 ^ 3 * u1
    + (20805201838080 : R) * hh * w1 ^ 2 * a41 ^ 2 * p31 * s1
    - (3392152473600 : R) * hh * w1 ^ 2 * a41 ^ 2 * q52
    - (8141165936640 : R) * hh * w1 ^ 2 * a41 * p31 * b62
    + (11307174912000 : R) * hh * w1 ^ 2 * a41 * p31 * p2
    - (9498026926080 : R) * hh * w1 ^ 2 * a41 * u1 * p2
    - (10854887915520 : R) * hh * w1 ^ 2 * p31 * s1 * p2
    + (2394460569600 : R) * hh * w1 ^ 2 * q52 * p2
    - (2889611366400 : R) * hh * w1 * a41 ^ 5
    + (3467533639680 : R) * hh * w1 * a41 ^ 4 * s1
    - (2713721978880 : R) * hh * w1 * a41 ^ 3 * b62
    + (10553363251200 : R) * hh * w1 * a41 ^ 3 * p2
    - (10854887915520 : R) * hh * w1 * a41 ^ 2 * s1 * p2
    + (5746705367040 : R) * hh * w1 * a41 * b62 * p2
    - (6385228185600 : R) * hh * w1 * a41 * p2 ^ 2
    - (1567283281920 : R) * hh * w1 * p31 * q3
    + (3831136911360 : R) * hh * w1 * s1 * p2 ^ 2
    - (783641640960 : R) * hh * a41 ^ 2 * q3
    + (4788921139200 : R) * hh * p31 ^ 2 * p1
    - (3656994324480 : R) * hh * p31 * u1 * p1
    + (1880739938304 : R) * hh * p2 * q3
    + (2507653251072 : R) * hh * p1 * q4
    - (7801950689280 : R) * hh * lam * w1 ^ 2 * a41 * p31 ^ 2
    - (5201300459520 : R) * hh * lam * w1 * a41 ^ 3 * p31
    + (8141165936640 : R) * hh * lam * w1 * a41 * p31 * p2
    - (260065022976 : R) * hh * lam * a41 ^ 5
    + (1356860989440 : R) * hh * lam * a41 ^ 3 * p2
    - (1436676341760 : R) * hh * lam * a41 * p2 ^ 2
    - (3491613734400 : R) * hh ^ 2 * w1 ^ 5 * p31 ^ 2
    - (2932955536896 : R) * hh ^ 2 * w1 ^ 5 * p31 * u1
    + (346753363968 : R) * hh ^ 2 * w1 ^ 5 * q4
    - (1745806867200 : R) * hh ^ 2 * w1 ^ 4 * a41 ^ 2 * p31
    - (7332388842240 : R) * hh ^ 2 * w1 ^ 4 * a41 ^ 2 * u1
    - (16759745925120 : R) * hh ^ 2 * w1 ^ 4 * a41 * p31 * s1
    + (2167208524800 : R) * hh ^ 2 * w1 ^ 4 * a41 * q52
    + (2600650229760 : R) * hh ^ 2 * w1 ^ 4 * p31 * b62
    + (5056819891200 : R) * hh ^ 2 * w1 ^ 4 * p31 * p2
    + (3034091934720 : R) * hh ^ 2 * w1 ^ 4 * u1 * p2
    + (4655484979200 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 4
    - (11173163950080 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 3 * s1
    + (5201300459520 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 2 * b62
    - (2889611366400 : R) * hh ^ 2 * w1 ^ 3 * a41 ^ 2 * p2
    + (13870134558720 : R) * hh ^ 2 * w1 ^ 3 * a41 * s1 * p2
    - (2713721978880 : R) * hh ^ 2 * w1 ^ 3 * b62 * p2
    - (1507623321600 : R) * hh ^ 2 * w1 ^ 3 * p2 ^ 2
    + (1436676341760 : R) * hh ^ 2 * w1 ^ 2 * a41 * q3
    - (12770456371200 : R) * hh ^ 2 * w1 * a41 * p31 * p1
    + (6704489594880 : R) * hh ^ 2 * w1 * a41 * u1 * p1
    + (7662273822720 : R) * hh ^ 2 * w1 * p31 * s1 * p1
    - (2612138803200 : R) * hh ^ 2 * w1 * q52 * p1
    - (4522869964800 : R) * hh ^ 2 * a41 ^ 3 * p1
    + (3831136911360 : R) * hh ^ 2 * a41 ^ 2 * s1 * p1
    - (3134566563840 : R) * hh ^ 2 * a41 * b62 * p1
    + (9577842278400 : R) * hh ^ 2 * a41 * p2 * p1
    + (1253826625536 : R) * hh ^ 2 * p31 * q2
    - (4179422085120 : R) * hh ^ 2 * s1 * p2 * p1
    + (3142452360960 : R) * hh ^ 2 * lam * w1 ^ 4 * p31 ^ 2
    + (12569809443840 : R) * hh ^ 2 * lam * w1 ^ 3 * a41 ^ 2 * p31
    - (5201300459520 : R) * hh ^ 2 * lam * w1 ^ 3 * p31 * p2
    + (3142452360960 : R) * hh ^ 2 * lam * w1 ^ 2 * a41 ^ 4
    - (7801950689280 : R) * hh ^ 2 * lam * w1 ^ 2 * a41 ^ 2 * p2
    + (2035291484160 : R) * hh ^ 2 * lam * w1 ^ 2 * p2 ^ 2
    - (2873352683520 : R) * hh ^ 2 * lam * a41 * p31 * p1
    + (8826023606400 : R) * hh ^ 3 * w1 ^ 6 * a41 * p31
    + (2851484549760 : R) * hh ^ 3 * w1 ^ 6 * a41 * u1
    + (3258839485440 : R) * hh ^ 3 * w1 ^ 6 * p31 * s1
    - (349161373440 : R) * hh ^ 3 * w1 ^ 6 * q52
    + (2715699571200 : R) * hh ^ 3 * w1 ^ 5 * a41 ^ 3
    + (9776518456320 : R) * hh ^ 3 * w1 ^ 5 * a41 ^ 2 * s1
    - (2513961888768 : R) * hh ^ 3 * w1 ^ 5 * a41 * b62
    - (6983227468800 : R) * hh ^ 3 * w1 ^ 5 * a41 * p2
    - (3351949185024 : R) * hh ^ 3 * w1 ^ 5 * s1 * p2
    - (339215247360 : R) * hh ^ 3 * w1 ^ 4 * q3
    - (3015246643200 : R) * hh ^ 3 * w1 ^ 3 * p31 * p1
    - (3166008975360 : R) * hh ^ 3 * w1 ^ 3 * u1 * p1
    + (5653587456000 : R) * hh ^ 3 * w1 ^ 2 * a41 ^ 2 * p1
    - (10854887915520 : R) * hh ^ 3 * w1 ^ 2 * a41 * s1 * p1
    + (2873352683520 : R) * hh ^ 3 * w1 ^ 2 * b62 * p1
    + (798153523200 : R) * hh ^ 3 * w1 ^ 2 * p2 * p1
    - (1044855521280 : R) * hh ^ 3 * w1 * a41 * q2
    + (9577842278400 : R) * hh ^ 3 * a41 * p31 * p0
    - (3656994324480 : R) * hh ^ 3 * a41 * u1 * p0
    - (4179422085120 : R) * hh ^ 3 * p31 * s1 * p0
    + (3134566563840 : R) * hh ^ 3 * q52 * p0
    - (7332388842240 : R) * hh ^ 3 * lam * w1 ^ 5 * a41 * p31
    - (6110324035200 : R) * hh ^ 3 * lam * w1 ^ 4 * a41 ^ 3
    + (6284904721920 : R) * hh ^ 3 * lam * w1 ^ 4 * a41 * p2
    + (4070582968320 : R) * hh ^ 3 * lam * w1 ^ 2 * p31 * p1
    + (4070582968320 : R) * hh ^ 3 * lam * w1 * a41 ^ 2 * p1
    - (2873352683520 : R) * hh ^ 3 * lam * w1 * p2 * p1
    - (2071125045000 : R) * hh ^ 4 * w1 ^ 8 * p31
    - (347949007560 : R) * hh ^ 4 * w1 ^ 8 * u1
    - (5302080115200 : R) * hh ^ 4 * w1 ^ 7 * a41 ^ 2
    - (3181248069120 : R) * hh ^ 4 * w1 ^ 7 * a41 * s1
    + (349161373440 : R) * hh ^ 4 * w1 ^ 7 * b62
    + (2133763948800 : R) * hh ^ 4 * w1 ^ 7 * p2
    + (5056819891200 : R) * hh ^ 4 * w1 ^ 4 * a41 * p1
    + (3467533639680 : R) * hh ^ 4 * w1 ^ 4 * s1 * p1
    + (319261409280 : R) * hh ^ 4 * w1 ^ 3 * q2
    + (798153523200 : R) * hh ^ 4 * w1 ^ 2 * p31 * p0
    + (3352244797440 : R) * hh ^ 4 * w1 ^ 2 * u1 * p0
    - (6385228185600 : R) * hh ^ 4 * w1 * a41 ^ 2 * p0
    + (7662273822720 : R) * hh ^ 4 * w1 * a41 * s1 * p0
    - (3134566563840 : R) * hh ^ 4 * w1 * b62 * p0
    + (1741425868800 : R) * hh ^ 4 * w1 * p2 * p0
    + (870712934400 : R) * hh ^ 4 * w1 * p1 ^ 2
    + (626913312768 : R) * hh ^ 4 * a41 * q1
    + (1192968025920 : R) * hh ^ 4 * lam * w1 ^ 7 * p31
    + (4175388090720 : R) * hh ^ 4 * lam * w1 ^ 6 * a41 ^ 2
    - (1222064807040 : R) * hh ^ 4 * lam * w1 ^ 6 * p2
    - (5201300459520 : R) * hh ^ 4 * lam * w1 ^ 3 * a41 * p1
    - (2873352683520 : R) * hh ^ 4 * lam * w1 * p31 * p0
    - (1436676341760 : R) * hh ^ 4 * lam * a41 ^ 2 * p0
    + (1567283281920 : R) * hh ^ 4 * lam * p2 * p0
    + (783641640960 : R) * hh ^ 4 * lam * p1 ^ 2
    + (2018963377200 : R) * hh ^ 5 * w1 ^ 9 * a41
    + (346108007520 : R) * hh ^ 5 * w1 ^ 9 * s1
    - (2211355365120 : R) * hh ^ 5 * w1 ^ 6 * p1
    - (3015246643200 : R) * hh ^ 5 * w1 ^ 3 * a41 * p0
    - (3618295971840 : R) * hh ^ 5 * w1 ^ 3 * s1 * p0
    - (261213880320 : R) * hh ^ 5 * w1 ^ 2 * q1
    - (5224277606400 : R) * hh ^ 5 * p1 * p0
    - (1168114525380 : R) * hh ^ 5 * lam * w1 ^ 8 * a41
    + (1256980944384 : R) * hh ^ 5 * lam * w1 ^ 5 * p1
    + (4070582968320 : R) * hh ^ 5 * lam * w1 ^ 2 * a41 * p0
    - (231612681800 : R) * hh ^ 6 * w1 ^ 11
    + (2311689093120 : R) * hh ^ 6 * w1 ^ 5 * p0
    + (114648277491 : R) * hh ^ 6 * lam * w1 ^ 10
    - (1300325114880 : R) * hh ^ 6 * lam * w1 ^ 4 * p0

end BridgeKappaJet610

/-! ## Jet factorization of the cleared `κ` defect -/

section BridgeKappaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- On the fifteenth-face jet the cleared `κ` defect factors exactly as
`h⁴⁸` times its factored order-`48` head plus `h` times the tail. -/
theorem localClearedEleventhDefect610_jet_factored
    (h w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 : k[X])
    (lambda : k) :
    localClearedEleventhDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h * p31) p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62)
        (h ^ 2 * q52) q4 q3 q2 q1 lambda =
      h ^ 48 *
        (bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4 +
          h * bridgeKappaJetTail610 h w1 a41 p31 s1 u1 b62 q52 p2 p1
            p0 q4 q3 q2 q1 (Polynomial.C lambda)) := by
  simp only [localClearedEleventhDefect610, bridgeKappaJetHead610,
    bridgeKappaJetTail610]
  ring

/-- Evaluation commutes with the order-`48` head. -/
theorem bridgeKappaJetHead610_eval
    (a41 p31 s1 u1 q52 q4 : k[X]) (x : k) :
    (bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4).eval x =
      bridgeKappaJetHead610 (a41.eval x) (p31.eval x) (s1.eval x)
        (u1.eval x) (q52.eval x) (q4.eval x) := by
  simp only [bridgeKappaJetHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

end BridgeKappaJetFactor610

/-! ## Scalar consequences of the vanishing order-`48` head -/

section BridgeKappaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free reduction of the vanishing order-`48` head modulo the
tenth-face root laws alone: the head reduces to the exact factored
relation `a₄₁ p₃₁³ = 0`. -/
theorem bridgeKappa_chamberFree_split610
    (a41 p31 s1 u1 q52 q4 : F)
    (hhead : bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4 = 0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hu : (3 : F) * u1 = (5 : F) * p31)
    (hq52 : (9 : F) * q52 = (10 : F) * a41 * p31)
    (hq4 : (9 : F) * q4 = (5 : F) * p31 ^ 2) :
    a41 * p31 ^ 3 = 0 := by
  simp only [bridgeKappaJetHead610] at hhead
  linear_combination (1 / 580475289600 : F) * hhead -
      (11 / 15 : F) * p31 ^ 3 * hs -
      (77 / 40 : F) * a41 * p31 ^ 2 * hu +
      (1 / 4 : F) * p31 ^ 2 * hq52 + (2 / 5 : F) * a41 * p31 * hq4

set_option maxHeartbeats 4000000 in
/-- On the `p₃₁ ≠ 0` complement child the factored root relation
forces `a₄₁ = 0`, the retained core forces `w₁ = 0`, and the two
remaining ground relations collapse to the pins `80 p₂ = 9 λ p₃₁` and
`16 b₆₂ = -5 λ p₃₁`. -/
theorem bridgeKappa_complement_pins610
    (w1 a41 p31 p2 b62 lam : F) (hnz : p31 ≠ 0)
    (hzero : a41 * p31 ^ 3 = 0)
    (hcore : (5 : F) * a41 ^ 2 + (2 : F) * p31 * w1 = 0)
    (hp2n : (80 : F) * p2 - (9 : F) * lam * p31 -
      (8 : F) * p31 * w1 = 0)
    (hb62n : (144 : F) * b62 + (45 : F) * lam * p31 -
      (152 : F) * p31 * w1 = 0) :
    a41 = 0 ∧ w1 = 0 ∧ (80 : F) * p2 = (9 : F) * lam * p31 ∧
      (16 : F) * b62 = -(5 : F) * lam * p31 := by
  have ha : a41 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (pow_ne_zero 3 hnz)
  have hpw : p31 * w1 = 0 := by
    linear_combination (1 / 2 : F) * hcore - (5 / 2 : F) * a41 * ha
  have hw : w1 = 0 := by
    rcases mul_eq_zero.mp hpw with h | h
    · exact absurd h hnz
    · exact h
  refine ⟨ha, hw, ?_, ?_⟩
  · linear_combination hp2n + (8 : F) * p31 * hw
  · linear_combination (1 / 9 : F) * hb62n + (152 / 9 : F) * p31 * hw

end BridgeKappaScalars610

/-! ## Finite local kappa integral bridge packet -/

section NonzeroKappaIntegralBridge610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- Finite local `κ` integral bridge: the terminal integral closure
packet (the `ι` packet reused opaquely) together with the imported
weight-`55` clearing of the degree-`4` first integral `κ`, its
`h₀⁴⁸`-peeled factored head, the chamber-free root split
`a₄₁(a) p₃₁(a)³ = 0`, and the four-children combination — the three
`p₃₁(a) = 0` children are retained unchanged (the head carries an
overall `p₃₁` factor there), while the `p₃₁(a) ≠ 0` child is refined
to `a₄₁(a) = 0`, `w₁(a) = 0` and the pins `80 p₂(a) = 9 λ p₃₁(a)`,
`16 b₆₂(a) = -5 λ p₃₁(a)`, with `ψ₂(a) = -209952 λ p₁(a)` collapsing
the retained boundary elimination into the Keller row.  No child is
closed. -/
theorem nonzeroFace610_linearRoot_kappaIntegralBridge
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ (w1 a41 s1 u1 p31 b62 q52 : k[X]) (iotaK kappaMu : k),
      p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        (3 : k) * s1.eval a = (5 : k) * a41.eval a ∧
        (3 : k) * u1.eval a = (5 : k) * p31.eval a ∧
        (9 : k) * q52.eval a =
          (10 : k) * a41.eval a * p31.eval a ∧
        (9 : k) * (q.coeff 4).eval a = (5 : k) * (p31.eval a) ^ 2 ∧
        (10 : k) * (a41.eval a) ^ 2 - (18 : k) * b62.eval a -
            (9 : k) * lambda * p31.eval a +
          (30 : k) * (p.coeff 2).eval a +
            (20 : k) * p31.eval a * w1.eval a = 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = j ∧
        terminalClearedIotaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda =
          Polynomial.C iotaK * h0 ^ 50 ∧
        bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 (p.coeff 2)
              (q.coeff 4) (Polynomial.C lambda) +
            h0 * bridgeIotaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
              (Polynomial.C lambda) =
          Polynomial.C iotaK * h0 ^ 6 ∧
        bridgeIotaJetHead610 (w1.eval a) (a41.eval a) (p31.eval a)
            (s1.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
            ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda = 0 ∧
        (p31.eval a) ^ 2 * ((27 : k) * b62.eval a -
            (30 : k) * (a41.eval a) ^ 2 - (5 : k) * (p.coeff 2).eval a +
            (9 : k) * lambda * p31.eval a -
            (40 : k) * p31.eval a * w1.eval a) = 0 ∧
        (p31.eval a) ^ 2 * ((144 : k) * b62.eval a -
            (170 : k) * (a41.eval a) ^ 2 +
            (45 : k) * lambda * p31.eval a -
            (220 : k) * p31.eval a * w1.eval a) = 0 ∧
        localClearedEleventhDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C kappaMu * h0 ^ 55 ∧
        bridgeKappaJetHead610 a41 p31 s1 u1 q52 (q.coeff 4) +
            h0 * bridgeKappaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C kappaMu * h0 ^ 7 ∧
        bridgeKappaJetHead610 (a41.eval a) (p31.eval a) (s1.eval a)
            (u1.eval a) (q52.eval a) ((q.coeff 4).eval a) = 0 ∧
        a41.eval a * (p31.eval a) ^ 3 = 0 ∧
        (a41.eval a = 0 ∨ p31.eval a = 0) ∧
        ((p31.eval a = 0 ∧
            ∃ (p32 u2 q53 q41 : k[X]),
              p.coeff 3 = h0 ^ 2 * p32 ∧
                q.coeff 7 = h0 ^ 6 * u2 ∧
                q.coeff 5 = h0 ^ 3 * q53 ∧
                q.coeff 4 = h0 * q41 ∧
                (18 : k) * u2.eval a - (30 : k) * p32.eval a -
                    (20 : k) * a41.eval a * w1.eval a +
                  (9 : k) * lambda * a41.eval a = 0 ∧
                (81 : k) * q41.eval a -
                    (90 : k) * a41.eval a * (p.coeff 2).eval a +
                  (5 : k) * (a41.eval a) ^ 3 = 0 ∧
                (216 : k) * q53.eval a +
                    (27 : k) * lambda * (a41.eval a) ^ 2 +
                  (40 : k) * (a41.eval a) ^ 2 * w1.eval a -
                    (240 : k) * a41.eval a * p32.eval a +
                  (108 : k) * lambda * (p.coeff 2).eval a -
                    (240 : k) * (p.coeff 2).eval a * w1.eval a = 0 ∧
                (3888 : k) * (q.coeff 3).eval a -
                    (81 : k) * lambda * (a41.eval a) ^ 3 -
                  (320 : k) * (a41.eval a) ^ 3 * w1.eval a +
                    (720 : k) * (a41.eval a) ^ 2 * p32.eval a +
                  (972 : k) * lambda * a41.eval a *
                      (p.coeff 2).eval a +
                    (1440 : k) * a41.eval a * (p.coeff 2).eval a *
                      w1.eval a -
                  (4320 : k) * (p.coeff 2).eval a * p32.eval a =
                    0 ∧
                bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
                    h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                      q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                      (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                      (Polynomial.C lambda) =
                  Polynomial.C iotaK * h0 ^ 5 ∧
                bridgeIotaLeftHead610 (a41.eval a) (s1.eval a)
                    (b62.eval a) ((p.coeff 2).eval a)
                    (q41.eval a) = 0 ∧
                (a41.eval a = 0 ∨
                  (4 : k) * (a41.eval a) ^ 4 -
                      (35 : k) * (p.coeff 2).eval a *
                        (a41.eval a) ^ 2 +
                    (90 : k) * ((p.coeff 2).eval a) ^ 2 = 0)) ∨
          ((240 : k) * (p.coeff 2).eval a -
                (40 : k) * (a41.eval a) ^ 2 -
              (27 : k) * lambda * p31.eval a -
                (40 : k) * p31.eval a * w1.eval a = 0 ∧
            (144 : k) * b62.eval a - (120 : k) * (a41.eval a) ^ 2 +
                (45 : k) * lambda * p31.eval a -
              (200 : k) * p31.eval a * w1.eval a = 0 ∧
            ((p31.eval a = 0 ∧
                (6 : k) * (p.coeff 2).eval a -
                  (a41.eval a) ^ 2 = 0 ∧
                (6 : k) * b62.eval a -
                  (5 : k) * (a41.eval a) ^ 2 = 0) ∨
              (p31.eval a ≠ 0 ∧ a41.eval a = 0 ∧ w1.eval a = 0 ∧
                (80 : k) * (p.coeff 2).eval a =
                  (9 : k) * lambda * p31.eval a ∧
                (16 : k) * b62.eval a =
                  -(5 : k) * lambda * p31.eval a ∧
                ∃ (omega psi psi2 : k[X]),
                  (583200 : k[X]) * p31 ^ 2 -
                      (489888 : k[X]) * p31 * u1 +
                    (419904 : k[X]) * q.coeff 4 = h0 * omega ∧
                  omega.eval a =
                    (648 : k) * a41.eval a *
                      ((80 : k) * (a41.eval a) ^ 2 +
                          (297 : k) * lambda * p31.eval a -
                        (960 : k) * p31.eval a * w1.eval a) ∧
                  omega + (-(518400 : k[X]) * a41 ^ 3 +
                      (466560 : k[X]) * a41 ^ 2 * s1 -
                      (419904 : k[X]) * a41 * b62 -
                      (349920 : k[X]) * a41 * Polynomial.C lambda *
                        p31 +
                      (1166400 : k[X]) * a41 * p.coeff 2 -
                      (1360800 : k[X]) * a41 * p31 * w1 +
                      (816480 : k[X]) * a41 * u1 * w1 -
                      (559872 : k[X]) * p.coeff 2 * s1 +
                      (933120 : k[X]) * p31 * s1 * w1 -
                      (349920 : k[X]) * q52 * w1) = h0 * psi ∧
                  psi.eval a =
                    (162 : k) * w1.eval a *
                      ((7600 : k) * (a41.eval a) ^ 2 * w1.eval a -
                          (2520 : k) * lambda * (a41.eval a) ^ 2 +
                          (243 : k) * lambda ^ 2 * p31.eval a -
                          (1980 : k) * lambda * p31.eval a *
                            w1.eval a +
                        (3200 : k) * p31.eval a *
                          (w1.eval a) ^ 2) ∧
                  psi + ((466560 : k[X]) * a41 ^ 2 *
                      Polynomial.C lambda * w1 +
                    (518400 : k[X]) * a41 ^ 2 * w1 ^ 2 -
                    (1244160 : k[X]) * a41 * s1 * w1 ^ 2 +
                    (349920 : k[X]) * b62 * w1 ^ 2 -
                    (349920 : k[X]) * Polynomial.C lambda *
                      p.coeff 2 * w1 +
                    (466560 : k[X]) * Polynomial.C lambda * p31 *
                      w1 ^ 2 +
                    (194400 : k[X]) * p.coeff 2 * w1 ^ 2 -
                    (432000 : k[X]) * p31 * w1 ^ 3 -
                    (362880 : k[X]) * u1 * w1 ^ 3) = h0 * psi2 ∧
                  psi2.eval a =
                    (288 : k) * ((1980 : k) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4400 : k) * a41.eval a * (w1.eval a) ^ 4 -
                      (729 : k) * lambda * (p.coeff 1).eval a -
                      (405 : k) * (p.coeff 1).eval a *
                        w1.eval a) ∧
                  psi2.eval a =
                    -(209952 : k) * lambda * (p.coeff 1).eval a ∧
                  (288 : k) * ((729 : k) * lambda +
                        (405 : k) * w1.eval a) *
                      (((p.coeff 0).derivative).eval a *
                          (q.coeff 1).eval a - j) =
                    ((q.coeff 0).derivative).eval a *
                      ((288 : k) * ((1980 : k) * lambda *
                            a41.eval a * (w1.eval a) ^ 3 -
                          (4400 : k) * a41.eval a *
                            (w1.eval a) ^ 4) -
                        psi2.eval a))))) := by
  obtain ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, hw, ha4s, hp3, hs, hu,
    hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow, hroweval, hipow,
    hipeel, hiheadeval, hires1, hires2, halt⟩ :=
    nonzeroFace610_linearRoot_terminalIntegralClosure p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6 hq10 hN hD hroot hlambda
  obtain ⟨kappaMu, hkpow⟩ :=
    nonzeroFace610_eleventhDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  have hkpowJet :
      localClearedEleventhDefect610 h0 (h0 ^ 5 * w1) (h0 ^ 3 * a41)
          (h0 * p31) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (h0 ^ 7 * s1) (h0 ^ 5 * u1) (h0 ^ 4 * b62) (h0 ^ 2 * q52)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C kappaMu * h0 ^ 55 := by
    rw [← hw, ← ha4s, ← hp3, ← hs, ← hu, ← hb6s, ← hq5]
    exact hkpow
  have hkpeel :
      bridgeKappaJetHead610 a41 p31 s1 u1 q52 (q.coeff 4) +
          h0 * bridgeKappaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
            (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
            (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (Polynomial.C lambda) =
        Polynomial.C kappaMu * h0 ^ 7 := by
    have h48 : (h0 : k[X]) ^ 48 ≠ 0 := pow_ne_zero 48 hh0
    apply mul_left_cancel₀ h48
    rw [← localClearedEleventhDefect610_jet_factored h0 w1 a41 p31 s1
      u1 b62 q52 (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
      (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda]
    rw [hkpowJet]
    ring
  have hkheadeval :
      bridgeKappaJetHead610 (a41.eval a) (p31.eval a) (s1.eval a)
        (u1.eval a) (q52.eval a) ((q.coeff 4).eval a) = 0 := by
    have hev := congrArg (Polynomial.eval a) hkpeel
    have h7z : (0 : k) ^ 7 = 0 := by norm_num
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, hroot,
      bridgeKappaJetHead610_eval, h7z, mul_zero, zero_mul,
      add_zero] at hev
    exact hev
  have hksplit0 : a41.eval a * (p31.eval a) ^ 3 = 0 :=
    bridgeKappa_chamberFree_split610 (a41.eval a) (p31.eval a)
      (s1.eval a) (u1.eval a) (q52.eval a) ((q.coeff 4).eval a)
      hkheadeval hMs hTu hVq hWq
  have hksplit : a41.eval a = 0 ∨ p31.eval a = 0 := by
    rcases mul_eq_zero.mp hksplit0 with h | h
    · exact Or.inl h
    · right
      by_contra hne
      exact pow_ne_zero 3 hne h
  refine ⟨w1, a41, s1, u1, p31, b62, q52, iotaK, kappaMu, hw, ha4s,
    hp3, hs, hu, hb6s, hq5, hMs, hTu, hVq, hWq, hUload, hrow,
    hroweval, hipow, hipeel, hiheadeval, hires1, hires2, hkpow,
    hkpeel, hkheadeval, hksplit0, hksplit, ?_⟩
  rcases halt with hleft | ⟨hload1, hload2, hcd⟩
  · exact Or.inl hleft
  · rcases hcd with ⟨hz, hp2pin, hb62pin⟩ | ⟨hnz, hcore, hp2n, hb62n,
      omega, psi, psi2, homega, homegaval, hpsieq, hpsival, hpsi2eq,
      hpsi2val, heli2⟩
    · exact Or.inr ⟨hload1, hload2, Or.inl ⟨hz, hp2pin, hb62pin⟩⟩
    · obtain ⟨ha41z, hw1z, hp2k, hb62k⟩ :=
        bridgeKappa_complement_pins610 (w1.eval a) (a41.eval a)
          (p31.eval a) ((p.coeff 2).eval a) (b62.eval a) lambda hnz
          hksplit0 hcore hp2n hb62n
      have hpsi2k : psi2.eval a =
          -(209952 : k) * lambda * (p.coeff 1).eval a := by
        rw [hpsi2val, ha41z, hw1z]
        ring
      exact Or.inr ⟨hload1, hload2, Or.inr ⟨hnz, ha41z, hw1z, hp2k,
        hb62k, omega, psi, psi2, homega, homegaval, hpsieq, hpsival,
        hpsi2eq, hpsi2val, hpsi2k, heli2⟩⟩

set_option maxHeartbeats 40000000 in
/-- Source-facing `κ` integral bridge packet of a normalized scale-two
`(6,10)` nonzero face: the terminal integral closure packet with the
weight-`55` clearing of the degree-`4` first integral `κ`, its
`h₀⁴⁸`-peeled factored head, the chamber-free root split
`a₄₁(a) p₃₁(a)³ = 0` (honestly `a₄₁(a) = 0 ∨ p₃₁(a) = 0`), and the
refined `p₃₁(a) ≠ 0` child carrying `a₄₁(a) = 0`, `w₁(a) = 0`, the
pins `80 p₂(a) = 9 λ p₃₁(a)`, `16 b₆₂(a) = -5 λ p₃₁(a)` and the
collapsed `ψ₂(a) = -209952 λ p₁(a)`.  The ground constants `iotaK` and
`kappaMu` are preserved, not cleared, and no child is closed. -/
theorem normalized610ScaleTwo_nonzeroFace_kappaIntegralBridge
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a jK iotaK kappaMu : K)
      (w1 a41 s1 u1 p31 b62 q52 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 5 = h0 ^ 5 * w1 ∧ p.coeff 4 = h0 ^ 3 * a41 ∧
        p.coeff 3 = h0 * p31 ∧ q.coeff 8 = h0 ^ 7 * s1 ∧
        q.coeff 7 = h0 ^ 5 * u1 ∧ q.coeff 6 = h0 ^ 4 * b62 ∧
        q.coeff 5 = h0 ^ 2 * q52 ∧
        h0 ^ 8 ∣ q.coeff 9 ∧
        h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧
        h0 ∣ p.coeff 3 ∧ h0 ^ 7 ∣ q.coeff 8 ∧ h0 ^ 5 ∣ q.coeff 7 ∧
        h0 ^ 4 ∣ q.coeff 6 ∧ h0 ^ 2 ∣ q.coeff 5 ∧
        (3 : K) * s1.eval a = (5 : K) * a41.eval a ∧
        (3 : K) * u1.eval a = (5 : K) * p31.eval a ∧
        (9 : K) * q52.eval a =
          (10 : K) * a41.eval a * p31.eval a ∧
        (9 : K) * (q.coeff 4).eval a = (5 : K) * (p31.eval a) ^ 2 ∧
        (10 : K) * (a41.eval a) ^ 2 - (18 : K) * b62.eval a -
            (9 : K) * lambda * p31.eval a +
          (30 : K) * (p.coeff 2).eval a +
            (20 : K) * p31.eval a * w1.eval a = 0 ∧
        jK ≠ 0 ∧
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C jK ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a -
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a = jK ∧
        ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
          (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a ∧
        terminalClearedIotaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda =
          Polynomial.C iotaK * h0 ^ 50 ∧
        bridgeIotaJetHead610 w1 a41 p31 s1 u1 b62 q52 (p.coeff 2)
              (q.coeff 4) (Polynomial.C lambda) +
            h0 * bridgeIotaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
              (Polynomial.C lambda) =
          Polynomial.C iotaK * h0 ^ 6 ∧
        bridgeIotaJetHead610 (w1.eval a) (a41.eval a) (p31.eval a)
            (s1.eval a) (u1.eval a) (b62.eval a) (q52.eval a)
            ((p.coeff 2).eval a) ((q.coeff 4).eval a) lambda = 0 ∧
        (p31.eval a) ^ 2 * ((27 : K) * b62.eval a -
            (30 : K) * (a41.eval a) ^ 2 - (5 : K) * (p.coeff 2).eval a +
            (9 : K) * lambda * p31.eval a -
            (40 : K) * p31.eval a * w1.eval a) = 0 ∧
        (p31.eval a) ^ 2 * ((144 : K) * b62.eval a -
            (170 : K) * (a41.eval a) ^ 2 +
            (45 : K) * lambda * p31.eval a -
            (220 : K) * p31.eval a * w1.eval a) = 0 ∧
        localClearedEleventhDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
          Polynomial.C kappaMu * h0 ^ 55 ∧
        bridgeKappaJetHead610 a41 p31 s1 u1 q52 (q.coeff 4) +
            h0 * bridgeKappaJetTail610 h0 w1 a41 p31 s1 u1 b62 q52
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (Polynomial.C lambda) =
          Polynomial.C kappaMu * h0 ^ 7 ∧
        bridgeKappaJetHead610 (a41.eval a) (p31.eval a) (s1.eval a)
            (u1.eval a) (q52.eval a) ((q.coeff 4).eval a) = 0 ∧
        a41.eval a * (p31.eval a) ^ 3 = 0 ∧
        (a41.eval a = 0 ∨ p31.eval a = 0) ∧
        ((p31.eval a = 0 ∧
            ∃ (p32 u2 q53 q41 : K[X]),
              p.coeff 3 = h0 ^ 2 * p32 ∧
                q.coeff 7 = h0 ^ 6 * u2 ∧
                q.coeff 5 = h0 ^ 3 * q53 ∧
                q.coeff 4 = h0 * q41 ∧
                (18 : K) * u2.eval a - (30 : K) * p32.eval a -
                    (20 : K) * a41.eval a * w1.eval a +
                  (9 : K) * lambda * a41.eval a = 0 ∧
                (81 : K) * q41.eval a -
                    (90 : K) * a41.eval a * (p.coeff 2).eval a +
                  (5 : K) * (a41.eval a) ^ 3 = 0 ∧
                (216 : K) * q53.eval a +
                    (27 : K) * lambda * (a41.eval a) ^ 2 +
                  (40 : K) * (a41.eval a) ^ 2 * w1.eval a -
                    (240 : K) * a41.eval a * p32.eval a +
                  (108 : K) * lambda * (p.coeff 2).eval a -
                    (240 : K) * (p.coeff 2).eval a * w1.eval a = 0 ∧
                (3888 : K) * (q.coeff 3).eval a -
                    (81 : K) * lambda * (a41.eval a) ^ 3 -
                  (320 : K) * (a41.eval a) ^ 3 * w1.eval a +
                    (720 : K) * (a41.eval a) ^ 2 * p32.eval a +
                  (972 : K) * lambda * a41.eval a *
                      (p.coeff 2).eval a +
                    (1440 : K) * a41.eval a * (p.coeff 2).eval a *
                      w1.eval a -
                  (4320 : K) * (p.coeff 2).eval a * p32.eval a =
                    0 ∧
                bridgeIotaLeftHead610 a41 s1 b62 (p.coeff 2) q41 +
                    h0 * bridgeIotaLeftTail610 h0 w1 a41 p32 s1 u2 b62
                      q53 (p.coeff 2) (p.coeff 1) (p.coeff 0) q41
                      (q.coeff 3) (q.coeff 2) (q.coeff 1) (q.coeff 0)
                      (Polynomial.C lambda) =
                  Polynomial.C iotaK * h0 ^ 5 ∧
                bridgeIotaLeftHead610 (a41.eval a) (s1.eval a)
                    (b62.eval a) ((p.coeff 2).eval a)
                    (q41.eval a) = 0 ∧
                (a41.eval a = 0 ∨
                  (4 : K) * (a41.eval a) ^ 4 -
                      (35 : K) * (p.coeff 2).eval a *
                        (a41.eval a) ^ 2 +
                    (90 : K) * ((p.coeff 2).eval a) ^ 2 = 0)) ∨
          ((240 : K) * (p.coeff 2).eval a -
                (40 : K) * (a41.eval a) ^ 2 -
              (27 : K) * lambda * p31.eval a -
                (40 : K) * p31.eval a * w1.eval a = 0 ∧
            (144 : K) * b62.eval a - (120 : K) * (a41.eval a) ^ 2 +
                (45 : K) * lambda * p31.eval a -
              (200 : K) * p31.eval a * w1.eval a = 0 ∧
            ((p31.eval a = 0 ∧
                (6 : K) * (p.coeff 2).eval a -
                  (a41.eval a) ^ 2 = 0 ∧
                (6 : K) * b62.eval a -
                  (5 : K) * (a41.eval a) ^ 2 = 0) ∨
              (p31.eval a ≠ 0 ∧ a41.eval a = 0 ∧ w1.eval a = 0 ∧
                (80 : K) * (p.coeff 2).eval a =
                  (9 : K) * lambda * p31.eval a ∧
                (16 : K) * b62.eval a =
                  -(5 : K) * lambda * p31.eval a ∧
                ∃ (omega psi psi2 : K[X]),
                  (583200 : K[X]) * p31 ^ 2 -
                      (489888 : K[X]) * p31 * u1 +
                    (419904 : K[X]) * q.coeff 4 = h0 * omega ∧
                  omega.eval a =
                    (648 : K) * a41.eval a *
                      ((80 : K) * (a41.eval a) ^ 2 +
                          (297 : K) * lambda * p31.eval a -
                        (960 : K) * p31.eval a * w1.eval a) ∧
                  omega + (-(518400 : K[X]) * a41 ^ 3 +
                      (466560 : K[X]) * a41 ^ 2 * s1 -
                      (419904 : K[X]) * a41 * b62 -
                      (349920 : K[X]) * a41 * Polynomial.C lambda *
                        p31 +
                      (1166400 : K[X]) * a41 * p.coeff 2 -
                      (1360800 : K[X]) * a41 * p31 * w1 +
                      (816480 : K[X]) * a41 * u1 * w1 -
                      (559872 : K[X]) * p.coeff 2 * s1 +
                      (933120 : K[X]) * p31 * s1 * w1 -
                      (349920 : K[X]) * q52 * w1) = h0 * psi ∧
                  psi.eval a =
                    (162 : K) * w1.eval a *
                      ((7600 : K) * (a41.eval a) ^ 2 * w1.eval a -
                          (2520 : K) * lambda * (a41.eval a) ^ 2 +
                          (243 : K) * lambda ^ 2 * p31.eval a -
                          (1980 : K) * lambda * p31.eval a *
                            w1.eval a +
                        (3200 : K) * p31.eval a *
                          (w1.eval a) ^ 2) ∧
                  psi + ((466560 : K[X]) * a41 ^ 2 *
                      Polynomial.C lambda * w1 +
                    (518400 : K[X]) * a41 ^ 2 * w1 ^ 2 -
                    (1244160 : K[X]) * a41 * s1 * w1 ^ 2 +
                    (349920 : K[X]) * b62 * w1 ^ 2 -
                    (349920 : K[X]) * Polynomial.C lambda *
                      p.coeff 2 * w1 +
                    (466560 : K[X]) * Polynomial.C lambda * p31 *
                      w1 ^ 2 +
                    (194400 : K[X]) * p.coeff 2 * w1 ^ 2 -
                    (432000 : K[X]) * p31 * w1 ^ 3 -
                    (362880 : K[X]) * u1 * w1 ^ 3) = h0 * psi2 ∧
                  psi2.eval a =
                    (288 : K) * ((1980 : K) * lambda * a41.eval a *
                        (w1.eval a) ^ 3 -
                      (4400 : K) * a41.eval a * (w1.eval a) ^ 4 -
                      (729 : K) * lambda * (p.coeff 1).eval a -
                      (405 : K) * (p.coeff 1).eval a *
                        w1.eval a) ∧
                  psi2.eval a =
                    -(209952 : K) * lambda * (p.coeff 1).eval a ∧
                  (288 : K) * ((729 : K) * lambda +
                        (405 : K) * w1.eval a) *
                      (((p.coeff 0).derivative).eval a *
                          (q.coeff 1).eval a - jK) =
                    ((q.coeff 0).derivative).eval a *
                      ((288 : K) * ((1980 : K) * lambda *
                            a41.eval a * (w1.eval a) ^ 3 -
                          (4400 : K) * a41.eval a *
                            (w1.eval a) ^ 4) -
                        psi2.eval a))))) ∧
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, w1, a41, s1, u1, p31, b62, q52, hh0, hlambda,
    hh0degree, hH, hroot, hw, ha4s, hp3, hs, hu, hb6s, hq5, hq9, hp5d,
    hp4d, hp3d, hq8d, hq7d, hq6d, hq5d, hMs, hTu, hVq, hWq, hUload,
    hXalt, hN'⟩ :=
    normalized610ScaleTwo_nonzeroFace_tenthPowerJet hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨w1', a41', s1', u1', p31', b62', q52', iotaK, kappaMu, hwN,
    ha4sN, hp3N, hsN, huN, hb6sN, hq5N, hMs', hTu', hVq', hWq',
    hUload', hrow, hroweval, hipow, hipeel, hiheadeval, hres1, hres2,
    hkpow, hkpeel, hkheadeval, hksplit0, hksplit, halt⟩ :=
    nonzeroFace610_linearRoot_kappaIntegralBridge p q H h0 j lambda
      a hp hq hh0 hh0degree hH hp6' hq10' hN' hD hroot hlambda
  have hsep : ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a ≠
      (p.coeff 1).eval a * ((q.coeff 0).derivative).eval a := by
    intro heq
    apply hj
    rw [← hroweval, heq, sub_self]
  exact ⟨h0, lambda, a, j, iotaK, kappaMu, w1', a41', s1', u1', p31',
    b62', q52', hh0, hlambda, hh0degree, hH, hroot, hwN, ha4sN, hp3N,
    hsN, huN, hb6sN, hq5N, hq9,
    (by rw [hwN]; exact dvd_mul_right _ _),
    (by rw [ha4sN]; exact dvd_mul_right _ _),
    (by rw [hp3N]; exact dvd_mul_right _ _),
    (by rw [hsN]; exact dvd_mul_right _ _),
    (by rw [huN]; exact dvd_mul_right _ _),
    (by rw [hb6sN]; exact dvd_mul_right _ _),
    (by rw [hq5N]; exact dvd_mul_right _ _),
    hMs', hTu', hVq', hWq', hUload', hj, hrow, hroweval, hsep, hipow,
    hipeel, hiheadeval, hres1, hres2, hkpow, hkpeel, hkheadeval,
    hksplit0, hksplit, halt, hN'⟩

end NonzeroKappaIntegralBridge610

#print axioms nonzeroFace610_linearRoot_kappaIntegralBridge
#print axioms normalized610ScaleTwo_nonzeroFace_kappaIntegralBridge

end Max11DegreeRoutes
