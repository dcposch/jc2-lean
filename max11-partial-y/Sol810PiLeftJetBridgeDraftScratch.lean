import Sol810PiSourceClearingDraftScratch

/-! # Draft first two left-jet bridges for π

These definitions are generated from the exact `h^96` and `h^97`
coefficients of the 762-term clearing polynomial after the four retained
left-jet solves.  The second coefficient is deliberately represented as
`lambda * piLeftHead97New810`; no division by `lambda` occurs.

Jet-job command-source SHA256:
`25e3507b2e2b674a6489443bd761bf3e7d7364fc23018661c0a3feda16d0f017`.
Jet-output SHA256:
`15865d780685e9a675aa61df9f1bcb30eb71f430b7a1e1e5dfba5bbf0f0cf2e7`.
-/

noncomputable section

namespace Max11DegreeRoutes

section PiLeftJetDraft

variable {F : Type*} [Field F] [CharZero F]

def piLeftS1Solve810 (t0 v1 : F) : F :=
  (40 * v1 + 5 * t0 ^ 2) / 32

def piLeftW1Solve810 (t0 v1 u1 : F) : F :=
  (160 * u1 + 40 * t0 * v1 - 5 * t0 ^ 3) / 128

def piLeftA4Solve810 (t0 v1 u1 b62 : F) : F :=
  (2048 * b62 - 35 * t0 ^ 4 + 240 * t0 ^ 2 * v1 -
      640 * t0 * u1 - 320 * v1 ^ 2) / 2560

def piLeftB5Solve810 (t0 v1 u1 b62 : F) : F :=
  -(81920 * piLeftA4Solve810 t0 v1 u1 b62 * t0 -
      98304 * b62 * t0 + 2912 * t0 ^ 5 - 20480 * t0 ^ 3 * v1 +
      46080 * t0 ^ 2 * u1 + 30720 * t0 * v1 ^ 2 - 40960 * u1 * v1) /
    131072

set_option maxHeartbeats 400000000 in
/-- The exact 64-term `h^96` coefficient.  It is retained explicitly even
though the preceding μ/ν/ξ bridge makes this head redundant. -/
def piLeftHead96Residual810 (t0 v1 u1 b62 : F) : F :=
  4*(4398046511104*b62 ^ 4
    - 24996709662720*b62 ^ 3*t0 ^ 4
    + 80401787781120*b62 ^ 3*t0 ^ 2*v1
    - 52226802319360*b62 ^ 3*t0*u1
    - 32985348833280*b62 ^ 3*v1 ^ 2
    + 14040705269760*b62 ^ 2*t0 ^ 8
    - 115952037396480*b62 ^ 2*t0 ^ 6*v1
    + 123174293340160*b62 ^ 2*t0 ^ 5*u1
    + 304687664332800*b62 ^ 2*t0 ^ 4*v1 ^ 2
    - 493276993945600*b62 ^ 2*t0 ^ 3*u1*v1
    + 190696547942400*b62 ^ 2*t0 ^ 2*u1 ^ 2
    - 268005959270400*b62 ^ 2*t0 ^ 2*v1 ^ 3
    + 371085174374400*b62 ^ 2*t0*u1*v1 ^ 2
    - 106515188940800*b62 ^ 2*u1 ^ 2*v1
    + 45097156608000*b62 ^ 2*v1 ^ 4
    - 2423147110400*b62*t0 ^ 12
    + 32889669222400*b62*t0 ^ 10*v1
    - 40511596134400*b62*t0 ^ 9*u1
    - 170233665945600*b62*t0 ^ 8*v1 ^ 2
    + 366381891584000*b62*t0 ^ 7*u1*v1
    - 200910517043200*b62*t0 ^ 6*u1 ^ 2
    + 416569255526400*b62*t0 ^ 6*v1 ^ 3
    - 1106622650777600*b62*t0 ^ 5*u1*v1 ^ 2
    + 965394563072000*b62*t0 ^ 4*u1 ^ 2*v1
    - 481057308672000*b62*t0 ^ 4*v1 ^ 4
    - 277159608320000*b62*t0 ^ 3*u1 ^ 3
    + 1249365721088000*b62*t0 ^ 3*u1*v1 ^ 3
    - 1082331758592000*b62*t0 ^ 2*u1 ^ 2*v1 ^ 2
    + 221841771724800*b62*t0 ^ 2*v1 ^ 5
    + 340376158208000*b62*t0*u1 ^ 3*v1
    - 398223998976000*b62*t0*u1*v1 ^ 4
    - 25769803776000*b62*u1 ^ 4
    + 165356240896000*b62*u1 ^ 2*v1 ^ 3
    - 21689584844800*b62*v1 ^ 6
    + 131584040875*t0 ^ 16
    - 2495990496000*t0 ^ 14*v1
    + 3303893504000*t0 ^ 13*u1
    + 19516626144000*t0 ^ 12*v1 ^ 2
    - 47336222208000*t0 ^ 11*u1*v1
    + 29453991936000*t0 ^ 10*u1 ^ 2
    - 80983979008000*t0 ^ 10*v1 ^ 3
    + 263182471168000*t0 ^ 9*u1*v1 ^ 2
    - 289621549056000*t0 ^ 8*u1 ^ 2*v1
    + 191056954368000*t0 ^ 8*v1 ^ 4
    + 108668649472000*t0 ^ 7*u1 ^ 3
    - 711634386944000*t0 ^ 7*u1*v1 ^ 3
    + 989106798592000*t0 ^ 6*u1 ^ 2*v1 ^ 2
    - 254275485696000*t0 ^ 6*v1 ^ 5
    - 609484800000000*t0 ^ 5*u1 ^ 3*v1
    + 955788034048000*t0 ^ 5*u1*v1 ^ 4
    + 141421445120000*t0 ^ 4*u1 ^ 4
    - 1367107174400000*t0 ^ 4*u1 ^ 2*v1 ^ 3
    + 176758849536000*t0 ^ 4*v1 ^ 6
    + 913016094720000*t0 ^ 3*u1 ^ 3*v1 ^ 2
    - 573602529280000*t0 ^ 3*u1*v1 ^ 5
    - 275649658880000*t0 ^ 2*u1 ^ 4*v1
    + 660602880000000*t0 ^ 2*u1 ^ 2*v1 ^ 4
    - 52533657600000*t0 ^ 2*v1 ^ 7
    + 28185722880000*t0*u1 ^ 5
    - 309371863040000*t0*u1 ^ 3*v1 ^ 3
    + 108733136896000*t0*u1*v1 ^ 6
    + 46305116160000*u1 ^ 4*v1 ^ 2
    - 53989081088000*u1 ^ 2*v1 ^ 5
    + 3454009344000*v1 ^ 8)/25

set_option maxHeartbeats 400000000 in
/-- The exact new 54-term factor at `h^97`; the actual coefficient is
`lambda * piLeftHead97New810`. -/
def piLeftHead97New810 (t0 v1 u1 b62 : F) : F :=
  -384*(-355945414656*b62 ^ 3*t0 ^ 3
    + 502511173632*b62 ^ 3*t0*v1
    - 154618822656*b62 ^ 3*u1
    + 396267356160*b62 ^ 2*t0 ^ 7
    - 2340799119360*b62 ^ 2*t0 ^ 5*v1
    + 2093544898560*b62 ^ 2*t0 ^ 4*u1
    + 3847351173120*b62 ^ 2*t0 ^ 3*v1 ^ 2
    - 4529848320000*b62 ^ 2*t0 ^ 2*u1*v1
    + 1087163596800*b62 ^ 2*t0*u1 ^ 2
    - 1570347417600*b62 ^ 2*t0*v1 ^ 3
    + 1014686023680*b62 ^ 2*u1*v1 ^ 2
    - 106567968000*b62*t0 ^ 11
    + 1169815296000*b62*t0 ^ 9*v1
    - 1282260787200*b62*t0 ^ 8*u1
    - 4675866624000*b62*t0 ^ 7*v1 ^ 2
    + 8627650560000*b62*t0 ^ 6*u1*v1
    - 3973762252800*b62*t0 ^ 5*u1 ^ 2
    + 8234355916800*b62*t0 ^ 5*v1 ^ 3
    - 17618514739200*b62*t0 ^ 4*u1*v1 ^ 2
    + 11664359424000*b62*t0 ^ 3*u1 ^ 2*v1
    - 6051358310400*b62*t0 ^ 3*v1 ^ 4
    - 2302672896000*b62*t0 ^ 2*u1 ^ 3
    + 11230248960000*b62*t0 ^ 2*u1*v1 ^ 3
    - 5934101299200*b62*t0*u1 ^ 2*v1 ^ 2
    + 1329887969280*b62*t0*v1 ^ 5
    + 785173708800*b62*u1 ^ 3*v1
    - 1140011827200*b62*u1*v1 ^ 4
    + 8210330625*t0 ^ 15
    - 133315918500*t0 ^ 13*v1
    + 159847917000*t0 ^ 12*u1
    + 872207544000*t0 ^ 11*v1 ^ 2
    - 1884396816000*t0 ^ 10*u1*v1
    + 1035096096000*t0 ^ 9*u1 ^ 2
    - 2937036128000*t0 ^ 9*v1 ^ 3
    + 8306764992000*t0 ^ 8*u1*v1 ^ 2
    - 7814697984000*t0 ^ 7*u1 ^ 2*v1
    + 5384590848000*t0 ^ 7*v1 ^ 4
    + 2454921216000*t0 ^ 6*u1 ^ 3
    - 16875436032000*t0 ^ 6*u1*v1 ^ 3
    + 19091533824000*t0 ^ 5*u1 ^ 2*v1 ^ 2
    - 5208437145600*t0 ^ 5*v1 ^ 5
    - 9129885696000*t0 ^ 4*u1 ^ 3*v1
    + 15615406080000*t0 ^ 4*u1*v1 ^ 4
    + 1530593280000*t0 ^ 3*u1 ^ 4
    - 16751591424000*t0 ^ 3*u1 ^ 2*v1 ^ 3
    + 2333795942400*t0 ^ 3*v1 ^ 6
    + 7582777344000*t0 ^ 2*u1 ^ 3*v1 ^ 2
    - 5437351526400*t0 ^ 2*u1*v1 ^ 5
    - 1288175616000*t0*u1 ^ 4*v1
    + 3898736640000*t0*u1 ^ 2*v1 ^ 4
    - 334312243200*t0*v1 ^ 7
    + 49073356800*u1 ^ 5
    - 817889280000*u1 ^ 3*v1 ^ 3
    + 336435609600*u1*v1 ^ 6)/25

/-- Exact proposition for extracting the already-redundant `h^96` head.
The existential tail contains only powers `h^97,...,h^112`. -/
def PiLeftHead96BridgeStatement810 : Prop :=
  ∀ (h t0 v1 u1 b62 a3 a2 a1 a0 b4 b3 b2 b1 lambda : F),
    ∃ tail : F,
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          (piLeftA4Solve810 t0 v1 u1 b62) a3 a2 a1 a0
          (h ^ 6 * piLeftS1Solve810 t0 v1)
          (h ^ 4 * piLeftW1Solve810 t0 v1 u1) (h ^ 2 * b62)
          (piLeftB5Solve810 t0 v1 u1 b62) b4 b3 b2 b1 lambda =
        h ^ 96 * (piLeftHead96Residual810 t0 v1 u1 b62 + h * tail)

/-- Exact proposition for extracting the `h^97` coefficient without
cancelling `lambda`.  The existential tail begins at `h^98`. -/
def PiLeftHead97BridgeStatement810 : Prop :=
  ∀ (h t0 v1 u1 b62 a3 a2 a1 a0 b4 b3 b2 b1 lambda : F),
    ∃ tail : F,
      localClearedSixteenthDefect810
          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
          (piLeftA4Solve810 t0 v1 u1 b62) a3 a2 a1 a0
          (h ^ 6 * piLeftS1Solve810 t0 v1)
          (h ^ 4 * piLeftW1Solve810 t0 v1 u1) (h ^ 2 * b62)
          (piLeftB5Solve810 t0 v1 u1 b62) b4 b3 b2 b1 lambda =
        h ^ 96 * (piLeftHead96Residual810 t0 v1 u1 b62 +
          h * (lambda * piLeftHead97New810 t0 v1 u1 b62 + h * tail))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
/-- Valuewise witness for `PiLeftHead96BridgeStatement810`.

**Warning.**  This theorem only establishes the current *weak valuewise
existential* statement: for every tuple of field values some `tail : F`
exists, and in the `h ≠ 0` chamber the witness is produced by plain field
division, so `tail` may depend arbitrarily on `h`.  In particular this
theorem does **not** certify that `piLeftHead96Residual810` is the
polynomial `h^96` coefficient of the cleared defect; that would require a
polynomial-level (`h`-uniform) statement. -/
theorem piLeftHead96Bridge810 : PiLeftHead96BridgeStatement810 (F := F) := by
  unfold PiLeftHead96BridgeStatement810
  intro h t0 v1 u1 b62 a3 a2 a1 a0 b4 b3 b2 b1 lambda
  by_cases hh : h = 0
  · subst h
    refine ⟨0, ?_⟩
    simp [localClearedSixteenthDefect810, localClearedSixteenthDefectCore810,
      localClearedSixteenthDefectBlock0_810, localClearedSixteenthDefectBlock1_810,
      localClearedSixteenthDefectBlock2_810, localClearedSixteenthDefectBlock3_810,
      localClearedSixteenthDefectBlock4_810, localClearedSixteenthDefectBlock5_810,
      localClearedSixteenthDefectBlock6_810, localClearedSixteenthDefectBlock7_810,
      localClearedSixteenthDefectBlock8_810, localClearedSixteenthDefectBlock9_810,
      localClearedSixteenthDefectBlock10_810, localClearedSixteenthDefectBlock11_810,
      localClearedSixteenthDefectBlock12_810, localClearedSixteenthDefectBlock13_810,
      localClearedSixteenthDefectBlock14_810, localClearedSixteenthDefectBlock15_810,
      localClearedSixteenthDefectBlock16_810, localClearedSixteenthDefectBlock17_810,
      localClearedSixteenthDefectBlock18_810]
  · refine ⟨(localClearedSixteenthDefect810
        h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
        (piLeftA4Solve810 t0 v1 u1 b62) a3 a2 a1 a0
        (h ^ 6 * piLeftS1Solve810 t0 v1)
        (h ^ 4 * piLeftW1Solve810 t0 v1 u1) (h ^ 2 * b62)
        (piLeftB5Solve810 t0 v1 u1 b62) b4 b3 b2 b1 lambda / h ^ 96 -
          piLeftHead96Residual810 t0 v1 u1 b62) / h, ?_⟩
    field_simp [hh]
    ring

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
/-- Valuewise witness for `PiLeftHead97BridgeStatement810`.

**Warning.**  As for `piLeftHead96Bridge810`, this only establishes the
current *weak valuewise existential* statement: the `h ≠ 0` witness is a
field-division quotient, so `tail` may depend arbitrarily on `h`.  It does
**not** certify that `lambda * piLeftHead97New810` is the polynomial
`h^97` coefficient of the cleared defect. -/
theorem piLeftHead97Bridge810 : PiLeftHead97BridgeStatement810 (F := F) := by
  unfold PiLeftHead97BridgeStatement810
  intro h t0 v1 u1 b62 a3 a2 a1 a0 b4 b3 b2 b1 lambda
  by_cases hh : h = 0
  · subst h
    refine ⟨0, ?_⟩
    simp [localClearedSixteenthDefect810, localClearedSixteenthDefectCore810,
      localClearedSixteenthDefectBlock0_810, localClearedSixteenthDefectBlock1_810,
      localClearedSixteenthDefectBlock2_810, localClearedSixteenthDefectBlock3_810,
      localClearedSixteenthDefectBlock4_810, localClearedSixteenthDefectBlock5_810,
      localClearedSixteenthDefectBlock6_810, localClearedSixteenthDefectBlock7_810,
      localClearedSixteenthDefectBlock8_810, localClearedSixteenthDefectBlock9_810,
      localClearedSixteenthDefectBlock10_810, localClearedSixteenthDefectBlock11_810,
      localClearedSixteenthDefectBlock12_810, localClearedSixteenthDefectBlock13_810,
      localClearedSixteenthDefectBlock14_810, localClearedSixteenthDefectBlock15_810,
      localClearedSixteenthDefectBlock16_810, localClearedSixteenthDefectBlock17_810,
      localClearedSixteenthDefectBlock18_810]
  · refine ⟨((localClearedSixteenthDefect810
        h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)
        (piLeftA4Solve810 t0 v1 u1 b62) a3 a2 a1 a0
        (h ^ 6 * piLeftS1Solve810 t0 v1)
        (h ^ 4 * piLeftW1Solve810 t0 v1 u1) (h ^ 2 * b62)
        (piLeftB5Solve810 t0 v1 u1 b62) b4 b3 b2 b1 lambda / h ^ 96 -
          piLeftHead96Residual810 t0 v1 u1 b62) / h -
          lambda * piLeftHead97New810 t0 v1 u1 b62) / h, ?_⟩
    field_simp [hh]
    ring

end PiLeftJetDraft

end Max11DegreeRoutes
