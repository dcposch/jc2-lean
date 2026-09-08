import Fable410ScaleTwoThetaSourceBridgeScratch

/-!
# Supplied-witness source packet for the nonzero square `(4,10)` face

This adapter advances the exact `h₀, λ, a` supplied by the caller through the
tenth, eleventh, and twelfth faces.  It deliberately does not call the
normalized convenience theorem that chooses a new square root of `H`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem nonzeroFace410_linearRoot_suppliedThetaInputs
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) (hlambda : lambda ≠ 0) :
    ∃ t2 a22 s22 vis w73 q54 b42 b31 : k[X],
      p.coeff 3 = h0 ^ 3 * t2 ∧
      p.coeff 2 = h0 ^ 2 * a22 ∧
      q.coeff 8 = h0 ^ 8 * s22 ∧
      q.coeff 7 = h0 ^ 6 * vis ∧
      q.coeff 6 = h0 ^ 5 * w73 ∧
      q.coeff 5 = h0 ^ 4 * q54 ∧
      q.coeff 4 = h0 ^ 2 * b42 ∧
      q.coeff 3 = h0 * b31 ∧
      (64 : k) * vis.eval a - (160 : k) * (p.coeff 1).eval a = 0 ∧
      (8 : k) * w73.eval a =
        (p.coeff 1).eval a *
          ((30 : k) * t2.eval a - (9 : k) * lambda) ∧
      (8 : k) * b42.eval a = (15 : k) * ((p.coeff 1).eval a) ^ 2 ∧
      (32 : k) * q54.eval a +
          (40 : k) * (p.coeff 1).eval a * a22.eval a -
          (64 : k) * (p.coeff 1).eval a * s22.eval a -
          (27 : k) * (p.coeff 1).eval a * lambda * t2.eval a +
          (90 : k) * (p.coeff 1).eval a * (t2.eval a) ^ 2 =
        0 ∧
      (64 : k) * b31.eval a =
        (15 : k) * ((p.coeff 1).eval a) ^ 2 *
          ((4 : k) * t2.eval a - (3 : k) * lambda) ∧
      (256 : k) * (q.coeff 2).eval a =
        ((p.coeff 1).eval a) ^ 2 *
          ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
            (243 : k) * lambda * t2.eval a -
            (540 : k) * (t2.eval a) ^ 2) := by
  obtain ⟨t2, _a21, _s21, vis, _w72, _q52, hp3, _hp2old, _hq8old,
      hq7, _hq6old, _hq5old, _hsrel, _hq52z, _hq4z, _hwrel, _ha21z,
      _hp3div, hp2div, hq8div, _hq7div, hq6div, hq5div, hq4div,
      _hq9div, hTweak⟩ :=
    nonzeroFace410_linearRoot_tenthInitialPacket p q H h0 j lambda a
      hp hq hh0 hdegree hH hp4 hq10 hN hD hroot hlambda
  have hT :
      (64 : k) * vis.eval a - (160 : k) * (p.coeff 1).eval a = 0 := by
    linear_combination (32 : k) * hTweak
  obtain ⟨a22, hp2⟩ := hp2div
  obtain ⟨s22, hq8⟩ := hq8div
  obtain ⟨w73, hq6⟩ := hq6div
  obtain ⟨q53, hq5three⟩ := hq5div
  obtain ⟨b42, hq4⟩ := hq4div

  obtain ⟨delta, hpowUraw⟩ :=
    nonzeroFace410_fourthDefectPowerRelation p q H h0 j lambda hp hq
      hh0 hH hp4 hq10 hN hD
  obtain ⟨eps, hpowVraw⟩ :=
    nonzeroFace410_fifthDefectPowerRelation p q H h0 j lambda hp hq
      hh0 hH hp4 hq10 hN hD
  obtain ⟨zeta, hpowWraw⟩ :=
    nonzeroFace410_sixthDefectPowerRelation p q H h0 j lambda hp hq
      hh0 hH hp4 hq10 hN hD
  obtain ⟨xi, hpowXraw⟩ :=
    nonzeroFace410_seventhDefectPowerRelation p q H h0 j lambda hp hq
      hh0 hH hp4 hq10 hN hD
  obtain ⟨eta, hpowYraw⟩ :=
    nonzeroFace410_eighthDefectPowerRelation p q H h0 j lambda hp hq
      hh0 hH hp4 hq10 hN hD

  have hpowU :
      localClearedFourthDefect410 h0 (h0 ^ 3 * t2) (h0 ^ 2 * a22)
          (p.coeff 1) (p.coeff 0) (h0 ^ 8 * s22) (h0 ^ 6 * vis)
          (h0 ^ 5 * w73) lambda =
        Polynomial.C delta * h0 ^ 14 := by
    simpa only [← hp3, ← hp2, ← hq8, ← hq7, ← hq6] using hpowUraw
  have hpowVthree :
      localClearedFifthDefect410 h0 (h0 ^ 3 * t2) (h0 ^ 2 * a22)
          (p.coeff 1) (p.coeff 0) (h0 ^ 8 * s22) (h0 ^ 6 * vis)
          (h0 ^ 5 * w73) (h0 ^ 3 * q53) lambda =
        Polynomial.C eps * h0 ^ 17 := by
    simpa only [← hp3, ← hp2, ← hq8, ← hq7, ← hq6, ← hq5three]
      using hpowVraw
  have hpowW :
      localClearedSixthDefect410 h0 (h0 ^ 3 * t2) (h0 ^ 2 * a22)
          (p.coeff 1) (p.coeff 0) (h0 ^ 8 * s22) (h0 ^ 6 * vis)
          (h0 ^ 5 * w73) (h0 ^ 3 * q53) (h0 ^ 2 * b42) lambda =
        Polynomial.C zeta * h0 ^ 20 := by
    simpa only [← hp3, ← hp2, ← hq8, ← hq7, ← hq6, ← hq5three,
      ← hq4] using hpowWraw
  have hpowXthree :
      localClearedSeventhDefect410 h0 (h0 ^ 3 * t2) (h0 ^ 2 * a22)
          (p.coeff 1) (p.coeff 0) (h0 ^ 8 * s22) (h0 ^ 6 * vis)
          (h0 ^ 5 * w73) (h0 ^ 3 * q53) (h0 ^ 2 * b42)
          (q.coeff 3) lambda =
        Polynomial.C xi * h0 ^ 23 := by
    simpa only [← hp3, ← hp2, ← hq8, ← hq7, ← hq6, ← hq5three,
      ← hq4] using hpowXraw

  have hq53zero : q53.eval a = 0 :=
    eleventhFace_evalV410 h0 t2 a22 s22 vis w73 q53 (p.coeff 1)
      (p.coeff 0) lambda a eps hh0 hroot hpowVthree
  have hU : (8 : k) * w73.eval a =
      (p.coeff 1).eval a *
        ((30 : k) * t2.eval a - (9 : k) * lambda) :=
    eleventhFace_evalU410 h0 t2 a22 s22 vis w73 (p.coeff 1)
      (p.coeff 0) lambda a delta hh0 hroot hpowU hT
  have hW : (8 : k) * b42.eval a =
      (15 : k) * ((p.coeff 1).eval a) ^ 2 :=
    eleventhFace_evalW410 h0 t2 a22 s22 vis w73 q53 (p.coeff 1)
      (p.coeff 0) b42 lambda a zeta hh0 hroot hpowW hT hq53zero
  have hq3zero : (q.coeff 3).eval a = 0 :=
    eleventhFace_evalX410 h0 t2 a22 s22 vis w73 q53 (p.coeff 1)
      (p.coeff 0) b42 (q.coeff 3) lambda a xi hh0 hroot hpowXthree

  obtain ⟨q54, hq53factor⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 q53 a hdegree hroot
      hq53zero
  have hq5 : q.coeff 5 = h0 ^ 4 * q54 := by
    calc
      q.coeff 5 = h0 ^ 3 * q53 := hq5three
      _ = h0 ^ 3 * (h0 * q54) := by rw [hq53factor]
      _ = h0 ^ 4 * q54 := by ring
  obtain ⟨b31, hq3⟩ :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h0 (q.coeff 3) a hdegree
      hroot hq3zero

  have hpowV :
      localClearedFifthDefect410 h0 (h0 ^ 3 * t2) (h0 ^ 2 * a22)
          (p.coeff 1) (p.coeff 0) (h0 ^ 8 * s22) (h0 ^ 6 * vis)
          (h0 ^ 5 * w73) (h0 ^ 4 * q54) lambda =
        Polynomial.C eps * h0 ^ 17 := by
    simpa only [← hp3, ← hp2, ← hq8, ← hq7, ← hq6, ← hq5]
      using hpowVraw
  have hpowX :
      localClearedSeventhDefect410 h0 (h0 ^ 3 * t2) (h0 ^ 2 * a22)
          (p.coeff 1) (p.coeff 0) (h0 ^ 8 * s22) (h0 ^ 6 * vis)
          (h0 ^ 5 * w73) (h0 ^ 4 * q54) (h0 ^ 2 * b42)
          (h0 * b31) lambda =
        Polynomial.C xi * h0 ^ 23 := by
    simpa only [← hp3, ← hp2, ← hq8, ← hq7, ← hq6, ← hq5,
      ← hq4, ← hq3] using hpowXraw
  have hpowY :
      localClearedEighthDefect410 h0 (h0 ^ 3 * t2) (h0 ^ 2 * a22)
          (p.coeff 1) (p.coeff 0) (h0 ^ 8 * s22) (h0 ^ 6 * vis)
          (h0 ^ 5 * w73) (h0 ^ 4 * q54) (h0 ^ 2 * b42)
          (h0 * b31) (q.coeff 2) lambda =
        Polynomial.C eta * h0 ^ 26 := by
    simpa only [← hp3, ← hp2, ← hq8, ← hq7, ← hq6, ← hq5,
      ← hq4, ← hq3] using hpowYraw

  have hV := twelfthFace_evalV410 h0 t2 a22 s22 vis w73 q54
    (p.coeff 1) (p.coeff 0) lambda a eps hh0 hroot hpowV hT hU
  have hX := twelfthFace_evalX410 h0 t2 a22 s22 vis w73 q54
    (p.coeff 1) (p.coeff 0) b42 b31 lambda a xi hh0 hroot hpowX hT hU
    hW
  have hVraw :
      (4096 : k) * q54.eval a -
          (8192 : k) * (p.coeff 1).eval a * s22.eval a -
          (7168 : k) * a22.eval a * vis.eval a +
          (23040 : k) * a22.eval a * (p.coeff 1).eval a -
          (6144 : k) * t2.eval a * w73.eval a -
          (10368 : k) * t2.eval a * (p.coeff 1).eval a * lambda +
          (8064 : k) * (t2.eval a) ^ 2 * vis.eval a +
          (14400 : k) * (t2.eval a) ^ 2 * (p.coeff 1).eval a =
        0 := by
    linear_combination (128 : k) * hV -
      ((112 : k) * a22.eval a - (126 : k) * (t2.eval a) ^ 2) * hT -
      (768 : k) * t2.eval a * hU
  have hXraw :
      (131072 : k) * b31.eval a -
          (196608 : k) * (p.coeff 1).eval a * w73.eval a -
          (131072 : k) * t2.eval a * b42.eval a -
          (129024 : k) * ((p.coeff 1).eval a) ^ 2 * lambda +
          (401408 : k) * t2.eval a * (p.coeff 1).eval a * vis.eval a -
          (143360 : k) * t2.eval a * ((p.coeff 1).eval a) ^ 2 =
        0 := by
    linear_combination (2048 : k) * hX -
      (-(6272 : k) * (p.coeff 1).eval a * t2.eval a) * hT -
      (24576 : k) * (p.coeff 1).eval a * hU -
      (16384 : k) * t2.eval a * hW
  have hY := twelfthFace_evalY410 h0 t2 a22 s22 vis w73 q54
    (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) lambda a eta hh0 hroot
    hpowY hT hU hW hVraw hXraw

  exact ⟨t2, a22, s22, vis, w73, q54, b42, b31, hp3, hp2, hq8, hq7,
    hq6, hq5, hq4, hq3, hT, hU, hW, hV, hX, hY⟩

end Max11DegreeRoutes
