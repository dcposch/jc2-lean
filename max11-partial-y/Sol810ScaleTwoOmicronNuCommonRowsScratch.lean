import Sol810ScaleTwoOmicronRightReductionScratch

/-! # Common nu rows on the exact `(8,10)` omicron right witnesses

Both retained subbranches of `bridgeNuRightPacket810` imply the same three
root rows after cancellation against the exact depth-two omicron witnesses.
The subbranch witnesses are identified with the omicron witnesses by
cancellation of the nonzero linear factor; they are never reselected.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section OmicronNuCommonRows810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- The two nu subbranches have the same exact depth-two root consequences:
`b₅₁(a)=0`, `32w₂(a)-40u₂(a)=0`, and
`40a₄₁(a)-32b₆₃(a)=0`. -/
theorem bridgeOmicron_nuRight_commonRows810
    (p q : k[X][X]) (h0 : k[X]) (lambda a : k)
    (t0 v0 u0 s0 w0 v1 s1 u1 w1 b62 : k[X])
    (t1 v2 u2 s2 w2 b63 a41 b51 : k[X])
    (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0)
    (ht1 : t0 = h0 * t1) (hv2 : v1 = h0 * v2)
    (hu2 : u1 = h0 * u2) (hs2 : s1 = h0 * s2)
    (hw2 : w1 = h0 * w2) (hb63 : b62 = h0 * b63)
    (ha41 : p.coeff 4 = h0 * a41) (hb51 : q.coeff 5 = h0 * b51)
    (hnu :
      bridgeNuRightPacket810 p q h0 lambda a t0 v0 u0 s0 w0 v1 s1 u1 w1
        b62) :
    b51.eval a = 0 ∧
      (32 : k) * w2.eval a - (40 : k) * u2.eval a = 0 ∧
      (40 : k) * a41.eval a - (32 : k) * b63.eval a = 0 := by
  unfold bridgeNuRightPacket810 at hnu
  obtain ⟨_ht0z, _hu0z, _hw0z, _hv0z, _hs0z, _hq6z, _hsr, _hwr,
    _ha4r, _hb5r, _hpir, _hualt, _hd1, _hd2, _hd3, _hd4, _hd5,
    hv1z, hu1z, hb62z, _ha4z, _hs1z, _hw1z, _hb5z, _hdp6, _hdp5,
    _hdq8, _hdq7, _hdq6, _hdp4, _hdq5, _hdisj, hsub⟩ := hnu
  rcases hsub with hfirst | hsecond
  · obtain ⟨_hu1z', t1', u2', w2', b51', sigma, rho, pi, ht1', hu2',
      hw2', hb51', _hsigma, hrho, _hpi, _hdp5', _hdq7', _hdq5',
      _hdsigma, _hdrho, _hdpi, hwrow, hb51row, _hvprod, _hrhorow,
      _hkz⟩ := hfirst
    have ht1eq : t1' = t1 :=
      mul_left_cancel₀ hh0 (ht1'.symm.trans ht1)
    have hu2eq : u2' = u2 :=
      mul_left_cancel₀ hh0 (hu2'.symm.trans hu2)
    have hw2eq : w2' = w2 :=
      mul_left_cancel₀ hh0 (hw2'.symm.trans hw2)
    have hb51eq : b51' = b51 :=
      mul_left_cancel₀ hh0 (hb51'.symm.trans hb51)
    have hwroot :
        (32 : k) * w2.eval a - (40 : k) * u2.eval a = 0 := by
      rw [ht1eq, hu2eq, hw2eq] at hwrow
      simpa [hv1z] using hwrow
    have hb51root : b51.eval a = 0 := by
      rw [hb51eq] at hb51row
      have hrow := hb51row
      simp [hb62z, hv1z] at hrow
      linear_combination (1 / 2560 : k) * hrow
    have hfactor :
        h0 *
            ((40 : k[X]) * a41 - (32 : k[X]) * b63 +
              (5 : k[X]) * h0 * v2 ^ 2) =
          h0 * (h0 * rho) := by
      calc
        _ = (40 : k[X]) * (h0 * a41) - (32 : k[X]) * (h0 * b63) +
              (5 : k[X]) * (h0 * v2) ^ 2 := by ring
        _ = (40 : k[X]) * p.coeff 4 - (32 : k[X]) * b62 +
              (5 : k[X]) * v1 ^ 2 := by rw [← ha41, ← hb63, ← hv2]
        _ = h0 ^ 2 * rho := hrho
        _ = h0 * (h0 * rho) := by ring
    have hcancel := mul_left_cancel₀ hh0 hfactor
    have heval := congrArg (Polynomial.eval a) hcancel
    have habroot :
        (40 : k) * a41.eval a - (32 : k) * b63.eval a = 0 := by
      simpa [hroot] using heval
    exact ⟨hb51root, hwroot, habroot⟩
  · obtain ⟨_hbwall, _ha4wall, _huwall, t1', omega, sigma, beta, _ht1',
      homega, _hsigma, hbeta, _hdsigma, _hdbeta, homegarow, hbetarow,
      rhoc, hrhoc, hrhocrow⟩ := hsecond
    have homegaFactor :
        h0 * ((4 : k[X]) * w2 - (5 : k[X]) * u2) = h0 * omega := by
      calc
        _ = (4 : k[X]) * (h0 * w2) - (5 : k[X]) * (h0 * u2) := by ring
        _ = (4 : k[X]) * w1 - (5 : k[X]) * u1 := by rw [← hw2, ← hu2]
        _ = h0 * omega := homega
    have homegaCancel := mul_left_cancel₀ hh0 homegaFactor
    have homegaEval := congrArg (Polynomial.eval a) homegaCancel
    have homegaRoot : omega.eval a = 0 := by
      have hrow := homegarow
      simp [hv1z] at hrow
      linear_combination (1 / 8 : k) * hrow
    have hwroot :
        (32 : k) * w2.eval a - (40 : k) * u2.eval a = 0 := by
      have hrow :
          (4 : k) * w2.eval a - (5 : k) * u2.eval a = omega.eval a := by
        simpa using homegaEval
      linear_combination (8 : k) * hrow + (8 : k) * homegaRoot
    have hbetaFactor :
        h0 *
            ((16 : k[X]) * b51 - (5 : k[X]) * h0 * u2 * v2) =
          h0 * beta := by
      calc
        _ = (16 : k[X]) * (h0 * b51) -
              (5 : k[X]) * (h0 * u2) * (h0 * v2) := by ring
        _ = (16 : k[X]) * q.coeff 5 - (5 : k[X]) * u1 * v1 := by
              rw [← hb51, ← hu2, ← hv2]
        _ = h0 * beta := hbeta
    have hbetaCancel := mul_left_cancel₀ hh0 hbetaFactor
    have hbetaEval := congrArg (Polynomial.eval a) hbetaCancel
    have hbetaRoot : beta.eval a = 0 := by
      have hrow := hbetarow
      simp [hv1z] at hrow
      linear_combination (1 / 32 : k) * hrow
    have hb51root : b51.eval a = 0 := by
      have hrow : (16 : k) * b51.eval a = beta.eval a := by
        simpa [hroot] using hbetaEval
      linear_combination (1 / 16 : k) * hrow +
        (1 / 16 : k) * hbetaRoot
    have hrhocFactor :
        h0 *
            ((40 : k[X]) * a41 - (32 : k[X]) * b63 +
              (5 : k[X]) * h0 * v2 ^ 2) =
          h0 * rhoc := by
      calc
        _ = (40 : k[X]) * (h0 * a41) - (32 : k[X]) * (h0 * b63) +
              (5 : k[X]) * (h0 * v2) ^ 2 := by ring
        _ = (40 : k[X]) * p.coeff 4 - (32 : k[X]) * b62 +
              (5 : k[X]) * v1 ^ 2 := by rw [← ha41, ← hb63, ← hv2]
        _ = h0 * rhoc := hrhoc
    have hrhocCancel := mul_left_cancel₀ hh0 hrhocFactor
    have hrhocEval := congrArg (Polynomial.eval a) hrhocCancel
    have hrhocRoot : rhoc.eval a = 0 := by
      have hrow := hrhocrow
      simp [hu1z] at hrow
      exact hrow
    have habroot :
        (40 : k) * a41.eval a - (32 : k) * b63.eval a = 0 := by
      have hrow :
          (40 : k) * a41.eval a - (32 : k) * b63.eval a = rhoc.eval a := by
        simpa [hroot] using hrhocEval
      linear_combination hrow + hrhocRoot
    exact ⟨hb51root, hwroot, habroot⟩

end OmicronNuCommonRows810

#print axioms bridgeOmicron_nuRight_commonRows810

end Max11DegreeRoutes
