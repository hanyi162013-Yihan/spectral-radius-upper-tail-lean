import SpectralRadiusUpperTail.MatrixExteriorPowerBound

namespace SpectralRadiusUpperTail

lemma matrixExteriorControl_radius_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (h : matrixExteriorControl A r C) :
    (spectralRadius ℂ A).toReal ≤ r := by
  have hs : spectralRadius ℂ A ≤ ENNReal.ofReal r := by
    apply iSup₂_le
    intro z hz
    have hzr : ‖z‖ ≤ r := by
      by_contra hn
      have hz' := (h z (le_of_lt (lt_of_not_ge hn))).1
      exact hz hz'
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hzr
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
  simpa only [ENNReal.toReal_ofReal hr] using ht

#print axioms matrixExteriorControl_radius_le
end SpectralRadiusUpperTail
