import SpectralRadiusUpperTail.FlatHaarWeightBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

lemma fullSpectralSphereWeight_measurable (n : ℕ) (hn : 0 < n) (u : ℝ) (z : ℂ) :
    Measurable (fullSpectralSphereWeight n u z) := by
  letI := haarDirectionLaw_probability ℂ n hn
  have hm : Measurable (fun p : (Fin n → ℂ) × (Fin n → Fin n → ℂ) =>
      ENNReal.ofReal (gaussianMatrixWeight u p.1
        (spectralTiltTarget z (zeroExtendVector p.1)) p.2)) := by
    unfold gaussianMatrixWeight
    simp only [spectralTiltTarget, zeroExtendVector_fin]
    fun_prop
  exact hm.lintegral_prod_left'

lemma fullSpectralSphereWeight_le_one (n : ℕ) (hn : 0 < n)
    (u : ℝ) (hu : 0 < u) (z : ℂ) (x : Fin n → Fin n → ℂ) :
    fullSpectralSphereWeight n u z x ≤ 1 := by
  letI := haarDirectionLaw_probability ℂ n hn
  calc
    _ ≤ ∫⁻ _v, (1 : ℝ≥0∞) ∂haarDirectionLaw ℂ n := by
      apply lintegral_mono
      intro v
      exact ENNReal.ofReal_le_one.mpr (gaussianMatrixWeight_le_one u hu _ _ _)
    _ = 1 := by simp

#print axioms fullSpectralSphereWeight_measurable
#print axioms fullSpectralSphereWeight_le_one
end SpectralRadiusUpperTail
