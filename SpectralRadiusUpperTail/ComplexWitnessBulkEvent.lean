import SpectralRadiusUpperTail.ComplexSphereWitnessLog
import SpectralRadiusUpperTail.ComplexResidualSphereWitness

namespace SpectralRadiusUpperTail
open scoped ENNReal

lemma complex_witness_on_bulk_event (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u)
    (x : Fin n → Fin n → ℂ) (z : ℂ) (v : EuclideanSpace ℂ (Fin n))
    (hv : ‖v‖ = 1) (d L : ℝ)
    (hd : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x-z • 1) v‖^2 ≤ d)
    (hbulk : regularizedResidualLogDet x z (2*u)/(n : ℝ) ≤ L) :
    ENNReal.ofReal (Real.exp ((n : ℝ)*(Real.log u-1-d/u-L))) ≤ fullSpectralSphereWeight n u z x := by
  let H := spectralResidualGram x z
  have hH := spectralResidualGram_posSemidef x z
  have he := matrix_gram_energy (normalizedArray x-z • (1 : Matrix (Fin n) (Fin n) ℂ)) v
  have hd' : (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re ≤ d := by
    convert! he.le.trans hd using 1
  have hw : (n : ℝ)*(Real.log u-1-d/u)-regularizedResidualLogDet x z (2*u) ≤
      Real.log (sphereQuadraticIntegral ℂ n ((n : ℝ)/u) H) := by
    convert! complex_sphere_witness_log n hn u hu H hH v hv d hd' using 1
  have hb := (div_le_iff₀ (Nat.cast_pos.mpr hn)).mp hbulk
  have hl : (n : ℝ)*(Real.log u-1-d/u-L) ≤
      Real.log (sphereQuadraticIntegral ℂ n ((n : ℝ)/u) H) := by nlinarith
  have hp := Real.exp_le_exp.mpr hl
  rw [Real.exp_log (sphereQuadraticIntegral_pos ℂ n hn _ (by positivity) H hH)] at hp
  rw [fullSphereWeight_eq_quadratic n hn u hu]
  exact ENNReal.ofReal_le_ofReal hp

#print axioms complex_witness_on_bulk_event
end SpectralRadiusUpperTail
