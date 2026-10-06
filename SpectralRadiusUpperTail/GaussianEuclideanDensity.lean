import SpectralRadiusUpperTail.GaussianProductDensity
import SpectralRadiusUpperTail.GaussianNormIntegrable
import SpectralRadiusUpperTail.NormalizedTiltMap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
open scoped BigOperators ENNReal

lemma standardNormal_euclidean_eq_normalizedTilt (n : ℕ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => standardNormal)).map (toLp 2) =
      normalizedTilt (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (fun x => ENNReal.ofReal (Real.exp (-(1/2)*‖x‖^2))) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hz := gaussian_norm_normalizer_bounds (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (1/2) (by norm_num)
  have he := normalizedTilt_map_measurePreserving (volume : Measure (Fin n → ℝ))
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (toLp 2)
    (PiLp.volume_preserving_toLp (Fin n))
    (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Real.exp (-(1/2)*‖x‖^2)))
    (by fun_prop) hz.1
  rw [← he,standardNormal_pi_eq_normalizedTilt]
  congr 2
  funext x
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 2
  change -(∑ i, (x i)^2)/2 = -(1/2)*(∑ i, (x i)^2)
  ring

#print axioms standardNormal_euclidean_eq_normalizedTilt
end SpectralRadiusUpperTail
