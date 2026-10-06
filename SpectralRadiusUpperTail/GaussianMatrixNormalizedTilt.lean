import SpectralRadiusUpperTail.GaussianMatrixDensity
import SpectralRadiusUpperTail.GaussianMatrixWeightIntegrable
import SpectralRadiusUpperTail.ChangeMeasure

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n : ℕ}

lemma gaussianTiltedMatrixLaw_eq_normalizedTilt (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v : ℕ → 𝕂) (t : Fin n → 𝕂) :
    gaussianTiltedMatrixLaw μ a v t =
      normalizedTilt (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
        (fun x => ENNReal.ofReal (gaussianMatrixWeight a (fun j : Fin n => v j.val) t x)) := by
  let w := gaussianMatrixWeight a (fun j : Fin n => v j.val) t
  have hi := gaussianMatrixWeight_integrable μ a ha (fun j : Fin n => v j.val) t
  have hp := gaussianMatrixWeight_integral_pos μ a ha (fun j : Fin n => v j.val) t
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => (gaussianMatrixWeight_pos a _ t x).le))
  rw [gaussianTiltedMatrixLaw_density μ a ha,normalizedTilt,← he,gaussianMatrixWeight_integral] 
  congr 1
  funext x
  rw [ENNReal.ofReal_div_of_pos (by rwa [gaussianMatrixWeight_integral] at hp)]

#print axioms gaussianTiltedMatrixLaw_eq_normalizedTilt
end SpectralRadiusUpperTail
