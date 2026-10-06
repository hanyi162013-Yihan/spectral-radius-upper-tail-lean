import SpectralRadiusUpperTail.FlatSpectralJointTilt
import SpectralRadiusUpperTail.GaussianMatrixNormalizedTilt
import SpectralRadiusUpperTail.PositiveWeightNormalizer

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n : ℕ} {L : ℝ}

lemma flatSpectralJointTilt_event_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (ν : Measure (flatUnitDirections 𝕂 n L)) [IsProbabilityMeasure ν]
    (a : ℝ) (ha : 0 < a) (b : 𝕂)
    (A : Set (Fin n → Fin n → 𝕂)) (hA : MeasurableSet A) (ε : ℝ≥0∞)
    (h : ∀ v : flatUnitDirections 𝕂 n L,
      gaussianTiltedMatrixLaw μ a (zeroExtendVector v.val)
        (spectralTiltTarget (n := n) b (zeroExtendVector v.val)) A ≤ ε) :
    flatSpectralJointTilt μ ν a b (Set.univ ×ˢ A) ≤ ε := by
  let M := Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))
  have hZ := positiveWeight_lintegral_bounds (ν.prod M) (flatSpectralJointWeight a b)
    (flatSpectralJointWeight_integrable μ ν a ha b)
    (fun p => gaussianMatrixWeight_pos a _ _ _)
  have hz (v : flatUnitDirections 𝕂 n L) := positiveWeight_lintegral_bounds M
    (gaussianMatrixWeight a v.val (spectralTiltTarget b (zeroExtendVector v.val)))
    (gaussianMatrixWeight_integrable μ a ha _ _)
    (fun x => gaussianMatrixWeight_pos a _ _ x)
  apply normalizedTilt_prod_event_le ν M
    (fun p => ENNReal.ofReal (flatSpectralJointWeight a b p))
    ((flatSpectralJointWeight_continuous a b).measurable.ennreal_ofReal) A hA ε hZ.1 hZ.2
  · exact fun v => (hz v).1
  · exact fun v => (hz v).2
  · intro v
    have he := gaussianTiltedMatrixLaw_eq_normalizedTilt μ a ha (zeroExtendVector v.val)
      (spectralTiltTarget (n := n) b (zeroExtendVector v.val))
    simp only [zeroExtendVector_fin] at he
    exact he ▸ h v

#print axioms flatSpectralJointTilt_event_le
end SpectralRadiusUpperTail
