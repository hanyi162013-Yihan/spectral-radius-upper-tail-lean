import SpectralRadiusUpperTail.TalagrandProductIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂]

/-- The iid product law transported from coordinate arrays to Euclidean
space. -/
noncomputable def talagrandEuclideanProductLaw
    (μ : Measure 𝕂) (N : ℕ) : Measure (EuclideanSpace 𝕂 (Fin N)) :=
  (Measure.pi fun _ : Fin N => μ).map (toLp 2)

instance talagrandEuclideanProductLaw_probability
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (N : ℕ) :
    IsProbabilityMeasure (talagrandEuclideanProductLaw μ N) := by
  unfold talagrandEuclideanProductLaw
  exact Measure.isProbabilityMeasure_map
    (WithLp.measurable_toLp 2 _).aemeasurable

lemma talagrandEuclideanProductLaw_real
    (μ : Measure 𝕂) (N : ℕ)
    (A : Set (EuclideanSpace 𝕂 (Fin N))) (hA : MeasurableSet A) :
    (talagrandEuclideanProductLaw μ N).real A =
      (Measure.pi (fun _ : Fin N => μ)).real
        {z : Fin N → 𝕂 | (toLp 2 z : EuclideanSpace 𝕂 (Fin N)) ∈ A} := by
  unfold talagrandEuclideanProductLaw
  exact map_measureReal_apply (WithLp.measurable_toLp 2 _) hA

lemma talagrandEuclideanProductLaw_integral
    (μ : Measure 𝕂) (N : ℕ)
    (f : EuclideanSpace 𝕂 (Fin N) → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂talagrandEuclideanProductLaw μ N) =
      ∫ z : Fin N → 𝕂,
        f (toLp 2 z : EuclideanSpace 𝕂 (Fin N))
          ∂Measure.pi (fun _ : Fin N => μ) := by
  unfold talagrandEuclideanProductLaw
  exact integral_map_of_stronglyMeasurable
    (WithLp.measurable_toLp 2 _) hf.stronglyMeasurable

#print axioms talagrandEuclideanProductLaw_probability
#print axioms talagrandEuclideanProductLaw_real
#print axioms talagrandEuclideanProductLaw_integral
end SpectralRadiusUpperTail
