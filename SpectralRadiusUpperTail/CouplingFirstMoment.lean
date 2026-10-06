import SpectralRadiusUpperTail.Centering
import Mathlib.MeasureTheory.Measure.Map

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Both prescribed first moments give the actual integrability and mean of
the source-minus-comparator increment under a coupling. -/
theorem coupling_difference_firstMoment (μ ν : Measure E) (Γ : Measure (E × E))
    (hfirst : Γ.map Prod.fst = μ) (hsecond : Γ.map Prod.snd = ν)
    (hμ : Integrable (fun x : E => x) μ) (hν : Integrable (fun x : E => x) ν) :
    Integrable (fun p : E × E => p.1-p.2) Γ ∧
      (∫ p, p.1-p.2 ∂Γ) = (∫ x : E, x ∂μ)-(∫ x : E, x ∂ν) := by
  have hi : Integrable (fun x : E => x) (Γ.map Prod.fst) := by rw [hfirst]; exact hμ
  have hj : Integrable (fun x : E => x) (Γ.map Prod.snd) := by rw [hsecond]; exact hν
  have hi' : Integrable (fun p : E × E => p.1) Γ := hi.comp_measurable measurable_fst
  have hj' : Integrable (fun p : E × E => p.2) Γ := hj.comp_measurable measurable_snd
  refine ⟨hi'.sub hj', ?_⟩
  rw [integral_sub hi' hj']
  have h1 := integral_map (μ := Γ) measurable_fst.aemeasurable hi.aestronglyMeasurable
  have h2 := integral_map (μ := Γ) measurable_snd.aemeasurable hj.aestronglyMeasurable
  rw [hfirst] at h1
  rw [hsecond] at h2
  rw [← h1, ← h2]

#print axioms coupling_difference_firstMoment
end SpectralRadiusUpperTail
