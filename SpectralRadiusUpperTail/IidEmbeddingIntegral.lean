import SpectralRadiusUpperTail.IidIndexEmbedding
import SpectralRadiusUpperTail.IidMixedMoments

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {σ τ υ ω 𝕂 : Type*} [Fintype σ] [Fintype τ] [Fintype υ] [Fintype ω]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma iidIndexEmbedding_integral (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (e : τ → σ) (he : Function.Injective e) (F : (τ → 𝕂) → 𝕂)
    (hF : AEStronglyMeasurable F (Measure.pi (fun _ : τ => μ))) :
    (∫ x : σ → 𝕂, F (fun i => x (e i)) ∂Measure.pi (fun _ : σ => μ)) =
      ∫ y : τ → 𝕂, F y ∂Measure.pi (fun _ : τ => μ) := by
  have hm := iidIndexEmbedding_law μ e he
  have hf : Measurable (fun x : σ → 𝕂 => fun i : τ => x (e i)) := by fun_prop
  have h := integral_map hf.aemeasurable (hm.symm ▸ hF)
  rw [hm] at h
  exact h.symm

/-- Actual paired iid word moments are invariant under injective index relabeling. -/
lemma iidWordPair_embedding_expectation (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (e : τ → σ) (he : Function.Injective e) (f : υ → τ) (g : ω → τ) :
    (∫ x : σ → 𝕂, (∏ a, x (e (f a)))*(∏ b, star (x (e (g b))))
      ∂Measure.pi (fun _ : σ => μ)) =
    (∫ y : τ → 𝕂, (∏ a, y (f a))*(∏ b, star (y (g b)))
      ∂Measure.pi (fun _ : τ => μ)) := by
  exact iidIndexEmbedding_integral μ e he
    (fun y : τ → 𝕂 => (∏ a, y (f a))*(∏ b, star (y (g b)))) (by fun_prop)

#print axioms iidIndexEmbedding_integral
#print axioms iidWordPair_embedding_expectation
end SpectralRadiusUpperTail
