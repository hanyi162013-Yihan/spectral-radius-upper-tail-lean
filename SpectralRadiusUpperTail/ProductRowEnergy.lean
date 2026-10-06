import SpectralRadiusUpperTail.IndependentEnergy
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {α E ι : Type*} [MeasurableSpace α] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma integral_product_coordinate (μ : Measure α) [IsProbabilityMeasure μ]
    (i : ι) (g : α → E) (hg : AEStronglyMeasurable g μ) :
    (∫ s, g (s i) ∂Measure.pi (fun _ : ι => μ)) = ∫ x, g x ∂μ := by
  have he := measurePreserving_eval (fun _ : ι => μ) i
  have hg' : AEStronglyMeasurable g ((Measure.pi (fun _ : ι => μ)).map (fun s => s i)) := by
    rw [he.map_eq]
    exact hg
  have h := integral_map (μ := Measure.pi (fun _ : ι => μ)) (φ := fun s : ι → α => s i)
    (f := g) (measurable_pi_apply i).aemeasurable hg'
  rw [he.map_eq] at h
  exact h.symm

variable [MeasurableSpace E] [BorelSpace E]

theorem product_sum_norm_sq (μ : Measure α) [IsProbabilityMeasure μ]
    (F : ι → α → E) (hF : ∀ i, MemLp (F i) 2 μ)
    (hmean : ∀ i, (∫ x, F i x ∂μ) = 0) :
    (∫ s, ‖∑ i, F i (s i)‖^2 ∂Measure.pi (fun _ : ι => μ)) =
      ∑ i, ∫ x, ‖F i x‖^2 ∂μ := by
  have hX (i : ι) : MemLp (fun s : ι → α => F i (s i)) 2 (Measure.pi (fun _ : ι => μ)) :=
    (hF i).comp_measurePreserving (measurePreserving_eval _ i)
  have hi := iIndepFun_pi (fun i => (hF i).aestronglyMeasurable.aemeasurable)
  have hm (i : ι) : (∫ s, F i (s i) ∂Measure.pi (fun _ : ι => μ)) = 0 := by
    rw [integral_product_coordinate μ i _ (hF i).aestronglyMeasurable, hmean i]
  rw [independent_sum_norm_sq _ _ hX (fun _ _ h => hi.indepFun h) hm]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_product_coordinate μ i _ ((hF i).aestronglyMeasurable.norm.pow 2)

section Scalar
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

theorem iid_linear_row_energy (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ι → 𝕂) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hmean : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) :
    (∫ s, ‖∑ i, v i*s i‖^2 ∂Measure.pi (fun _ : ι => μ)) = ∑ i, ‖v i‖^2 := by
  have hF (i : ι) := hX.const_mul (v i)
  have hm (i : ι) : (∫ x, v i*x ∂μ) = 0 := by rw [integral_const_mul, hmean, mul_zero]
  rw [product_sum_norm_sq μ (fun i x => v i*x) hF hm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [norm_mul, mul_pow]
  rw [integral_const_mul, hvar, mul_one]

end Scalar
#print axioms iid_linear_row_energy
end SpectralRadiusUpperTail
