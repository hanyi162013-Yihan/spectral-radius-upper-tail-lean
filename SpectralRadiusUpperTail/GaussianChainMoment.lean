import SpectralRadiusUpperTail.GaussianBridgeArray
import SpectralRadiusUpperTail.GaussianBridgeMoment
import SpectralRadiusUpperTail.MatrixChainExpansion

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma gaussianBridgeProduct_fromArray {d : ℕ} (t : ℝ) (l : ℕ)
    (D : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ)
    (x : Fin l → Fin d × Fin d → ℝ) :
    gaussianBridgeProduct t l D (gaussianBridgeFromArray d l x) =
      gaussianMatrixChain d l D (fun j => t • gaussianEntryBlock (x j)) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    simp only [gaussianBridgeProduct, gaussianBridgeFromArray, gaussianMatrixChain, ih]

/-- Exact Gaussian sandwich iteration in the ordinary finite array model. -/
theorem gaussian_matrix_chain_second_moment {d : ℕ} (t : ℝ) (l : ℕ)
    (D : Fin (l+1) → Matrix (Fin d) (Fin d) ℝ) :
    Integrable (fun x : Fin l → Fin d × Fin d → ℝ =>
      ‖gaussianMatrixChain d l D (fun j => t • gaussianEntryBlock (x j))‖^2)
      (Measure.pi (fun _ => Measure.pi (fun _ => standardNormal))) ∧
    (∫ x : Fin l → Fin d × Fin d → ℝ,
      ‖gaussianMatrixChain d l D (fun j => t • gaussianEntryBlock (x j))‖^2
      ∂Measure.pi (fun _ => Measure.pi (fun _ => standardNormal))) =
      (t^2)^l * ∏ i, ‖D i‖^2 := by
  have hp := gaussianBridgeFromArray_measurePreserving d l
  have hm := gaussianBridgeProduct_second_moment t l D
  have hi := hp.integrable_comp_of_integrable hm.1
  have he := integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hm.1.aestronglyMeasurable)
  rw [hp.map_eq] at he
  constructor
  · simpa only [Function.comp_def, gaussianBridgeProduct_fromArray] using hi
  · calc
      _ = ∫ x, ‖gaussianBridgeProduct t l D x‖^2 ∂gaussianBridgeLaw d l := by
        simpa only [gaussianBridgeProduct_fromArray] using he.symm
      _ = _ := hm.2

#print axioms gaussian_matrix_chain_second_moment
end SpectralRadiusUpperTail
