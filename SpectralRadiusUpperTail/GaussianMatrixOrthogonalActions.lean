import SpectralRadiusUpperTail.GaussianMatrixRowIsometry
import SpectralRadiusUpperTail.GaussianProductPermutation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp

/-- Apply a Euclidean isometry to each column of a real array. -/
noncomputable def gaussianMatrixColumnIsometry (n : ℕ)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : (Fin n × Fin n) → ℝ) : (Fin n × Fin n) → ℝ :=
  fun ij => ofLp (U (toLp 2 (fun i => x (i, ij.2)))) ij.1

theorem gaussianMatrixLaw_map_columnIsometry (n : ℕ)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (gaussianMatrixLaw n).map (gaussianMatrixColumnIsometry n U) =
      gaussianMatrixLaw n := by
  let τ : ((Fin n × Fin n) → ℝ) → ((Fin n × Fin n) → ℝ) :=
    fun x ij => x (ij.2, ij.1)
  have hτ : (gaussianMatrixLaw n).map τ = gaussianMatrixLaw n :=
    gaussianMatrixLaw_map_transpose n
  have hτmeas : Measurable τ := by fun_prop
  have hrowMeas : Measurable (gaussianMatrixRowIsometry n U) := by
    unfold gaussianMatrixRowIsometry
    fun_prop
  have hcol : gaussianMatrixColumnIsometry n U =
      τ ∘ gaussianMatrixRowIsometry n U ∘ τ := by
    funext x ij
    cases ij
    rfl
  rw [hcol]
  change (gaussianMatrixLaw n).map
    ((τ ∘ gaussianMatrixRowIsometry n U) ∘ τ) = gaussianMatrixLaw n
  rw [← Measure.map_map (hτmeas.comp hrowMeas) hτmeas,
    hτ, ← Measure.map_map hτmeas hrowMeas,
    gaussianMatrixLaw_map_rowIsometry, hτ]

/-- Independent deterministic orthogonal changes of row and column
coordinates preserve the entire iid Gaussian matrix law. -/
theorem gaussianMatrixLaw_map_twoSidedIsometry (n : ℕ)
    (U V : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n)) :
    (gaussianMatrixLaw n).map
      (fun x => gaussianMatrixColumnIsometry n V
        (gaussianMatrixRowIsometry n U x)) = gaussianMatrixLaw n := by
  have hrowMeas : Measurable (gaussianMatrixRowIsometry n U) := by
    unfold gaussianMatrixRowIsometry
    fun_prop
  have hcolMeas : Measurable (gaussianMatrixColumnIsometry n V) := by
    unfold gaussianMatrixColumnIsometry
    fun_prop
  change (gaussianMatrixLaw n).map
    (gaussianMatrixColumnIsometry n V ∘ gaussianMatrixRowIsometry n U) =
      gaussianMatrixLaw n
  rw [← Measure.map_map hcolMeas hrowMeas,
    gaussianMatrixLaw_map_rowIsometry,
    gaussianMatrixLaw_map_columnIsometry]

#print axioms gaussianMatrixLaw_map_columnIsometry
#print axioms gaussianMatrixLaw_map_twoSidedIsometry
end SpectralRadiusUpperTail
