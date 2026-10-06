import SpectralRadiusUpperTail.GaussianProductIsometry
import SpectralRadiusUpperTail.IidMatrixFlatten
import SpectralRadiusUpperTail.MatrixMoments
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp

/-- Apply the same Euclidean linear isometry to each row of a real array. -/
noncomputable def gaussianMatrixRowIsometry (n : ℕ)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : (Fin n × Fin n) → ℝ) : (Fin n × Fin n) → ℝ :=
  fun ij => ofLp (U (toLp 2 (fun j => x (ij.1, j)))) ij.2

/-- An iid standard Gaussian matrix law is invariant under a deterministic
orthogonal transformation of all rows. This is the array-level form of the
Euclidean Gaussian isometry theorem. -/
theorem gaussianMatrixLaw_map_rowIsometry (n : ℕ)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (gaussianMatrixLaw n).map (gaussianMatrixRowIsometry n U) =
      gaussianMatrixLaw n := by
  let rowU : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun x => ofLp (U (toLp 2 x))
  let μrow : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => standardNormal)
  let P : Measure (Fin n → Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n => μrow)
  let flat : (Fin n → Fin n → ℝ) → ((Fin n × Fin n) → ℝ) :=
    fun x ij => x ij.1 ij.2
  have hrow : μrow.map rowU = μrow := by
    exact gaussianProductLaw_map_euclidean_isometry U
  have hrowMeas : Measurable rowU := by
    dsimp [rowU]
    fun_prop
  have hP : P.map (fun x i => rowU (x i)) = P := by
    change (Measure.pi (fun _ : Fin n => μrow)).map
      (fun x i => rowU (x i)) = Measure.pi (fun _ : Fin n => μrow)
    rw [Measure.pi_map_pi (fun _ => hrowMeas.aemeasurable)]
    simp only [hrow]
  have hflat : P.map flat = gaussianMatrixLaw n := by
    exact iid_matrix_flatten_law standardNormal n
  have hflatMeas : Measurable flat := by fun_prop
  have hactionMeas : Measurable (gaussianMatrixRowIsometry n U) := by
    unfold gaussianMatrixRowIsometry
    fun_prop
  have hnestedMeas : Measurable
      (fun x : Fin n → Fin n → ℝ => fun i => rowU (x i)) := by
    fun_prop
  calc
    (gaussianMatrixLaw n).map (gaussianMatrixRowIsometry n U) =
        (P.map flat).map (gaussianMatrixRowIsometry n U) := by rw [hflat]
    _ = P.map ((gaussianMatrixRowIsometry n U) ∘ flat) := by
      rw [Measure.map_map hactionMeas hflatMeas]
    _ = P.map (flat ∘ (fun x i => rowU (x i))) := rfl
    _ = (P.map (fun x i => rowU (x i))).map flat := by
      rw [Measure.map_map hflatMeas hnestedMeas]
    _ = gaussianMatrixLaw n := by rw [hP, hflat]

#print axioms gaussianMatrixLaw_map_rowIsometry
end SpectralRadiusUpperTail
