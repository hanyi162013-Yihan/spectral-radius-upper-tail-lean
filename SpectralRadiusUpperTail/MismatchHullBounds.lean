import SpectralRadiusUpperTail.MismatchHullProjection
import SpectralRadiusUpperTail.TalagrandQuadraticInterpolation

namespace SpectralRadiusUpperTail
open Set
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂]

lemma mismatchHull_norm_sq_le_dimension {N : ℕ} (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) (v : EuclideanSpace ℝ (Fin N))
    (hv : v ∈ mismatchHull x A) : ‖v‖^2 ≤ (N : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨h0, h1⟩ := mismatchHull_coordinates_unit_interval x A v hv i
      rw [Real.norm_eq_abs, sq_abs]
      nlinarith
    _ = _ := by simp

/-- The zero interpolation weight does not require the matching fiber to be
nonempty. This separate projection bound handles empty or null fibers. -/
lemma mismatchHull_projection_energy_lift (N : ℕ) (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) (v : EuclideanSpace ℝ (Fin N))
    (hv : v ∈ mismatchHull (euclideanCoordinateTail N x) (euclideanCoordinateTail N '' A)) :
    ∃ w ∈ mismatchHull x A, ‖w‖^2 ≤ ‖v‖^2+1 := by
  obtain ⟨w, hw, htail, h0, h1⟩ := mismatchHull_projection_lift N x A v hv
  refine ⟨w, hw, ?_⟩
  have he : w=euclideanConsReal N (w 0) v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · have hj := congrArg (fun z : EuclideanSpace ℝ (Fin N) => z j) htail
      exact hj
  rw [he, euclideanConsReal_norm_sq]
  nlinarith

#print axioms mismatchHull_norm_sq_le_dimension
#print axioms mismatchHull_projection_energy_lift
end SpectralRadiusUpperTail
