import SpectralRadiusUpperTail.CoordinateConvexHull

namespace SpectralRadiusUpperTail
open Set
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂]

lemma euclidean_norm_le_of_coordinate_bound {N : ℕ}
    (u : EuclideanSpace 𝕂 (Fin N)) (v : EuclideanSpace ℝ (Fin N))
    (D : ℝ) (hD : 0 ≤ D) (h : ∀ i, ‖u i‖ ≤ D*v i) :
    ‖u‖ ≤ D*‖v‖ := by
  have hs : ‖u‖^2 ≤ D^2*‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := (sq_le_sq₀ (norm_nonneg (u i)) ((norm_nonneg (u i)).trans (h i))).mpr (h i)
    simpa only [mul_pow, Real.norm_eq_abs, sq_abs] using hh
  have hnn := mul_nonneg hD (norm_nonneg v)
  nlinarith [norm_nonneg u]

/-- Euclidean separation from a convex set forces every convex combination
of mismatch indicators to have large Euclidean norm. -/
lemma mismatchHull_norm_lower {N : ℕ} (x : EuclideanSpace 𝕂 (Fin N))
    (S A : Set (EuclideanSpace 𝕂 (Fin N))) (hA : Convex ℝ A) (hSA : S ⊆ A)
    (D t : ℝ) (hD : 0 < D) (hdiam : ∀ y ∈ S, ∀ i, ‖x i-y i‖ ≤ D)
    (hsep : ∀ y ∈ A, t ≤ dist x y)
    (v : EuclideanSpace ℝ (Fin N)) (hv : v ∈ mismatchHull x S) :
    t/D ≤ ‖v‖ := by
  obtain ⟨y, hy, hcoord⟩ := mismatchHull_witness x S A hA hSA D hD.le hdiam v hv
  have hn := euclidean_norm_le_of_coordinate_bound (x-y) v D hD.le hcoord
  have ht := hsep y hy
  rw [dist_eq_norm] at ht
  apply (div_le_iff₀ hD).mpr
  nlinarith only [hn, ht]

#print axioms euclidean_norm_le_of_coordinate_bound
#print axioms mismatchHull_norm_lower
end SpectralRadiusUpperTail
