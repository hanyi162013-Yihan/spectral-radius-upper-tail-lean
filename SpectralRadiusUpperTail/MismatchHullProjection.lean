import SpectralRadiusUpperTail.CoordinateConvexHull

namespace SpectralRadiusUpperTail
open WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

noncomputable def euclideanCoordinateTail (N : ℕ) :
    EuclideanSpace 𝕂 (Fin (N+1)) →ₗ[ℝ] EuclideanSpace 𝕂 (Fin N) where
  toFun v := toLp 2 (fun i => v i.succ)
  map_add' v w := by ext i; rfl
  map_smul' a v := by ext i; rfl

lemma coordinateMismatch_tail (N : ℕ) (x y : EuclideanSpace 𝕂 (Fin (N+1))) :
    euclideanCoordinateTail (𝕂 := ℝ) N (coordinateMismatch x y) =
      coordinateMismatch (euclideanCoordinateTail N x) (euclideanCoordinateTail N y) := by
  ext i
  rfl

lemma mismatchHull_tail_image (N : ℕ) (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) :
    euclideanCoordinateTail (𝕂 := ℝ) N '' mismatchHull x A =
      mismatchHull (euclideanCoordinateTail N x) (euclideanCoordinateTail N '' A) := by
  unfold mismatchHull
  rw [LinearMap.image_convexHull]
  congr 1
  rw [Set.image_image, Set.image_image]
  congr 1

lemma mismatchHull_coordinates_unit_interval {N : ℕ} (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) (v : EuclideanSpace ℝ (Fin N))
    (hv : v ∈ mismatchHull x A) : ∀ i, 0 ≤ v i ∧ v i ≤ 1 := by
  let C : Set (EuclideanSpace ℝ (Fin N)) := {v | ∀ i, 0 ≤ v i ∧ v i ≤ 1}
  have hC : Convex ℝ C := by
    intro v hv w hw a b ha hb hab i
    change 0 ≤ a*v i+b*w i ∧ a*v i+b*w i ≤ 1
    constructor
    · exact add_nonneg (mul_nonneg ha (hv i).1) (mul_nonneg hb (hw i).1)
    · have h1 := mul_le_mul_of_nonneg_left (hv i).2 ha
      have h2 := mul_le_mul_of_nonneg_left (hw i).2 hb
      nlinarith only [h1, h2, hab]
  apply convexHull_min (t := C) ?_ hC hv
  rintro _ ⟨y, hy, rfl⟩ i
  change 0 ≤ (if x i=y i then (0 : ℝ) else 1) ∧ (if x i=y i then (0 : ℝ) else 1) ≤ 1
  split_ifs <;> norm_num

/-- A convex mismatch vector for a projected set lifts to a vector for the
original set, and the extra coordinate is between zero and one. -/
lemma mismatchHull_projection_lift (N : ℕ) (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) (v : EuclideanSpace ℝ (Fin N))
    (hv : v ∈ mismatchHull (euclideanCoordinateTail N x) (euclideanCoordinateTail N '' A)) :
    ∃ w ∈ mismatchHull x A,
      euclideanCoordinateTail (𝕂 := ℝ) N w=v ∧ 0 ≤ w 0 ∧ w 0 ≤ 1 := by
  rw [← mismatchHull_tail_image] at hv
  obtain ⟨w, hw, hproj⟩ := hv
  exact ⟨w, hw, hproj, mismatchHull_coordinates_unit_interval x A w hw 0⟩

#print axioms coordinateMismatch_tail
#print axioms mismatchHull_tail_image
#print axioms mismatchHull_coordinates_unit_interval
#print axioms mismatchHull_projection_lift
end SpectralRadiusUpperTail
