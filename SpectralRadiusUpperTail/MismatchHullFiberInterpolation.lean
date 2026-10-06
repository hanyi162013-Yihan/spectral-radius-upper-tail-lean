import SpectralRadiusUpperTail.MismatchHullProjection
import SpectralRadiusUpperTail.TalagrandQuadraticInterpolation

namespace SpectralRadiusUpperTail
open WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

noncomputable def euclideanWithHead (N : ℕ) (t : 𝕂) (v : EuclideanSpace 𝕂 (Fin N)) :
    EuclideanSpace 𝕂 (Fin (N+1)) := toLp 2 (Fin.cons t (fun i => v i))

noncomputable def euclideanZeroHead (N : ℕ) :
    EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin (N+1)) where
  toFun v := euclideanWithHead N 0 v
  map_add' v w := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [euclideanWithHead]
  map_smul' a v := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [euclideanWithHead]

lemma coordinateMismatch_with_matching_head (N : ℕ) (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (y : EuclideanSpace 𝕂 (Fin N)) :
    coordinateMismatch x (euclideanWithHead N (x 0) y) =
      euclideanZeroHead N (coordinateMismatch (euclideanCoordinateTail N x) y) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [coordinateMismatch, euclideanWithHead, euclideanZeroHead]
  · rfl

lemma mismatchHull_fiber_embed (N : ℕ) (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) (v : EuclideanSpace ℝ (Fin N))
    (hv : v ∈ mismatchHull (euclideanCoordinateTail N x)
      {y | euclideanWithHead N (x 0) y ∈ A}) :
    euclideanZeroHead N v ∈ mismatchHull x A := by
  have him : euclideanZeroHead N v ∈ euclideanZeroHead N ''
      mismatchHull (euclideanCoordinateTail N x) {y | euclideanWithHead N (x 0) y ∈ A} :=
    ⟨v, hv, rfl⟩
  unfold mismatchHull at him ⊢
  rw [LinearMap.image_convexHull] at him
  apply convexHull_mono (𝕜 := ℝ) ?_ him
  rintro _ ⟨u, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨euclideanWithHead N (x 0) y, hy, coordinateMismatch_with_matching_head N x y⟩

/-- The deterministic fiber recursion behind the product induction: combine
a vector from the matching fiber with a projected vector, paying at most b²
for the additional coordinate. -/
lemma mismatchHull_fiber_interpolation (N : ℕ) (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) (v w : EuclideanSpace ℝ (Fin N))
    (hv : v ∈ mismatchHull (euclideanCoordinateTail N x)
      {y | euclideanWithHead N (x 0) y ∈ A})
    (hw : w ∈ mismatchHull (euclideanCoordinateTail N x) (euclideanCoordinateTail N '' A))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    ∃ u ∈ mismatchHull x A, ‖u‖^2 ≤ a*‖v‖^2+b*‖w‖^2+b^2 := by
  obtain ⟨w', hw', htail, hhead0, hhead1⟩ := mismatchHull_projection_lift N x A w hw
  have hv' := mismatchHull_fiber_embed N x A v hv
  let u := a • euclideanZeroHead N v+b • w'
  have hu : u ∈ mismatchHull x A := (convex_convexHull ℝ _) hv' hw' ha hb hab
  refine ⟨u, hu, ?_⟩
  have he : u=euclideanConsReal N (b*w' 0) (a • v+b • w) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [u, euclideanZeroHead, euclideanWithHead, euclideanConsReal]
    · have hj := congrArg (fun z : EuclideanSpace ℝ (Fin N) => z j) htail
      change w' j.succ=w j at hj
      change a*v j+b*w' j.succ=a*v j+b*w j
      rw [hj]
  rw [he]
  apply talagrand_cons_interpolation_bound N v w a b (w' 0) ha hb hab
  exact abs_le.mpr ⟨by linarith, hhead1⟩

#print axioms coordinateMismatch_with_matching_head
#print axioms mismatchHull_fiber_embed
#print axioms mismatchHull_fiber_interpolation
end SpectralRadiusUpperTail
