import SpectralRadiusUpperTail.TalagrandMaskAdmissibility
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

/-- The convex hull of Boolean masks that permit agreement on all zero
coordinates. This finite mask family has closed admissibility events for
compact target sets. -/
noncomputable def dominatingMismatchHull {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) :
    Set (EuclideanSpace ℝ (Fin N)) :=
  convexHull ℝ (booleanMismatchVector N ''
    {b | dominatingMaskAdmissible x A b})

lemma actualMismatchMask_admissible {N : ℕ}
    (x y : EuclideanSpace 𝕂 (Fin N)) :
    dominatingMaskAdmissible x {y}
      (fun i => decide (x i ≠ y i)) := by
  refine ⟨y, by simp, ?_⟩
  intro i hi
  by_contra hne
  simp [hne] at hi

lemma actualMismatchMask_vector {N : ℕ}
    (x y : EuclideanSpace 𝕂 (Fin N)) :
    booleanMismatchVector N (fun i => decide (x i ≠ y i)) =
      coordinateMismatch x y := by
  ext i
  by_cases hi : x i = y i <;>
    simp [booleanMismatchVector, coordinateMismatch, hi]

lemma mismatchHull_subset_dominatingHull {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) :
    mismatchHull x A ⊆ dominatingMismatchHull x A := by
  unfold mismatchHull dominatingMismatchHull
  apply convexHull_mono
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨fun i => decide (x i ≠ y i), ?_, actualMismatchMask_vector x y⟩
  refine ⟨y, hy, ?_⟩
  intro i hi
  by_contra hne
  simp [hne] at hi

/-- Every admissible dominating mask majorizes the actual disagreement
mask of one target point, coordinate by coordinate. -/
lemma admissible_mask_majorizes_mismatch {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N)))
    (b : Fin N → Bool) (hb : dominatingMaskAdmissible x A b) :
    ∃ y ∈ A, ∀ i,
      coordinateMismatch x y i ≤ booleanMismatchVector N b i := by
  obtain ⟨y, hy, hxy⟩ := hb
  refine ⟨y, hy, ?_⟩
  intro i
  by_cases heq : x i = y i
  · by_cases hbi : b i <;>
      simp [coordinateMismatch, booleanMismatchVector, heq, hbi]
  · have hbi : b i = true := by
      cases h : b i
      · exact (heq (hxy i h)).elim
      · rfl
    simp [coordinateMismatch, booleanMismatchVector, heq, hbi]

/-- A convex combination of dominating masks has an actual convex
mismatch vector below it in every coordinate. -/
lemma dominatingHull_has_lower_actual_vector {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N)))
    (z : EuclideanSpace ℝ (Fin N)) (hz : z ∈ dominatingMismatchHull x A) :
    ∃ w ∈ mismatchHull x A, ∀ i, w i ≤ z i := by
  let C : Set (EuclideanSpace ℝ (Fin N)) :=
    {z | ∃ w ∈ mismatchHull x A, ∀ i, w i ≤ z i}
  have hC : Convex ℝ C := by
    intro z hz z' hz' a b ha hb hab
    obtain ⟨w, hw, hle⟩ := hz
    obtain ⟨w', hw', hle'⟩ := hz'
    refine ⟨a • w+b • w', (convex_convexHull ℝ _) hw hw' ha hb hab, ?_⟩
    intro i
    change a*w i+b*w' i ≤ a*z i+b*z' i
    exact add_le_add (mul_le_mul_of_nonneg_left (hle i) ha)
      (mul_le_mul_of_nonneg_left (hle' i) hb)
  have hgen : booleanMismatchVector N ''
      {b | dominatingMaskAdmissible x A b} ⊆ C := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨y, hy, hle⟩ := admissible_mask_majorizes_mismatch x A b hb
    exact ⟨coordinateMismatch x y,
      subset_convexHull ℝ _ ⟨y, hy, rfl⟩, hle⟩
  exact convexHull_min hgen hC hz

#print axioms mismatchHull_subset_dominatingHull
#print axioms admissible_mask_majorizes_mismatch
#print axioms dominatingHull_has_lower_actual_vector
end SpectralRadiusUpperTail
