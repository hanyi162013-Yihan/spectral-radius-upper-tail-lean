import SpectralRadiusUpperTail.MismatchHullBounds
import Mathlib.Analysis.Convex.Topology

namespace SpectralRadiusUpperTail
open WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

noncomputable def booleanMismatchVector (N : ℕ) (b : Fin N → Bool) :
    EuclideanSpace ℝ (Fin N) := toLp 2 (fun i => if b i then 1 else 0)

lemma coordinateMismatch_mem_boolean_range {N : ℕ} (x y : EuclideanSpace 𝕂 (Fin N)) :
    coordinateMismatch x y ∈ range (booleanMismatchVector N) := by
  classical
  refine ⟨fun i => decide (x i ≠ y i), ?_⟩
  ext i
  by_cases hi : x i=y i <;> simp [booleanMismatchVector, coordinateMismatch, hi]

/-- Even for an infinite entry space, only finitely many disagreement masks
occur in a fixed dimension. No finiteness assumption on A is needed. -/
lemma coordinateMismatch_image_finite {N : ℕ} (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) : (coordinateMismatch x '' A).Finite := by
  apply (Set.finite_range (booleanMismatchVector N)).subset
  rintro _ ⟨y, hy, rfl⟩
  exact coordinateMismatch_mem_boolean_range x y

lemma mismatchHull_compact {N : ℕ} (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) : IsCompact (mismatchHull x A) :=
  (coordinateMismatch_image_finite x A).isCompact_convexHull ℝ

/-- The convex distance minimum is attained for every nonempty set, including
sets of probability zero. Measurability as the base point varies is separate. -/
lemma mismatchHull_minimum_attained {N : ℕ} (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) (hA : A.Nonempty) :
    ∃ v ∈ mismatchHull x A, (∀ w ∈ mismatchHull x A, ‖v‖^2 ≤ ‖w‖^2) ∧
      0 ≤ ‖v‖^2 ∧ ‖v‖^2 ≤ (N : ℝ) := by
  have hne : (mismatchHull x A).Nonempty := by
    obtain ⟨y, hy⟩ := hA
    exact ⟨coordinateMismatch x y, subset_convexHull ℝ _ ⟨y, hy, rfl⟩⟩
  obtain ⟨v, hv, hmin⟩ := (mismatchHull_compact x A).exists_isMinOn hne
    (show ContinuousOn (fun v : EuclideanSpace ℝ (Fin N) => ‖v‖^2) (mismatchHull x A) by fun_prop)
  exact ⟨v, hv, hmin, sq_nonneg _, mismatchHull_norm_sq_le_dimension x A v hv⟩

#print axioms coordinateMismatch_mem_boolean_range
#print axioms coordinateMismatch_image_finite
#print axioms mismatchHull_compact
#print axioms mismatchHull_minimum_attained
end SpectralRadiusUpperTail
