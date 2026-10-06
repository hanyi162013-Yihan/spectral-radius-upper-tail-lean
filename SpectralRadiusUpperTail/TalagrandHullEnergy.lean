import SpectralRadiusUpperTail.FiniteMismatchHull
import SpectralRadiusUpperTail.MismatchHullFiberInterpolation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

/-- Minimum squared convex-mismatch distance, with value zero for an empty
target set. Compactness of the finite mask hull ensures the chosen minimum
is attained whenever the target is nonempty. -/
noncomputable def mismatchHullEnergy {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) : ℝ := by
  classical
  exact if hA : A.Nonempty then
    ‖(mismatchHull_minimum_attained x A hA).choose‖^2
  else 0

lemma mismatchHullEnergy_minimum {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) (hA : A.Nonempty) :
    ∃ v ∈ mismatchHull x A,
      mismatchHullEnergy x A = ‖v‖^2 ∧
      ∀ w ∈ mismatchHull x A, mismatchHullEnergy x A ≤ ‖w‖^2 := by
  let v := (mismatchHull_minimum_attained x A hA).choose
  obtain ⟨hv, hmin, _, _⟩ :=
    (mismatchHull_minimum_attained x A hA).choose_spec
  refine ⟨v, hv, ?_, ?_⟩
  · simp [mismatchHullEnergy, hA, v]
  · intro w hw
    simpa [mismatchHullEnergy, hA, v] using hmin w hw

lemma mismatchHullEnergy_le_of_mem {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N)))
    (v : EuclideanSpace ℝ (Fin N)) (hv : v ∈ mismatchHull x A) :
    mismatchHullEnergy x A ≤ ‖v‖^2 := by
  have hA : A.Nonempty := by
    by_contra h
    have hnil : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [hnil, mismatchHull] at hv
  obtain ⟨_, _, _, hmin⟩ := mismatchHullEnergy_minimum x A hA
  exact hmin v hv

lemma mismatchHullEnergy_bounds {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) :
    0 ≤ mismatchHullEnergy x A ∧ mismatchHullEnergy x A ≤ (N : ℝ) := by
  by_cases hA : A.Nonempty
  · obtain ⟨v, hv, heq, _⟩ := mismatchHullEnergy_minimum x A hA
    rw [heq]
    exact ⟨sq_nonneg _, mismatchHull_norm_sq_le_dimension x A v hv⟩
  · simp [mismatchHullEnergy, hA]

/-- Empty matching fibers require only the projected set; the extra
coordinate costs at most one unit of squared distance. -/
lemma mismatchHullEnergy_projection (N : ℕ)
    (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) (hA : A.Nonempty) :
    mismatchHullEnergy x A ≤
      mismatchHullEnergy (euclideanCoordinateTail N x)
        (euclideanCoordinateTail N '' A)+1 := by
  have hB : (euclideanCoordinateTail N '' A).Nonempty := hA.image _
  obtain ⟨v, hv, heq, _⟩ :=
    mismatchHullEnergy_minimum (euclideanCoordinateTail N x)
      (euclideanCoordinateTail N '' A) hB
  obtain ⟨w, hw, hbound⟩ := mismatchHull_projection_energy_lift N x A v hv
  calc
    mismatchHullEnergy x A ≤ ‖w‖^2 := mismatchHullEnergy_le_of_mem x A w hw
    _ ≤ ‖v‖^2+1 := hbound
    _ = _ := by rw [heq]

/-- Deterministic minimum-distance recursion for a nonempty matching
fiber. The coefficient `b` is the complement of `a`. -/
lemma mismatchHullEnergy_fiber_interpolation (N : ℕ)
    (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1))))
    (hF : {y | euclideanWithHead N (x 0) y ∈ A}.Nonempty)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    mismatchHullEnergy x A ≤
      a*mismatchHullEnergy (euclideanCoordinateTail N x)
        {y | euclideanWithHead N (x 0) y ∈ A}+
      b*mismatchHullEnergy (euclideanCoordinateTail N x)
        (euclideanCoordinateTail N '' A)+b^2 := by
  have hA : A.Nonempty := by
    obtain ⟨y, hy⟩ := hF
    exact ⟨euclideanWithHead N (x 0) y, hy⟩
  have hB : (euclideanCoordinateTail N '' A).Nonempty := hA.image _
  obtain ⟨v, hv, hev, _⟩ :=
    mismatchHullEnergy_minimum (euclideanCoordinateTail N x)
      {y | euclideanWithHead N (x 0) y ∈ A} hF
  obtain ⟨w, hw, hew, _⟩ :=
    mismatchHullEnergy_minimum (euclideanCoordinateTail N x)
      (euclideanCoordinateTail N '' A) hB
  obtain ⟨u, hu, hbound⟩ :=
    mismatchHull_fiber_interpolation N x A v w hv hw a b ha hb hab
  calc
    mismatchHullEnergy x A ≤ ‖u‖^2 := mismatchHullEnergy_le_of_mem x A u hu
    _ ≤ a*‖v‖^2+b*‖w‖^2+b^2 := hbound
    _ = _ := by rw [hev, hew]

#print axioms mismatchHullEnergy_minimum
#print axioms mismatchHullEnergy_bounds
#print axioms mismatchHullEnergy_projection
#print axioms mismatchHullEnergy_fiber_interpolation
end SpectralRadiusUpperTail
