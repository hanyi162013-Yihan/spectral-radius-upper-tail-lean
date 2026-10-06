import SpectralRadiusUpperTail.TalagrandDominatingMasks
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

private lemma norm_sq_le_of_coordinatewise_le {N : ℕ}
    (u v : EuclideanSpace ℝ (Fin N))
    (hu : ∀ i, 0 ≤ u i) (h : ∀ i, u i ≤ v i) :
    ‖u‖^2 ≤ ‖v‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  have hv : 0 ≤ v i := le_trans (hu i) (h i)
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [hu i, h i]

lemma mismatchHullEnergy_eq_of_two_admissible_mask_families {N : ℕ}
    (A B : Set (EuclideanSpace 𝕂 (Fin N)))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (x x' : EuclideanSpace 𝕂 (Fin N))
    (hstate : ∀ b : Fin N → Bool,
      dominatingMaskAdmissible x A b ↔
        dominatingMaskAdmissible x' B b) :
    mismatchHullEnergy x A = mismatchHullEnergy x' B := by
  have hHull : dominatingMismatchHull x A =
      dominatingMismatchHull x' B := by
    have hset : {b : Fin N → Bool | dominatingMaskAdmissible x A b} =
        {b : Fin N → Bool | dominatingMaskAdmissible x' B b} := by
      ext b
      exact hstate b
    simp only [dominatingMismatchHull, hset]
  have hforward : mismatchHullEnergy x A ≤ mismatchHullEnergy x' B := by
    obtain ⟨v, hv, heq, _⟩ := mismatchHullEnergy_minimum x' B hB
    have hvdom : v ∈ dominatingMismatchHull x A := by
      rw [hHull]
      exact mismatchHull_subset_dominatingHull x' B hv
    obtain ⟨w, hw, hle⟩ := dominatingHull_has_lower_actual_vector x A v hvdom
    have hnorm : ‖w‖^2 ≤ ‖v‖^2 :=
      norm_sq_le_of_coordinatewise_le w v
        (fun i => (mismatchHull_coordinates_unit_interval x A w hw i).1) hle
    exact (mismatchHullEnergy_le_of_mem x A w hw).trans (by rwa [← heq] at hnorm)
  have hbackward : mismatchHullEnergy x' B ≤ mismatchHullEnergy x A := by
    obtain ⟨v, hv, heq, _⟩ := mismatchHullEnergy_minimum x A hA
    have hvdom : v ∈ dominatingMismatchHull x' B := by
      rw [← hHull]
      exact mismatchHull_subset_dominatingHull x A hv
    obtain ⟨w, hw, hle⟩ := dominatingHull_has_lower_actual_vector x' B v hvdom
    have hnorm : ‖w‖^2 ≤ ‖v‖^2 :=
      norm_sq_le_of_coordinatewise_le w v
        (fun i => (mismatchHull_coordinates_unit_interval x' B w hw i).1) hle
    exact (mismatchHullEnergy_le_of_mem x' B w hw).trans (by rwa [← heq] at hnorm)
  exact le_antisymm hforward hbackward

lemma mismatchHullEnergy_eq_of_admissible_masks {N : ℕ}
    (A : Set (EuclideanSpace 𝕂 (Fin N)))
    (x x' : EuclideanSpace 𝕂 (Fin N))
    (hstate : ∀ b : Fin N → Bool,
      dominatingMaskAdmissible x A b ↔
        dominatingMaskAdmissible x' A b) :
    mismatchHullEnergy x A = mismatchHullEnergy x' A := by
  by_cases hA : A.Nonempty
  · exact mismatchHullEnergy_eq_of_two_admissible_mask_families
      A A hA hA x x' hstate
  · simp [mismatchHullEnergy, hA]

/-- The finite Boolean state of all admissible dominating masks. -/
def admissibleMaskState {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) : Set (Fin N → Bool) :=
  {b | dominatingMaskAdmissible x A b}

lemma admissibleMaskState_measurable {N : ℕ}
    [MeasurableSpace (EuclideanSpace 𝕂 (Fin N))]
    [BorelSpace (EuclideanSpace 𝕂 (Fin N))]
    (A : Set (EuclideanSpace 𝕂 (Fin N))) (hA : IsCompact A) :
    Measurable (fun x => admissibleMaskState x A) := by
  rw [measurable_set_iff]
  intro b
  change Measurable fun x : EuclideanSpace 𝕂 (Fin N) =>
    dominatingMaskAdmissible x A b
  exact measurableSet_setOfPred.mp
    (dominatingMaskAdmissible_closed A hA b).measurableSet
    
/-- For a compact target, the squared convex mismatch distance is Borel
measurable. It factors through the finite state of admissible masks. -/
lemma mismatchHullEnergy_measurable {N : ℕ}
    [MeasurableSpace (EuclideanSpace 𝕂 (Fin N))]
    [BorelSpace (EuclideanSpace 𝕂 (Fin N))]
    (A : Set (EuclideanSpace 𝕂 (Fin N))) (hA : IsCompact A) :
    Measurable (fun x => mismatchHullEnergy x A) := by
  classical
  let state := fun x : EuclideanSpace 𝕂 (Fin N) => admissibleMaskState x A
  let F : Set (Fin N → Bool) → ℝ := fun s =>
    if h : ∃ x, state x = s then mismatchHullEnergy (Classical.choose h) A else 0
  have hfactor : ∀ x, mismatchHullEnergy x A = F (state x) := by
    intro x
    have hx : ∃ y, state y = state x := ⟨x, rfl⟩
    have heq : F (state x) = mismatchHullEnergy (Classical.choose hx) A := by
      simp [F, hx]
    rw [heq]
    apply mismatchHullEnergy_eq_of_admissible_masks A x (Classical.choose hx)
    intro b
    have hs := Classical.choose_spec hx
    exact Eq.to_iff (congrArg (fun s : Set (Fin N → Bool) => b ∈ s) hs).symm
  have hF : Measurable F := measurable_of_finite F
  have hs : Measurable state := admissibleMaskState_measurable A hA
  have heq : (fun x => mismatchHullEnergy x A) = F ∘ state :=
    funext hfactor
  rw [heq]
  exact hF.comp hs

#print axioms mismatchHullEnergy_eq_of_admissible_masks
#print axioms mismatchHullEnergy_eq_of_two_admissible_mask_families
#print axioms admissibleMaskState_measurable
#print axioms mismatchHullEnergy_measurable
end SpectralRadiusUpperTail
