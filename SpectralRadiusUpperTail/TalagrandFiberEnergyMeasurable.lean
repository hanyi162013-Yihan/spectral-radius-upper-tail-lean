import SpectralRadiusUpperTail.TalagrandMaskEnergyMeasurable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Set
variable {𝕂 : Type*} [RCLike 𝕂]

/-- Matching-head fiber in the last `N` coordinates. -/
def matchingHeadFiber (N : ℕ)
    (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) :
    Set (EuclideanSpace 𝕂 (Fin N)) :=
  {y | euclideanWithHead N (x 0) y ∈ A}

lemma dominatingMaskAdmissible_matchingHeadFiber_iff (N : ℕ)
    (x : EuclideanSpace 𝕂 (Fin (N+1)))
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1))))
    (b : Fin N → Bool) :
    dominatingMaskAdmissible (euclideanCoordinateTail N x)
      (matchingHeadFiber N x A) b ↔
    dominatingMaskAdmissible x A (Fin.cons false b) := by
  constructor
  · rintro ⟨z, hz, hmatch⟩
    refine ⟨euclideanWithHead N (x 0) z, hz, ?_⟩
    intro i hi
    cases i using Fin.cases with
    | zero => simp [euclideanWithHead]
    | succ j =>
      have hj : b j = false := by simpa using hi
      simpa [euclideanWithHead, euclideanCoordinateTail] using hmatch j hj
  · rintro ⟨y, hy, hmatch⟩
    have hhead : x 0 = y 0 := hmatch 0 (by simp)
    have he : euclideanWithHead N (x 0) (euclideanCoordinateTail N y) = y := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [euclideanWithHead] using hhead
      · simp [euclideanWithHead, euclideanCoordinateTail]
    refine ⟨euclideanCoordinateTail N y, ?_, ?_⟩
    · change euclideanWithHead N (x 0) (euclideanCoordinateTail N y) ∈ A
      rwa [he]
    · intro j hj
      have hh := hmatch j.succ (by simpa using hj)
      simpa [euclideanCoordinateTail] using hh

omit [RCLike 𝕂] in
lemma dominatingMaskAdmissible_all_true_iff_nonempty {N : ℕ}
    (x : EuclideanSpace 𝕂 (Fin N))
    (A : Set (EuclideanSpace 𝕂 (Fin N))) :
    dominatingMaskAdmissible x A (fun _ => true) ↔ A.Nonempty := by
  constructor
  · rintro ⟨y, hy, _⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hy, by simp⟩

/-- The matching-fiber energy is determined by the finite state of masks
with the new coordinate forced to match. -/
lemma matchingHeadFiber_energy_eq_of_mask_state (N : ℕ)
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1))))
    (x x' : EuclideanSpace 𝕂 (Fin (N+1)))
    (hstate : ∀ b : Fin N → Bool,
      dominatingMaskAdmissible x A (Fin.cons false b) ↔
        dominatingMaskAdmissible x' A (Fin.cons false b)) :
    mismatchHullEnergy (euclideanCoordinateTail N x) (matchingHeadFiber N x A) =
      mismatchHullEnergy (euclideanCoordinateTail N x') (matchingHeadFiber N x' A) := by
  have hfiber : ∀ b : Fin N → Bool,
      dominatingMaskAdmissible (euclideanCoordinateTail N x)
        (matchingHeadFiber N x A) b ↔
      dominatingMaskAdmissible (euclideanCoordinateTail N x')
        (matchingHeadFiber N x' A) b := by
    intro b
    rw [dominatingMaskAdmissible_matchingHeadFiber_iff,
      dominatingMaskAdmissible_matchingHeadFiber_iff]
    exact hstate b
  have hne : (matchingHeadFiber N x A).Nonempty ↔
      (matchingHeadFiber N x' A).Nonempty := by
    rw [← dominatingMaskAdmissible_all_true_iff_nonempty
      (euclideanCoordinateTail N x) (matchingHeadFiber N x A),
      ← dominatingMaskAdmissible_all_true_iff_nonempty
      (euclideanCoordinateTail N x') (matchingHeadFiber N x' A)]
    exact hfiber _
  by_cases hF : (matchingHeadFiber N x A).Nonempty
  · exact mismatchHullEnergy_eq_of_two_admissible_mask_families
      (matchingHeadFiber N x A) (matchingHeadFiber N x' A)
      hF (hne.mp hF) (euclideanCoordinateTail N x)
      (euclideanCoordinateTail N x') hfiber
  · have hF' : ¬(matchingHeadFiber N x' A).Nonempty :=
      fun h => hF (hne.mpr h)
    simp [mismatchHullEnergy, hF, hF']

/-- Joint Borel measurability of the fiber distance in the head coordinate
and the remaining coordinates. Compactness of the original target supplies
closed mask-admissibility events even though the fibers vary. -/
lemma matchingHeadFiber_energy_measurable (N : ℕ)
    [MeasurableSpace (EuclideanSpace 𝕂 (Fin (N+1)))]
    [BorelSpace (EuclideanSpace 𝕂 (Fin (N+1)))]
    (A : Set (EuclideanSpace 𝕂 (Fin (N+1)))) (hA : IsCompact A) :
    Measurable (fun x => mismatchHullEnergy (euclideanCoordinateTail N x)
      (matchingHeadFiber N x A)) := by
  classical
  let state := fun x : EuclideanSpace 𝕂 (Fin (N+1)) =>
    {b : Fin N → Bool | dominatingMaskAdmissible x A (Fin.cons false b)}
  have hs : Measurable state := by
    rw [measurable_set_iff]
    intro b
    change Measurable fun x : EuclideanSpace 𝕂 (Fin (N+1)) =>
      dominatingMaskAdmissible x A (Fin.cons false b)
    exact measurableSet_setOfPred.mp
      (dominatingMaskAdmissible_closed A hA (Fin.cons false b)).measurableSet
  let F : Set (Fin N → Bool) → ℝ := fun s =>
    if h : ∃ x, state x = s then
      mismatchHullEnergy (euclideanCoordinateTail N (Classical.choose h))
        (matchingHeadFiber N (Classical.choose h) A) else 0
  have hfactor : ∀ x, mismatchHullEnergy (euclideanCoordinateTail N x)
      (matchingHeadFiber N x A) = F (state x) := by
    intro x
    have hx : ∃ y, state y = state x := ⟨x, rfl⟩
    have heq : F (state x) =
        mismatchHullEnergy (euclideanCoordinateTail N (Classical.choose hx))
          (matchingHeadFiber N (Classical.choose hx) A) := by
      simp [F, hx]
    rw [heq]
    apply matchingHeadFiber_energy_eq_of_mask_state N A x (Classical.choose hx)
    intro b
    exact Eq.to_iff
      ((congrArg (fun s : Set (Fin N → Bool) => b ∈ s)
        (Classical.choose_spec hx)).symm)
  have hF : Measurable F := measurable_of_finite F
  have heq : (fun x => mismatchHullEnergy (euclideanCoordinateTail N x)
      (matchingHeadFiber N x A)) = F ∘ state := funext hfactor
  rw [heq]
  exact hF.comp hs

#print axioms matchingHeadFiber_energy_eq_of_mask_state
#print axioms matchingHeadFiber_energy_measurable
end SpectralRadiusUpperTail
