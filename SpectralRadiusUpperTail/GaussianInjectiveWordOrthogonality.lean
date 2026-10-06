import SpectralRadiusUpperTail.IidWordSupport
import SpectralRadiusUpperTail.IidSimpleWordVariance
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- Distinct finite sets of Gaussian coordinates give orthogonal
square-integrable products, provided each product uses every one of
its coordinates exactly once. -/
theorem gaussian_injective_words_cross_zero_of_ranges_ne
    {σ τ υ : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [Fintype υ]
    (e : τ → σ) (f : υ → σ)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hne : Set.range e ≠ Set.range f) :
    (∫ x : σ → ℝ, (∏ j, x (e j))*(∏ j, x (f j))
      ∂Measure.pi (fun _ => standardNormal)) = 0 := by
  have hm : (∫ z : ℝ, z ∂standardNormal) = 0 := by
    simpa using standardNormal_odd_moment 0
  by_cases hsub : Set.range e ⊆ Set.range f
  · have hnot : ¬Set.range f ⊆ Set.range e := by
      intro hback
      exact hne (Set.Subset.antisymm hsub hback)
    obtain ⟨i,hi,hni⟩ := Set.not_subset.mp hnot
    obtain ⟨j,rfl⟩ := hi
    have hzero : entryMultiplicity e (f j) = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hp
      exact hni ((entryMultiplicity_pos_iff e (f j)).mp hp)
    have hone : entryMultiplicity f (f j) = 1 :=
      entryMultiplicity_of_injective f hf j
    have h := iidWordPair_singleton_zero standardNormal hm
      e f (f j) (by omega)
    simpa only [star_trivial] using h
  · obtain ⟨i,hi,hni⟩ := Set.not_subset.mp hsub
    obtain ⟨j,rfl⟩ := hi
    have hzero : entryMultiplicity f (e j) = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hp
      exact hni ((entryMultiplicity_pos_iff f (e j)).mp hp)
    have hone : entryMultiplicity e (e j) = 1 :=
      entryMultiplicity_of_injective e he j
    have h := iidWordPair_singleton_zero standardNormal hm
      e f (e j) (by omega)
    simpa only [star_trivial] using h

#print axioms gaussian_injective_words_cross_zero_of_ranges_ne
end SpectralRadiusUpperTail
