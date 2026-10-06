import SpectralRadiusUpperTail.GaussianPrincipalMinorExpansion
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- Every nonempty principal-minor determinant monomial has mean zero. -/
theorem gaussian_principalPermutation_word_mean_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : PrincipalPermutation ι) (hp : p.1.Nonempty) :
    (∫ x : ι × ι → ℝ,
      principalPermutationWord p x
      ∂Measure.pi (fun _ => standardNormal)) = 0 := by
  have hrange : Set.range (principalPermutationEdge p) ≠
      Set.range (fun z : Empty => (z.elim : ι × ι)) := by
    intro h
    obtain ⟨i,hi⟩ := hp
    have hm : principalPermutationEdge p (⟨i,hi⟩ : p.1) ∈
        Set.range (principalPermutationEdge p) := ⟨⟨i,hi⟩,rfl⟩
    rw [h] at hm
    obtain ⟨z,_⟩ := hm
    exact z.elim
  have h := gaussian_injective_words_cross_zero_of_ranges_ne
    (principalPermutationEdge p)
    (fun z : Empty => (z.elim : ι × ι))
    (principalPermutationEdge_injective p)
    (fun z => z.elim) hrange
  simpa [principalPermutationWord] using h

#print axioms gaussian_principalPermutation_word_mean_zero
end SpectralRadiusUpperTail
