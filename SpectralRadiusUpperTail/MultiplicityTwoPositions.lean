import SpectralRadiusUpperTail.IidWordMoments
import Mathlib.Data.Finset.Card

namespace SpectralRadiusUpperTail
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

/-- Multiplicity two supplies the two actual positions, with no other occurrence. -/
lemma entryMultiplicity_two_positions (e : τ → σ) (x : σ)
    (h : entryMultiplicity e x = 2) :
    ∃ i j : τ, i ≠ j ∧ ∀ t : τ, e t = x ↔ t = i ∨ t = j := by
  classical
  obtain ⟨i,j,hij,hs⟩ := Finset.card_eq_two.mp h
  refine ⟨i,j,hij,?_⟩
  intro t
  have hm : t ∈ Finset.univ.filter (fun u => e u = x) ↔ t ∈ ({i,j} : Finset τ) := by
    rw [hs]
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton] using hm

#print axioms entryMultiplicity_two_positions
end SpectralRadiusUpperTail
