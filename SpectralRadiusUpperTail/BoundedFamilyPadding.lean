import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Function.Basic

namespace SpectralRadiusUpperTail

noncomputable def boundedFamilyEmbedding {ι : Type*} [Fintype ι] (m : ℕ)
    (h : Fintype.card ι ≤ m) : ι ↪ Fin m :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using h))

noncomputable def padFiniteFamily {ι α : Type*} {m : ℕ} (e : ι ↪ Fin m)
    (f : ι → α) (a : α) : Fin m → α := Function.extend e f (fun _ => a)

lemma padFiniteFamily_apply {ι α : Type*} {m : ℕ} (e : ι ↪ Fin m)
    (f : ι → α) (a : α) (i : ι) : padFiniteFamily e f a (e i) = f i :=
  e.injective.extend_apply f (fun _ => a) i

lemma padFiniteFamily_property {ι α : Type*} {m : ℕ} (e : ι ↪ Fin m)
    (f : ι → α) (a : α) (P : α → Prop) (hf : ∀ i, P (f i)) (ha : P a) :
    ∀ j, P (padFiniteFamily e f a j) := by
  intro j
  by_cases h : ∃ i, e i = j
  · obtain ⟨i,rfl⟩ := h
    rw [padFiniteFamily_apply]
    exact hf i
  · rw [padFiniteFamily,Function.extend_apply' f (fun _ => a) j h]
    exact ha

#print axioms boundedFamilyEmbedding
#print axioms padFiniteFamily
#print axioms padFiniteFamily_apply
#print axioms padFiniteFamily_property
end SpectralRadiusUpperTail
