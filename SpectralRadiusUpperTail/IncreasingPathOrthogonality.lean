import SpectralRadiusUpperTail.PairedSimpleWords
import SpectralRadiusUpperTail.IidWordMoments
import Mathlib.Order.WellFounded

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- Off-diagonal edges of a strictly increasing Schur block path. -/
def increasingPathEdge {n k : ℕ} (p : Fin (k+1) → Fin n) (j : Fin k) : Fin n × Fin n :=
  (p j.castSucc, p j.succ)

lemma increasingPathEdge_injective {n k : ℕ} {p : Fin (k+1) → Fin n}
    (hp : StrictMono p) : Function.Injective (increasingPathEdge p) := by
  intro i j hij
  have h := hp.injective (congrArg Prod.fst hij)
  exact Fin.castSucc_injective k h

lemma increasingPath_vertices_of_edges {n k : ℕ} {p q : Fin (k+1) → Fin n}
    (hlast : p (Fin.last k) = q (Fin.last k))
    (he : Set.range (increasingPathEdge p) = Set.range (increasingPathEdge q)) :
    Set.range p = Set.range q := by
  have hsub : ∀ (p q : Fin (k+1) → Fin n),
      p (Fin.last k) = q (Fin.last k) →
      Set.range (increasingPathEdge p) = Set.range (increasingPathEdge q) →
      Set.range p ⊆ Set.range q := by
    intro p q hl he x hx
    obtain ⟨i, rfl⟩ := hx
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨Fin.last k, hl.symm⟩
    · have hm : increasingPathEdge p j ∈ Set.range (increasingPathEdge q) := by
        rw [← he]
        exact ⟨j, rfl⟩
      obtain ⟨a, ha⟩ := hm
      exact ⟨a.castSucc, congrArg Prod.fst ha⟩
  exact Set.Subset.antisymm (hsub p q hlast he) (hsub q p hlast.symm he.symm)

/-- Increasing paths with the same terminal vertex are determined by their
edge sets. Shared intermediate vertices do not invalidate this statement. -/
lemma increasingPath_eq_of_edges {n k : ℕ} {p q : Fin (k+1) → Fin n}
    (hp : StrictMono p) (hq : StrictMono q)
    (hlast : p (Fin.last k) = q (Fin.last k))
    (he : Finset.univ.image (increasingPathEdge p) =
      Finset.univ.image (increasingPathEdge q)) : p = q := by
  apply (StrictMono.range_inj hp hq).mp
  apply increasingPath_vertices_of_edges hlast
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
    congrArg (fun s : Finset (Fin n × Fin n) => (s : Set (Fin n × Fin n))) he

lemma increasingPath_singleton {n k : ℕ} {p q : Fin (k+1) → Fin n}
    (hp : StrictMono p) (hq : StrictMono q)
    (hlast : p (Fin.last k) = q (Fin.last k)) (hne : p ≠ q) :
    ∃ e, entryMultiplicity (increasingPathEdge p) e +
      entryMultiplicity (increasingPathEdge q) e = 1 := by
  by_contra h
  push Not at h
  apply hne
  exact increasingPath_eq_of_edges hp hq hlast
    (pairedSimpleWords_images_eq _ _ (increasingPathEdge_injective hp)
      (increasingPathEdge_injective hq) h)

/-- Cross terms vanish because one edge occurs only once across the two
paths, not because the two complete paths are independent. -/
theorem increasingPath_cross_moment_zero {𝕂 : Type*} [RCLike 𝕂]
    [MeasurableSpace 𝕂] [BorelSpace 𝕂] (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) {n k : ℕ} {p q : Fin (k+1) → Fin n}
    (hp : StrictMono p) (hq : StrictMono q)
    (hlast : p (Fin.last k) = q (Fin.last k)) (hne : p ≠ q) :
    (∫ x : Fin n × Fin n → 𝕂,
      (∏ j, x (increasingPathEdge p j)) *
      (∏ j, star (x (increasingPathEdge q j)))
      ∂Measure.pi (fun _ => μ)) = 0 := by
  obtain ⟨e, he⟩ := increasingPath_singleton hp hq hlast hne
  exact iidWordPair_singleton_zero μ hm _ _ e he


/-- Injective edge words of different lengths also have an unmatched edge. -/
lemma injective_words_different_length_singleton {σ : Type*} [Fintype σ]
    [DecidableEq σ] {k l : ℕ} (e : Fin k → σ) (f : Fin l → σ)
    (he : Function.Injective e) (hf : Function.Injective f) (hkl : k ≠ l) :
    ∃ i, entryMultiplicity e i + entryMultiplicity f i = 1 := by
  by_contra h
  push Not at h
  have hi := pairedSimpleWords_images_eq e f he hf h
  have hc := congrArg Finset.card hi
  rw [Finset.card_image_of_injective _ he, Finset.card_image_of_injective _ hf] at hc
  exact hkl (by simpa using hc)

/-- Orthogonality also holds when the increasing paths have different
numbers of edges; no disjointness of their vertex sets is required. -/
theorem increasingPath_different_length_cross_zero {𝕂 : Type*} [RCLike 𝕂]
    [MeasurableSpace 𝕂] [BorelSpace 𝕂] (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) {n k l : ℕ}
    {p : Fin (k+1) → Fin n} {q : Fin (l+1) → Fin n}
    (hp : StrictMono p) (hq : StrictMono q) (hkl : k ≠ l) :
    (∫ x : Fin n × Fin n → 𝕂,
      (∏ j, x (increasingPathEdge p j)) *
      (∏ j, star (x (increasingPathEdge q j)))
      ∂Measure.pi (fun _ => μ)) = 0 := by
  obtain ⟨e, he⟩ := injective_words_different_length_singleton _ _
    (increasingPathEdge_injective hp) (increasingPathEdge_injective hq) hkl
  exact iidWordPair_singleton_zero μ hm _ _ e he

#print axioms increasingPath_different_length_cross_zero

#print axioms increasingPath_eq_of_edges
#print axioms increasingPath_cross_moment_zero
end SpectralRadiusUpperTail
