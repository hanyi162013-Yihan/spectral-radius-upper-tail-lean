import SpectralRadiusUpperTail.IncreasingPathOrthogonality

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma entryMultiplicity_le_project {σ ρ τ : Type*} [Fintype τ]
    [DecidableEq σ] [DecidableEq ρ] (π : σ → ρ) (e : τ → σ) (i : σ) :
    entryMultiplicity e i ≤ entryMultiplicity (fun j => π (e j)) (π i) := by
  apply Finset.card_le_card
  intro j hj
  have he := (Finset.mem_filter.mp hj).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg π he⟩

/-- A block occurring once forces one of its scalar entry coordinates to
occur once. This is the bridge from block paths to expanded matrix entries. -/
lemma projected_word_singleton_lifts {σ ρ τ υ : Type*} [Fintype σ] [Fintype ρ] [Fintype τ] [Fintype υ]
    [DecidableEq σ] [DecidableEq ρ] (π : σ → ρ) (e : τ → σ) (f : υ → σ)
    (b : ρ) (hb : entryMultiplicity (fun j => π (e j)) b+
      entryMultiplicity (fun j => π (f j)) b = 1) :
    ∃ i, entryMultiplicity e i+entryMultiplicity f i = 1 := by
  have hchoose : ∀ (e : τ → σ) (f : υ → σ),
      entryMultiplicity (fun j => π (e j)) b+entryMultiplicity (fun j => π (f j)) b = 1 →
      (∃ j, π (e j) = b) →
      ∃ i, entryMultiplicity e i+entryMultiplicity f i = 1 := by
    intro e f hh ⟨j, hj⟩
    refine ⟨e j, ?_⟩
    have he := entryMultiplicity_le_project π e (e j)
    have hf := entryMultiplicity_le_project π f (e j)
    rw [hj] at he hf
    have hp : 0 < entryMultiplicity e (e j) :=
      (entryMultiplicity_pos_iff e (e j)).mpr ⟨j, rfl⟩
    omega
  by_cases he : 0 < entryMultiplicity (fun j => π (e j)) b
  · exact hchoose e f hb ((entryMultiplicity_pos_iff _ _).mp he)
  · have hf : 0 < entryMultiplicity (fun j => π (f j)) b := by omega
    obtain ⟨j, hj⟩ := (entryMultiplicity_pos_iff _ _).mp hf
    refine ⟨f j, ?_⟩
    have he' := entryMultiplicity_le_project π e (f j)
    have hf' := entryMultiplicity_le_project π f (f j)
    rw [hj] at he' hf'
    have hp : 0 < entryMultiplicity f (f j) :=
      (entryMultiplicity_pos_iff f (f j)).mpr ⟨j, rfl⟩
    omega

/-- Orthogonality of arbitrary scalar terms obtained by expanding two
matrix-block path products. Internal row/column indices may be arbitrary;
only their projected block paths matter. -/
theorem schur_block_path_cross_zero {σ 𝕂 : Type*} [Fintype σ] [DecidableEq σ]
    [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (hm : (∫ x : 𝕂, x ∂μ) = 0)
    {n k : ℕ} (π : σ → Fin n × Fin n) (e f : Fin k → σ)
    (p q : Fin (k+1) → Fin n) (hp : StrictMono p) (hq : StrictMono q)
    (he : (fun j => π (e j)) = increasingPathEdge p)
    (hf : (fun j => π (f j)) = increasingPathEdge q)
    (hlast : p (Fin.last k) = q (Fin.last k)) (hne : p ≠ q) :
    (∫ x : σ → 𝕂, (∏ j, x (e j))*(∏ j, star (x (f j)))
      ∂Measure.pi (fun _ => μ)) = 0 := by
  obtain ⟨b, hb⟩ := increasingPath_singleton hp hq hlast hne
  rw [← he, ← hf] at hb
  obtain ⟨i, hi⟩ := projected_word_singleton_lifts π e f b hb
  exact iidWordPair_singleton_zero μ hm e f i hi

theorem schur_block_path_different_length_cross_zero {σ 𝕂 : Type*}
    [Fintype σ] [DecidableEq σ] [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (hm : (∫ x : 𝕂, x ∂μ) = 0)
    {n k l : ℕ} (π : σ → Fin n × Fin n) (e : Fin k → σ) (f : Fin l → σ)
    (p : Fin (k+1) → Fin n) (q : Fin (l+1) → Fin n)
    (hp : StrictMono p) (hq : StrictMono q)
    (he : (fun j => π (e j)) = increasingPathEdge p)
    (hf : (fun j => π (f j)) = increasingPathEdge q) (hkl : k ≠ l) :
    (∫ x : σ → 𝕂, (∏ j, x (e j))*(∏ j, star (x (f j)))
      ∂Measure.pi (fun _ => μ)) = 0 := by
  obtain ⟨b, hb⟩ := injective_words_different_length_singleton
    (increasingPathEdge p) (increasingPathEdge q)
    (increasingPathEdge_injective hp) (increasingPathEdge_injective hq) hkl
  rw [← he, ← hf] at hb
  obtain ⟨i, hi⟩ := projected_word_singleton_lifts π e f b hb
  exact iidWordPair_singleton_zero μ hm e f i hi

#print axioms projected_word_singleton_lifts
#print axioms schur_block_path_cross_zero
#print axioms schur_block_path_different_length_cross_zero
end SpectralRadiusUpperTail
