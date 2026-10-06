import SpectralRadiusUpperTail.IidWordSupport

namespace SpectralRadiusUpperTail
variable {σ τ υ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [Fintype υ]

lemma entryImage_subset_of_no_singleton (e : τ → σ) (f : υ → σ)
    (he : Function.Injective e)
    (hs : ∀ i, entryMultiplicity e i + entryMultiplicity f i ≠ 1) :
    Finset.univ.image e ⊆ Finset.univ.image f := by
  intro i hi
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
  have h1 := entryMultiplicity_of_injective e he j
  have hn := hs (e j)
  have hp : 0 < entryMultiplicity f (e j) := by omega
  obtain ⟨a,ha⟩ := (entryMultiplicity_pos_iff f (e j)).mp hp
  exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha⟩

/-- Two injective words without a singleton have identical image sets. -/
lemma pairedSimpleWords_images_eq (e : τ → σ) (f : υ → σ)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hs : ∀ i, entryMultiplicity e i + entryMultiplicity f i ≠ 1) :
    Finset.univ.image e = Finset.univ.image f := by
  apply Finset.Subset.antisymm
  · exact entryImage_subset_of_no_singleton e f he hs
  · exact entryImage_subset_of_no_singleton f e hf (by
      intro i
      simpa only [Nat.add_comm] using hs i)

#print axioms entryImage_subset_of_no_singleton
#print axioms pairedSimpleWords_images_eq
end SpectralRadiusUpperTail
