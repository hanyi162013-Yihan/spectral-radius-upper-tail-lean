import SpectralRadiusUpperTail.ConstantRunPartition
import SpectralRadiusUpperTail.FiniteWordListCount

namespace SpectralRadiusUpperTail
variable {A B : Type*} [DecidableEq B]

lemma labelConstant_count (f : A → B) (l : List A) (a : A) (ha : a ∈ l)
    (hc : labelConstant f l) : (l.map f).count (f a) = l.length := by
  have hrep : l.map f = List.replicate l.length (f a) := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp,?_⟩
    intro b hb
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hb
    exact hc x hx a ha
  rw [hrep,List.count_replicate_self]

/-- A constant original-block fragment cannot be longer than that block's
number of surviving occurrences, hence not longer than the original block. -/
lemma labelConstant_length_le_count (f : A → B) (l k : List A)
    (hl : l.Sublist k) (hne : l ≠ []) (hc : labelConstant f l) :
    ∃ b, l.length ≤ (k.map f).count b := by
  obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil l hne
  refine ⟨f a,?_⟩
  rw [← labelConstant_count f l a ha hc]
  exact List.Sublist.count_le (f a) (hl.map f)

lemma constantRunPartition_lengths_le (f : A → B) (l : List A) (C : List (List A))
    (hflat : C.flatten = l) (hC : ∀ c ∈ C, c ≠ [] ∧ labelConstant f c)
    (m : ℕ) (hcount : ∀ b, (l.map f).count b ≤ m) : ∀ c ∈ C, c.length ≤ m := by
  intro c hc
  have hsub : c.Sublist l := hflat ▸ List.sublist_flatten_of_mem hc
  obtain ⟨b,hb⟩ := labelConstant_length_le_count f c l hsub (hC c hc).1 (hC c hc).2
  exact hb.trans (hcount b)

#print axioms labelConstant_count
#print axioms labelConstant_length_le_count
#print axioms constantRunPartition_lengths_le
end SpectralRadiusUpperTail
