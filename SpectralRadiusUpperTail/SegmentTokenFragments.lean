import SpectralRadiusUpperTail.SegmentPositionSublist
import SpectralRadiusUpperTail.ConstantRunLengths
import SpectralRadiusUpperTail.IndexedFragmentRunBudget

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {V B : Type*} [Fintype V] [DecidableEq V] [DecidableEq B] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.exists_segment_token_fragments (c : DefectRouteCertificate s v)
    (block : Fin (2*r) → B) (N m : ℕ)
    (hrun : signRunCount (List.ofFn block) ≤ N)
    (hcount : ∀ b, (List.ofFn block).count b ≤ m)
    (hsign : ∀ i j, block i = block j → s i = s j) :
    ∃ P : Fin c.segments.length → List (List (Fin (2*r) × Bool)),
      (∀ i, (P i).flatten = c.positionWords i) ∧
      (∀ i w, w ∈ P i → w ≠ [] ∧ labelConstant Prod.snd w ∧ w.length ≤ m) ∧
      (∑ i, (P i).length) ≤ N+8*(r+1-Fintype.card V) := by
  classical
  have hex := fun i : Fin c.segments.length => exists_constant_run_partition block (c.segmentPositions i)
  choose Q hQ hconst hnum using hex
  let tok := fun j : Fin (2*r) => (j,s j)
  let P := fun i => (Q i).map (List.map tok)
  refine ⟨P,?_,?_,?_⟩
  · intro i
    change ((Q i).map (List.map tok)).flatten = (c.segmentPositions i).map tok
    rw [← List.map_flatten,hQ i]
  · intro i w hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    have hc := hconst i a ha
    have hsub : a.Sublist (List.ofFn (fun j : Fin (2*r) => j)) := by
      have h : a.Sublist (c.segmentPositions i) := (hQ i) ▸ List.sublist_flatten_of_mem ha
      exact h.trans (c.segmentPositions_sublist i)
    obtain ⟨b,hb⟩ := labelConstant_length_le_count block a _ hsub hc.1 hc.2
    have hlen : a.length ≤ m := hb.trans (by simpa only [List.map_ofFn,Function.comp_def] using hcount b)
    refine ⟨by simpa using hc.1,?_,by simpa using hlen⟩
    intro x hx y hy
    obtain ⟨a',ha',rfl⟩ := List.mem_map.mp hx
    obtain ⟨b',hb',rfl⟩ := List.mem_map.mp hy
    exact hsign a' b' (hc.2 a' ha' b' hb')
  · have h := c.segment_fragment_run_budget block N hrun
    rw [← c.segmentPositions_ofFn] at h
    simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def] at h
    simpa only [P,List.length_map,hnum] using h

#print axioms DefectRouteCertificate.exists_segment_token_fragments
end SpectralRadiusUpperTail
