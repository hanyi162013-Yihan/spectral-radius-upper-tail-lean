import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup

namespace SpectralRadiusUpperTail
variable {ι : Type*} [DecidableEq ι]

/-- Directed edges visited by a finite vertex list. -/
def listWalkEdges : List ι → Finset (ι × ι)
  | [] => ∅
  | [_] => ∅
  | a :: b :: rest => insert (a,b) (listWalkEdges (b :: rest))

lemma listWalkEdges_endpoints {l : List ι} {edge : ι × ι}
    (h : edge ∈ listWalkEdges l) : edge.1 ∈ l ∧ edge.2 ∈ l.tail := by
  induction l with
  | nil => simp [listWalkEdges] at h
  | cons a l ih =>
    cases l with
    | nil => simp [listWalkEdges] at h
    | cons b rest =>
      rcases Finset.mem_insert.mp h with he | he
      · subst edge
        simp
      · have hi := ih he
        exact ⟨List.mem_cons_of_mem a hi.1, List.mem_cons_of_mem b hi.2⟩

/-- Repeating any vertex removes the possible one-vertex excess over
 distinct directed edges. Loops and opposite orientations are retained. -/
lemma listWalk_vertex_count (l : List ι) :
    l.toFinset.card ≤ (listWalkEdges l).card+1 ∧
      (¬l.Nodup → l.toFinset.card ≤ (listWalkEdges l).card) := by
  induction l with
  | nil => simp [listWalkEdges]
  | cons a l ih =>
    cases l with
    | nil => simp [listWalkEdges]
    | cons b rest =>
      by_cases ha : a ∈ (b :: rest).toFinset
      · rw [List.toFinset_cons, Finset.insert_eq_of_mem ha, listWalkEdges]
        have hle := Finset.card_le_card
          (Finset.subset_insert (a,b) (listWalkEdges (b :: rest)))
        constructor
        · omega
        · intro _
          by_cases ht : (b :: rest).Nodup
          · have he : (a,b) ∉ listWalkEdges (b :: rest) := by
              intro h
              have hx := (listWalkEdges_endpoints h).2
              exact (List.nodup_cons.mp ht).1 hx
            rw [Finset.card_insert_of_notMem he]
            exact ih.1
          · exact le_trans (ih.2 ht) hle
      · have he : (a,b) ∉ listWalkEdges (b :: rest) := by
          intro h
          exact ha (List.mem_toFinset.mpr (listWalkEdges_endpoints h).1)
        rw [List.toFinset_cons, Finset.card_insert_of_notMem ha, listWalkEdges,
          Finset.card_insert_of_notMem he]
        constructor
        · omega
        · intro hn
          have ht : ¬(b :: rest).Nodup := by
            intro ht
            apply hn
            exact List.nodup_cons.mpr ⟨fun h => ha (List.mem_toFinset.mpr h), ht⟩
          have h := ih.2 ht
          omega

#print axioms listWalkEdges_endpoints
#print axioms listWalk_vertex_count
end SpectralRadiusUpperTail
