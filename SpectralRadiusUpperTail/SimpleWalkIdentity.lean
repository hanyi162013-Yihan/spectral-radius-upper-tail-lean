import SpectralRadiusUpperTail.ListWalkCount

namespace SpectralRadiusUpperTail
variable {ι : Type*} [DecidableEq ι]

lemma listWalk_tail_has_incoming (l : List ι) {x : ι} (hx : x ∈ l.tail) :
    ∃ a, (a,x) ∈ listWalkEdges l := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    cases l with
    | nil => simp at hx
    | cons b rest =>
      rcases List.mem_cons.mp hx with h | h
      · subst x
        exact ⟨a,Finset.mem_insert_self _ _⟩
      · obtain ⟨c,hc⟩ := ih h
        exact ⟨c,Finset.mem_insert_of_mem hc⟩

lemma simpleWalk_head_eq (a b c : ι) (l r : List ι)
    (hn : (a :: b :: l).Nodup)
    (he : listWalkEdges (a :: b :: l) = listWalkEdges (c :: r)) : a = c := by
  have hab : (a,b) ∈ listWalkEdges (c :: r) :=
    he ▸ Finset.mem_insert_self (a,b) (listWalkEdges (b :: l))
  rcases List.mem_cons.mp (listWalkEdges_endpoints hab).1 with h | h
  · exact h
  · obtain ⟨x,hx⟩ := listWalk_tail_has_incoming (c :: r) h
    have hx' : (x,a) ∈ listWalkEdges (a :: b :: l) := he.symm ▸ hx
    exact False.elim ((List.nodup_cons.mp hn).1 (listWalkEdges_endpoints hx').2)

/-- A simple directed path is determined by its initial vertex and edge set. -/
lemma simpleWalk_eq_of_same_start (a : ι) (l r : List ι)
    (hl : (a :: l).Nodup) (hr : (a :: r).Nodup)
    (he : listWalkEdges (a :: l) = listWalkEdges (a :: r)) : a :: l = a :: r := by
  induction l generalizing a r with
  | nil =>
    cases r with
    | nil => rfl
    | cons b r =>
      have h : (a,b) ∈ listWalkEdges [a] :=
        he.symm ▸ Finset.mem_insert_self (a,b) (listWalkEdges (b :: r))
      simp [listWalkEdges] at h
  | cons b l ih =>
    cases r with
    | nil =>
      have h : (a,b) ∈ listWalkEdges [a] :=
        he ▸ Finset.mem_insert_self (a,b) (listWalkEdges (b :: l))
      simp [listWalkEdges] at h
    | cons c r =>
      have hac : (a,c) ∈ listWalkEdges (a :: b :: l) :=
        he.symm ▸ Finset.mem_insert_self (a,c) (listWalkEdges (c :: r))
      have hcb : c = b := by
        rcases Finset.mem_insert.mp hac with h | h
        · exact congrArg Prod.snd h
        · exact False.elim ((List.nodup_cons.mp hl).1 (listWalkEdges_endpoints h).1)
      subst c
      have hn1 : (a,b) ∉ listWalkEdges (b :: l) := by
        intro h
        exact (List.nodup_cons.mp hl).1 (listWalkEdges_endpoints h).1
      have hn2 : (a,b) ∉ listWalkEdges (b :: r) := by
        intro h
        exact (List.nodup_cons.mp hr).1 (listWalkEdges_endpoints h).1
      have ht := congrArg (fun s : Finset (ι × ι) => s.erase (a,b)) he
      simp [listWalkEdges, hn1, hn2] at ht
      exact congrArg (List.cons a) (ih b r (List.nodup_cons.mp hl).2
        (List.nodup_cons.mp hr).2 ht)

/-- Nontrivial simple directed paths with the same edges are identical. -/
lemma simpleWalk_eq_of_edges (a b c : ι) (l r : List ι)
    (hl : (a :: b :: l).Nodup) (hr : (c :: r).Nodup)
    (he : listWalkEdges (a :: b :: l) = listWalkEdges (c :: r)) :
    a :: b :: l = c :: r := by
  have hac := simpleWalk_head_eq a b c l r hl he
  subst c
  exact simpleWalk_eq_of_same_start a (b :: l) r hl hr he

#print axioms listWalk_tail_has_incoming
#print axioms simpleWalk_head_eq
#print axioms simpleWalk_eq_of_same_start
#print axioms simpleWalk_eq_of_edges
end SpectralRadiusUpperTail
