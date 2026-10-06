import SpectralRadiusUpperTail.OrientedTreeWalk

namespace SpectralRadiusUpperTail
variable {ι : Type*} [DecidableEq ι]

lemma listWalk_support_isChain (E : Finset (ι × ι))
    (hloop : ∀ a b, (a,b) ∈ E → a ≠ b) (l : List ι)
    (hE : listWalkEdges l ⊆ E) : l.IsChain (walkSupportGraph E).Adj := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b rest =>
      rw [List.isChain_cons_cons]
      have hab := hE (Finset.mem_insert_self (a,b) (listWalkEdges (b :: rest)))
      exact ⟨⟨hloop a b hab,Or.inl hab⟩,
        ih (fun _ he => hE (Finset.mem_insert_of_mem he))⟩

lemma graphWalk_directed_edges {G : SimpleGraph ι} {u v : ι} (p : G.Walk u v) :
    listWalkEdges p.support = (p.darts.map (fun d => (d.fst,d.snd))).toFinset := by
  induction p with
  | nil => simp [listWalkEdges]
  | cons h p ih =>
    cases p with
    | nil => simp [listWalkEdges]
    | cons h' q =>
      simpa only [SimpleGraph.Walk.support_cons, listWalkEdges,
        SimpleGraph.Walk.darts_cons, List.map_cons, List.toFinset_cons] using
        congrArg (insert _) ih

/-- Every directed vertex list in an oriented tree has no repeated vertex. -/
lemma listWalk_nodup_of_oriented_tree (E : Finset (ι × ι))
    (hG : (walkSupportGraph E).IsTree)
    (hloop : ∀ a b, (a,b) ∈ E → a ≠ b)
    (hop : ∀ a b, (a,b) ∈ E → (b,a) ∉ E)
    (l : List ι) (hE : listWalkEdges l ⊆ E) : l.Nodup := by
  by_cases hn : l = []
  · subst l
    simp
  · have hchain := listWalk_support_isChain E hloop l hE
    let p := SimpleGraph.Walk.ofSupport l hn hchain
    have hs : p.support = l := SimpleGraph.Walk.support_ofSupport hn hchain
    have hd : ∀ d ∈ p.darts, (d.fst,d.snd) ∈ E := by
      intro d hd
      apply hE
      rw [← hs, graphWalk_directed_edges]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨d,hd,rfl⟩)
    have hp := orientedTreeWalk_isPath E hG hop p hd
    rw [SimpleGraph.Walk.isPath_def, hs] at hp
    exact hp

#print axioms listWalk_support_isChain
#print axioms graphWalk_directed_edges
#print axioms listWalk_nodup_of_oriented_tree
end SpectralRadiusUpperTail
