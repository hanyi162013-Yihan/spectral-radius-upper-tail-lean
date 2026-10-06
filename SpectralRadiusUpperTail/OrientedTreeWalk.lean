import SpectralRadiusUpperTail.WalkSupportOrientation

namespace SpectralRadiusUpperTail
variable {ι : Type*} [DecidableEq ι]

/-- A walk whose directed edges have no opposite orientation cannot
 immediately traverse the same undirected edge twice. -/
lemma orientedWalk_edges_chain {G : SimpleGraph ι} (E : Finset (ι × ι))
    (hop : ∀ a b, (a,b) ∈ E → (b,a) ∉ E) {u v : ι} (p : G.Walk u v) :
    (∀ d ∈ p.darts, (d.fst,d.snd) ∈ E) → p.edges.IsChain (· ≠ ·) := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    intro hE
    have ht : ∀ d ∈ p.darts, (d.fst,d.snd) ∈ E := by
      intro d hd
      exact hE d (List.mem_cons_of_mem _ hd)
    have habE : (a,b) ∈ E := hE ⟨(a,b),hab⟩ List.mem_cons_self
    have hc := ih ht
    cases p with
    | nil => simp
    | @cons b c d hbc q =>
      rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons, List.isChain_cons_cons]
      refine ⟨?_,hc⟩
      intro heq
      have hbcE : (b,c) ∈ E := ht ⟨(b,c),hbc⟩ List.mem_cons_self
      rcases Sym2.eq_iff.mp heq with h | h
      · exact hab.ne h.1
      · have hac : a = c := h.1
        subst c
        exact hop a b habE hbcE

lemma orientedTreeWalk_isPath {G : SimpleGraph ι} (E : Finset (ι × ι))
    (hG : G.IsTree) (hop : ∀ a b, (a,b) ∈ E → (b,a) ∉ E)
    {u v : ι} (p : G.Walk u v) (hE : ∀ d ∈ p.darts, (d.fst,d.snd) ∈ E) :
    p.IsPath :=
  (hG.isAcyclic.isPath_iff_isChain p).mpr (orientedWalk_edges_chain E hop p hE)

#print axioms orientedWalk_edges_chain
#print axioms orientedTreeWalk_isPath
end SpectralRadiusUpperTail
