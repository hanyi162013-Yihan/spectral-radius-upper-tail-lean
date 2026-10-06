import SpectralRadiusUpperTail.FiniteEntryRepresentatives
import SpectralRadiusUpperTail.WalkSupportCard

namespace SpectralRadiusUpperTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma walkSupportGraph_eq_of_edge_image (T : Finset (ι × ι)) (H : SimpleGraph ι)
    [DecidableRel H.Adj] (him : T.image (fun e => s(e.1,e.2)) = H.edgeFinset) :
    walkSupportGraph T = H := by
  classical
  ext a b
  constructor
  · intro hab
    have hm : s(a,b) ∈ (walkSupportGraph T).edgeFinset := by simpa using hab
    have hi := walkSupportGraph_edges_subset T hm
    rw [him] at hi
    simpa using hi
  · intro hab
    have hm : s(a,b) ∈ H.edgeFinset := by simpa using hab
    rw [← him] at hm
    obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hm
    refine ⟨H.ne_of_adj hab,?_⟩
    rcases Sym2.eq_iff.mp heq with heq | heq
    · left
      have hh : e = (a,b) := Prod.ext heq.1 heq.2
      simpa only [hh] using he
    · right
      have hh : e = (b,a) := Prod.ext heq.1 heq.2
      simpa only [hh] using he

/-- A connected directed support contains exactly one orientation of each edge
of a spanning tree. Loops and opposite-orientation duplicates are excluded. -/
lemma directedSupport_exists_spanning_tree (E : Finset (ι × ι))
    (hc : (walkSupportGraph E).Connected) :
    ∃ T : Finset (ι × ι), T ⊆ E ∧ (walkSupportGraph T).IsTree ∧
      T.card + 1 = Fintype.card ι ∧
      (∀ a b, (a,b) ∈ T → a ≠ b) ∧
      (∀ a b, (a,b) ∈ T → (b,a) ∉ T) := by
  classical
  obtain ⟨H,hHE,hH⟩ := hc.exists_isTree_le
  have hsub : H.edgeFinset ⊆ E.image (fun e => s(e.1,e.2)) := by
    apply Finset.Subset.trans _ (walkSupportGraph_edges_subset E)
    simpa using hHE
  obtain ⟨T,hTE,him,hinj,hcard⟩ := finset_image_representatives E H.edgeFinset
    (fun e => s(e.1,e.2)) hsub
  have hgraph := walkSupportGraph_eq_of_edge_image T H him
  have hnoloop : ∀ a b, (a,b) ∈ T → a ≠ b := by
    intro a b hab
    have hm : s(a,b) ∈ H.edgeFinset := by
      rw [← him]
      exact Finset.mem_image.mpr ⟨(a,b),hab,rfl⟩
    have ha : H.Adj a b := by simpa using hm
    exact H.ne_of_adj ha
  refine ⟨T,hTE,hgraph.symm ▸ hH,?_,hnoloop,?_⟩
  · rw [hcard]
    exact hH.card_edgeFinset
  · intro a b hab hba
    have heq : (a,b) = (b,a) := hinj hab hba Sym2.eq_swap
    exact hnoloop a b hab (congrArg Prod.fst heq)

#print axioms walkSupportGraph_eq_of_edge_image
#print axioms directedSupport_exists_spanning_tree
end SpectralRadiusUpperTail
