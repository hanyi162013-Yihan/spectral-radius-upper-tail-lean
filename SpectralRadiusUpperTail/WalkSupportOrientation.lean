import SpectralRadiusUpperTail.WalkSupportCard

namespace SpectralRadiusUpperTail
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

lemma walkSupportGraph_edge_card_eq_of_maximal (E : Finset (ι × ι))
    (h : (walkSupportGraph E).Connected) (hc : E.card+1 = Fintype.card ι) :
    (walkSupportGraph E).edgeFinset.card = E.card := by
  have hv := h.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card] at hv
  have he := walkSupportGraph_edge_card_le E
  omega

/-- If forgetting directions loses no edges, there are no loops or opposing
 orientations in the original directed set. -/
lemma walkSupportGraph_orientation_of_card (E : Finset (ι × ι))
    (hc : (walkSupportGraph E).edgeFinset.card = E.card) :
    (∀ a b, (a,b) ∈ E → a ≠ b) ∧ (∀ a b, (a,b) ∈ E → (b,a) ∉ E) := by
  have hsub := walkSupportGraph_edges_subset E
  have hcard : (E.image (fun e => s(e.1,e.2))).card ≤ E.card := Finset.card_image_le
  have heq : (walkSupportGraph E).edgeFinset = E.image (fun e => s(e.1,e.2)) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hinj : Set.InjOn (fun e : ι × ι => s(e.1,e.2)) E :=
    Finset.card_image_iff.mp (by rw [← heq,hc])
  have hloop : ∀ a b, (a,b) ∈ E → a ≠ b := by
    intro a b hab
    have he : s(a,b) ∈ (walkSupportGraph E).edgeFinset := by
      rw [heq]
      exact Finset.mem_image.mpr ⟨(a,b),hab,rfl⟩
    have ha : (walkSupportGraph E).Adj a b := by simpa using he
    exact ha.1
  refine ⟨hloop,?_⟩
  intro a b hab hba
  have he := hinj hab hba (Sym2.eq_swap : s(a,b) = s(b,a))
  exact hloop a b hab (congrArg Prod.fst he)

lemma walkSupportGraph_oriented_tree (E : Finset (ι × ι))
    (h : (walkSupportGraph E).Connected) (hc : E.card+1 = Fintype.card ι) :
    (walkSupportGraph E).IsTree ∧ (∀ a b, (a,b) ∈ E → a ≠ b) ∧
      (∀ a b, (a,b) ∈ E → (b,a) ∉ E) :=
  ⟨walkSupportGraph_tree_of_card E h hc,
    walkSupportGraph_orientation_of_card E (walkSupportGraph_edge_card_eq_of_maximal E h hc)⟩

#print axioms walkSupportGraph_edge_card_eq_of_maximal
#print axioms walkSupportGraph_orientation_of_card
#print axioms walkSupportGraph_oriented_tree
end SpectralRadiusUpperTail
