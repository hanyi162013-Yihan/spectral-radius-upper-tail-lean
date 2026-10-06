import SpectralRadiusUpperTail.OrientedSupportCardinality
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Fintype.BigOperators

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def componentEntries (E : Finset (V × V))
    (c : (walkSupportGraph E).ConnectedComponent) : Finset (c × c) := by
  classical
  exact Finset.univ.filter (fun e => (e.1.val,e.2.val) ∈ E)

noncomputable def componentEntryFiber (E : Finset (V × V))
    (c : (walkSupportGraph E).ConnectedComponent) : Finset (V × V) := by
  classical
  exact E.filter (fun e => (walkSupportGraph E).connectedComponentMk e.1 = c)

lemma componentEntries_graph (E : Finset (V × V))
    (c : (walkSupportGraph E).ConnectedComponent) :
    walkSupportGraph (componentEntries E c) = c.toSimpleGraph := by
  classical
  ext a b
  change (a ≠ b ∧ ((a,b) ∈ componentEntries E c ∨ (b,a) ∈ componentEntries E c)) ↔
    (a.val ≠ b.val ∧ ((a.val,b.val) ∈ E ∨ (b.val,a.val) ∈ E))
  simp only [componentEntries, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr (not_congr Subtype.val_injective.eq_iff.symm) Iff.rfl

lemma componentEntries_image (E : Finset (V × V))
    (c : (walkSupportGraph E).ConnectedComponent) :
    (componentEntries E c).image (Prod.map Subtype.val Subtype.val) =
      componentEntryFiber E c := by
  classical
  ext e
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hab).2,a.property⟩
  · intro h
    obtain ⟨he,ha⟩ := Finset.mem_filter.mp h
    have hb : (walkSupportGraph E).connectedComponentMk e.2 = c :=
      (SimpleGraph.ConnectedComponent.sound (walkSupportGraph_edge_reachable E he)).symm.trans ha
    exact Finset.mem_image.mpr ⟨(⟨e.1,ha⟩,⟨e.2,hb⟩),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩

lemma componentEntries_card (E : Finset (V × V))
    (c : (walkSupportGraph E).ConnectedComponent) :
    (componentEntries E c).card =
      (componentEntryFiber E c).card := by
  classical
  rw [← componentEntries_image E c]
  symm
  apply Finset.card_image_of_injective
  intro x y h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

lemma oriented_forest_component_card (E : Finset (V × V))
    (ha : (walkSupportGraph E).IsAcyclic)
    (hloop : ∀ a b, (a,b) ∈ E → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ E → (b,a) ∉ E)
    (c : (walkSupportGraph E).ConnectedComponent) :
    Nat.card c = (componentEntryFiber E c).card + 1 := by
  classical
  have ht : (walkSupportGraph (componentEntries E c)).IsTree := by
    rw [componentEntries_graph]
    exact ha.isTree_connectedComponent c
  have hc := oriented_tree_vertex_card (componentEntries E c) ht
    (fun a b hab he => hloop a.val b.val (Finset.mem_filter.mp hab).2 (congrArg Subtype.val he))
    (fun a b hab hba => hno a.val b.val (Finset.mem_filter.mp hab).2 (Finset.mem_filter.mp hba).2)
  simpa only [Nat.card_eq_fintype_card, componentEntries_card] using hc

#print axioms componentEntries
#print axioms componentEntryFiber
#print axioms componentEntries_graph
#print axioms componentEntries_image
#print axioms componentEntries_card
#print axioms oriented_forest_component_card
end SpectralRadiusUpperTail
