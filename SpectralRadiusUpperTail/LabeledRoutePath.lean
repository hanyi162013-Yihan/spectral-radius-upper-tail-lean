import SpectralRadiusUpperTail.SegmentChainPayload
import SpectralRadiusUpperTail.FiniteWordListCount

namespace SpectralRadiusUpperTail
variable {A V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex realization of a route with arbitrary labels and a specified
endpoint map. Only existence of this realization uses choice. -/
structure LabeledRoutePath (ends : A → V × V) (p : SegmentRoute V A) where
  vertices : Fin (p.tokens.length+1) → V
  start_eq : vertices 0 = p.start
  finish_eq : vertices (Fin.last p.tokens.length) = p.finish
  entries : ∀ i, orientedWalkEdge (fun j : Fin p.tokens.length => (p.tokens.get j).2)
    vertices i = ends (p.tokens.get i).1

lemma labeledRoutePath_nonempty (ends : A → V × V) (p : SegmentRoute V A)
    (hp : OrientedSegmentChain ends p.start p.finish p.tokens) :
    Nonempty (LabeledRoutePath ends p) := by
  obtain ⟨v,h0,hl,he⟩ := labeledRoute_exists_entry_path ends p hp
  exact ⟨⟨v,h0,hl,he⟩⟩

lemma LabeledRoutePath.entry_list {ends : A → V × V} {p : SegmentRoute V A}
    (q : LabeledRoutePath ends p) :
    List.ofFn (orientedWalkEdge (fun j : Fin p.tokens.length => (p.tokens.get j).2)
      q.vertices) = p.tokens.map (fun t => ends t.1) := by
  rw [show orientedWalkEdge (fun j : Fin p.tokens.length => (p.tokens.get j).2)
    q.vertices = (fun j => ends (p.tokens.get j).1) from funext q.entries]
  have h := congrArg (List.map (fun t : A × Bool => ends t.1)) (List.ofFn_get p.tokens)
  simpa only [List.map_ofFn,Function.comp_def] using h

lemma LabeledRoutePath.double_entries {ends : A → V × V} {p : SegmentRoute V A}
    (q : LabeledRoutePath ends p)
    (h : ∀ t ∈ p.tokens, (p.tokens.map (fun a => ends a.1)).count (ends t.1) = 2)
    (i : Fin p.tokens.length) :
    entryMultiplicity (orientedWalkEdge (fun j : Fin p.tokens.length => (p.tokens.get j).2)
      q.vertices) (orientedWalkEdge (fun j : Fin p.tokens.length => (p.tokens.get j).2)
      q.vertices i) = 2 := by
  rw [← list_ofFn_entryMultiplicity,q.entry_list,q.entries]
  exact h _ (List.get_mem _ i)

lemma LabeledRoutePath.support {ends : A → V × V} {p : SegmentRoute V A}
    (q : LabeledRoutePath ends p) (T : Finset (V × V))
    (h : ∀ t ∈ p.tokens, ends t.1 ∈ T) :
    Finset.univ.image (orientedWalkEdge (fun j : Fin p.tokens.length => (p.tokens.get j).2)
      q.vertices) ⊆ T := by
  intro e he
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  rw [q.entries]
  exact h _ (List.get_mem _ i)

#print axioms LabeledRoutePath
#print axioms labeledRoutePath_nonempty
#print axioms LabeledRoutePath.entry_list
#print axioms LabeledRoutePath.double_entries
#print axioms LabeledRoutePath.support
end SpectralRadiusUpperTail
