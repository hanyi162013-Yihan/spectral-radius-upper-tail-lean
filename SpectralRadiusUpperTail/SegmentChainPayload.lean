import SpectralRadiusUpperTail.SegmentPayloadTransport
import SpectralRadiusUpperTail.SegmentChainFinitePath
import SpectralRadiusUpperTail.SignedWalkSupport

namespace SpectralRadiusUpperTail
variable {A B V : Type*}

/-- A primitive chain can be checked either before or after relabeling its
payload, provided its endpoint function is composed with the same map. -/
lemma segmentChain_map_payload_iff (ends : B → V × V) (f : A → B)
    (L : List (A × Bool)) (a b : V) :
    OrientedSegmentChain ends a b (L.map (mapSegmentToken f)) ↔
      OrientedSegmentChain (ends ∘ f) a b L := by
  induction L generalizing a b with
  | nil =>
    constructor <;> intro h <;> cases h <;> exact .nil _
  | cons t L ih =>
    simp only [List.map_cons]
    constructor
    · intro h
      cases h with
      | cons _ h => exact .cons t ((ih _ _).mp h)
    · intro h
      cases h with
      | cons _ h => exact .cons (mapSegmentToken f t) ((ih _ _).mpr h)

variable [Fintype V] [DecidableEq V]

/-- General payload version of the finite vertex-path conversion. -/
lemma labeledRoute_exists_entry_path (ends : A → V × V) (p : SegmentRoute V A)
    (hp : OrientedSegmentChain ends p.start p.finish p.tokens) :
    ∃ v : Fin (p.tokens.length+1) → V,
      v 0 = p.start ∧ v (Fin.last p.tokens.length) = p.finish ∧
      ∀ i, orientedWalkEdge (fun j : Fin p.tokens.length => (p.tokens.get j).2) v i =
        ends (p.tokens.get i).1 := by
  obtain ⟨v,hv0,hvl,hv⟩ := hp.exists_fin_path
  refine ⟨v,hv0,hvl,?_⟩
  intro i
  have hs := (hv i).1
  have hf := (hv i).2
  cases hi : (p.tokens.get i).2
  · simp only [segmentTokenStart,segmentTokenFinish,hi,Bool.false_eq_true,if_false] at hs hf
    simp only [orientedWalkEdge,hi,Bool.false_eq_true,if_false]
    exact Prod.ext hs.symm hf.symm
  · simp only [segmentTokenStart,segmentTokenFinish,hi,if_true] at hs hf
    simp only [orientedWalkEdge,hi,if_true]
    exact Prod.ext hf.symm hs.symm

#print axioms segmentChain_map_payload_iff
#print axioms labeledRoute_exists_entry_path
end SpectralRadiusUpperTail
