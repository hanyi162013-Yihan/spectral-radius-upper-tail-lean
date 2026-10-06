import SpectralRadiusUpperTail.AmbientTreeMatching
import SpectralRadiusUpperTail.SegmentChainFinitePath
import SpectralRadiusUpperTail.SegmentRoute
import SpectralRadiusUpperTail.FiniteWordListCount

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every actual closed double-entry route in a fixed oriented tree yields an
opposite-sign noncrossing matching of its primitive positions. -/
lemma treeRoute_signed_matching (T : Finset (V × V)) (ht : (walkSupportGraph T).IsTree)
    (hloop : ∀ a b, (a,b) ∈ T → a ≠ b)
    (hno : ∀ a b, (a,b) ∈ T → (b,a) ∉ T)
    (p : SegmentRoute V (V × V))
    (hp : OrientedSegmentChain (fun e => e) p.start p.finish p.tokens)
    (hclosed : p.start = p.finish) (hT : ∀ t ∈ p.tokens, t.1 ∈ T)
    (hdouble : ∀ t ∈ p.tokens, (p.tokens.map Prod.fst).count t.1 = 2) :
    ∃ f : SignedNoncrossingMatching (fun i : Fin p.tokens.length => (p.tokens.get i).2),
      ∀ i, (p.tokens.get (f.val.val i)).1 = (p.tokens.get i).1 := by
  obtain ⟨v,hv0,hvlast,hv⟩ := hp.exists_fin_path
  let s : Fin p.tokens.length → Bool := fun i => (p.tokens.get i).2
  have he : ∀ i, orientedWalkEdge s v i = (p.tokens.get i).1 := by
    intro i
    have hs := (hv i).1
    have hf := (hv i).2
    cases hi : (p.tokens.get i).2
    · simp only [segmentTokenStart,segmentTokenFinish,hi,Bool.false_eq_true,if_false] at hs hf
      simp only [orientedWalkEdge,s,hi,Bool.false_eq_true,if_false]
      exact Prod.ext hs.symm hf.symm
    · simp only [segmentTokenStart,segmentTokenFinish,hi,if_true] at hs hf
      simp only [orientedWalkEdge,s,hi,if_true]
      exact Prod.ext hf.symm hs.symm
  have hsub : Finset.univ.image (orientedWalkEdge s v) ⊆ T := by
    intro e he'
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he'
    rw [he]
    exact hT (p.tokens.get i) (List.get_mem p.tokens i)
  have hlist : List.ofFn (orientedWalkEdge s v) = p.tokens.map Prod.fst := by
    have hefun : orientedWalkEdge s v = fun i => (p.tokens.get i).1 := funext he
    rw [hefun]
    have hh := congrArg (List.map Prod.fst) (List.ofFn_get p.tokens)
    simpa only [List.map_ofFn,Function.comp_def] using hh
  have hm : ∀ i, entryMultiplicity (orientedWalkEdge s v) (orientedWalkEdge s v i) = 2 := by
    intro i
    rw [← list_ofFn_entryMultiplicity (orientedWalkEdge s v),hlist,he]
    exact hdouble (p.tokens.get i) (List.get_mem p.tokens i)
  have hc : v (Fin.last p.tokens.length) = v 0 := by
    rw [hvlast,hv0]
    exact hclosed.symm
  obtain ⟨f,hf⟩ := ambientTree_signed_matching T ht hloop hno s v hsub hm hc
  refine ⟨f,?_⟩
  intro i
  simpa only [he] using hf i

#print axioms treeRoute_signed_matching
end SpectralRadiusUpperTail
