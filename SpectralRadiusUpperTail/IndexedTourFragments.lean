import SpectralRadiusUpperTail.SegmentTokenFragments
import SpectralRadiusUpperTail.FragmentCollectionFlatten
import SpectralRadiusUpperTail.FragmentExpansionSigns
import SpectralRadiusUpperTail.FragmentExpansionCount

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {V B : Type*} [Fintype V] [DecidableEq V] [DecidableEq B] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

/-- Actual post-rearrangement fragments cover the indexed tours exactly, keep
constant signs and length <=m, and cost at most the original runs plus 8g. -/
lemma DefectRouteCertificate.exists_indexed_tour_fragments (c : DefectRouteCertificate s v)
    (block : Fin (2*r) → B) (N m : ℕ)
    (hrun : signRunCount (List.ofFn block) ≤ N)
    (hcount : ∀ b, (List.ofFn block).count b ≤ m)
    (hsign : ∀ i j, block i = block j → s i = s j) :
    ∃ P : List (List (Fin (2*r) × Bool)),
      P.flatten = (c.indexedTours.map SegmentRoute.tokens).flatten ∧
      (∀ w ∈ P, w ≠ [] ∧ labelConstant Prod.snd w ∧ w.length ≤ m) ∧
      P.length ≤ N+8*(r+1-Fintype.card V) := by
  obtain ⟨P,hflat,hP,hbudget⟩ := c.exists_segment_token_fragments block N m hrun hcount hsign
  let F := c.routeShape.flatMap (fun toks => toks.flatMap (expandFragmentToken P))
  have hperm : (c.routeShape.flatten.map Prod.fst).Perm (List.ofFn (fun i : Fin c.segments.length => i)) := by
    simpa only [DefectRouteCertificate.routeShape,List.map_flatten,List.map_map,
      List.flatMap_def,Function.comp_def] using c.segment_permutation
  refine ⟨F,?_,?_,?_⟩
  · have h := expandFragmentCollection_flatten P c.routeShape
    have hp : (fun i => (P i).flatten) = c.positionWords := funext hflat
    rw [hp] at h
    simpa only [F,DefectRouteCertificate.routeShape,DefectRouteCertificate.indexedTours,
      List.map_map,Function.comp_def,expandSegmentRoute] using h
  · intro w hw
    obtain ⟨toks,_,ht⟩ := List.mem_flatMap.mp hw
    exact expandFragmentRoute_properties P m hP toks w ht
  · exact (expandFragmentCollection_fin_count P c.routeShape hperm).le.trans hbudget

#print axioms DefectRouteCertificate.exists_indexed_tour_fragments
end SpectralRadiusUpperTail
