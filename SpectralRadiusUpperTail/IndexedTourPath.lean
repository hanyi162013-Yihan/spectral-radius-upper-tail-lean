import SpectralRadiusUpperTail.IndexedTourValidity
import SpectralRadiusUpperTail.LabeledRoutePath
import SpectralRadiusUpperTail.TreeMatchingVertexDecoder

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

noncomputable def DefectRouteCertificate.indexedPath (c : DefectRouteCertificate s v)
    (i : Fin c.indexedTours.length) :
    LabeledRoutePath (orientedWalkEdge s v) (c.indexedTours.get i) :=
  Classical.choice (labeledRoutePath_nonempty _ _ (c.indexedTour_valid _ (List.get_mem _ i)).1.1)

noncomputable def DefectRouteCertificate.indexedSigns (c : DefectRouteCertificate s v)
    (i : Fin c.indexedTours.length) : Fin (c.indexedTours.get i).tokens.length → Bool :=
  fun j => ((c.indexedTours.get i).tokens.get j).2

lemma DefectRouteCertificate.indexedPath_support (c : DefectRouteCertificate s v)
    (i : Fin c.indexedTours.length) :
    Finset.univ.image (orientedWalkEdge (c.indexedSigns i) (c.indexedPath i).vertices) ⊆
      c.treeEntries :=
  (c.indexedPath i).support c.treeEntries (c.indexedTour_support _ (List.get_mem _ i))

lemma DefectRouteCertificate.indexedPath_double (c : DefectRouteCertificate s v)
    (i : Fin c.indexedTours.length) (j : Fin (c.indexedTours.get i).tokens.length) :
    entryMultiplicity (orientedWalkEdge (c.indexedSigns i) (c.indexedPath i).vertices)
      (orientedWalkEdge (c.indexedSigns i) (c.indexedPath i).vertices j) = 2 :=
  (c.indexedPath i).double_entries (c.indexedTour_double _ (List.get_mem _ i)) j

lemma DefectRouteCertificate.indexedPath_matching (c : DefectRouteCertificate s v)
    (i : Fin c.indexedTours.length) :
    ∃ f : SignedNoncrossingMatching (c.indexedSigns i), ∀ j,
      orientedWalkEdge (c.indexedSigns i) (c.indexedPath i).vertices (f.val.val j) =
        orientedWalkEdge (c.indexedSigns i) (c.indexedPath i).vertices j := by
  apply ambientTree_signed_matching c.treeEntries c.tree c.no_loops c.no_opposites
    (c.indexedSigns i) (c.indexedPath i).vertices (c.indexedPath_support i) (c.indexedPath_double i)
  rw [(c.indexedPath i).finish_eq,(c.indexedPath i).start_eq]
  exact (c.indexedTour_valid _ (List.get_mem _ i)).2.symm

noncomputable def DefectRouteCertificate.indexedMatching (c : DefectRouteCertificate s v)
    (i : Fin c.indexedTours.length) : SignedNoncrossingMatching (c.indexedSigns i) :=
  Classical.choose (c.indexedPath_matching i)

lemma DefectRouteCertificate.indexedMatching_decoder (c : DefectRouteCertificate s v)
    (i : Fin c.indexedTours.length) (a b : Fin ((c.indexedTours.get i).tokens.length+1)) :
    (c.indexedPath i).vertices a = (c.indexedPath i).vertices b ↔
      matchingVertexSetoid (c.indexedMatching i).val.val a b := by
  apply ambientTree_vertex_eq_matchingDecoder c.treeEntries c.tree c.no_loops c.no_opposites
    (c.indexedSigns i) (c.indexedPath i).vertices (c.indexedPath_support i) (c.indexedPath_double i)
    (c.indexedMatching i).val.val
  · exact (c.indexedMatching i).val.property.2.1
  · exact Classical.choose_spec (c.indexedPath_matching i)

#print axioms DefectRouteCertificate.indexedPath
#print axioms DefectRouteCertificate.indexedSigns
#print axioms DefectRouteCertificate.indexedPath_support
#print axioms DefectRouteCertificate.indexedPath_double
#print axioms DefectRouteCertificate.indexedPath_matching
#print axioms DefectRouteCertificate.indexedMatching
#print axioms DefectRouteCertificate.indexedMatching_decoder
end SpectralRadiusUpperTail
