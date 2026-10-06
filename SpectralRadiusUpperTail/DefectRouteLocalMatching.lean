import SpectralRadiusUpperTail.DefectRouteLocalVertices
import SpectralRadiusUpperTail.AmbientMatchingReconstruction

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

noncomputable def DefectRouteCertificate.localMatching (c : DefectRouteCertificate s v)
    (i : Fin (expandedDefectRoutes c.segments c.tours).length) :
    SignedNoncrossingMatching (c.tourSigns i) :=
  Classical.choose (c.route_matching _ (List.get_mem _ i))

lemma DefectRouteCertificate.localMatching_preserves_entry (c : DefectRouteCertificate s v)
    (i : Fin (expandedDefectRoutes c.segments c.tours).length)
    (j : Fin ((expandedDefectRoutes c.segments c.tours).get i).tokens.length) :
    orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices
      ((c.localMatching i).val.val j) =
    orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices j := by
  have h := Classical.choose_spec (c.route_matching _ (List.get_mem _ i)) j
  exact ((c.localTourModel i).entries ((c.localMatching i).val.val j)).trans
    (h.trans ((c.localTourModel i).entries j).symm)

lemma DefectRouteCertificate.localTour_multiplicity (c : DefectRouteCertificate s v)
    (i : Fin (expandedDefectRoutes c.segments c.tours).length)
    (j : Fin ((expandedDefectRoutes c.segments c.tours).get i).tokens.length) :
    entryMultiplicity (orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices)
      (orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices j) = 2 := by
  have hlist : List.ofFn (orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices) =
      ((expandedDefectRoutes c.segments c.tours).get i).tokens.map Prod.fst := by
    have he : orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices =
        fun k => (((expandedDefectRoutes c.segments c.tours).get i).tokens.get k).1 :=
      funext (c.localTourModel i).entries
    rw [he]
    have hh := congrArg (List.map Prod.fst)
      (List.ofFn_get ((expandedDefectRoutes c.segments c.tours).get i).tokens)
    simpa only [List.map_ofFn,Function.comp_def] using hh
  rw [← list_ofFn_entryMultiplicity, hlist]
  exact c.localTour_entry_count i _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)

#print axioms DefectRouteCertificate.localMatching
#print axioms DefectRouteCertificate.localMatching_preserves_entry
#print axioms DefectRouteCertificate.localTour_multiplicity
end SpectralRadiusUpperTail
