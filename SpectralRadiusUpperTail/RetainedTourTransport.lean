import SpectralRadiusUpperTail.RetainedPositionExtension
import SpectralRadiusUpperTail.DefectRouteGluing

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.retained_entry_in_tour (c : DefectRouteCertificate s v)
    (e : V × V) (he : e ∈ c.treeEntries ∧ entryMultiplicity (orientedWalkEdge s v) e = 2) :
    ∃ (i : Fin (expandedDefectRoutes c.segments c.tours).length)
      (j : Fin ((expandedDefectRoutes c.segments c.tours).get i).tokens.length),
      orientedWalkEdge (c.tourSigns i) (c.localTourModel i).vertices j = e := by
  classical
  have hc : 0 < ((expandedDefectRoutes c.segments c.tours).flatMap
      (fun p => p.tokens.map Prod.fst)).count e := by
    rw [c.total_entry_counts e,if_pos he]
    omega
  obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp (List.count_pos_iff.mp hc)
  obtain ⟨i,rfl⟩ := List.get_of_mem hp
  obtain ⟨t,ht,hte⟩ := List.mem_map.mp hep
  obtain ⟨j,hj⟩ := List.get_of_mem ht
  exact ⟨i,j,((c.localTourModel i).entries j).trans ((congrArg Prod.fst hj).trans hte)⟩

/-- Both endpoints of a retained original entry occur among the actual local
tour vertices, even when their chronological orientation has been reversed. -/
lemma DefectRouteCertificate.retained_start_in_tour (c : DefectRouteCertificate s v)
    (k : Fin (2*r)) (hk : k ∉ c.deletedPositions) :
    ∃ x : c.TourPosition, (c.localTourModel x.1).vertices x.2 = v k.castSucc := by
  classical
  have hret : orientedWalkEdge s v k ∈ c.treeEntries ∧
      entryMultiplicity (orientedWalkEdge s v) (orientedWalkEdge s v k) = 2 := by
    simpa [DefectRouteCertificate.deletedPositions,not_or,not_not,and_comm] using hk
  obtain ⟨i,j,he⟩ := c.retained_entry_in_tour _ hret
  cases hs : s k <;> cases ht : c.tourSigns i j
  · refine ⟨⟨i,j.castSucc⟩,?_⟩
    simpa only [orientedWalkEdge,hs,ht,Bool.false_eq_true,if_false] using congrArg Prod.fst he
  · refine ⟨⟨i,j.succ⟩,?_⟩
    simpa only [orientedWalkEdge,hs,ht,Bool.false_eq_true,if_false,if_true] using congrArg Prod.fst he
  · refine ⟨⟨i,j.succ⟩,?_⟩
    simpa only [orientedWalkEdge,hs,ht,Bool.false_eq_true,if_false,if_true] using congrArg Prod.snd he
  · refine ⟨⟨i,j.castSucc⟩,?_⟩
    simpa only [orientedWalkEdge,hs,ht,if_true] using congrArg Prod.snd he

lemma DefectRouteCertificate.retained_position_in_tour (c : DefectRouteCertificate s v)
    (a : retainedInitialPositions c.deletedPositions) :
    ∃ x : c.TourPosition, (c.localTourModel x.1).vertices x.2 = v a.val := by
  obtain ⟨k,hk,hka⟩ := Finset.mem_image.mp a.property
  obtain ⟨x,hx⟩ := c.retained_start_in_tour k (Finset.mem_compl.mp hk)
  exact ⟨x,hka ▸ hx⟩

/-- An actual transport exists; no claim is made here that an arbitrary
transport table has small encoding cost. Its economical code must use the
already retained segment permutation and reversals. -/
noncomputable def DefectRouteCertificate.retainedTransport (c : DefectRouteCertificate s v) :
    retainedInitialPositions c.deletedPositions → c.TourPosition :=
  fun a => Classical.choose (c.retained_position_in_tour a)

lemma DefectRouteCertificate.retainedTransport_vertex (c : DefectRouteCertificate s v)
    (a : retainedInitialPositions c.deletedPositions) :
    (c.localTourModel (c.retainedTransport a).1).vertices (c.retainedTransport a).2 = v a.val :=
  Classical.choose_spec (c.retained_position_in_tour a)

#print axioms DefectRouteCertificate.retained_entry_in_tour
#print axioms DefectRouteCertificate.retained_start_in_tour
#print axioms DefectRouteCertificate.retained_position_in_tour
#print axioms DefectRouteCertificate.retainedTransport
#print axioms DefectRouteCertificate.retainedTransport_vertex
end SpectralRadiusUpperTail
