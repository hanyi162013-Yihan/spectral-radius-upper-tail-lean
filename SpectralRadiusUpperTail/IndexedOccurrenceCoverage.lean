import SpectralRadiusUpperTail.DefectIndexedTours

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

noncomputable def DefectRouteCertificate.indexedWord (c : DefectRouteCertificate s v)
    (i : Fin c.indexedTours.length) (j : Fin (c.indexedTours.get i).tokens.length) :
    Fin (2*r) × Bool := (c.indexedTours.get i).tokens.get j

lemma DefectRouteCertificate.indexedWord_coverage (c : DefectRouteCertificate s v)
    (k : Fin (2*r)) :
    (∃ i j, (c.indexedWord i j).1 = k) ↔ k ∉ c.deletedPositions := by
  rw [← c.mem_survivingPositions,← c.indexedTours_positions_perm.mem_iff]
  constructor
  · rintro ⟨i,j,h⟩
    exact List.mem_flatMap.mpr ⟨_,List.get_mem _ i,
      List.mem_map.mpr ⟨_,List.get_mem _ j,h⟩⟩
  · intro h
    obtain ⟨p,hp,hk'⟩ := List.mem_flatMap.mp h
    obtain ⟨t,ht,hk⟩ := List.mem_map.mp hk'
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp ht
    exact ⟨i,j,hk⟩

#print axioms DefectRouteCertificate.indexedWord
#print axioms DefectRouteCertificate.indexedWord_coverage
end SpectralRadiusUpperTail
