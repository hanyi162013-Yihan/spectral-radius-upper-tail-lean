import SpectralRadiusUpperTail.IndexedSegmentPositions
import Mathlib.Data.List.Flatten

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.segmentPositions_sublist (c : DefectRouteCertificate s v)
    (i : Fin c.segments.length) :
    (c.segmentPositions i).Sublist (List.ofFn (fun j : Fin (2*r) => j)) := by
  have h : (c.segmentPositions i).Sublist (List.ofFn c.segmentPositions).flatten :=
    List.sublist_flatten_of_mem (List.mem_ofFn.mpr ⟨i,rfl⟩)
  rw [c.segmentPositions_flatten] at h
  exact h.trans List.filter_sublist

#print axioms DefectRouteCertificate.segmentPositions_sublist
end SpectralRadiusUpperTail
