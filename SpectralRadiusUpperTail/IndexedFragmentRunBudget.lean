import SpectralRadiusUpperTail.DefectArrangementShape
import SpectralRadiusUpperTail.DeletedRunBudget

namespace SpectralRadiusUpperTail
variable {A B : Type*} [DecidableEq B]

/-- Delete arbitrary payload positions before mapping to original block IDs.
This permits partial deletion within a block. -/
lemma mapped_sublist_chunk_run_budget (f : A → B) (l : List A) (C : List (List A))
    (hsub : C.flatten.Sublist l) (N S : ℕ)
    (hN : signRunCount (l.map f) ≤ N) (hS : C.length ≤ S) :
    (C.map (fun c => signRunCount (c.map f))).sum ≤ N+(S-1) := by
  have hc := signRunCount_chunks (C.map (List.map f))
  have hf : (C.map (List.map f)).flatten = C.flatten.map f := (List.map_flatten).symm
  rw [hf] at hc
  have hs := (signRunCount_sublist_bounds (hsub.map f)).1
  simp only [List.map_map,List.length_map,Function.comp_def] at hc
  exact Nat.le_trans hc (Nat.add_le_add (Nat.le_trans hs hN) (Nat.sub_le_sub_right hS 1))

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.segment_fragment_run_budget (c : DefectRouteCertificate s v)
    (block : Fin (2*r) → B) (N : ℕ) (hN : signRunCount (List.ofFn block) ≤ N) :
    (c.segmentPositionChunks.map (fun w => signRunCount (w.map block))).sum ≤
      N+8*(r+1-Fintype.card V) := by
  have hsub : c.segmentPositionChunks.flatten.Sublist (List.ofFn (fun i : Fin (2*r) => i)) := by
    rw [c.segmentPositionChunks_flatten]
    exact List.filter_sublist
  have hN' : signRunCount ((List.ofFn (fun i : Fin (2*r) => i)).map block) ≤ N := by
    simpa only [List.map_ofFn,Function.comp_def] using hN
  have hS : c.segmentPositionChunks.length ≤ 8*(r+1-Fintype.card V)+1 := by
    rw [c.segmentPositionChunks_length]
    exact c.segment_budget
  have h := mapped_sublist_chunk_run_budget block _ _ hsub N _ hN' hS
  simpa only [Nat.add_sub_cancel] using h

#print axioms mapped_sublist_chunk_run_budget
#print axioms DefectRouteCertificate.segment_fragment_run_budget
end SpectralRadiusUpperTail
