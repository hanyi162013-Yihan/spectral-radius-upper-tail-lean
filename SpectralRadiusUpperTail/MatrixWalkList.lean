import SpectralRadiusUpperTail.ListWalkCount
import SpectralRadiusUpperTail.IidWalkSingleton
import Mathlib.Data.List.OfFn

namespace SpectralRadiusUpperTail
variable {ι : Type*} [DecidableEq ι]

lemma listWalkEdges_ofFn (k : ℕ) (f : Fin (k+1) → ι) :
    listWalkEdges (List.ofFn f) =
      (List.ofFn (fun j : Fin k => (f j.castSucc, f j.succ))).toFinset := by
  induction k with
  | zero => simp [List.ofFn_succ, listWalkEdges]
  | succ k ih =>
    have hs : listWalkEdges (List.ofFn f) =
        insert (f 0, f (Fin.succ 0))
          (listWalkEdges (List.ofFn (fun j : Fin (k+1) => f j.succ))) := by
      rw [List.ofFn_succ, List.ofFn_succ, listWalkEdges]
    rw [hs, ih, List.ofFn_succ, List.toFinset_cons]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ]

/-- Exact bridge from the matrix-power path encoding to finite list edges. -/
lemma matrixWalk_list_edges (k : ℕ) (i : ι) (v : Fin k → ι) :
    listWalkEdges (i :: List.ofFn v) =
      Finset.univ.image (matrixWalkEdge i v) := by
  have hl : List.ofFn (Fin.cons i v : Fin (k+1) → ι) = i :: List.ofFn v := by
    simp [List.ofFn_succ]
  rw [← hl, listWalkEdges_ofFn]
  ext edge
  simp [matrixWalkEdge]

/-- Actual matrix-walk vertex count, with the stronger bound for repeated vertices. -/
lemma matrixWalk_vertex_count (k : ℕ) (i : ι) (v : Fin k → ι) :
    (i :: List.ofFn v).toFinset.card ≤ (Finset.univ.image (matrixWalkEdge i v)).card+1 ∧
      (¬(i :: List.ofFn v).Nodup →
        (i :: List.ofFn v).toFinset.card ≤ (Finset.univ.image (matrixWalkEdge i v)).card) := by
  simpa only [matrixWalk_list_edges] using listWalk_vertex_count (i :: List.ofFn v)

#print axioms listWalkEdges_ofFn
#print axioms matrixWalk_list_edges
#print axioms matrixWalk_vertex_count
end SpectralRadiusUpperTail
