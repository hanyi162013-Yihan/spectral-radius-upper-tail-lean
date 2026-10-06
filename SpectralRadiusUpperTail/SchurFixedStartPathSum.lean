import SpectralRadiusUpperTail.SchurFixedStartWaitingFirstEdge
import SpectralRadiusUpperTail.SchurWaitingSum
import SpectralRadiusUpperTail.SchurStrictPathTerm

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Sum all strict length-`l` paths from a fixed start to a fixed terminal,
with exactly `k-l` diagonal waits. -/
noncomputable def schurFixedStartPathSum (d N l k : ℕ)
    (D : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin N) (Fin N) (Matrix (Fin d) (Fin d) ℝ))
    (i j : Fin N) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ pm : SchurFixedStartWaiting N k l i,
    if pm.1.val.val (Fin.last l) = j then
      schurStrictPathTerm d N l D U pm.1.val.val pm.2.val else 0

/-- Exact first-edge reindexing of the explicit path sum. -/
theorem schurFixedStartPathSum_succ_reindex (d N l k : ℕ) (hlk : l < k)
    (D : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin N) (Fin N) (Matrix (Fin d) (Fin d) ℝ))
    (i j : Fin N) :
    schurFixedStartPathSum d N (l+1) k D U i j =
      ∑ s : Fin (k-l),
        ∑ q : {q : IncreasingBlockPath N l // i < q.val 0},
          ∑ t : SchurWaitingTimes (k-s.val-1) l,
            if q.val.val (Fin.last l) = j then
              (D i)^s.val * U i (q.val.val 0) *
                schurStrictPathTerm d N l D U q.val.val t.val else 0 := by
  unfold schurFixedStartPathSum
  conv_lhs => rw [← (schurFixedStartWaitingFirstEdgeEquiv N k l hlk i).symm.sum_comp]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro t _
  have hend :
      ((schurFixedStartWaitingFirstEdgeEquiv N k l hlk i).symm
        ⟨s,(q,t)⟩).1.val.val (Fin.last (l+1)) =
        q.val.val (Fin.last l) := by rfl
  rw [hend]
  split_ifs with hj
  · change schurStrictPathTerm d N (l+1) D U
        (Fin.cons i q.val.val) (Fin.cons s.val t.val) = _
    exact schurStrictPathTerm_cons d N l D U i q.val.val s.val t.val
  · rfl

#print axioms schurFixedStartPathSum_succ_reindex
end SpectralRadiusUpperTail
