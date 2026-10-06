import SpectralRadiusUpperTail.TreePathTraversalBalance

namespace SpectralRadiusUpperTail
variable {V : Type*} [DecidableEq V]

/-- Every occurrence in a closed tree path has a reverse geometric occurrence. -/
lemma closedTreePath_reverse_occurrence {n : ℕ} (G : SimpleGraph V) (ht : G.IsTree)
    (p : Fin (n+1) → V) (hadj : ∀ t : Fin n, G.Adj (p t.castSucc) (p t.succ))
    (hclosed : p (Fin.last n) = p 0) (i : Fin n) :
    ∃ j : Fin n, p j.castSucc = p i.succ ∧ p j.succ = p i.castSucc := by
  classical
  by_contra hn
  have hnone (j : Fin n) : ¬ (p j.castSucc = p i.succ ∧ p j.succ = p i.castSucc) :=
    fun h => hn ⟨j,h⟩
  have hz : (∑ j : Fin n, if p j.castSucc = p i.succ ∧ p j.succ = p i.castSucc
      then (1 : ℕ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact if_neg (hnone j)
  have he := closedTreePath_traversals_eq G ht (p i.castSucc) (p i.succ)
    (hadj i) n p hadj hclosed
  rw [hz] at he
  have hle := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      Nat.zero_le (if p j.castSucc = p i.castSucc ∧ p j.succ = p i.succ then (1 : ℕ) else 0))
    (Finset.mem_univ i)
  simp only [and_self, if_true, he] at hle
  omega

#print axioms closedTreePath_reverse_occurrence
end SpectralRadiusUpperTail
