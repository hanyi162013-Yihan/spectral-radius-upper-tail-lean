import SpectralRadiusUpperTail.BridgeCutCrossing

namespace SpectralRadiusUpperTail
variable {V : Type*} [DecidableEq V]

lemma closedTreePath_traversals_eq (G : SimpleGraph V) (ht : G.IsTree)
    (a b : V) (hab : G.Adj a b) (k : ℕ) (p : Fin (k+1) → V)
    (hadj : ∀ i : Fin k, G.Adj (p i.castSucc) (p i.succ))
    (hclosed : p (Fin.last k) = p 0) :
    (∑ i : Fin k, if p i.castSucc = a ∧ p i.succ = b then (1 : ℕ) else 0) =
    (∑ i : Fin k, if p i.castSucc = b ∧ p i.succ = a then (1 : ℕ) else 0) :=
  closedPath_bridge_traversals_eq G a b
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ht.isAcyclic hab) k p hadj hclosed

/-- A tree edge traversed twice by a closed path is traversed once in each direction. -/
lemma closedTreePath_two_traversals (G : SimpleGraph V) (ht : G.IsTree)
    (a b : V) (hab : G.Adj a b) (k : ℕ) (p : Fin (k+1) → V)
    (hadj : ∀ i : Fin k, G.Adj (p i.castSucc) (p i.succ))
    (hclosed : p (Fin.last k) = p 0)
    (htwo : (∑ i : Fin k, if p i.castSucc = a ∧ p i.succ = b then (1 : ℕ) else 0) +
      (∑ i : Fin k, if p i.castSucc = b ∧ p i.succ = a then (1 : ℕ) else 0) = 2) :
    (∑ i : Fin k, if p i.castSucc = a ∧ p i.succ = b then (1 : ℕ) else 0) = 1 ∧
    (∑ i : Fin k, if p i.castSucc = b ∧ p i.succ = a then (1 : ℕ) else 0) = 1 := by
  have h := closedTreePath_traversals_eq G ht a b hab k p hadj hclosed
  omega

#print axioms closedTreePath_traversals_eq
#print axioms closedTreePath_two_traversals
end SpectralRadiusUpperTail
