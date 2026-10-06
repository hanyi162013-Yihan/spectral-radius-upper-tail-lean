import SpectralRadiusUpperTail.BridgeCutColor
import SpectralRadiusUpperTail.ClosedPathCutBalance

namespace SpectralRadiusUpperTail
variable {V : Type*}

lemma bridgeCutColor_crossing_iff (G : SimpleGraph V) (a b u v : V)
    (hb : G.IsBridge s(a,b)) (huv : G.Adj u v) :
    (bridgeCutColor G a b u = true ∧ bridgeCutColor G a b v = false) ↔
      u = a ∧ v = b := by
  constructor
  · intro hc
    have he : s(u,v) = s(a,b) := by
      by_contra hn
      have hs := bridgeCutColor_same_of_other_edge G a b u v huv hn
      rw [hc.1, hc.2] at hs
      cases hs
    rcases Sym2.eq_iff.mp he with h | h
    · exact h
    · have hn := bridgeCutColor_end G a b hb
      have hp : bridgeCutColor G a b b = true := by simpa only [h.1] using hc.1
      rw [hp] at hn
      cases hn
  · rintro ⟨hu, hv⟩
    rw [hu, hv]
    exact ⟨bridgeCutColor_start G a b, bridgeCutColor_end G a b hb⟩

/-- Every closed vertex path traverses a bridge equally often in both directions. -/
lemma closedPath_bridge_traversals_eq [DecidableEq V] (G : SimpleGraph V) (a b : V)
    (hb : G.IsBridge s(a,b)) (k : ℕ) (p : Fin (k+1) → V)
    (hadj : ∀ i : Fin k, G.Adj (p i.castSucc) (p i.succ))
    (hclosed : p (Fin.last k) = p 0) :
    (∑ i : Fin k, if p i.castSucc = a ∧ p i.succ = b then (1 : ℕ) else 0) =
    (∑ i : Fin k, if p i.castSucc = b ∧ p i.succ = a then (1 : ℕ) else 0) := by
  classical
  have h := closedPath_cut_crossings_eq k (fun i => bridgeCutColor G a b (p i))
    (congrArg (bridgeCutColor G a b) hclosed)
  have hf (i : Fin k) :
      (bridgeCutColor G a b (p i.castSucc) = true ∧
       bridgeCutColor G a b (p i.succ) = false) ↔
      p i.castSucc = a ∧ p i.succ = b :=
    bridgeCutColor_crossing_iff G a b _ _ hb (hadj i)
  have hr (i : Fin k) :
      (bridgeCutColor G a b (p i.castSucc) = false ∧
       bridgeCutColor G a b (p i.succ) = true) ↔
      p i.castSucc = b ∧ p i.succ = a := by
    rw [and_comm, bridgeCutColor_crossing_iff G a b _ _ hb (hadj i).symm, and_comm]
  simp only [hf, hr] at h
  exact h.symm

#print axioms bridgeCutColor_crossing_iff
#print axioms closedPath_bridge_traversals_eq
end SpectralRadiusUpperTail
