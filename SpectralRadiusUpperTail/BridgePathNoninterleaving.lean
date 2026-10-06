import SpectralRadiusUpperTail.BridgeCutCrossing
import SpectralRadiusUpperTail.PathIntervalConstancy

namespace SpectralRadiusUpperTail
variable {V : Type*}

lemma bridgeCutColor_ne_of_edge_eq (G : SimpleGraph V) (a b u v : V)
    (hb : G.IsBridge s(a,b)) (he : s(u,v) = s(a,b)) :
    bridgeCutColor G a b u ≠ bridgeCutColor G a b v := by
  have ha := bridgeCutColor_start G a b
  have hz := bridgeCutColor_end G a b hb
  rcases Sym2.eq_iff.mp he with h | h
  · rw [h.1, h.2, ha, hz]
    decide
  · rw [h.1, h.2, ha, hz]
    decide

/-- Two occurrences of a bridge cannot interleave with two occurrences of another
edge when the bridge has no further occurrence in the intervening segment. -/
lemma bridgePath_no_interleaving (G : SimpleGraph V) (a b : V)
    (hb : G.IsBridge s(a,b)) (p : ℕ → V) (i k j l : ℕ)
    (hik : i < k) (hkj : k < j) (hjl : j < l)
    (hadj : ∀ t, t ≤ l → G.Adj (p t) (p (t+1)))
    (hj : s(p j,p (j+1)) = s(a,b))
    (hother : ∀ t, i < t → t ≤ l → t ≠ j → s(p t,p (t+1)) ≠ s(a,b))
    (hpair : s(p k,p (k+1)) = s(p l,p (l+1))) : False := by
  let c : ℕ → Bool := fun t => bridgeCutColor G a b (p t)
  have hconst (u v : ℕ) (huv : u ≤ v)
      (hu : i < u) (hv : v ≤ l+1)
      (hjout : j < u ∨ v ≤ j) : c v = c u := by
    apply path_constant_on_interval c u v huv
    intro t hut htv
    apply Eq.symm
    apply bridgeCutColor_same_of_other_edge G a b _ _ (hadj t (by omega))
    apply hother t (by omega) (by omega)
    omega
  have hkjc : c j = c k := hconst k j (by omega) hik (by omega) (Or.inr le_rfl)
  have hjlc : c l = c (j+1) := hconst (j+1) l (by omega) (by omega)
    (by omega) (Or.inl (by omega))
  have hkc : c k = c (k+1) :=
    bridgeCutColor_same_of_other_edge G a b _ _ (hadj k (by omega))
      (hother k hik (by omega) (by omega))
  have hklc : c k = c l := by
    rcases Sym2.eq_iff.mp hpair with h | h
    · exact congrArg (bridgeCutColor G a b) h.1
    · have hh : c (k+1) = c l := congrArg (bridgeCutColor G a b) h.2
      exact hkc.trans hh
  have hne : c j ≠ c (j+1) := bridgeCutColor_ne_of_edge_eq G a b _ _ hb hj
  exact hne (hkjc.trans (hklc.trans hjlc))

#print axioms bridgeCutColor_ne_of_edge_eq
#print axioms bridgePath_no_interleaving
end SpectralRadiusUpperTail
