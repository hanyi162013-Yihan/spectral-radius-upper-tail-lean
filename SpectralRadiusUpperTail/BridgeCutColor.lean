import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace SpectralRadiusUpperTail
variable {V : Type*}

noncomputable def bridgeCutColor (G : SimpleGraph V) (a b x : V) : Bool := by
  classical
  exact decide ((G.deleteEdges {s(a,b)}).Reachable a x)

lemma bridgeCutColor_start (G : SimpleGraph V) (a b : V) : bridgeCutColor G a b a = true := by
  classical
  simp only [bridgeCutColor, decide_eq_true_eq]
  exact SimpleGraph.Reachable.refl _

lemma bridgeCutColor_end (G : SimpleGraph V) (a b : V) (h : G.IsBridge s(a,b)) :
    bridgeCutColor G a b b = false := by
  classical
  simp only [bridgeCutColor, decide_eq_false_iff_not]
  exact SimpleGraph.isBridge_iff.mp h

lemma bridgeCutColor_same_of_other_edge (G : SimpleGraph V) (a b u v : V)
    (h : G.Adj u v) (hne : s(u,v) ≠ s(a,b)) :
    bridgeCutColor G a b u = bridgeCutColor G a b v := by
  classical
  have hd : (G.deleteEdges {s(a,b)}).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨h,by simpa using hne⟩
  have he : (G.deleteEdges {s(a,b)}).Reachable a u ↔
      (G.deleteEdges {s(a,b)}).Reachable a v :=
    ⟨fun hu => hu.trans hd.reachable,fun hv => hv.trans hd.reachable.symm⟩
  simp only [bridgeCutColor, he]

#print axioms bridgeCutColor
#print axioms bridgeCutColor_start
#print axioms bridgeCutColor_end
#print axioms bridgeCutColor_same_of_other_edge
end SpectralRadiusUpperTail
