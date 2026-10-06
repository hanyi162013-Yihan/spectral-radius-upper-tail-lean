import SpectralRadiusUpperTail.TreeCutSeparation

namespace SpectralRadiusUpperTail
variable {V : Type*}

lemma tree_bridgeCut_separates_both (G : SimpleGraph V) (ht : G.IsTree)
    (x y : V) (hxy : x ≠ y) :
    ∃ z, G.Adj x z ∧
      bridgeCutColor G x z x ≠ bridgeCutColor G x z y ∧
      bridgeCutColor G z x x ≠ bridgeCutColor G z x y := by
  classical
  obtain ⟨p,hp,_⟩ := ht.existsUnique_path x y
  cases p with
  | nil => exact False.elim (hxy rfl)
  | @cons x z y hadj q =>
    have hn : s(x,z) ∉ q.edges := (List.nodup_cons.mp hp.edges_nodup).1
    have hzy : (G.deleteEdges {s(x,z)}).Reachable z y :=
      SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨q,hn⟩
    have hb : G.IsBridge s(x,z) :=
      SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ht.isAcyclic hadj
    have hny : ¬ (G.deleteEdges {s(x,z)}).Reachable x y := by
      intro h
      exact SimpleGraph.isBridge_iff.mp hb (h.trans hzy.symm)
    have hfalse : bridgeCutColor G x z y = false := by
      simpa only [bridgeCutColor, decide_eq_false_iff_not] using hny
    have hb' : G.IsBridge s(z,x) := by simpa only [Sym2.eq_swap] using hb
    have htrue : bridgeCutColor G z x y = true := by
      simp only [bridgeCutColor, decide_eq_true_eq]
      simpa only [Sym2.eq_swap] using hzy
    refine ⟨z,hadj,?_,?_⟩
    · rw [bridgeCutColor_start,hfalse]
      decide
    · rw [bridgeCutColor_end G z x hb',htrue]
      decide

#print axioms tree_bridgeCut_separates_both
end SpectralRadiusUpperTail
