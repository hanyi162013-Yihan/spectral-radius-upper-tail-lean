import SpectralRadiusUpperTail.PairedPatternStructure

namespace SpectralRadiusUpperTail
variable {k : ℕ}

/-- Coincident simple quotient paths have k+1 vertices and distinct endpoints. -/
lemma pairedPattern_simple_endpoints (hk : 0 < k)
    (r : Setoid (Fin (k+1) ⊕ Fin (k+1))) [DecidableRel r.r]
    (h0 : patternLeftVertex r 0 = patternRightVertex r 0)
    (ht : (fun a : Fin k => patternLeftVertex r a.succ) =
      (fun a : Fin k => patternRightVertex r a.succ))
    (hn : (patternLeftVertex r 0 :: List.ofFn (fun a : Fin k => patternLeftVertex r a.succ)).Nodup) :
    patternLeftVertex r = patternRightVertex r ∧
      Fintype.card (Quotient r) = k+1 ∧
      patternLeftVertex r (Fin.last k) ≠ patternLeftVertex r 0 := by
  have he : patternLeftVertex r = patternRightVertex r := by
    funext a
    exact Fin.cases h0 (fun b => congrFun ht b) a
  have hlist : List.ofFn (patternLeftVertex r) =
      patternLeftVertex r 0 :: List.ofFn (fun a : Fin k => patternLeftVertex r a.succ) :=
    List.ofFn_succ
  have hnodup : (List.ofFn (patternLeftVertex r)).Nodup := hlist.symm ▸ hn
  have hu : (List.ofFn (patternLeftVertex r)).toFinset = Finset.univ := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    have hc := pairedPattern_vertex_cover r x
    rw [← h0, ← ht, or_self, ← hlist] at hc
    exact hc
  have hcard : Fintype.card (Quotient r) = k+1 := by
    have h := List.toFinset_card_of_nodup hnodup
    rw [hu, Finset.card_univ, List.length_ofFn] at h
    exact h
  have hinj := List.nodup_ofFn.mp hnodup
  refine ⟨he,hcard,?_⟩
  intro h
  have hv := congrArg Fin.val (hinj h)
  simp only [Fin.val_last, Fin.val_zero] at hv
  omega

#print axioms pairedPattern_simple_endpoints
end SpectralRadiusUpperTail
