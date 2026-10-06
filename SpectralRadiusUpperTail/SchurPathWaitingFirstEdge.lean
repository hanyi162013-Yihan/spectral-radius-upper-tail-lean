import SpectralRadiusUpperTail.SchurPathConsEquiv
import SpectralRadiusUpperTail.SchurWaitingFirstEdge
import SpectralRadiusUpperTail.SchurStrictPathTerm

namespace SpectralRadiusUpperTail

abbrev SchurPathWaiting (N k l : ℕ) :=
  IncreasingBlockPath N l × SchurWaitingTimes k l

/-- A strict path together with all its diagonal waits decomposes into
the first vertex, first wait, and a shorter strict path with its waits. -/
noncomputable def schurPathWaitingFirstEdgeEquiv (N k l : ℕ) (hlk : l < k) :
    SchurPathWaiting N k (l+1) ≃
      Σ i : Fin N, Σ s : Fin (k-l),
        {q : IncreasingBlockPath N l // i < q.val 0} ×
          SchurWaitingTimes (k-s.val-1) l where
  toFun pm := by
    let pp := increasingPathConsEquiv N l pm.1
    let mm := schurWaitingFirstEdgeEquiv k l hlk pm.2
    exact ⟨pp.val.1, mm.1, ⟨⟨pp.val.2, pp.property⟩, mm.2⟩⟩
  invFun v :=
    ⟨(increasingPathConsEquiv N l).symm
      ⟨(v.1, v.2.2.1.val), v.2.2.1.property⟩,
     (schurWaitingFirstEdgeEquiv k l hlk).symm ⟨v.2.1, v.2.2.2⟩⟩
  left_inv pm := by
    apply Prod.ext
    · change (increasingPathConsEquiv N l).symm
          ((increasingPathConsEquiv N l) pm.1) = pm.1
      exact (increasingPathConsEquiv N l).left_inv pm.1
    · change (schurWaitingFirstEdgeEquiv k l hlk).symm
          ((schurWaitingFirstEdgeEquiv k l hlk) pm.2) = pm.2
      exact (schurWaitingFirstEdgeEquiv k l hlk).left_inv pm.2
  right_inv v := by
    cases v with
    | mk i v =>
      cases v with
      | mk s qt =>
        cases qt with
        | mk q t => rfl

#print axioms schurPathWaitingFirstEdgeEquiv
end SpectralRadiusUpperTail
