import SpectralRadiusUpperTail.SchurPathFixedStart
import SpectralRadiusUpperTail.SchurWaitingFirstEdge

namespace SpectralRadiusUpperTail

abbrev SchurFixedStartWaiting (N k l : ℕ) (i : Fin N) :=
  {p : IncreasingBlockPath N l // p.val 0 = i} × SchurWaitingTimes k l

/-- The first vertex is fixed, so only the first wait and a strict tail
remain in the recursive reindexing. -/
noncomputable def schurFixedStartWaitingFirstEdgeEquiv
    (N k l : ℕ) (hlk : l < k) (i : Fin N) :
    SchurFixedStartWaiting N k (l+1) i ≃
      Σ s : Fin (k-l),
        {q : IncreasingBlockPath N l // i < q.val 0} ×
          SchurWaitingTimes (k-s.val-1) l where
  toFun pm := by
    let pp := increasingPathFixedStartEquiv N l i pm.1
    let mm := schurWaitingFirstEdgeEquiv k l hlk pm.2
    exact ⟨mm.1, (pp, mm.2)⟩
  invFun v :=
    ⟨(increasingPathFixedStartEquiv N l i).symm v.2.1,
      (schurWaitingFirstEdgeEquiv k l hlk).symm ⟨v.1,v.2.2⟩⟩
  left_inv pm := by
    apply Prod.ext
    · exact (increasingPathFixedStartEquiv N l i).left_inv pm.1
    · exact (schurWaitingFirstEdgeEquiv k l hlk).left_inv pm.2
  right_inv v := by
    cases v with
    | mk s qt =>
      cases qt with
      | mk q t => rfl

#print axioms schurFixedStartWaitingFirstEdgeEquiv
end SpectralRadiusUpperTail
