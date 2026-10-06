import SpectralRadiusUpperTail.SchurPathFixedStart

namespace SpectralRadiusUpperTail

/-- A strict tail above `i` is classified by its first vertex. -/
noncomputable def schurStrictTailFirstVertexEquiv (N l : ℕ) (i : Fin N) :
    {q : IncreasingBlockPath N l // i < q.val 0} ≃
      Σ h : {h : Fin N // i < h},
        {q : IncreasingBlockPath N l // q.val 0 = h.val} where
  toFun q := ⟨⟨q.val.val 0, q.property⟩, ⟨q.val, rfl⟩⟩
  invFun v := ⟨v.2.val, by
    calc
      i < v.1.val := v.1.property
      _ = v.2.val.val 0 := v.2.property.symm⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv v := by
    cases v with
    | mk h q =>
      cases h with
      | mk h hi =>
        cases q with
        | mk q hq =>
          simp only at hq
          subst h
          rfl

#print axioms schurStrictTailFirstVertexEquiv
end SpectralRadiusUpperTail
