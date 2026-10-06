import SpectralRadiusUpperTail.SchurPathConsEquiv

namespace SpectralRadiusUpperTail

/-- After fixing the first vertex, deleting it leaves exactly the
strict tails whose first vertex is larger. -/
noncomputable def increasingPathFixedStartEquiv (N l : ℕ) (i : Fin N) :
    {p : IncreasingBlockPath N (l+1) // p.val 0 = i} ≃
      {q : IncreasingBlockPath N l // i < q.val 0} where
  toFun p := ⟨⟨Fin.tail p.val.val, by
    intro a b hab
    exact p.val.property (by simpa using hab)⟩, by
    change i < p.val.val (Fin.succ 0)
    exact (p.property.symm).trans_lt (p.val.property (by simp))⟩
  invFun q := ⟨⟨Fin.cons i q.val.val,
    (Fin.strictMono_cons).2 ⟨fun j =>
      q.property.trans_le (q.val.property.monotone (Fin.zero_le j)),
      q.val.property⟩⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    change Fin.cons i (Fin.tail p.val.val) = p.val.val
    calc
      Fin.cons i (Fin.tail p.val.val) =
          Fin.cons (p.val.val 0) (Fin.tail p.val.val) :=
            congrArg (fun x : Fin N => Fin.cons x (Fin.tail p.val.val)) p.property.symm
      _ = p.val.val := Fin.cons_self_tail p.val.val
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

#print axioms increasingPathFixedStartEquiv
end SpectralRadiusUpperTail
