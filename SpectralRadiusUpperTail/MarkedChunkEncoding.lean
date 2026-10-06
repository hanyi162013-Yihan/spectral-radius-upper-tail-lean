import SpectralRadiusUpperTail.MarkedChunkCount

namespace SpectralRadiusUpperTail
variable {A : Type*} {n : ℕ}

abbrev NonemptyChunks (A : Type*) (n : ℕ) :=
  {C : List (List A) // (∀ l ∈ C, l ≠ []) ∧ C.flatten.length = n}

def nonemptyChunkEncoding (p : NonemptyChunks A n) (i : Fin n) : A × Bool :=
  (markChunkEnds p.val).get ⟨i.val,by rw [markChunkEnds_length,p.property.2]; exact i.isLt⟩

lemma nonemptyChunkEncoding_injective : Function.Injective (@nonemptyChunkEncoding A n) := by
  intro p q hpq
  apply Subtype.ext
  apply markChunkEnds_injective p.property.1 q.property.1
  apply List.ext_getElem
  · rw [markChunkEnds_length,markChunkEnds_length,p.property.2,q.property.2]
  · intro i hi hj
    have hi' : i < n := by simpa only [markChunkEnds_length,p.property.2] using hi
    exact congrFun hpq ⟨i,hi'⟩

instance nonemptyChunks_finite [Finite A] : Finite (NonemptyChunks A n) :=
  Finite.of_injective nonemptyChunkEncoding nonemptyChunkEncoding_injective

#print axioms NonemptyChunks
#print axioms nonemptyChunkEncoding
#print axioms nonemptyChunkEncoding_injective
#print axioms nonemptyChunks_finite
end SpectralRadiusUpperTail
