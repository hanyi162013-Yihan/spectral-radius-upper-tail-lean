import SpectralRadiusUpperTail.AppendNoncrossingMatching

namespace SpectralRadiusUpperTail
variable {n m : ℕ} {s : Fin n → Bool} {t : Fin m → Bool}

/-- Concatenating tours preserves their signs and noncrossing matchings. -/
def appendSignedMatching (f : SignedNoncrossingMatching s) (g : SignedNoncrossingMatching t) :
    SignedNoncrossingMatching (Fin.addCases s t) := by
  refine ⟨appendNoncrossingMatching f.val g.val,?_⟩
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [appendNoncrossingMatching,appendMatchingFn_left,Fin.addCases_left] using f.property j
  · simpa only [appendNoncrossingMatching,appendMatchingFn_right,Fin.addCases_right] using g.property j

lemma appendSignedMatching_injective : Function.Injective
    (fun p : SignedNoncrossingMatching s × SignedNoncrossingMatching t =>
      appendSignedMatching p.1 p.2) := by
  intro p q h
  have hf (i : Fin n) : p.1.val.val i = q.1.val.val i := by
    have hi := congrArg (fun f : SignedNoncrossingMatching (Fin.addCases s t) =>
      f.val.val (i.castAdd m)) h
    simpa only [appendSignedMatching,appendNoncrossingMatching,appendMatchingFn_left,
      Fin.castAdd_inj] using hi
  have hg (i : Fin m) : p.2.val.val i = q.2.val.val i := by
    have hi := congrArg (fun f : SignedNoncrossingMatching (Fin.addCases s t) =>
      f.val.val (Fin.natAdd n i)) h
    simpa only [appendSignedMatching,appendNoncrossingMatching,appendMatchingFn_right,
      Fin.natAdd_inj] using hi
  exact Prod.ext (Subtype.ext (Subtype.ext (funext hf)))
    (Subtype.ext (Subtype.ext (funext hg)))

/-- A product of local matching counts can be bounded by the matching count
of the concatenated word. Shared vertices are handled separately by gluing. -/
lemma appendSignedMatching_count_le (s : Fin n → Bool) (t : Fin m → Bool) :
    Nat.card (SignedNoncrossingMatching s) * Nat.card (SignedNoncrossingMatching t) ≤
      Nat.card (SignedNoncrossingMatching (Fin.addCases s t)) := by
  classical
  letI : Fintype (SignedNoncrossingMatching s) := Fintype.ofFinite _
  letI : Fintype (SignedNoncrossingMatching t) := Fintype.ofFinite _
  letI : Fintype (SignedNoncrossingMatching (Fin.addCases s t)) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod] using
    Fintype.card_le_of_injective _ (@appendSignedMatching_injective n m s t)

#print axioms appendSignedMatching
#print axioms appendSignedMatching_injective
#print axioms appendSignedMatching_count_le
end SpectralRadiusUpperTail
