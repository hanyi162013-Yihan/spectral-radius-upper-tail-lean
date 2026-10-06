import SpectralRadiusUpperTail.OccurrenceFamily
import SpectralRadiusUpperTail.MatchingLocalRelation
import SpectralRadiusUpperTail.OccurrenceVertexTransport

namespace SpectralRadiusUpperTail

/-- Vertex-free reconstruction data for a fixed original sign word. A separate
arrangement certificate will determine the occurrence family economically. -/
structure OccurrenceKernelCode (L : ℕ) where
  family : OccurrenceFamily L
  matchings : ∀ i : Fin family.count,
    SignedNoncrossingMatching (fun j => (family.words i j).2)
  gluing : Finset (family.VertexSlot × family.VertexSlot)
  restoration : Finset (Fin (L+1) × Fin (L+1))

def OccurrenceKernelCode.decode {L : ℕ} (s : Fin L → Bool) (C : OccurrenceKernelCode L) :
    Setoid (Fin (L+1)) :=
  Relation.EqvGen.setoid (fun a b =>
    occurrencePullbackRelation s C.family.words
      (Relation.EqvGen (fun u w =>
        matchingLocalRelation (fun i => (C.matchings i).val.val) u w ∨ (u,w) ∈ C.gluing)) a b ∨
      (a,b) ∈ C.restoration)

lemma occurrenceKernelCode_eq_of_decode {L : ℕ} (s : Fin L → Bool)
    {R S : Setoid (Fin (L+1))} {C D : OccurrenceKernelCode L}
    (hR : C.decode s = R) (hS : D.decode s = S) (h : C = D) : R = S := by
  subst D
  exact hR.symm.trans hS

#print axioms OccurrenceKernelCode
#print axioms OccurrenceKernelCode.decode
#print axioms occurrenceKernelCode_eq_of_decode
end SpectralRadiusUpperTail
