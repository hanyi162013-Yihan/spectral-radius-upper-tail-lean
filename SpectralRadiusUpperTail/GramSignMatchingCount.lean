import SpectralRadiusUpperTail.GramSignBlockConstant
import SpectralRadiusUpperTail.SignedBlockMatchingCount

namespace SpectralRadiusUpperTail

lemma gramSignWord_length (m q : ℕ) : (gramSignWord m q).length = 2*q*m := by
  calc (gramSignWord m q).length = q*(m+m) := by simp [gramSignWord]
       _ = 2*q*m := by ring

/-- Finite indexing of the actual Gram sign list, always within its length. -/
def gramFiniteSign (m q : ℕ) (t : Fin (2*q*m)) : Bool :=
  (gramSignWord m q).getD t.val false

lemma gramFiniteSign_eq_getElem (m q : ℕ) (t : Fin (2*q*m)) :
    gramFiniteSign m q t = (gramSignWord m q)[t.val]'(by rw [gramSignWord_length]; exact t.isLt) := by
  exact List.getD_eq_getElem _ _ _

lemma gramFiniteSign_block_constant (m q : ℕ) (b : Fin (2*q)) (i j : Fin m) :
    gramFiniteSign m q (uniformBlockIndex b i) = gramFiniteSign m q (uniformBlockIndex b j) := by
  change (gramSignWord m q).getD (i.val+m*b.val) false =
    (gramSignWord m q).getD (j.val+m*b.val) false
  simpa only [Nat.add_comm] using gramSignWord_block_constant m q b.val i.val j.val
    b.isLt i.isLt j.isLt

/-- Matching count for the actual signed Gram word (+^m -^m)^q. This counts
pairings; an injective reconstruction is still required to count vertex patterns. -/
lemma gramSign_matching_count_le (m q : ℕ) :
    Nat.card (SignedNoncrossingMatching (gramFiniteSign m q)) ≤ (m+1)^(2*q) :=
  uniformSignBlock_matching_count_le (2*q) m (gramFiniteSign m q)
    (gramFiniteSign_block_constant m q)

#print axioms gramSignWord_length
#print axioms gramFiniteSign
#print axioms gramFiniteSign_eq_getElem
#print axioms gramFiniteSign_block_constant
#print axioms gramSign_matching_count_le
end SpectralRadiusUpperTail
