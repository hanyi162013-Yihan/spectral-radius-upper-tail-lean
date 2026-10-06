import SpectralRadiusUpperTail.IndexedMatchingCount
import SpectralRadiusUpperTail.GramBlockLabels
import SpectralRadiusUpperTail.OccurrenceMatchingCard

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {m q : ℕ}
variable {v : Fin (2*(q*m)+1) → V}

lemma DefectRouteCertificate.gram_indexedMatching_count_le
    (c : DefectRouteCertificate (gramTreeSign m q) v) (hq : 1 ≤ q) :
    c.occurrenceFamily.matchingCard ≤
      (m+1)^(2*q) * (2*(q*m)+1)^(8*(q*m+1-Fintype.card V)) := by
  have hm : m ≤ 2*(q*m) := by
    have hmul := Nat.mul_le_mul_right m hq
    omega
  exact c.indexedMatching_count_le (gramTreeBlock m q) (2*q) m
    (gramTreeBlock_run_budget m q) (fun b => (gramTreeBlock_count m q b).le)
    (gramTreeBlock_same_sign m q) hm

#print axioms DefectRouteCertificate.gram_indexedMatching_count_le
end SpectralRadiusUpperTail
