import SpectralRadiusUpperTail.OccurrenceFamily
import SpectralRadiusUpperTail.DefectArrangementShape

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma OccurrenceFamily.vertexSlot_card {L : ℕ} (W : OccurrenceFamily L) :
    Fintype.card W.VertexSlot = W.rows.flatten.length + W.count := by
  simp only [OccurrenceFamily.VertexSlot,Fintype.card_sigma,Fintype.card_fin,
    OccurrenceFamily.rows,occurrenceWordRows,List.length_flatten,List.map_ofFn,
    Function.comp_def,List.length_ofFn,List.sum_ofFn,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.occurrenceFamily_total_length (c : DefectRouteCertificate s v) :
    c.occurrenceFamily.rows.flatten.length = c.survivingPositions.length := by
  have h := c.indexedTours_positions_perm.length_eq
  rw [c.occurrenceFamily_rows]
  simpa only [List.length_flatMap,List.length_map,List.length_flatten,List.map_map,
    Function.comp_def] using h

lemma DefectRouteCertificate.occurrenceFamily_slot_budget (c : DefectRouteCertificate s v) :
    Fintype.card c.occurrenceFamily.VertexSlot ≤ 4*r := by
  rw [OccurrenceFamily.vertexSlot_card,c.occurrenceFamily_total_length]
  have ht : c.occurrenceFamily.count ≤ 2*r := by
    change c.indexedTours.length ≤ 2*r
    simp only [DefectRouteCertificate.indexedTours,List.length_map]
    exact c.tour_budget.trans c.segment_count_le_length
  have hl := c.survivingPositions_length_le
  omega

#print axioms OccurrenceFamily.vertexSlot_card
#print axioms DefectRouteCertificate.occurrenceFamily_total_length
#print axioms DefectRouteCertificate.occurrenceFamily_slot_budget
end SpectralRadiusUpperTail
