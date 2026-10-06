import SpectralRadiusUpperTail.DefectRouteSlotBudget
import SpectralRadiusUpperTail.RelativeGluingCode

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

/-- The extra vertex identifications have a code of length at most 8g,
whose alphabet consists of pairs of bounded primitive slots. -/
lemma DefectRouteCertificate.exists_gluing_code (c : DefectRouteCertificate s v) :
    ∃ d ≤ 8*(r+1-Fintype.card V), ∃ code : Fin d → c.TourPosition × c.TourPosition,
      ∀ x y, Relation.EqvGen
        (fun a b => c.localVertexMap a = c.localVertexMap b ∨ ∃ k, code k = (a,b)) x y ↔
        (c.localTourModel x.1).vertices x.2 = (c.localTourModel y.1).vertices y.2 := by
  classical
  obtain ⟨E,hE,hrec⟩ := c.exists_gluing_pairs
  obtain ⟨code,hcode⟩ := finset_pairs_code E
  refine ⟨E.card,hE,code,?_⟩
  have he : (fun a b => c.localVertexMap a = c.localVertexMap b ∨ ∃ k, code k = (a,b)) =
      (fun a b => c.localVertexMap a = c.localVertexMap b ∨ (a,b) ∈ E) := by
    funext a b
    exact propext (or_congr Iff.rfl (hcode a b))
  simpa only [he] using hrec

/-- For a fixed local relation and code length, gluing has polynomial cost
in the original word length. This counts relations, not arbitrary vertex labels. -/
lemma DefectRouteCertificate.gluing_pattern_count (c : DefectRouteCertificate s v)
    (Rlocal : c.TourPosition → c.TourPosition → Prop) (d : ℕ) :
    Nat.card {R : Setoid c.TourPosition // ∃ code : Fin d → c.TourPosition × c.TourPosition,
      ∀ x y, R x y ↔ Relation.EqvGen
        (fun a b => Rlocal a b ∨ ∃ k, code k = (a,b)) x y} ≤ (4*r)^(2*d) := by
  classical
  exact (relative_gluing_pattern_count Rlocal d).trans
    (Nat.pow_le_pow_left (by simpa only [Nat.card_eq_fintype_card] using c.tourPosition_card_le) _)

#print axioms DefectRouteCertificate.exists_gluing_code
#print axioms DefectRouteCertificate.gluing_pattern_count
end SpectralRadiusUpperTail
