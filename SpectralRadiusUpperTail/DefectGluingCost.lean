import SpectralRadiusUpperTail.DefectRouteGluingCode
import SpectralRadiusUpperTail.BoundedGluingCount
import SpectralRadiusUpperTail.RetainedPositionExtension

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

/-- Total shared-vertex cost over all allowed gluing lengths, conditional on
the local tour relation. It is polynomial in word length with exponent O(g). -/
lemma DefectRouteCertificate.bounded_gluing_cost (c : DefectRouteCertificate s v)
    (Rlocal : c.TourPosition → c.TourPosition → Prop) :
    Nat.card {R : Setoid c.TourPosition // ∃ d ≤ 8*(r+1-Fintype.card V),
      ∃ code : Fin d → c.TourPosition × c.TourPosition,
      ∀ x y, R x y ↔ Relation.EqvGen
        (fun a b => Rlocal a b ∨ ∃ k, code k = (a,b)) x y} ≤
      (8*(r+1-Fintype.card V)+1)*(max 1 (4*r))^(16*(r+1-Fintype.card V)) := by
  classical
  have hc : Fintype.card c.TourPosition ≤ 4*r := by
    simpa only [Nat.card_eq_fintype_card] using c.tourPosition_card_le
  have h := bounded_gluing_pattern_count Rlocal (8*(r+1-Fintype.card V))
  have hp := Nat.pow_le_pow_left (max_le_max_left 1 hc) (2*(8*(r+1-Fintype.card V)))
  have he : 2*(8*(r+1-Fintype.card V)) = 16*(r+1-Fintype.card V) := by omega
  rw [he] at h hp
  exact h.trans (Nat.mul_le_mul_left _ hp)

/-- Conditional restoration cost on original chronological positions.
The retained relation and its transport are inputs, not counted by this lemma. -/
lemma original_restoration_pattern_cost (Rlocal : Fin (2*r+1) → Fin (2*r+1) → Prop)
    (g : ℕ) :
    Nat.card {R : Setoid (Fin (2*r+1)) // ∃ d ≤ 8*g+1,
      ∃ code : Fin d → Fin (2*r+1) × Fin (2*r+1),
      ∀ x y, R x y ↔ Relation.EqvGen
        (fun a b => Rlocal a b ∨ ∃ k, code k = (a,b)) x y} ≤
      (8*g+2)*(2*r+1)^(16*g+2) := by
  have h := bounded_gluing_pattern_count Rlocal (8*g+1)
  have he : 2*(8*g+1) = 16*g+2 := by omega
  simpa only [Fintype.card_fin, max_eq_right (by omega : 1 ≤ 2*r+1), he,
    Nat.add_assoc] using h

#print axioms DefectRouteCertificate.bounded_gluing_cost
#print axioms original_restoration_pattern_cost
end SpectralRadiusUpperTail
