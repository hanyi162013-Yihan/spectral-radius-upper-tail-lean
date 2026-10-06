import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
variable {α σ : Type*} [BEq σ]

lemma list_count_le_flatMap_of_mem (words : α → List σ) (L : List α)
    (a : α) (ha : a ∈ L) (j : σ) : (words a).count j ≤ (L.flatMap words).count j := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    rw [List.flatMap_cons,List.count_append]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have hh := ih ha
      omega

#print axioms list_count_le_flatMap_of_mem
end SpectralRadiusUpperTail
