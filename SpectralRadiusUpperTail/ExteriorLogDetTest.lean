import SpectralRadiusUpperTail.ExteriorLogDetPropagation
import SpectralRadiusUpperTail.LogShiftAtInfinity

namespace SpectralRadiusUpperTail

lemma exists_exteriorLogDet_test (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ), 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℂ,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ ≤ 3 →
      matrixTraceControl A b δ → |normalizedExteriorLogDet A b-Real.log b| < ε := by
  obtain ⟨B, hB, hlo, hup⟩ := exists_large_log_normalization b 3 (ε/2) (by positivity)
  have hbB : b < B := (le_max_left _ _).trans_lt hB
  have h3B : 3 < B := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hB
  let δ := ε/(2*(B-b+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro n hn A hA ht
  have hnorm := exteriorLogDet_normalization hn A B 3 (by norm_num) h3B hA
  have hfar : |normalizedExteriorLogDet A B-Real.log B| < ε/2 := by
    rw [abs_lt] at hlo hup ⊢
    constructor <;> linarith [hnorm.1, hnorm.2]
  have hprop := exteriorLogDet_propagation A b b B δ hb le_rfl hbB.le ht
  have he : δ*(2*(B-b+1)) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith

#print axioms exists_exteriorLogDet_test
end SpectralRadiusUpperTail
