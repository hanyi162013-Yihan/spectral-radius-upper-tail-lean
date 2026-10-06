import SpectralRadiusUpperTail.ExteriorLogDetTest
import SpectralRadiusUpperTail.PhaseRotationLogDet

namespace SpectralRadiusUpperTail

lemma exists_uniform_realLogDet_test (r R ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ), 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℂ,
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ 3 → matrixTraceControl A r δ →
      ∀ b : ℝ, r ≤ b → b ≤ R → |normalizedExteriorLogDet A b-Real.log b| < ε := by
  obtain ⟨B, hB, hlo, hup⟩ := exists_large_log_normalization (max r R) 3 (ε/2) (by positivity)
  have hrB : r < B := (le_trans (le_max_left _ _) (le_max_left _ _)).trans_lt hB
  have hRB : R < B := (le_trans (le_max_right _ _) (le_max_left _ _)).trans_lt hB
  have h3B : 3 < B := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hB
  let δ := ε/(2*(B-r+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro n hn A hA ht b hrb hbR
  have hnorm := exteriorLogDet_normalization hn A B 3 (by norm_num) h3B hA
  have hfar : |normalizedExteriorLogDet A B-Real.log B| < ε/2 := by
    rw [abs_lt] at hlo hup ⊢
    constructor <;> linarith [hnorm.1, hnorm.2]
  have hprop := exteriorLogDet_propagation A r b B δ hr hrb (hbR.trans hRB.le) ht
  have he : δ*(2*(B-r+1)) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith

lemma exists_uniform_complexLogDet_test (r R ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ), 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℂ,
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ 3 → matrixTraceControl A r δ →
      ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → |normalizedComplexLogDet A z-Real.log ‖z‖| < ε := by
  obtain ⟨δ, hδ, ht⟩ := exists_uniform_realLogDet_test r R ε hr hε
  refine ⟨δ, hδ, ?_⟩
  intro n hn A hA htrace z hrz hzR
  have hz : 0 < ‖z‖ := hr.trans_le hrz
  let q := z/(‖z‖ : ℂ)
  have hq : ‖q‖ = 1 := by simp [q, norm_div, abs_of_pos hz, hz.ne']
  have he : q*(‖z‖ : ℂ) = z := div_mul_cancel₀ _ (by exact_mod_cast hz.ne')
  have hh := ht n hn (q⁻¹ • A) (by rw [phase_operator_norm A q hq]; exact hA)
    (matrixTraceControl_phase A q hq r δ htrace) ‖z‖ hrz hzR
  rwa [phase_normalizedLogDet A q hq, he] at hh

#print axioms exists_uniform_realLogDet_test
#print axioms exists_uniform_complexLogDet_test
end SpectralRadiusUpperTail
