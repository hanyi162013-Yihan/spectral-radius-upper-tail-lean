import SpectralRadiusUpperTail.MatrixSpectralOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace SpectralRadiusUpperTail
open scoped Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- A large Hermitian operator norm comes from one of its two spectral sides. -/
lemma matrix_norm_spectral_event {A : Matrix ι ι 𝕂} (hA : A.IsHermitian)
    {t : ℝ} (ht : t ≤ ‖A‖) :
    (∃ l ∈ spectrum ℝ A, t ≤ l) ∨ (∃ l ∈ spectrum ℝ (-A), t ≤ l) := by
  obtain ⟨l, hl, he⟩ := (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) A
    (show IsSelfAdjoint A from hA)).1
  change ‖l‖ = ‖A‖ at he
  by_cases hl0 : 0 ≤ l
  · left
    refine ⟨l, hl, ?_⟩
    rwa [← he, Real.norm_of_nonneg hl0] at ht
  · right
    refine ⟨-l, ?_, ?_⟩
    · rw [← spectrum.neg_eq]
      simpa only [Set.mem_neg, neg_neg] using hl
    · rwa [← he, Real.norm_of_nonpos (le_of_not_ge hl0)] at ht

#print axioms matrix_norm_spectral_event
end SpectralRadiusUpperTail
