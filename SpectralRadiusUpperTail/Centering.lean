import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)

theorem integral_centered_eq_zero (hX : Integrable X μ) :
    (∫ ω, X ω - ∫ z, X z ∂μ ∂μ) = 0 := by
  rw [integral_sub hX (integrable_const _)]
  simp

/-- Centering removes exactly the squared norm of the actual Bochner mean.
Both first and second moment integrability are explicit hypotheses. -/
theorem integral_centered_norm_sq (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) μ) :
    (∫ ω, ‖X ω - ∫ z, X z ∂μ‖ ^ 2 ∂μ) =
      (∫ ω, ‖X ω‖ ^ 2 ∂μ) - ‖∫ ω, X ω ∂μ‖ ^ 2 := by
  let m := ∫ ω, X ω ∂μ
  have hi : Integrable (fun ω => 2 * inner ℝ m (X ω)) μ :=
    (hX.const_inner m).const_mul 2
  have hd : Integrable (fun ω => ‖X ω‖ ^ 2 - 2 * inner ℝ m (X ω)) μ := hX2.sub hi
  have hc : Integrable (fun _ω : Ω => ‖m‖ ^ 2) μ := integrable_const _
  have hfun : (fun ω => ‖X ω - m‖ ^ 2) =
      (fun ω => ‖X ω‖ ^ 2 - 2 * inner ℝ m (X ω) + ‖m‖ ^ 2) := by
    funext ω
    rw [norm_sub_sq_real, real_inner_comm (X ω) m]
  change (∫ ω, ‖X ω - m‖ ^ 2 ∂μ) = (∫ ω, ‖X ω‖ ^ 2 ∂μ) - ‖m‖ ^ 2
  rw [hfun, integral_add hd hc, integral_sub hX2 hi,
    integral_const_mul, integral_inner hX]
  change (∫ ω, ‖X ω‖ ^ 2 ∂μ) - 2 * inner ℝ m m + (∫ _ω, ‖m‖ ^ 2 ∂μ) = _
  rw [real_inner_self_eq_norm_sq]
  simp only [integral_const, probReal_univ, one_smul]
  ring

theorem integral_centered_norm_sq_le (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) μ) :
    (∫ ω, ‖X ω - ∫ z, X z ∂μ‖ ^ 2 ∂μ) ≤ ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
  rw [integral_centered_norm_sq μ X hX hX2]
  exact sub_le_self _ (sq_nonneg _)

#print axioms integral_centered_norm_sq
end SpectralRadiusUpperTail
