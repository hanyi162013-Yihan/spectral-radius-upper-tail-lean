import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A]

/-- A Banach-algebra exponential is bounded by the real exponential
of its norm; the proof compares the actual convergent power series. -/
lemma algebra_exp_norm_le (a : A) : ‖NormedSpace.exp a‖ ≤ Real.exp ‖a‖ := by
  have hs := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) a
  have hr := NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖a‖
  calc
    _ = ‖∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • a^n‖ := by
      rw [NormedSpace.exp_eq_tsum ℝ]
    _ ≤ ∑' n : ℕ, ‖((n.factorial : ℝ)⁻¹) • a^n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • ‖a‖^n := by
      apply Summable.tsum_le_tsum _ hs hr
      intro n
      rw [norm_smul, Real.norm_of_nonneg (by positivity), smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (norm_pow_le a n) (by positivity)
    _ = Real.exp ‖a‖ := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]

theorem algebra_exp_integrable_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {F : Ω → A}
    (hF : AEStronglyMeasurable F μ) (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) :
    Integrable (fun x => NormedSpace.exp (F x)) μ := by
  have hc : Continuous (NormedSpace.exp : A → A) :=
    continuous_iff_continuousAt.mpr fun a =>
      (NormedSpace.exp_analytic (𝕂 := ℝ) a).continuousAt
  apply Integrable.of_bound (hc.comp_aestronglyMeasurable hF)
    (Real.exp C)
  filter_upwards [hbound] with x hx
  exact (algebra_exp_norm_le (F x)).trans (Real.exp_le_exp.mpr hx)

#print axioms algebra_exp_norm_le
#print axioms algebra_exp_integrable_of_bound
end SpectralRadiusUpperTail
