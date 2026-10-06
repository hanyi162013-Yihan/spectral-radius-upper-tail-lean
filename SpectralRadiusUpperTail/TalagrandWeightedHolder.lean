import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- The weighted geometric-mean form of Hölder's inequality, including
the endpoint weights needed by the Talagrand fiber induction. -/
theorem lintegral_geometric_mean_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ≥0∞) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (∫⁻ x, f x ^ θ * g x ^ (1-θ) ∂μ) ≤
      (∫⁻ x, f x ∂μ) ^ θ * (∫⁻ x, g x ∂μ) ^ (1-θ) := by
  by_cases hzero : θ = 0
  · subst θ
    simp
  by_cases hone : θ = 1
  · subst θ
    simp
  have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
  have hθlt : θ < 1 := lt_of_le_of_ne hθ1 hone
  have hcomppos : 0 < 1-θ := by linarith
  have hconj : (1/θ).HolderConjugate (1/(1-θ)) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · apply (one_lt_div hθpos).mpr
      linarith
    · field_simp
      ring
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    (hf.pow_const θ) (hg.pow_const (1-θ))
  convert hh using 1
  · rfl
  · simp [← ENNReal.rpow_mul, hθpos.ne', hcomppos.ne']

#print axioms lintegral_geometric_mean_le
end SpectralRadiusUpperTail
