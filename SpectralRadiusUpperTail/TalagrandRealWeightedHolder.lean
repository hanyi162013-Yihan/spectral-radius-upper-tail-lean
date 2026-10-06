import SpectralRadiusUpperTail.TalagrandWeightedHolder
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- Real-valued weighted Hölder for bounded or otherwise integrable
nonnegative functions. Endpoint weights are included. -/
theorem integral_geometric_mean_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hprod : Integrable (fun x => (f x)^θ*(g x)^(1-θ)) μ) :
    (∫ x, (f x)^θ*(g x)^(1-θ) ∂μ) ≤
      (∫ x, f x ∂μ)^θ*(∫ x, g x ∂μ)^(1-θ) := by
  have hθc : 0 ≤ 1-θ := by linarith
  have hF : AEMeasurable (fun x => ENNReal.ofReal (f x)) μ :=
    (ENNReal.measurable_ofReal.comp hf).aemeasurable
  have hG : AEMeasurable (fun x => ENNReal.ofReal (g x)) μ :=
    (ENNReal.measurable_ofReal.comp hg).aemeasurable
  have hlin := lintegral_geometric_mean_le μ
    (fun x => ENNReal.ofReal (f x))
    (fun x => ENNReal.ofReal (g x)) hF hG θ hθ hθ1
  have hprod0 : 0 ≤ᵐ[μ] fun x => (f x)^θ*(g x)^(1-θ) :=
    Filter.Eventually.of_forall (fun x => mul_nonneg
      (Real.rpow_nonneg (hf0 x) _) (Real.rpow_nonneg (hg0 x) _))
  have hF0 : 0 ≤ ∫ x, f x ∂μ := integral_nonneg (fun x => hf0 x)
  have hG0 : 0 ≤ ∫ x, g x ∂μ := integral_nonneg (fun x => hg0 x)
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg hF0 _) (Real.rpow_nonneg hG0 _))).mp
  rw [ofReal_integral_eq_lintegral_ofReal hprod hprod0,
    ENNReal.ofReal_mul (Real.rpow_nonneg hF0 _),
    ← ENNReal.ofReal_rpow_of_nonneg hF0 hθ,
    ← ENNReal.ofReal_rpow_of_nonneg hG0 hθc,
    ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
    ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)]
  calc
    (∫⁻ x, ENNReal.ofReal (f x ^ θ * g x ^ (1 - θ)) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (f x) ^ θ *
          ENNReal.ofReal (g x) ^ (1-θ) ∂μ := by
            apply lintegral_congr
            intro x
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) _),
              ← ENNReal.ofReal_rpow_of_nonneg (hf0 x) hθ,
              ← ENNReal.ofReal_rpow_of_nonneg (hg0 x) hθc]
    _ ≤ _ := hlin

#print axioms integral_geometric_mean_le
end SpectralRadiusUpperTail
