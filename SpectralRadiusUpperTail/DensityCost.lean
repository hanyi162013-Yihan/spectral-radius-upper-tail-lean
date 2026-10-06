import SpectralRadiusUpperTail.DensityCoupling
import SpectralRadiusUpperTail.CouplingCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

lemma density_residual_cost (μ : Measure α) (k f : α → ℝ≥0∞)
    (hk : Measurable k) (hf : Measurable f) :
    (∫⁻ x, f x ∂positiveDensityResidual μ k) +
        (∫⁻ x, f x ∂negativeDensityResidual μ k) =
      ∫⁻ x, ((k x - min (k x) 1) + (1 - min (k x) 1)) * f x ∂μ := by
  have hp : Measurable (fun x => k x - min (k x) 1) := hk.sub (hk.min measurable_const)
  have hq : Measurable (fun x => 1 - min (k x) 1) :=
    measurable_const.sub (hk.min measurable_const)
  have hpf : Measurable (fun x => (k x - min (k x) 1) * f x) := hp.mul hf
  unfold positiveDensityResidual negativeDensityResidual
  rw [lintegral_withDensity_eq_lintegral_mul μ hp hf,
    lintegral_withDensity_eq_lintegral_mul μ hq hf]
  simp only [Pi.mul_apply]
  rw [← lintegral_add_left hpf]
  congr 1
  funext x
  simp only [Pi.add_apply, Pi.mul_apply, add_mul]

theorem densityCoupling_cost_le (μ : Measure α) [IsProbabilityMeasure μ]
    (k f : α → ℝ≥0∞) (c : α × α → ℝ≥0∞)
    (hk : Measurable k) (hf : Measurable f) (hc : Measurable c)
    (hnorm : (∫⁻ x, k x ∂μ) = 1)
    (hdiag : ∀ x, c (x,x) = 0) (hcost : ∀ z, c z ≤ 2 * (f z.1 + f z.2)) :
    (∫⁻ z, c z ∂densityCoupling μ k) ≤
      2 * ∫⁻ x, ((k x - min (k x) 1) + (1 - min (k x) 1)) * f x ∂μ := by
  have : IsProbabilityMeasure (μ.withDensity k) := normalizedDensity_probability μ k hnorm
  have : IsFiniteMeasure (positiveDensityResidual μ k) :=
    isFiniteMeasure_of_le (μ.withDensity k) (positiveDensityResidual_le_tilt μ k)
  have h := commonPartCoupling_cost_le (commonDensityPart μ k)
    (positiveDensityResidual μ k) (negativeDensityResidual μ k)
    (density_residual_masses_eq μ k hk hnorm) c f hc hf hdiag hcost
  rw [density_residual_cost μ k f hk hf] at h
  exact h

lemma ofReal_density_residual (k : ℝ) (hk : 0 ≤ k) :
    (ENNReal.ofReal k - min (ENNReal.ofReal k) 1) +
        (1 - min (ENNReal.ofReal k) 1) = ENNReal.ofReal |k-1| := by
  by_cases h : k ≤ 1
  · have hE : ENNReal.ofReal k ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal h
    simp [min_eq_left hE, abs_of_nonpos (sub_nonpos.mpr h), neg_sub,
      ENNReal.ofReal_sub 1 hk]
  · have h' : 1 ≤ k := le_of_lt (lt_of_not_ge h)
    have hE : 1 ≤ ENNReal.ofReal k := by simpa using ENNReal.ofReal_le_ofReal h'
    simp [min_eq_right hE, abs_of_nonneg (sub_nonneg.mpr h'),
      ENNReal.ofReal_sub k (by norm_num : (0:ℝ) ≤ 1)]

variable {E : Type*} [NormedAddCommGroup E]

lemma norm_sub_sq_le_twice (x y : E) :
    ‖x-y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := norm_sub_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hd := norm_nonneg (x-y)
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The uncentered second moment under the actual normalized density coupling.
It is stated with nonnegative integrals, so no integrability is silently assumed. -/
theorem densityCoupling_secondMoment_le (μ : Measure E) [IsProbabilityMeasure μ]
    (k : E → ℝ) (hk : Measurable k) (hk_nonneg : ∀ x, 0 ≤ k x)
    (hnorm : (∫⁻ x, ENNReal.ofReal (k x) ∂μ) = 1) :
    (∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ 2)
        ∂densityCoupling μ (fun x => ENNReal.ofReal (k x))) ≤
      2 * ∫⁻ x, ENNReal.ofReal (|k x-1| * ‖x‖ ^ 2) ∂μ := by
  have hkE : Measurable (fun x => ENNReal.ofReal (k x)) := hk.ennreal_ofReal
  have hf : Measurable (fun x : E => ENNReal.ofReal (‖x‖ ^ 2)) :=
    (continuous_norm.pow 2).measurable.ennreal_ofReal
  have hc : Measurable (fun z : E × E => ENNReal.ofReal (‖z.1-z.2‖ ^ 2)) :=
    ((continuous_fst.sub continuous_snd).norm.pow 2).measurable.ennreal_ofReal
  have h := densityCoupling_cost_le μ (fun x => ENNReal.ofReal (k x))
    (fun x => ENNReal.ofReal (‖x‖ ^ 2))
    (fun z : E × E => ENNReal.ofReal (‖z.1-z.2‖ ^ 2)) hkE hf hc hnorm
    (by intro x; simp) (by
      intro z
      have hz := ENNReal.ofReal_le_ofReal (norm_sub_sq_le_twice z.1 z.2)
      simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ENNReal.ofReal_ofNat] using hz)
  simpa only [ofReal_density_residual _ (hk_nonneg _),
    ← ENNReal.ofReal_mul (abs_nonneg _)] using h

#print axioms densityCoupling_secondMoment_le
end SpectralRadiusUpperTail
