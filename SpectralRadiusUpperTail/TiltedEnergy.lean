import SpectralRadiusUpperTail.DensityCoupling
import SpectralRadiusUpperTail.SoftNormalizer

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

lemma boundedDensity_le_smul (μ : Measure α) (k : α → ℝ) (C : ℝ)
    (hkC : ∀ x, k x ≤ C) :
    μ.withDensity (fun x => ENNReal.ofReal (k x)) ≤ ENNReal.ofReal C • μ := by
  calc
    _ ≤ μ.withDensity (fun _ => ENNReal.ofReal C) :=
      withDensity_mono (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_le_ofReal (hkC x)))
    _ = _ := withDensity_const _

lemma boundedDensity_integrable (μ : Measure α) (k f : α → ℝ) (C : ℝ)
    (hkC : ∀ x, k x ≤ C) (hf : Integrable f μ) :
    Integrable f (μ.withDensity (fun x => ENNReal.ofReal (k x))) :=
  (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure (boundedDensity_le_smul μ k C hkC)

lemma boundedDensity_integral_le (μ : Measure α) (k f : α → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hkC : ∀ x, k x ≤ C) (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂μ.withDensity (fun x => ENNReal.ofReal (k x))) ≤ C * ∫ x, f x ∂μ := by
  have h := integral_mono_measure (boundedDensity_le_smul μ k C hkC)
    (Filter.Eventually.of_forall hfn) (hf.smul_measure ENNReal.ofReal_ne_top)
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul] using h

/-- A bounded likelihood and an exponential moment control the tilted mean
through Jensen; this is the energy estimate used before bounding a Gaussian score. -/
theorem tilted_energy_le (μ : Measure α) (k V : α → ℝ)
    (hnorm : (∫⁻ x, ENNReal.ofReal (k x) ∂μ) = 1)
    (hV : Integrable V μ) (c K L : ℝ) (hc : 0 < c)
    (hk : ∀ x, k x ≤ Real.exp K)
    (hexp : Integrable (fun x => Real.exp (c*V x)) μ)
    (hmoment : (∫ x, Real.exp (c*V x) ∂μ) ≤ Real.exp L) :
    (∫ x, V x ∂μ.withDensity (fun x => ENNReal.ofReal (k x))) ≤ (K+L)/c := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (k x))
  let : IsProbabilityMeasure ν := normalizedDensity_probability μ _ hnorm
  have hVν : Integrable V ν := boundedDensity_integrable μ k V (Real.exp K) hk hV
  have heν : Integrable (fun x => Real.exp (c*V x)) ν :=
    boundedDensity_integrable μ k _ (Real.exp K) hk hexp
  have hj := convexOn_exp.map_integral_le (μ := ν) Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (hVν.const_mul c) heν
  have hb := boundedDensity_integral_le μ k (fun x => Real.exp (c*V x)) (Real.exp K)
    (Real.exp_nonneg K) hk hexp (fun _ => Real.exp_nonneg _)
  have hupper : (∫ x, Real.exp (c*V x) ∂ν) ≤ Real.exp (K+L) := by
    apply hb.trans
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_left hmoment (Real.exp_nonneg K)
  have he : Real.exp (c * ∫ x, V x ∂ν) ≤ Real.exp (K+L) := by
    simpa only [integral_const_mul] using hj.trans hupper
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using Real.exp_le_exp.mp he)

#print axioms tilted_energy_le
end SpectralRadiusUpperTail
