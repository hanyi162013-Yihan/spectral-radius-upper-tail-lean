import SpectralRadiusUpperTail.TiltedEnergy
import SpectralRadiusUpperTail.RowNormalizerBound

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

noncomputable def softDensity (μ : Measure α) (q : α → ℝ) (a : ℝ) (x : α) : ℝ :=
  Real.exp (-q x/a) / ∫ y, Real.exp (-q y/a) ∂μ

lemma softDensity_normalized (μ : Measure α) [IsProbabilityMeasure μ]
    (q : α → ℝ) (hq : Measurable q) (hqi : Integrable q μ) (hqn : ∀ x, 0 ≤ q x)
    (a : ℝ) (ha : 0 < a) : (∫⁻ x, ENNReal.ofReal (softDensity μ q a x) ∂μ) = 1 := by
  have hi := soft_exponential_integrable μ q hq hqn a ha
  have hZ := lt_of_lt_of_le (Real.exp_pos _) (soft_normalizer_jensen μ q hq hqi hqn a ha)
  have hki : Integrable (softDensity μ q a) μ := hi.div_const _
  have hkn (x : α) : 0 ≤ softDensity μ q a x := div_nonneg (Real.exp_nonneg _) hZ.le
  rw [← ofReal_integral_eq_lintegral_ofReal hki (Filter.Eventually.of_forall hkn)]
  unfold softDensity
  rw [integral_div, div_self (ne_of_gt hZ), ENNReal.ofReal_one]

/-- The tilted-energy estimate for the actual normalized exponential weight. -/
theorem soft_tilted_energy_le (μ : Measure α) [IsProbabilityMeasure μ]
    (q V : α → ℝ) (hq : Measurable q) (hqi : Integrable q μ) (hqn : ∀ x, 0 ≤ q x)
    (hV : Integrable V μ) (a M c L : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hqM : (∫ x, q x ∂μ) ≤ M)
    (hexp : Integrable (fun x => Real.exp (c*V x)) μ)
    (hL : (∫ x, Real.exp (c*V x) ∂μ) ≤ Real.exp L) :
    (∫ x, V x ∂μ.withDensity (fun x => ENNReal.ofReal (softDensity μ q a x))) ≤
      (M/a+L)/c :=
  tilted_energy_le μ (softDensity μ q a) V (softDensity_normalized μ q hq hqi hqn a ha)
    hV c (M/a) L hc (soft_normalized_likelihood_le μ q hq hqi hqn a M ha hqM) hexp hL

section Gaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

noncomputable def gaussianSoftTilt (μ : Measure E) (a : ℝ) (s : E) : Measure E :=
  μ.withDensity (fun x => ENNReal.ofReal (softDensity μ (fun x => ‖s-x‖^2) a x))

lemma gaussian_energy_measurable (s : E) : Measurable (fun x : E => ‖s-x‖^2) :=
  ((continuous_const.sub continuous_id).norm.pow 2).measurable

theorem gaussianSoftTilt_energy (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (hm : (∫ x : E, x ∂μ) = 0)
    (hvar : (∫ x : E, ‖x‖^2 ∂μ) ≤ 1) (a c L : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hexp : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ)
    (hL : (∫ x : E, Real.exp (c*‖x‖^2) ∂μ) ≤ Real.exp L) (s : E) :
    IsProbabilityMeasure (gaussianSoftTilt μ a s) ∧
      (∫ x : E, ‖x‖^2 ∂gaussianSoftTilt μ a s) ≤ ((1+‖s‖^2)/a+L)/c := by
  obtain ⟨hqi, hqe⟩ := centered_shift_energy μ (fun x : E => x) hX hm s
  have hqM : (∫ x : E, ‖s-x‖^2 ∂μ) ≤ 1+‖s‖^2 := by rw [hqe]; linarith
  have hV := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hn := softDensity_normalized μ _ (gaussian_energy_measurable s) hqi
    (fun _ => sq_nonneg _) a ha
  refine ⟨normalizedDensity_probability μ _ hn, ?_⟩
  exact soft_tilted_energy_le μ _ _ (gaussian_energy_measurable s) hqi (fun _ => sq_nonneg _)
    hV a (1+‖s‖^2) c L ha hc hqM hexp hL

theorem gaussianSoftTilt_mean_sq (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (hm : (∫ x : E, x ∂μ) = 0)
    (hvar : (∫ x : E, ‖x‖^2 ∂μ) ≤ 1) (a c L : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hexp : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ)
    (hL : (∫ x : E, Real.exp (c*‖x‖^2) ∂μ) ≤ Real.exp L) (s : E) :
    ‖∫ x : E, x ∂gaussianSoftTilt μ a s‖^2 ≤ ((1+‖s‖^2)/a+L)/c := by
  obtain ⟨hν, he⟩ := gaussianSoftTilt_energy μ hX hm hvar a c L ha hc hexp hL s
  let : IsProbabilityMeasure (gaussianSoftTilt μ a s) := hν
  obtain ⟨hqi, hqe⟩ := centered_shift_energy μ (fun x : E => x) hX hm s
  have hqM : (∫ x : E, ‖s-x‖^2 ∂μ) ≤ 1+‖s‖^2 := by rw [hqe]; linarith
  have hb := soft_normalized_likelihood_le μ _ (gaussian_energy_measurable s) hqi
    (fun _ => sq_nonneg _) a (1+‖s‖^2) ha hqM
  have hdom := boundedDensity_le_smul μ (softDensity μ (fun x => ‖s-x‖^2) a)
    (Real.exp ((1+‖s‖^2)/a)) hb
  have hXi := ((hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).smul_measure
    ENNReal.ofReal_ne_top).mono_measure hdom
  have hX2 := (((memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX).smul_measure
    ENNReal.ofReal_ne_top).mono_measure hdom
  have hv := integral_centered_norm_sq (gaussianSoftTilt μ a s) (fun x : E => x) hXi hX2
  have hn : 0 ≤ ∫ x : E, ‖x-∫ y : E, y ∂gaussianSoftTilt μ a s‖^2
      ∂gaussianSoftTilt μ a s := integral_nonneg (fun _ => sq_nonneg _)
  linarith

end Gaussian
#print axioms gaussianSoftTilt_energy
#print axioms gaussianSoftTilt_mean_sq
end SpectralRadiusUpperTail
