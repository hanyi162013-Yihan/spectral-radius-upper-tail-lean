import SpectralRadiusUpperTail.DecreasingWeightMean
import SpectralRadiusUpperTail.ExponentialFirstMoment
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma exponential_first_moment (r : ℝ) (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (expMeasure r) ∧
      (∫ x : ℝ, x ∂expMeasure r) = r⁻¹ := by
  have hn := exponential_nonnegative_ae r hr
  have hi : Integrable (fun x : ℝ => x) (expMeasure r) := by
    apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop) hn).mp
    rw [exponential_firstMoment_lintegral r hr]
    exact ENNReal.ofReal_ne_top
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn (by fun_prop),
    exponential_firstMoment_lintegral r hr, ENNReal.toReal_ofReal (by positivity)]

/-- Weight in the squared Schur-gap coordinate s=Delta^2. On the support
s>=0 it is (s+4y^2)^(-1/2); max only extends it harmlessly to all real s. -/
noncomputable def schurGapWeight (y s : ℝ) : ℝ := (Real.sqrt (max 0 s+4*y^2))⁻¹

lemma schurGapWeight_positive (y : ℝ) (hy : 0 < y) (s : ℝ) : 0 < schurGapWeight y s := by
  unfold schurGapWeight
  apply inv_pos.mpr
  apply Real.sqrt_pos.mpr
  have hm := le_max_left (0 : ℝ) s
  nlinarith [sq_pos_of_pos hy]

lemma schurGapWeight_antitone (y : ℝ) (hy : 0 < y) : Antitone (schurGapWeight y) := by
  intro s t hst
  unfold schurGapWeight
  apply inv_anti₀ (Real.sqrt_pos.mpr (by nlinarith [le_max_left (0 : ℝ) s, sq_pos_of_pos hy]))
  exact Real.sqrt_le_sqrt (add_le_add (max_le_max_left 0 hst) le_rfl)

lemma schurGapWeight_bound (y : ℝ) (hy : 0 < y) (s : ℝ) :
    schurGapWeight y s ≤ (Real.sqrt (4*y^2))⁻¹ := by
  unfold schurGapWeight
  apply inv_anti₀ (Real.sqrt_pos.mpr (by positivity))
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (le_max_left 0 s))

lemma schurGapWeight_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (y : ℝ) (hy : 0 < y) : Integrable (schurGapWeight y) μ := by
  apply (integrable_const ((Real.sqrt (4*y^2))⁻¹)).mono_nonneg (by unfold schurGapWeight; fun_prop)
    (Filter.Eventually.of_forall (fun s => (schurGapWeight_positive y hy s).le))
    (Filter.Eventually.of_forall (schurGapWeight_bound y hy))

lemma schurGapWeight_id_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hx : Integrable (fun x : ℝ => x) μ) (y : ℝ) (hy : 0 < y) :
    Integrable (fun s => s*schurGapWeight y s) μ := by
  apply (hx.norm.mul_const ((Real.sqrt (4*y^2))⁻¹)).mono' (by unfold schurGapWeight; fun_prop)
  filter_upwards [] with s
  rw [norm_mul, Real.norm_of_nonneg (schurGapWeight_positive y hy s).le]
  exact mul_le_mul_of_nonneg_left (schurGapWeight_bound y hy s) (norm_nonneg s)

/-- The squared Schur-gap coordinate has mean <=2/n under its normalized
weighted exponential density, uniformly over y>0. Identification with the
conditional Schur law is a separate change-of-variables theorem. -/
theorem schur_gap_weighted_second_moment (n y : ℝ) (hn : 0 < n) (hy : 0 < y) :
    (∫ s : ℝ, s*schurGapWeight y s ∂expMeasure (n/2))/
      (∫ s : ℝ, schurGapWeight y s ∂expMeasure (n/2)) ≤ 2/n := by
  have hn2 : 0 < n/2 := by positivity
  letI := isProbabilityMeasure_expMeasure hn2
  have hx := exponential_first_moment (n/2) hn2
  have hw := schurGapWeight_integrable (expMeasure (n/2)) y hy
  have hp : 0 < ∫ s : ℝ, schurGapWeight y s ∂expMeasure (n/2) := by
    apply (integral_pos_iff_support_of_nonneg
      (fun s => (schurGapWeight_positive y hy s).le) hw).mpr
    have hs : Function.support (schurGapWeight y) = Set.univ := by
      ext s
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (schurGapWeight_positive y hy s).ne'
    rw [hs]
    simp
  have hh := decreasing_weight_mean_le (expMeasure (n/2)) (schurGapWeight y)
    hx.1 hw (schurGapWeight_id_integrable _ hx.1 y hy) (schurGapWeight_antitone y hy) hp
  rw [hx.2] at hh
  simpa only [inv_div, one_div] using hh

#print axioms exponential_first_moment
#print axioms schur_gap_weighted_second_moment
end SpectralRadiusUpperTail
