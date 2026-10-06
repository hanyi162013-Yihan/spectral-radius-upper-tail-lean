import SpectralRadiusUpperTail.GaussianDifferentiation
import SpectralRadiusUpperTail.SoftTiltEnergy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma gaussianSoftTilt_basics (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (hm : (∫ x : E, x ∂μ) = 0)
    (a : ℝ) (ha : 0 < a) (s : E) :
    0 < gaussianConvolution μ a s ∧ IsProbabilityMeasure (gaussianSoftTilt μ a s) ∧
      Integrable (fun x : E => x) (gaussianSoftTilt μ a s) := by
  obtain ⟨hqi, hqe⟩ := centered_shift_energy μ (fun x : E => x) hX hm s
  have hp := lt_of_lt_of_le (Real.exp_pos _)
    (soft_normalizer_jensen μ _ (gaussian_energy_measurable s) hqi (fun _ => sq_nonneg _) a ha)
  have hn := softDensity_normalized μ _ (gaussian_energy_measurable s) hqi
    (fun _ => sq_nonneg _) a ha
  have hb := soft_normalized_likelihood_le μ _ (gaussian_energy_measurable s) hqi
    (fun _ => sq_nonneg _) a (‖s‖^2+∫ x : E, ‖x‖^2 ∂μ) ha hqe.le
  have hdom := boundedDensity_le_smul μ (softDensity μ (fun x => ‖s-x‖^2) a) _ hb
  exact ⟨hp, normalizedDensity_probability μ _ hn,
    ((hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).smul_measure
      ENNReal.ofReal_ne_top).mono_measure hdom⟩

/-- The actual derivative of the log Gaussian convolution, expressed through
the mean of its actual normalized weighted probability measure. -/
theorem gaussian_log_score (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (hm : (∫ x : E, x ∂μ) = 0)
    (a : ℝ) (ha : 0 < a) (s : E) :
    HasFDerivAt (fun t => Real.log (gaussianConvolution μ a t))
      ((-2/a) • innerSL ℝ (s-∫ x : E, x ∂gaussianSoftTilt μ a s)) s := by
  let A := gaussianConvolution μ a s
  let ν := gaussianSoftTilt μ a s
  let k := softDensity μ (fun x => ‖s-x‖^2) a
  obtain ⟨hA, hν, hXi⟩ := gaussianSoftTilt_basics μ hX hm a ha s
  let : IsProbabilityMeasure ν := hν
  have hk : Measurable k := (gaussianKernelReal_continuous a s).measurable.div_const A
  have hkn (x : E) : 0 ≤ k x := div_nonneg (Real.exp_nonneg _) hA.le
  have hweighted : (∫ x, k x • innerSL ℝ (s-x) ∂μ) =
      innerSL ℝ (s-∫ x : E, x ∂ν) := by
    calc
      _ = ∫ x : E, innerSL ℝ (s-x) ∂ν := by
        symm
        rw [show ν = μ.withDensity (fun x => ENNReal.ofReal (k x)) from rfl,
          integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
            (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
        simp only [ENNReal.toReal_ofReal (hkn _)]
      _ = innerSL ℝ (∫ x : E, s-x ∂ν) :=
        (innerSL ℝ (E := E)).integral_comp_comm ((integrable_const s).sub hXi)
      _ = _ := by
        rw [integral_sub (integrable_const s) hXi]
        simp only [integral_const, probReal_univ, one_smul]
        rfl
  have hd : A⁻¹ • (∫ x, gaussianKernelDerivative a s x ∂μ) =
      (-2/a) • innerSL ℝ (s-∫ x : E, x ∂ν) := by
    unfold gaussianKernelDerivative
    rw [integral_smul, smul_comm A⁻¹ (-2/a), ← integral_smul]
    have hfun : (fun x => A⁻¹ • (gaussianKernelReal a s x • innerSL ℝ (s-x))) =
        fun x => k x • innerSL ℝ (s-x) := by
      funext x
      rw [smul_smul]
      congr 1
      change A⁻¹ * gaussianKernelReal a s x = gaussianKernelReal a s x / A
      ring
    rw [hfun, hweighted]
  have hlog := (gaussianConvolution_hasFDerivAt μ
    (hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) a ha s).log (ne_of_gt hA)
  rw [hd] at hlog
  exact hlog

#print axioms gaussian_log_score
end SpectralRadiusUpperTail
