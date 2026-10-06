import SpectralRadiusUpperTail.SoftNormalizer
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def gaussianKernelReal (a : ℝ) (s x : E) : ℝ :=
  Real.exp (-‖s-x‖^2/a)

noncomputable def gaussianKernelDerivative (a : ℝ) (s x : E) : E →L[ℝ] ℝ :=
  (-2/a) • (gaussianKernelReal a s x • innerSL ℝ (s-x))

lemma gaussianKernel_hasFDerivAt (a : ℝ) (s x : E) :
    HasFDerivAt (fun t => gaussianKernelReal a t x) (gaussianKernelDerivative a s x) s := by
  have h := ((hasStrictFDerivAt_norm_sq (s-x)).hasFDerivAt.comp s
    ((hasFDerivAt_id s).sub_const x)).const_mul (-1/a)
  have hfun : (fun t : E => (-1/a)*‖t-x‖^2) = fun t => -‖t-x‖^2/a := by
    funext t
    ring
  simp only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] at h
  rw [hfun] at h
  have he := h.exp
  have hd : gaussianKernelDerivative a s x = Real.exp (-‖s-x‖^2/a) •
      ((-1/a) • (2 • innerSL ℝ (s-x))) := by
    ext z
    simp only [gaussianKernelDerivative, gaussianKernelReal, smul_apply,
      innerSL_apply_apply, smul_eq_mul, two_smul, add_apply]
    ring
  rw [hd]
  exact he

lemma gaussianKernelDerivative_norm_le (a : ℝ) (ha : 0 < a) (s x : E) :
    ‖gaussianKernelDerivative a s x‖ ≤ (2/a)*‖s-x‖ := by
  have hcoef : |(-2/a : ℝ)| = 2/a := by norm_num [abs_div, abs_of_pos ha]
  have he : gaussianKernelReal a s x ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) ha.le)
  have hn : 0 ≤ gaussianKernelReal a s x := Real.exp_nonneg _
  simp only [gaussianKernelDerivative, norm_smul, Real.norm_eq_abs, hcoef,
    abs_of_nonneg hn, innerSL_apply_norm]
  have hmul := mul_le_mul_of_nonneg_left he
    (mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha.le) (norm_nonneg (s-x)))
  nlinarith only [hmul]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma gaussianKernelReal_continuous (a : ℝ) (s : E) : Continuous (gaussianKernelReal a s) :=
  Real.continuous_exp.comp (((continuous_const.sub continuous_id).norm.pow 2).neg.div_const a)

lemma gaussianKernelDerivative_continuous (a : ℝ) (s : E) :
    Continuous (gaussianKernelDerivative a s) := by
  exact ((gaussianKernelReal_continuous a s).smul
    ((innerSL ℝ (E := E)).continuous.comp (continuous_const.sub continuous_id))).const_smul (-2/a)

noncomputable def gaussianConvolution (μ : Measure E) (a : ℝ) (s : E) : ℝ :=
  ∫ x, gaussianKernelReal a s x ∂μ

/-- Actual differentiation of the Gaussian convolution under the integral.
The proof uses an integrable local derivative bound, not a formal interchange. -/
theorem gaussianConvolution_hasFDerivAt (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : Integrable (fun x : E => x) μ) (a : ℝ) (ha : 0 < a) (s₀ : E) :
    HasFDerivAt (gaussianConvolution μ a)
      (∫ x, gaussianKernelDerivative a s₀ x ∂μ) s₀ := by
  have hq : Measurable (fun x : E => ‖s₀-x‖^2) :=
    ((continuous_const.sub continuous_id).norm.pow 2).measurable
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := gaussianKernelReal a) (F' := gaussianKernelDerivative a)
    (bound := fun x : E => (2/a)*(‖s₀‖+1+‖x‖)) (Metric.ball_mem_nhds s₀ (by norm_num : (0 : ℝ) < 1))
  · exact Filter.Eventually.of_forall (fun s => (gaussianKernelReal_continuous a s).aestronglyMeasurable)
  · exact soft_exponential_integrable μ _ hq (fun _ => sq_nonneg _) a ha
  · exact (gaussianKernelDerivative_continuous a s₀).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x s hs
    have hs' : ‖s-s₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hs
    have hsn : ‖s‖ ≤ ‖s₀‖+1 := by
      have h := norm_add_le (s-s₀) s₀
      rw [sub_add_cancel] at h
      linarith
    apply (gaussianKernelDerivative_norm_le a ha s x).trans
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) ha.le)
    exact (norm_sub_le s x).trans (by linarith)
  · exact ((integrable_const (‖s₀‖+1)).add hX.norm).const_mul (2/a)
  · exact Filter.Eventually.of_forall (fun x s _ => gaussianKernel_hasFDerivAt a s x)

#print axioms gaussianConvolution_hasFDerivAt
end SpectralRadiusUpperTail
