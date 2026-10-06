import SpectralRadiusUpperTail.GaussianDirectionalBounds
import SpectralRadiusUpperTail.ProductSumIntegration

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Topology
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma gaussian_shift_line_deriv (a : ℝ) (s w z : E) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-‖s+u • w-z‖^2/a))
      (gaussianDirectional a w (s+t • w-z)) t := by
  have hfun : (fun u : ℝ => Real.exp (-‖s+u • w-z‖^2/a)) = gaussianLine a (s-z) w := by
    funext u
    unfold gaussianLine
    rw [sub_add_eq_add_sub]
  have hd : gaussianDirectional a w (s+t • w-z) = gaussianLineFirst a (s-z) w t := by
    unfold gaussianDirectional gaussianLineFirst gaussianLineSlope gaussianLine
    rw [sub_add_eq_add_sub]
  rw [hfun, hd]
  exact gaussianLine_deriv a (s-z) w t

/-- A bounded derivative envelope justifies actual differentiation of every
Gaussian-soft normalizer, including actual finite-product sums. -/
theorem gaussian_shift_integral_hasDerivAt (μ : Measure α) [IsProbabilityMeasure μ]
    (T : α → E) (hT : Measurable T) (a : ℝ) (ha : 0 < a) (s w : E) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (-‖s+t • w-T x‖^2/a) ∂μ)
      (∫ x, gaussianDirectional a w (s+t₀ • w-T x) ∂μ) t₀ := by
  have hi : Integrable (fun x => Real.exp (-‖s+t₀ • w-T x‖^2/a)) μ := by
    apply (integrable_const (1 : ℝ)).mono_nonneg (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))
    exact Filter.Eventually.of_forall (fun _ => Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) ha.le))
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => Real.exp (-‖s+t • w-T x‖^2/a))
    (F' := fun t x => gaussianDirectional a w (s+t • w-T x))
    (bound := fun _ : α => (2/a)*(1+a)*‖w‖)
    (show Set.univ ∈ nhds t₀ from Filter.univ_mem)
    (Filter.Eventually.of_forall (fun _ => by fun_prop)) hi
    (by unfold gaussianDirectional; fun_prop)
    (Filter.Eventually.of_forall (fun x t _ => by
      simpa only [Real.norm_eq_abs] using gaussianDirectional_bound a ha w (s+t • w-T x)))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun x t _ => gaussian_shift_line_deriv a s w (T x) t))
  exact hh.2

#print axioms gaussian_shift_integral_hasDerivAt
end SpectralRadiusUpperTail
