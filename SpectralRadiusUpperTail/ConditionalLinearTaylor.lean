import SpectralRadiusUpperTail.IsotropicLinearMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma bounded_weight_projection_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (f : E → ℝ) (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ 1) (w : E) :
    Integrable f μ ∧ Integrable (fun x => inner ℝ w x*f x) μ := by
  have hi := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hp : Integrable (fun x : E => inner ℝ w x) μ := hi.const_inner w
  constructor
  · apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)
  · apply hp.norm.mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [Real.norm_eq_abs, mul_one] using
      mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (inner ℝ w x))

/-- Centering cancels the denominator's actual first-order term. -/
theorem centered_linear_taylor_denominator (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (hm : (∫ x : E, x ∂μ) = 0)
    (hvar : (∫ x : E, ‖x‖^2 ∂μ) = 1)
    (f : E → ℝ) (hf : Integrable f μ) (A C : ℝ) (L : E →L[ℝ] ℝ)
    (hrem : ∀ x, |f x-(A-L x)| ≤ C*‖x‖^2) :
    |(∫ x, f x ∂μ)-A| ≤ C := by
  have hi := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hL := L.integrable_comp hi
  have hP : Integrable (fun x : E => A-L x) μ := (integrable_const A).sub hL
  have hmean : (∫ x : E, A-L x ∂μ) = A := by
    rw [integral_sub (integrable_const A) hL, L.integral_comp_comm hi, hm, map_zero]
    simp
  have h2 := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hh := norm_integral_le_of_norm_le (f := fun x : E => f x-(A-L x))
    (h2.const_mul C) (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hrem x))
  rw [integral_sub hf hP, hmean, integral_const_mul, hvar, mul_one] at hh
  simpa only [Real.norm_eq_abs] using hh

/-- The actual weighted numerator has the covariance-determined linear term,
and its error is controlled by the third absolute entry moment. -/
theorem isotropic_linear_taylor_numerator (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (hm : (∫ x : E, x ∂μ) = 0)
    (h3 : Integrable (fun x : E => ‖x‖^3) μ) (c : ℝ)
    (hc : ∀ s : E, (∫ x : E, (inner ℝ s x)^2 ∂μ) = c*‖s‖^2)
    (f : E → ℝ) (A C : ℝ) (hC : 0 ≤ C) (L : E →L[ℝ] ℝ) (w : E)
    (hf : Integrable (fun x : E => inner ℝ w x*f x) μ)
    (hrem : ∀ x, |f x-(A-L x)| ≤ C*‖x‖^2) :
    |(∫ x : E, inner ℝ w x*f x ∂μ)+c*L w| ≤ C*‖w‖*(∫ x : E, ‖x‖^3 ∂μ) := by
  have hi := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hp : Integrable (fun x : E => inner ℝ w x) μ := hi.const_inner w
  obtain ⟨hLi, hLm⟩ := isotropic_linear_moment μ hX c hc L w
  have he (x : E) : inner ℝ w x*(A-L x) = inner ℝ w x*A-inner ℝ w x*L x := by ring
  have hP : Integrable (fun x : E => inner ℝ w x*(A-L x)) μ := by
    simp_rw [he]
    exact (hp.mul_const A).sub hLi
  have hmean : (∫ x : E, inner ℝ w x*(A-L x) ∂μ) = -c*L w := by
    simp_rw [he]
    rw [integral_sub (hp.mul_const A) hLi, integral_mul_const, integral_inner hi, hm,
      inner_zero_right, zero_mul, hLm]
    ring
  have hb (x : E) :
      |inner ℝ w x*f x-inner ℝ w x*(A-L x)| ≤ (C*‖w‖)*‖x‖^3 := by
    rw [← mul_sub, abs_mul]
    calc
      _ ≤ (‖w‖*‖x‖)*(C*‖x‖^2) :=
        mul_le_mul (abs_real_inner_le_norm _ _) (hrem x) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hh := norm_integral_le_of_norm_le
    (f := fun x : E => inner ℝ w x*f x-inner ℝ w x*(A-L x))
    (h3.const_mul (C*‖w‖)) (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hb x))
  rw [integral_sub hf hP, hmean, integral_const_mul] at hh
  convert! hh using 1 <;> (try rw [Real.norm_eq_abs]) <;> congr 1 <;> ring

#print axioms centered_linear_taylor_denominator
#print axioms isotropic_linear_taylor_numerator
end SpectralRadiusUpperTail
