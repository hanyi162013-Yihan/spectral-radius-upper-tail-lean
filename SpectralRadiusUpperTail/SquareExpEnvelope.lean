import SpectralRadiusUpperTail.ExponentialVariation

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma polynomial_exp_envelope_bound (d r : ℝ) (hd : 0 < d) (hr : 0 ≤ r) :
    (1+r^2)*(d*(r+r^2))*Real.exp (d*(r+r^2)) ≤
      (4*d*(1+1/(2*d^2))*Real.exp d)*Real.exp (4*d*r^2) := by
  have hp : (1+r^2)*(r+r^2) ≤ 4*(1+r^4) := by
    calc
      _ ≤ (1+r^2)*(2*(1+r^2)) := mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (r-1)]) (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (r^2-1)]
  have ht := Real.pow_div_factorial_le_exp (2*d*r^2)
    (show 0 ≤ 2*d*r^2 by positivity) 2
  norm_num [Nat.factorial] at ht
  have h4 : r^4 ≤ Real.exp (2*d*r^2)/(2*d^2) := by
    apply (le_div_iff₀ (show 0 < 2*d^2 by positivity)).mpr
    nlinarith only [ht]
  have he1 : 1 ≤ Real.exp (2*d*r^2) := Real.one_le_exp_iff.mpr (by positivity)
  have hp1 : 1+r^4 ≤ (1+1/(2*d^2))*Real.exp (2*d*r^2) := by
    calc
      _ ≤ Real.exp (2*d*r^2)+Real.exp (2*d*r^2)/(2*d^2) := add_le_add he1 h4
      _ = _ := by ring
  have hp2 : (1+r^2)*(d*(r+r^2)) ≤
      4*d*(1+1/(2*d^2))*Real.exp (2*d*r^2) := by
    have hdp := mul_le_mul_of_nonneg_left hp hd.le
    have hdp1 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ 4*d by positivity)
    nlinarith only [hdp, hdp1]
  have he2 : Real.exp (d*(r+r^2)) ≤ Real.exp d * Real.exp (2*d*r^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (show r ≤ 1+r^2 by nlinarith [sq_nonneg (r-1)]) hd.le
    nlinarith only [h]
  have hh := mul_le_mul hp2 he2 (Real.exp_nonneg _)
    (show 0 ≤ 4*d*(1+1/(2*d^2))*Real.exp (2*d*r^2) by positivity)
  have heprod : Real.exp (2*d*r^2)*Real.exp (2*d*r^2) = Real.exp (4*d*r^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (4*d*(1+1/(2*d^2))*Real.exp (2*d*r^2))*(Real.exp d*Real.exp (2*d*r^2)) := hh
    _ = (4*d*(1+1/(2*d^2))*Real.exp d)*(Real.exp (2*d*r^2)*Real.exp (2*d*r^2)) := by ring
    _ = _ := by rw [heprod]

/-- A square-exponential moment supplies the polynomial exponential envelope
required by the logarithmic-perturbation estimate. -/
theorem squareExp_weighted_envelope_integrable {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (d : ℝ) (hd : 0 < d)
    (he : Integrable (fun x : E => Real.exp (4*d*‖x‖^2)) μ) :
    Integrable (fun x : E => (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
      Real.exp (d*(‖x‖+‖x‖^2))) μ := by
  have hm : Measurable (fun x : E => (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*
      Real.exp (d*(‖x‖+‖x‖^2))) :=
    ((measurable_const.add (measurable_norm.pow_const 2)).mul
      (measurable_const.mul (measurable_norm.add (measurable_norm.pow_const 2)))).mul
      (Real.measurable_exp.comp (measurable_const.mul
        (measurable_norm.add (measurable_norm.pow_const 2))))
  apply (he.const_mul (4*d*(1+1/(2*d^2))*Real.exp d)).mono_nonneg hm.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by positivity)
  · exact Filter.Eventually.of_forall (fun x => polynomial_exp_envelope_bound d ‖x‖ hd (norm_nonneg x))

#print axioms squareExp_weighted_envelope_integrable
end SpectralRadiusUpperTail
