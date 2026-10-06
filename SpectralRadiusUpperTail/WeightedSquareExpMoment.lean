import SpectralRadiusUpperTail.SquareExpPolynomialMoments

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Polynomial factors can be absorbed by half of an actual square-exponential
moment, leaving a positive exponent for the global regression envelope. -/
theorem weighted_squareExp_norm_pow_integrable {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (d : ℝ) (hd : 0 < d)
    (he : Integrable (fun x : E => Real.exp (4*d*‖x‖^2)) μ) (n : ℕ) :
    Integrable (fun x : E => ‖x‖^n*Real.exp (2*d*‖x‖^2)) μ := by
  let C := 1+(n.factorial : ℝ)*(1/(2*d))^n
  have hb (x : E) : ‖x‖^n*Real.exp (2*d*‖x‖^2) ≤ C*Real.exp (4*d*‖x‖^2) := by
    have h := mul_le_mul_of_nonneg_right
      (norm_pow_squareExp_bound (2*d) ‖x‖ (by positivity) n) (Real.exp_nonneg (2*d*‖x‖^2))
    calc
      _ ≤ (C*Real.exp (2*d*‖x‖^2))*Real.exp (2*d*‖x‖^2) := h
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2 <;> ring
  exact (he.const_mul C).mono_nonneg (by fun_prop)
    (Filter.Eventually.of_forall (fun x => by positivity)) (Filter.Eventually.of_forall hb)

theorem squareExp_regression_weight_integrable {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (d : ℝ) (hd : 0 < d)
    (he : Integrable (fun x : E => Real.exp (4*d*‖x‖^2)) μ) :
    Integrable (fun x : E => (‖x‖^2+‖x‖^3)*Real.exp (2*d*‖x‖^2)) μ := by
  convert! (weighted_squareExp_norm_pow_integrable μ d hd he 2).add
      (weighted_squareExp_norm_pow_integrable μ d hd he 3) using 1
  funext x
  exact add_mul _ _ _

#print axioms squareExp_regression_weight_integrable
end SpectralRadiusUpperTail
