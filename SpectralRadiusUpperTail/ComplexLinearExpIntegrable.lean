import SpectralRadiusUpperTail.SquareExpMGF
import Mathlib.Analysis.Complex.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- A square-exponential moment supplies every complex linear exponential
moment; this need not be an independent sharp-subgaussian hypothesis. -/
lemma complex_linear_exp_integrable (μ : Measure ℂ) (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ) (u : ℂ) :
    Integrable (fun z : ℂ => Real.exp (2*(star u*z).re)) μ := by
  have hb (z : ℂ) : 2*(star u*z).re ≤ (2*‖u‖)^2/(4*c)+c*‖z‖^2 := by
    have hRe : (star u*z).re ≤ ‖u‖*‖z‖ := by
      simpa only [norm_mul, norm_star] using Complex.re_le_norm (star u*z)
    have hy := young_linear_square (2*‖u‖) ‖z‖ c hc
    nlinarith
  apply (hexp.const_mul (Real.exp ((2*‖u‖)^2/(4*c)))).mono_nonneg (by fun_prop)
    (Filter.Eventually.of_forall (fun z => Real.exp_nonneg _))
  filter_upwards [] with z
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (hb z)

#print axioms complex_linear_exp_integrable
end SpectralRadiusUpperTail
