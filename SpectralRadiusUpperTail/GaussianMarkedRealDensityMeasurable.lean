import SpectralRadiusUpperTail.GaussianMarkedRealDensitySandwich
import SpectralRadiusUpperTail.CharpolyPrincipalMinorEvaluation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Joint measurability of the shifted absolute characteristic polynomial. -/
theorem measurable_gaussian_charpoly_abs_parameter (m : ℕ) :
    Measurable (fun p : ℝ × (Fin m × Fin m → ℝ) =>
      |(Matrix.of p.2.curry).charpoly.eval p.1|) := by
  classical
  simp_rw [charpoly_eval_eq_sum_principalMinors, Matrix.det_apply,
    Matrix.submatrix_apply, Matrix.of_apply]
  fun_prop

/-- The marked-eigenline candidate is a measurable scalar function, so its
tail integral is well-defined as an ordinary real integral. -/
theorem measurable_gaussianMarkedRealDensity (n : ℕ) :
    Measurable (gaussianMarkedRealDensity n) := by
  classical
  have hm := measurable_gaussian_charpoly_abs_parameter (n-1)
  have hsqrt : Measurable (fun r : ℝ => Real.sqrt (n : ℝ)*r) := by fun_prop
  have hpair : Measurable (fun p : ℝ × (Fin (n-1) × Fin (n-1) → ℝ) =>
      (Real.sqrt (n : ℝ)*p.1, p.2)) :=
    (hsqrt.comp measurable_fst).prodMk measurable_snd
  have hjoint : Measurable (fun p : ℝ × (Fin (n-1) × Fin (n-1) → ℝ) =>
      |(Matrix.of p.2.curry).charpoly.eval (Real.sqrt (n : ℝ)*p.1)|) :=
    hm.comp hpair
  have hint : Measurable (fun r : ℝ =>
      ∫ z : Fin (n-1) × Fin (n-1) → ℝ,
        |(Matrix.of z.curry).charpoly.eval (Real.sqrt (n : ℝ)*r)|
          ∂Measure.pi (fun _ => standardNormal)) :=
    hjoint.stronglyMeasurable.integral_prod_right'.measurable
  have hcore : Measurable (realGinibreCoreDensity n) := by
    unfold realGinibreCoreDensity
    fun_prop
  unfold gaussianMarkedRealDensity
  exact hcore.mul (hint.div (hsqrt.pow_const _))

#print axioms measurable_gaussian_charpoly_abs_parameter
#print axioms measurable_gaussianMarkedRealDensity
end SpectralRadiusUpperTail
