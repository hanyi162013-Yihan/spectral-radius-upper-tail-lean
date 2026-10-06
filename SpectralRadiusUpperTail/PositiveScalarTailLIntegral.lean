import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal

/-- Nonnegative tail integrals under positive scalar rescaling. No
integrability assumption is needed at this stage. -/
theorem positiveScalar_tail_lintegral (c r : ℝ) (hc : 0 < c)
    (g : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioi (c*r), g x) =
      ∫⁻ y in Ioi r, ENNReal.ofReal c * g (c*y) := by
  let L : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ
  have hL : |L.det| = c := by
    change |LinearMap.det (c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))| = c
    simp only [LinearMap.det_smul, Module.finrank_self, pow_one,
      LinearMap.det_id, mul_one, abs_of_pos hc]
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (s := Ioi r) (f := fun x : ℝ => c*x) (f' := fun _ => L) volume measurableSet_Ioi
    (fun x _ => L.hasFDerivAt.hasFDerivWithinAt)
    (fun _ _ _ _ he => mul_left_cancel₀ hc.ne' he) g
  rw [image_mul_left_Ioi hc, hL] at hh
  exact hh

#print axioms positiveScalar_tail_lintegral
end SpectralRadiusUpperTail
