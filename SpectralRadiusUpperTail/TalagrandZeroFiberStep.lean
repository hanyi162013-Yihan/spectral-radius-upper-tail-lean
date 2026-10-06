import SpectralRadiusUpperTail.TalagrandInterpolationWeight
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Empty or zero-probability matching fibers use only the projected
distance, with a one-coordinate energy cost. -/
theorem talagrand_zero_fiber_step
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d g : Ω → ℝ)
    (hdInt : Integrable (fun x => Real.exp (d x)) μ)
    (hgInt : Integrable (fun x => Real.exp (g x)) μ)
    (p : ℝ)
    (hpoint : ∀ x, d x ≤ g x+1/4)
    (hgMoment : (∫ x, Real.exp (g x) ∂μ) ≤ 1/p) :
    (∫ x, Real.exp (d x) ∂μ) ≤
      (1/p)*Real.exp
        (-talagrandWeight 0*Real.log 0+
          (1-talagrandWeight 0)^2/4) := by
  have hpointExp (x : Ω) : Real.exp (d x) ≤ Real.exp (1/4)*Real.exp (g x) := by
    calc
      Real.exp (d x) ≤ Real.exp (g x+1/4) := Real.exp_le_exp.mpr (hpoint x)
      _ = _ := by rw [Real.exp_add]; ring
  have hint : (∫ x, Real.exp (d x) ∂μ) ≤
      Real.exp (1/4)*(∫ x, Real.exp (g x) ∂μ) := by
    calc
      _ ≤ ∫ x, Real.exp (1/4)*Real.exp (g x) ∂μ :=
        integral_mono hdInt (hgInt.const_mul _) hpointExp
      _ = _ := by rw [integral_const_mul]
  have hbound : Real.exp (1/4)*(∫ x, Real.exp (g x) ∂μ) ≤
      Real.exp (1/4)*(1/p) :=
    mul_le_mul_of_nonneg_left hgMoment (Real.exp_pos _).le
  calc
    (∫ x, Real.exp (d x) ∂μ) ≤ Real.exp (1/4)*(1/p) := hint.trans hbound
    _ = (1/p)*Real.exp
        (-talagrandWeight 0*Real.log 0+
          (1-talagrandWeight 0)^2/4) := by
      norm_num [talagrandWeight]
      ring

#print axioms talagrand_zero_fiber_step
end SpectralRadiusUpperTail
