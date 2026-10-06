import SpectralRadiusUpperTail.TalagrandExponentialInterpolation
import SpectralRadiusUpperTail.TalagrandFiberRatioAlgebra
import SpectralRadiusUpperTail.TalagrandInterpolationWeight
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The complete analytic estimate for a positive-probability head fiber.
The geometric fiber recursion and induction moment estimates are explicit
inputs, while Hölder, normalization and scalar cancellation are proved. -/
theorem talagrand_positive_fiber_step
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hdInt : Integrable (fun x => Real.exp (d x)) μ)
    (hfInt : Integrable (fun x => Real.exp (f x)) μ)
    (hgInt : Integrable (fun x => Real.exp (g x)) μ)
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (ha1 : a ≤ 1)
    (hmixInt : Integrable (fun x =>
      (Real.exp (f x))^(talagrandWeight a)*
      (Real.exp (g x))^(1-talagrandWeight a)) μ)
    (hpoint : ∀ x, d x ≤
      talagrandWeight a*f x+(1-talagrandWeight a)*g x+
        (1-talagrandWeight a)^2/4)
    (hfMoment : (∫ x, Real.exp (f x) ∂μ) ≤ 1/(p*a))
    (hgMoment : (∫ x, Real.exp (g x) ∂μ) ≤ 1/p) :
    (∫ x, Real.exp (d x) ∂μ) ≤
      (1/p)*Real.exp
        (-talagrandWeight a*Real.log a+
          (1-talagrandWeight a)^2/4) := by
  have hθ := talagrandWeight_mem a ha.le ha1
  have hbaseF : 0 ≤ ∫ x, Real.exp (f x) ∂μ :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  have hbaseG : 0 ≤ ∫ x, Real.exp (g x) ∂μ :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  have hpowF := Real.rpow_le_rpow hbaseF hfMoment hθ.1
  have hpowG := Real.rpow_le_rpow hbaseG hgMoment (by linarith : 0 ≤ 1-talagrandWeight a)
  have hcore := integral_exp_interpolation_le μ d f g hf hg
    hdInt hfInt hgInt (talagrandWeight a)
    ((1-talagrandWeight a)^2/4) hθ.1 hθ.2 hmixInt hpoint
  calc
    (∫ x, Real.exp (d x) ∂μ) ≤
        Real.exp ((1-talagrandWeight a)^2/4)*
          (∫ x, Real.exp (f x) ∂μ)^(talagrandWeight a)*
          (∫ x, Real.exp (g x) ∂μ)^(1-talagrandWeight a) := hcore
    _ ≤ Real.exp ((1-talagrandWeight a)^2/4)*
          (1/(p*a))^(talagrandWeight a)*
          (1/p)^(1-talagrandWeight a) := by
      gcongr
    _ = (1/p)*Real.exp
          (-talagrandWeight a*Real.log a+
            (1-talagrandWeight a)^2/4) :=
      talagrand_fiber_ratio_identity p a (talagrandWeight a) hp ha

#print axioms talagrand_positive_fiber_step
end SpectralRadiusUpperTail
