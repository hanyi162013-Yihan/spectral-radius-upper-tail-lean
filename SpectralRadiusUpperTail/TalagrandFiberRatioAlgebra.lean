import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Numerical cancellation of the projected-set probability in the
Hölder fiber estimate. This leaves precisely the scalar mixing factor
handled by the averaged Talagrand budget. -/
theorem talagrand_fiber_ratio_identity
    (p a θ : ℝ) (hp : 0 < p) (ha : 0 < a) :
    Real.exp ((1-θ)^2/4)*(1/(p*a))^θ*(1/p)^(1-θ) =
      (1/p)*Real.exp (-θ*Real.log a+(1-θ)^2/4) := by
  have hpa : 0 < p*a := mul_pos hp ha
  have hlogpa : Real.log (1/(p*a)) = -Real.log p-Real.log a := by
    rw [one_div, Real.log_inv, Real.log_mul hp.ne' ha.ne']
    ring
  have hlogp : Real.log (1/p) = -Real.log p := by
    rw [one_div, Real.log_inv]
  have harg : (1-θ)^2/4+Real.log (1/(p*a))*θ+
      Real.log (1/p)*(1-θ) =
      Real.log (1/p)+(-θ*Real.log a+(1-θ)^2/4) := by
    rw [hlogpa, hlogp]
    ring
  calc
    Real.exp ((1-θ)^2/4)*(1/(p*a))^θ*(1/p)^(1-θ) =
        Real.exp ((1-θ)^2/4+Real.log (1/(p*a))*θ+
          Real.log (1/p)*(1-θ)) := by
      rw [Real.rpow_def_of_pos (one_div_pos.mpr hpa),
        Real.rpow_def_of_pos (one_div_pos.mpr hp),
        ← Real.exp_add, ← Real.exp_add]
    _ = Real.exp (Real.log (1/p)+(-θ*Real.log a+(1-θ)^2/4)) := by
      rw [harg]
    _ = (1/p)*Real.exp (-θ*Real.log a+(1-θ)^2/4) := by
      rw [Real.exp_add, Real.exp_log (one_div_pos.mpr hp)]

#print axioms talagrand_fiber_ratio_identity
end SpectralRadiusUpperTail
