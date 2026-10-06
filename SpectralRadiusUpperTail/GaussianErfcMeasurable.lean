import SpectralRadiusUpperTail.GaussianErfcEnvelope
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- Measurability of the complementary Gaussian tail as its lower
integration endpoint varies. -/
theorem gaussianErfc_measurable : Measurable gaussianErfc := by
  have hpair : Measurable (fun p : ℝ × ℝ =>
      if p.1 < p.2 then Real.exp (-p.2^2) else 0) := by
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (by fun_prop) measurable_const
  have htail : Measurable (fun t : ℝ =>
      ∫ x : ℝ, if t < x then Real.exp (-x^2) else 0) :=
    hpair.stronglyMeasurable.integral_prod_right'.measurable
  have heq (t : ℝ) :
      (∫ x : ℝ, if t < x then Real.exp (-x^2) else 0) =
        ∫ x : ℝ in Ioi t, Real.exp (-x^2) := by
    simpa only [Set.indicator, mem_Ioi] using
      (integral_indicator (μ := volume)
        (f := fun x : ℝ => Real.exp (-x^2)) measurableSet_Ioi)
  unfold gaussianErfc
  exact measurable_const.mul (by simpa only [heq] using htail)

#print axioms gaussianErfc_measurable
end SpectralRadiusUpperTail
