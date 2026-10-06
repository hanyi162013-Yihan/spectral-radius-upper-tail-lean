import SpectralRadiusUpperTail.RealGinibreNonrealDensity
import SpectralRadiusUpperTail.GaussianErfcMeasurable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The factored real-Ginibre nonreal one-point expression at a complex
point. The scaled imaginary coordinate is the argument of erfc. -/
noncomputable def realGinibreNonrealDensityAt (n : ℕ) (z : ℂ) : ℝ :=
  realGinibreNonrealDensity n ‖z‖
    (Real.sqrt (2*(n : ℝ)) * |z.im|)

theorem realGinibreNonrealDensityAt_bound (n : ℕ) (z : ℂ)
    (hz : 1 ≤ ‖z‖) :
    0 ≤ realGinibreNonrealDensityAt n z ∧
    realGinibreNonrealDensityAt n z ≤
      (n : ℝ)/Real.pi * Real.exp (-(n : ℝ)*rate 2 ‖z‖) := by
  exact realGinibreNonrealDensity_bound n ‖z‖
    (Real.sqrt (2*(n : ℝ)) * |z.im|) hz (by positivity)

theorem realGinibreNonrealDensityAt_measurable (n : ℕ) :
    Measurable (realGinibreNonrealDensityAt n) := by
  unfold realGinibreNonrealDensityAt realGinibreNonrealDensity
    gaussianErfcCorrection ginibreExpPartial
  have herfc : Measurable (fun z : ℂ =>
      gaussianErfc (Real.sqrt (2*(n : ℝ)) * |z.im|)) :=
    gaussianErfc_measurable.comp (by fun_prop)
  fun_prop

#print axioms realGinibreNonrealDensityAt_bound
#print axioms realGinibreNonrealDensityAt_measurable
end SpectralRadiusUpperTail
