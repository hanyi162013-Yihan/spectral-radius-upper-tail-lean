import SpectralRadiusUpperTail.GaussianNormSquareExponential
import SpectralRadiusUpperTail.StandardGaussianRadialDensity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory

lemma stdComplexGaussian_normSquare_exponential :
    (stdGaussian ℂ).map (fun z : ℂ => ‖z‖^2) = expMeasure (1/2) := by
  rw [stdGaussian_eq_radial_normalizedTilt]
  exact gaussian_normSquare_exponential (volume : Measure ℂ) Complex.finrank_real_complex (1/2) (by norm_num)

/-- Independent complex Gaussian coordinates have independent exponential squared moduli. -/
lemma stdComplexGaussian_pi_normSquare_exponential (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian ℂ)).map
      (fun z : Fin m → ℂ => fun i => ‖z i‖^2) =
        Measure.pi (fun _ : Fin m => expMeasure (1/2)) := by
  rw [Measure.pi_map_pi (fun _ : Fin m => (show Measurable (fun z : ℂ => ‖z‖^2) by fun_prop).aemeasurable)]
  simp only [stdComplexGaussian_normSquare_exponential]

#print axioms stdComplexGaussian_normSquare_exponential
#print axioms stdComplexGaussian_pi_normSquare_exponential
end SpectralRadiusUpperTail
