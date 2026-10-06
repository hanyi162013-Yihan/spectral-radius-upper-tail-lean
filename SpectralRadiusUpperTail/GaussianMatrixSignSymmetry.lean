import SpectralRadiusUpperTail.MatrixMoments
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory

/-- Negating every entry preserves the finite iid standard Gaussian matrix
law. This is a finite-dimensional fact independent of Schur coordinates. -/
theorem gaussianMatrixLaw_map_neg (n : ℕ) :
    (gaussianMatrixLaw n).map
      (fun x : (Fin n × Fin n) → ℝ => -x) = gaussianMatrixLaw n := by
  have hsingle : standardNormal.map (fun x : ℝ => -x) = standardNormal := by
    simp [standardNormal, gaussianReal_map_neg]
  change (Measure.pi (fun _ : Fin n × Fin n => standardNormal)).map
      (fun x : (Fin n × Fin n) → ℝ => -x) =
    Measure.pi (fun _ : Fin n × Fin n => standardNormal)
  rw [show (fun x : (Fin n × Fin n) → ℝ => -x) =
      (fun x i => -(x i)) from rfl]
  rw [Measure.pi_map_pi (fun _ => measurable_neg.aemeasurable)]
  simp [hsingle]

#print axioms gaussianMatrixLaw_map_neg
end SpectralRadiusUpperTail
