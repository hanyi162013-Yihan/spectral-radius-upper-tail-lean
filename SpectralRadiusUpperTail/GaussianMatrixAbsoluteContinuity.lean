import SpectralRadiusUpperTail.GaussianProductDensity
import SpectralRadiusUpperTail.MatrixMoments
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

/-- The actual iid real Gaussian matrix law has a density with respect to
finite-dimensional Lebesgue measure. The exact density is unnecessary for
excluding polynomial exceptional loci. -/
theorem gaussianMatrixLaw_absolutelyContinuous_volume (n : ℕ) :
    gaussianMatrixLaw n ≪
      (volume : Measure ((Fin n × Fin n) → ℝ)) := by
  let μ0 : Measure ((Fin n × Fin n) → ℝ) :=
    Measure.pi (fun _ : Fin n × Fin n => (volume : Measure ℝ))
  let w : ((Fin n × Fin n) → ℝ) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal
      (∏ ij, Real.exp (-(1/2 : ℝ)*(x ij)^2))
  have hpi := pi_normalizedTilt_ofReal
    (μ := fun _ : Fin n × Fin n => (volume : Measure ℝ))
    (f := fun _ x => Real.exp (-(1/2 : ℝ)*x^2))
    (fun _ => integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2))
    (fun _ _ => (Real.exp_pos _).le)
    (fun _ => integral_exp_pos
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)))
  have hgauss : gaussianMatrixLaw n = normalizedTilt μ0 w := by
    change Measure.pi (fun _ : Fin n × Fin n => standardNormal) =
      normalizedTilt μ0 w
    simp_rw [standardNormal_eq_normalizedTilt]
    exact hpi.symm
  rw [hgauss, normalizedTilt]
  change μ0.withDensity (fun x => w x / ∫⁻ y, w y ∂μ0) ≪
      (volume : Measure ((Fin n × Fin n) → ℝ))
  rw [show μ0 = (volume : Measure ((Fin n × Fin n) → ℝ)) from
    (volume_pi (ι := Fin n × Fin n)).symm]
  exact withDensity_absolutelyContinuous _ _

#print axioms gaussianMatrixLaw_absolutelyContinuous_volume
end SpectralRadiusUpperTail
