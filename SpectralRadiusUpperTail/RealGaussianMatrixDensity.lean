import SpectralRadiusUpperTail.GaussianMatrixAbsoluteContinuity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

/-- The actual iid real Gaussian matrix law in fixed entry coordinates,
written as the normalized Frobenius Gaussian density. This is the input
measure for a future real Schur change-of-variables calculation. -/
theorem gaussianMatrixLaw_eq_normalizedFrobeniusDensity (n : ℕ) :
    gaussianMatrixLaw n =
      normalizedTilt (volume : Measure ((Fin n × Fin n) → ℝ))
        (fun x => ENNReal.ofReal
          (Real.exp (-(∑ ij : Fin n × Fin n, (x ij)^2)/2))) := by
  have he (x : (Fin n × Fin n) → ℝ) :
      Real.exp (-(∑ ij : Fin n × Fin n, (x ij)^2)/2) =
        ∏ ij : Fin n × Fin n,
          Real.exp (-(1/2 : ℝ)*(x ij)^2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    ring
  simp_rw [he]
  rw [volume_pi]
  change Measure.pi (fun _ : Fin n × Fin n => standardNormal) =
    normalizedTilt
      (Measure.pi (fun _ : Fin n × Fin n => (volume : Measure ℝ)))
      (fun x => ENNReal.ofReal
        (∏ ij : Fin n × Fin n,
          Real.exp (-(1/2 : ℝ)*(x ij)^2)))
  simp_rw [standardNormal_eq_normalizedTilt]
  exact (pi_normalizedTilt_ofReal
    (μ := fun _ : Fin n × Fin n => (volume : Measure ℝ))
    (f := fun _ x => Real.exp (-(1/2 : ℝ)*x^2))
    (fun _ => integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2))
    (fun _ _ => (Real.exp_pos _).le)
    (fun _ => integral_exp_pos
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)))).symm

#print axioms gaussianMatrixLaw_eq_normalizedFrobeniusDensity
end SpectralRadiusUpperTail
