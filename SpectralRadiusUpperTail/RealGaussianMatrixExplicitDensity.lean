import SpectralRadiusUpperTail.RealGaussianMatrixDensity
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

noncomputable def realGaussianMatrixWeight (n : ℕ)
    (x : (Fin n × Fin n) → ℝ) : ℝ :=
  Real.exp (-(∑ ij : Fin n × Fin n, (x ij)^2)/2)

private lemma realGaussianMatrixWeight_prod (n : ℕ)
    (x : (Fin n × Fin n) → ℝ) :
    realGaussianMatrixWeight n x =
      ∏ ij : Fin n × Fin n,
        Real.exp (-(1/2 : ℝ)*(x ij)^2) := by
  unfold realGaussianMatrixWeight
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.mul_sum]
  ring

theorem realGaussianMatrixWeight_integrable (n : ℕ) :
    Integrable (realGaussianMatrixWeight n)
      (volume : Measure ((Fin n × Fin n) → ℝ)) := by
  have heq : realGaussianMatrixWeight n =
      (fun x => ∏ ij : Fin n × Fin n,
        Real.exp (-(1/2 : ℝ)*(x ij)^2)) :=
    funext (realGaussianMatrixWeight_prod n)
  rw [heq]
  exact Integrable.fintype_prod
    (fun _ => integrable_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1/2))

theorem integral_realGaussianMatrixWeight (n : ℕ) :
    (∫ x : (Fin n × Fin n) → ℝ,
      realGaussianMatrixWeight n x) =
      (Real.sqrt (2*Real.pi))^(n*n) := by
  simp_rw [realGaussianMatrixWeight_prod]
  rw [integral_fintype_prod_volume_eq_prod
    (fun _ : Fin n × Fin n =>
      fun x : ℝ => Real.exp (-(1/2 : ℝ)*x^2))]
  have hscalar : (∫ x : ℝ,
      Real.exp (-(1/2 : ℝ)*x^2)) =
      Real.sqrt (2*Real.pi) := by
    rw [integral_gaussian]
    congr 1
    ring
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin] using
      congrArg (fun t : ℝ => t^(n*n)) hscalar

theorem gaussianMatrixLaw_eq_explicitDensity (n : ℕ) :
    gaussianMatrixLaw n =
      (volume : Measure ((Fin n × Fin n) → ℝ)).withDensity
        (fun x => ENNReal.ofReal
          (realGaussianMatrixWeight n x /
            (Real.sqrt (2*Real.pi))^(n*n))) := by
  rw [gaussianMatrixLaw_eq_normalizedFrobeniusDensity]
  change normalizedTilt
      (volume : Measure ((Fin n × Fin n) → ℝ))
      (fun x => ENNReal.ofReal (realGaussianMatrixWeight n x)) = _
  rw [normalizedTilt_ofReal_eq_density volume _
    (realGaussianMatrixWeight_integrable n)
    (fun x => (Real.exp_pos _).le)
    (integral_exp_pos (realGaussianMatrixWeight_integrable n))]
  simp only [integral_realGaussianMatrixWeight]

#print axioms realGaussianMatrixWeight_integrable
#print axioms integral_realGaussianMatrixWeight
#print axioms gaussianMatrixLaw_eq_explicitDensity
end SpectralRadiusUpperTail
