import SpectralRadiusUpperTail.RealGaussianMatrixExplicitDensity
import SpectralRadiusUpperTail.RealSchurMixedGaussianWeight
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

/-- The unnormalized Gaussian weight of a finite square entry array. -/
noncomputable def realGaussianArrayWeight
    (ι : Type*) [Fintype ι] (x : (ι × ι) → ℝ) : ℝ :=
  Real.exp (-(∑ ij : ι × ι, (x ij)^2)/2)

theorem realGaussianArrayWeight_eq_matrixWeight
    (ι : Type*) [Fintype ι] (x : (ι × ι) → ℝ) :
    realGaussianArrayWeight ι x =
      realMatrixGaussianWeight ι (Matrix.of x.curry) := rfl

private theorem realGaussianArrayWeight_prod
    (ι : Type*) [Fintype ι] (x : (ι × ι) → ℝ) :
    realGaussianArrayWeight ι x =
      ∏ ij : ι × ι, Real.exp (-(1/2 : ℝ)*(x ij)^2) := by
  unfold realGaussianArrayWeight
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.mul_sum]
  ring

theorem realGaussianArrayWeight_integrable
    (ι : Type*) [Fintype ι] :
    Integrable (realGaussianArrayWeight ι)
      (volume : Measure ((ι × ι) → ℝ)) := by
  have heq : realGaussianArrayWeight ι =
      (fun x => ∏ ij : ι × ι,
        Real.exp (-(1/2 : ℝ)*(x ij)^2)) :=
    funext (realGaussianArrayWeight_prod ι)
  rw [heq]
  exact Integrable.fintype_prod
    (fun _ => integrable_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1/2))

theorem integral_realGaussianArrayWeight
    (ι : Type*) [Fintype ι] :
    (∫ x : (ι × ι) → ℝ, realGaussianArrayWeight ι x) =
      (Real.sqrt (2*Real.pi))^((Fintype.card ι)^2) := by
  simp_rw [realGaussianArrayWeight_prod]
  rw [integral_fintype_prod_volume_eq_prod
    (fun _ : ι × ι => fun x : ℝ =>
      Real.exp (-(1/2 : ℝ)*x^2))]
  have hscalar : (∫ x : ℝ,
      Real.exp (-(1/2 : ℝ)*x^2)) =
      Real.sqrt (2*Real.pi) := by
    rw [integral_gaussian]
    congr 1
    ring
  simpa only [Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, pow_two] using
      congrArg (fun t : ℝ => t^(Fintype.card ι * Fintype.card ι)) hscalar

/-- The genuine iid standard-Gaussian law on an arbitrary finite square
array has its explicit normalized Frobenius density. -/
theorem gaussianArrayLaw_eq_explicitDensity
    (ι : Type*) [Fintype ι] :
    Measure.pi (fun _ : ι × ι => standardNormal) =
      (volume : Measure ((ι × ι) → ℝ)).withDensity
        (fun x => ENNReal.ofReal
          (realGaussianArrayWeight ι x /
            (Real.sqrt (2*Real.pi))^((Fintype.card ι)^2))) := by
  have htilt :
      Measure.pi (fun _ : ι × ι => standardNormal) =
        normalizedTilt (volume : Measure ((ι × ι) → ℝ))
          (fun x => ENNReal.ofReal (realGaussianArrayWeight ι x)) := by
    simp_rw [realGaussianArrayWeight_prod]
    rw [volume_pi]
    simp_rw [standardNormal_eq_normalizedTilt]
    exact (pi_normalizedTilt_ofReal
      (μ := fun _ : ι × ι => (volume : Measure ℝ))
      (f := fun _ x => Real.exp (-(1/2 : ℝ)*x^2))
      (fun _ => integrable_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 1/2))
      (fun _ _ => (Real.exp_pos _).le)
      (fun _ => integral_exp_pos
        (integrable_exp_neg_mul_sq
          (by norm_num : (0 : ℝ) < 1/2)))).symm
  rw [htilt, normalizedTilt_ofReal_eq_density volume _
    (realGaussianArrayWeight_integrable ι)
    (fun x => (Real.exp_pos _).le)
    (integral_exp_pos (realGaussianArrayWeight_integrable ι))]
  simp only [integral_realGaussianArrayWeight]

#print axioms realGaussianArrayWeight_integrable
#print axioms integral_realGaussianArrayWeight
#print axioms gaussianArrayLaw_eq_explicitDensity
end SpectralRadiusUpperTail
