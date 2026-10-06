import SpectralRadiusUpperTail.SphericalGaussianDeterminant
import SpectralRadiusUpperTail.MatrixSqrtEnergy
import SpectralRadiusUpperTail.MatrixSqrtDeterminant
import SpectralRadiusUpperTail.MatrixRealDeterminant

namespace SpectralRadiusUpperTail
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Metric
open scoped ENNReal

lemma real_sphere_quadratic_bound (n : ℕ) (hn : 0 < n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosSemidef) (hd : H.det ≠ 0) :
    (∫⁻ v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      ENNReal.ofReal (Real.exp (-(inner ℝ v.val (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) H v.val))))
      ∂haarSphereProbability (volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ENNReal.ofReal (Real.Gamma ((n : ℝ)/2+1)/Real.sqrt |H.det|) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hdet : LinearMap.det (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (CFC.sqrt H)).toLinearMap ≠ 0 := by
    rw [determinant_toEuclideanCLM]
    exact matrix_sqrt_det_ne_zero H hH hd
  have hh := spherical_gaussian_determinant_bound
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (CFC.sqrt H)).toLinearMap hdet
  change (∫⁻ v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    ENNReal.ofReal (Real.exp (-‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (CFC.sqrt H) v.val‖^2))
      ∂haarSphereProbability volume) ≤ _ at hh
  simp_rw [matrix_sqrt_energy H hH] at hh
  simp only [RCLike.re_to_real,determinant_toEuclideanCLM,abs_inv,real_matrix_sqrt_det_abs H hH] at hh
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  rw [hdim] at hh
  convert hh using 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  congr 1
  ring

#print axioms real_sphere_quadratic_bound
end SpectralRadiusUpperTail
