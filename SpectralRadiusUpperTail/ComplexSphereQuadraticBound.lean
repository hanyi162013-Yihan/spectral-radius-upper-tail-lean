import SpectralRadiusUpperTail.SphericalGaussianDeterminant
import SpectralRadiusUpperTail.MatrixSqrtEnergy
import SpectralRadiusUpperTail.MatrixSqrtDeterminant
import SpectralRadiusUpperTail.MatrixRealDeterminant

namespace SpectralRadiusUpperTail
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Metric
open scoped ENNReal

lemma complex_sphere_quadratic_bound (n : ℕ) (hn : 0 < n)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (hd : H.det ≠ 0) :
    (∫⁻ v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
      ENNReal.ofReal (Real.exp (-(inner ℂ v.val (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) H v.val)).re))
      ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))) ≤
        ENNReal.ofReal ((n.factorial : ℝ)/‖H.det‖) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hdet : LinearMap.det ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (CFC.sqrt H)).toLinearMap.restrictScalars ℝ) ≠ 0 := by
    rw [complex_real_determinant,matrix_sqrt_det_norm_square H hH]
    exact norm_ne_zero_iff.mpr hd
  have hh := spherical_gaussian_determinant_bound
    (volume : Measure (EuclideanSpace ℂ (Fin n)))
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (CFC.sqrt H)).toLinearMap.restrictScalars ℝ) hdet
  change (∫⁻ v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1,
    ENNReal.ofReal (Real.exp (-‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (CFC.sqrt H) v.val‖^2))
      ∂haarSphereProbability volume) ≤ _ at hh
  simp_rw [matrix_sqrt_energy H hH] at hh
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2*n := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin n))]
    simp
  rw [complex_real_determinant,matrix_sqrt_det_norm_square H hH,hdim] at hh
  have hnalg : ((2*n : ℕ) : ℝ)/2+1 = (n : ℝ)+1 := by push_cast; ring
  rw [hnalg,Real.Gamma_nat_eq_factorial,abs_inv,abs_of_nonneg (norm_nonneg _)] at hh
  simp only [RCLike.re_eq_complex_re] at hh
  convert hh using 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))]
  congr 1
  ring

#print axioms complex_sphere_quadratic_bound
end SpectralRadiusUpperTail
