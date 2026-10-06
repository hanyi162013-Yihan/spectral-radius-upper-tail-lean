import SpectralRadiusUpperTail.MatrixCoefficient

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix
variable {n : ℕ} {ι : Type*}

lemma vector_inv_scale_energy (p : Fin n → ℂ) (C : ℝ) (hC : 0 < C)
    (hp : (∑ i, ‖p i‖^2) ≤ C^2) :
    (∑ i, ‖(C : ℂ)⁻¹*p i‖^2) ≤ 1 := by
  have hne : C ≠ 0 := ne_of_gt hC
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC,mul_pow]
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg C⁻¹)
  have he : (C⁻¹)^2*C^2 = 1 := by field_simp
  exact hh.trans_eq he

lemma matrix_inv_scale_column_energy (Q : Matrix (Fin n) ι ℂ) (C : ℝ) (hC : 0 < C)
    (hQ : ∀ j, (∑ i, ‖Q i j‖^2) ≤ C^2) :
    ∀ j, (∑ i, ‖(((C : ℂ)⁻¹) • Q) i j‖^2) ≤ 1 := by
  intro j
  exact vector_inv_scale_energy (fun i => Q i j) C hC (hQ j)

#print axioms vector_inv_scale_energy
#print axioms matrix_inv_scale_column_energy
end SpectralRadiusUpperTail
