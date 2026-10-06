import SpectralRadiusUpperTail.MatrixRealDeterminant
import SpectralRadiusUpperTail.MatrixVectorEnergyRows

namespace SpectralRadiusUpperTail
open scoped BigOperators

noncomputable def positiveDiagonalRoot {n : ℕ} (h : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (Real.sqrt (h i) : ℂ))

lemma positiveDiagonalRoot_energy {n : ℕ} (h : Fin n → ℝ) (hh : ∀ i, 0 ≤ h i)
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (positiveDiagonalRoot h) v‖^2 = ∑ i, h i*‖v i‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i, ‖(Matrix.diagonal (fun j => (Real.sqrt (h j) : ℂ))).mulVec (WithLp.ofLp v) i‖^2) = _
  simp only [Matrix.mulVec_diagonal, Pi.mul_apply, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hh _)]

lemma positiveDiagonalRoot_det_norm_sq {n : ℕ} (h : Fin n → ℝ) (hh : ∀ i, 0 ≤ h i) :
    ‖(positiveDiagonalRoot h).det‖^2 = ∏ i, h i := by
  unfold positiveDiagonalRoot
  rw [Matrix.det_diagonal, norm_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hh i)]

lemma positive_weighted_unit_energy {n : ℕ} (h : Fin n → ℝ) (hh : ∀ i, 0 < h i)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1) : 0 < ∑ i, h i*‖v i‖^2 := by
  have he : ∑ i, ‖v i‖^2 = 1 := by rw [← EuclideanSpace.norm_sq_eq, hv]; norm_num
  obtain ⟨i, hi, hvi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖v i‖)).mp
    (by rw [he]; norm_num : 0 < ∑ i, ‖v i‖^2)
  exact (Finset.sum_pos_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
    mul_nonneg (hh j).le (sq_nonneg ‖v j‖))).mpr ⟨i, hi, mul_pos (hh i) hvi⟩

#print axioms positiveDiagonalRoot
#print axioms positiveDiagonalRoot_energy
#print axioms positiveDiagonalRoot_det_norm_sq
#print axioms positive_weighted_unit_energy
end SpectralRadiusUpperTail
