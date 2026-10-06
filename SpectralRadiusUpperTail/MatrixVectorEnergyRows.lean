import SpectralRadiusUpperTail.ResidualGram

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma matrix_vector_energy_rows {n : ℕ} (x : Fin n → Fin n → ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.of x) v‖^2 =
      ∑ i, ‖∑ j, v j*x i j‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  congr 1
  funext i
  congr 2
  change ∑ j, x i j*v j = ∑ j, v j*x i j
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

lemma normalizedArray_opNorm {n : ℕ} (x : Fin n → Fin n → ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖ =
      (Real.sqrt (n : ℝ))⁻¹*‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.of x)‖ := by
  have he : normalizedArray x = (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) • Matrix.of x := by
    ext i j
    simp only [normalizedArray, one_div, Matrix.smul_apply, Matrix.of_apply,
      RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    rfl
  rw [he, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma normalizedArray_opNorm_square (n : ℕ) (hn : 0 < n) (x : Fin n → Fin n → ℂ) :
    (n : ℝ)*‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖^2 =
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.of x)‖^2 := by
  rw [normalizedArray_opNorm, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

#print axioms normalizedArray_opNorm_square
#print axioms matrix_vector_energy_rows
#print axioms normalizedArray_opNorm
end SpectralRadiusUpperTail
