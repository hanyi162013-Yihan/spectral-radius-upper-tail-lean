import SpectralRadiusUpperTail.MatrixCoefficient

namespace SpectralRadiusUpperTail
open WithLp
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

lemma complex_vector_energy_split (v : ι → ℂ) :
    ‖toLp 2 v‖^2 = ‖toLp 2 (fun i => (v i).re)‖^2+‖toLp 2 (fun i => (v i).im)‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Complex.normSq_apply,sq] using (Complex.sq_norm (v i))

lemma real_matrix_complex_mulVec_re {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℂ) :
    (fun i => (((A.map Complex.ofRealHom).mulVec v) i).re) = A.mulVec (fun i => (v i).re) := by
  funext i
  simp [Matrix.mulVec,dotProduct,Complex.re_sum,Complex.mul_re]

lemma real_matrix_complex_mulVec_im {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℂ) :
    (fun i => (((A.map Complex.ofRealHom).mulVec v) i).im) = A.mulVec (fun i => (v i).im) := by
  funext i
  simp [Matrix.mulVec,dotProduct,Complex.im_sum,Complex.mul_im]

#print axioms complex_vector_energy_split
#print axioms real_matrix_complex_mulVec_re
#print axioms real_matrix_complex_mulVec_im
end SpectralRadiusUpperTail
