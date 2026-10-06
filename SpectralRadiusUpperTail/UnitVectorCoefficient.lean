import SpectralRadiusUpperTail.MatrixCoefficient

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix
variable {n : ℕ}

lemma matrixCoefficient_unit_self (v : Fin n → ℂ) (hv : (∑ i, ‖v i‖^2) = 1) :
    matrixCoefficient v v 1 = 1 := by
  rw [matrixCoefficient_eq_sum,Matrix.one_mulVec]
  have he (i : Fin n) : star (v i)*v i = ((‖v i‖^2 : ℝ) : ℂ) := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp only [he]
  rw [← Complex.ofReal_sum,hv]
  rfl

#print axioms matrixCoefficient_unit_self
end SpectralRadiusUpperTail
