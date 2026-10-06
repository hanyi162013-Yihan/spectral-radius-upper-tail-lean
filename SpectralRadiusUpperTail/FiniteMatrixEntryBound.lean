import SpectralRadiusUpperTail.MatrixOperatorComparison

namespace SpectralRadiusUpperTail
open WithLp
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finite_operator_norm_le_frobenius (A : Matrix ι ι ℂ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  have he : A * Matrix.replicateCol (Fin 1) (ofLp x) =
      Matrix.replicateCol (Fin 1) (A.mulVec (ofLp x)) := by ext i j; rfl
  have hh := Matrix.frobenius_norm_mul A (Matrix.replicateCol (Fin 1) (ofLp x))
  have hcol (y : ι → ℂ) : ‖Matrix.replicateCol (Fin 1) y‖ = ‖toLp 2 y‖ := by
    convert! Matrix.frobenius_norm_replicateCol (ι := Fin 1) y using 1
  rw [he,hcol,hcol,← Matrix.toEuclideanCLM_toLp] at hh
  simpa only [toLp_ofLp] using hh

lemma finite_matrix_frobenius_sq (A : Matrix ι ι ℂ) :
    ‖A‖^2 = ∑ i, ∑ j, ‖A i j‖^2 := by
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]
  exact Real.sq_sqrt (by positivity)

lemma finite_matrix_operator_entry_bound (A : Matrix ι ι ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ i j, ‖A i j‖ ≤ δ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A‖ ≤ (Fintype.card ι : ℝ)*δ := by
  apply (finite_operator_norm_le_frobenius A).trans
  have hh : ‖A‖^2 ≤ ((Fintype.card ι : ℝ)*δ)^2 := by
    rw [finite_matrix_frobenius_sq]
    calc
      _ ≤ ∑ _i : ι, ∑ _j : ι, δ^2 := Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2))
      _ = _ := by simp; ring
  have hn : 0 ≤ (Fintype.card ι : ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ
  nlinarith [norm_nonneg A]

#print axioms finite_operator_norm_le_frobenius
#print axioms finite_matrix_frobenius_sq
#print axioms finite_matrix_operator_entry_bound
end SpectralRadiusUpperTail
