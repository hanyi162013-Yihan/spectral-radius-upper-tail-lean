import SpectralRadiusUpperTail.DescendingHSBudget
import SpectralRadiusUpperTail.GaussianMeanRankOne

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.Frobenius

lemma real_descendingTriangular_HSsq_le {n : ℕ} (η : ℝ) (hη : 0 < η)
    (v : Fin n → ℝ) (hv : (∑ i, ‖v i‖^2) = 1) :
    matrixHSsq ((descendingTriangularInverse η v).map Complex.ofRealHom-1) ≤ 1/(2*η^2) := by
  have hh := descendingTriangularInverse_norm_sq_le η hη v hv
  rw [frobenius_norm_sq_eq_sum] at hh
  have he : (descendingTriangularInverse η v).map Complex.ofRealHom-1 =
      (descendingTriangularInverse η v-1).map Complex.ofRealHom := by
    simp [Matrix.map_sub,Matrix.map_one]
  rw [he,matrixHSsq]
  simpa only [Matrix.map_apply,Complex.ofRealHom_eq_coe,Complex.norm_real] using hh

lemma real_descendingTriangular_HS_budget (η : ℝ) (hη : 0 < η)
    (v : (n : ℕ) → Fin n → ℝ) (hv : ∀ n, 0 < n → (∑ i, ‖v n i‖^2) = 1) :
    ∀ n, matrixHSsq ((descendingTriangularInverse η (v n)).map Complex.ofRealHom-1) ≤
      (1+Real.sqrt (1/(2*η^2)))^2 := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [matrixHSsq,Finset.univ_eq_empty,Finset.sum_empty]
    positivity
  · have hh := real_descendingTriangular_HSsq_le η hη (v n) (hv n (Nat.pos_of_ne_zero hn))
    have hs : 0 ≤ 1/(2*η^2) := by positivity
    have he := Real.sq_sqrt hs
    nlinarith [Real.sqrt_nonneg (1/(2*η^2))]

lemma real_unit_energy_complexify {n : ℕ} (v : Fin n → ℝ) :
    (∑ i, ‖(v i : ℂ)‖^2) = ∑ i, ‖v i‖^2 := by simp only [Complex.norm_real]

lemma real_gaussianMeanMatrix_rankOne {n : ℕ} (η : ℝ) (hη : 0 < η) (b : ℝ)
    (v : ℕ → ℝ) (hn : 0 < n) (hv : (∑ i : Fin n, ‖v i.val‖^2) = 1) :
    (gaussianMeanMatrix v (rankOneTiltTarget η b v) η).map Complex.ofRealHom =
      (b : ℂ) • Matrix.vecMulVec (fun i : Fin n => (v i.val : ℂ))
        (star (fun i : Fin n => (v i.val : ℂ))) := by
  rw [gaussianMeanMatrix_rankOne η hη b v hn hv]
  ext i j
  simp [Matrix.vecMulVec_apply,Matrix.smul_apply,smul_eq_mul]

#print axioms real_descendingTriangular_HSsq_le
#print axioms real_descendingTriangular_HS_budget
#print axioms real_unit_energy_complexify
#print axioms real_gaussianMeanMatrix_rankOne
end SpectralRadiusUpperTail
