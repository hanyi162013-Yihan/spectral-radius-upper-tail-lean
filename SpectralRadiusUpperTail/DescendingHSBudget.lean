import SpectralRadiusUpperTail.ReversedMatrix
import SpectralRadiusUpperTail.MatrixGramEigenbasis

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius

lemma descendingTriangular_HSsq_le {n : ℕ} (η : ℝ) (hη : 0 < η)
    (v : Fin n → ℂ) (hv : (∑ i, ‖v i‖^2) = 1) :
    matrixHSsq (descendingTriangularInverse η v-1) ≤ 1/(2*η^2) := by
  rw [matrixHSsq,← frobenius_norm_sq_eq_sum]
  exact descendingTriangularInverse_norm_sq_le η hη v hv

lemma descendingTriangular_HS_budget (η : ℝ) (hη : 0 < η)
    (v : (n : ℕ) → Fin n → ℂ) (hv : ∀ n, 0 < n → (∑ i, ‖v n i‖^2) = 1) :
    ∀ n, matrixHSsq (descendingTriangularInverse η (v n)-1) ≤
      (1+Real.sqrt (1/(2*η^2)))^2 := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [matrixHSsq,Finset.univ_eq_empty,Finset.sum_empty]
    positivity
  · have hh := descendingTriangular_HSsq_le η hη (v n) (hv n (Nat.pos_of_ne_zero hn))
    have hs : 0 ≤ 1/(2*η^2) := by positivity
    have he := Real.sq_sqrt hs
    nlinarith [Real.sqrt_nonneg (1/(2*η^2))]

#print axioms descendingTriangular_HSsq_le
#print axioms descendingTriangular_HS_budget
end SpectralRadiusUpperTail
