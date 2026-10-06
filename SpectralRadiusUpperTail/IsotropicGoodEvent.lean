import SpectralRadiusUpperTail.UniformCoefficientApproximation
import SpectralRadiusUpperTail.MatrixExteriorPowerBound

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The uniform isotropic statement refers to each prescribed deterministic pair. -/
def matrixIsotropicControl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (p q : Fin n → ℂ) (r ε : ℝ) : Prop :=
  ∀ z : ℂ, r ≤ ‖z‖ → z ∈ resolventSet ℂ A ∧
    ‖matrixCoefficient p q (resolvent A z)-z⁻¹*matrixCoefficient p q 1‖ < ε

lemma matrixIsotropicControl_of_finite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (p q : Fin n → ℂ) (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (r C ε : ℝ) (hr : 1 ≤ r) (hε : 0 < ε) (k : ℕ)
    (htail : (k+3 : ℝ)*C/r^(k+1) ≤ ε/2)
    (hbase : matrixExteriorControl A r C)
    (hpower : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A^(k+1))‖ ≤ k+3)
    (hcoeff : ∀ j ∈ Finset.range k,
      ‖matrixCoefficient p q (A^(j+1))‖ ≤ ε/(4*(k+1))) :
    matrixIsotropicControl A p q r ε := by
  intro z hz
  refine ⟨(hbase z hz).1,?_⟩
  have hh := resolvent_coefficient_error_le p q hp hq A z k r (k+3) C hr hz
    (hbase z hz).1 hpower (hbase z hz).2
  have hs : (∑ j ∈ Finset.range k, ‖matrixCoefficient p q (A^(j+1))‖) ≤
      (k : ℝ)*(ε/(4*(k+1))) := by
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using
      Finset.sum_le_sum hcoeff
  have hd : 0 < (4*(k+1 : ℝ)) := by positivity
  have he : (k+1 : ℝ)*(ε/(4*(k+1))) = ε/4 := by field_simp
  have hδ : 0 ≤ ε/(4*(k+1 : ℝ)) := by positivity
  have hsmall : (k : ℝ)*(ε/(4*(k+1))) ≤ ε/4 := by nlinarith
  linarith

#print axioms matrixIsotropicControl
#print axioms matrixIsotropicControl_of_finite
end SpectralRadiusUpperTail
