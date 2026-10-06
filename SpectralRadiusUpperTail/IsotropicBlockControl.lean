import SpectralRadiusUpperTail.MatrixCoefficientBlock
import SpectralRadiusUpperTail.IsotropicGoodEvent

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Euclidean operator control of a compressed resolvent block. -/
def matrixIsotropicBlockControl (A : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Matrix (Fin n) ι ℂ) (r ε : ℝ) : Prop :=
  ∀ z : ℂ, r ≤ ‖z‖ → z ∈ resolventSet ℂ A ∧
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
      (Pᴴ*resolvent A z*Q-z⁻¹ • (Pᴴ*Q))‖ < ε

lemma isotropic_block_of_entries (A : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Matrix (Fin n) ι ℂ) (r ε δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : (Fintype.card ι : ℝ)*δ < ε)
    (hinv : ∀ z : ℂ, r ≤ ‖z‖ → z ∈ resolventSet ℂ A)
    (h : ∀ i j, matrixIsotropicControl A (fun k => P k i) (fun k => Q k j) r δ) :
    matrixIsotropicBlockControl A P Q r ε := by
  intro z hz
  refine ⟨hinv z hz,lt_of_le_of_lt ?_ hsmall⟩
  exact matrixCoefficient_block_norm_le P Q (resolvent A z) z⁻¹ δ hδ
    (fun i j => ((h i j) z hz).2.le)

#print axioms matrixIsotropicBlockControl
#print axioms isotropic_block_of_entries
end SpectralRadiusUpperTail
