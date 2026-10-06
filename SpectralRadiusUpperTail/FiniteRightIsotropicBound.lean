import SpectralRadiusUpperTail.RectangularCoefficientExpansion
import SpectralRadiusUpperTail.RightColumnCoefficient
import SpectralRadiusUpperTail.MatrixResolventWoodbury

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finite_right_isotropic_error_bound (A : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Matrix (Fin n) ι ℂ) (p q : Fin n → ℂ)
    (hP : ∀ j, (∑ i, ‖P i j‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (z : ℂ) (hz : z ∈ resolventSet ℂ A) (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hR : ‖resolvent A z‖ ≤ M)
    (hsmall : ‖Pᴴ*resolvent A z*(A*Q)‖ ≤ 1/2)
    (hleft : ∀ i, ‖∑ a, star (p a)*(resolvent A z*A*Q) a i‖ ≤ δ) :
    z ∈ resolventSet ℂ (A*(1+Q*Pᴴ)) ∧
      ‖matrixCoefficient p q (resolvent (A*(1+Q*Pᴴ)) z)-z⁻¹*matrixCoefficient p q 1‖ ≤
      ‖matrixCoefficient p q (resolvent A z)-z⁻¹*matrixCoefficient p q 1‖+
        (Fintype.card ι : ℝ)^2*(2*δ*M) := by
  let S := (1-Pᴴ*resolvent A z*(A*Q))⁻¹
  have hb := matrix_neumann_inverse_bound (Pᴴ*resolvent A z*(A*Q)) hsmall
  have hw := matrix_resolvent_woodbury A (A*Q) Pᴴ z hz hb.1
  have he : A*(1+Q*Pᴴ) = A+(A*Q)*Pᴴ := by
    rw [Matrix.mul_add,Matrix.mul_one,Matrix.mul_assoc]
  rw [he]
  refine ⟨hw.1,?_⟩
  have hright := fun j => left_frame_resolvent_coefficient_bound A P q hP hq z M hR j
  have hc := rectangular_coefficient_bound p q (resolvent A z*A*Q) S (Pᴴ*resolvent A z)
    δ M hδ hM hleft hb.2 hright
  have hid : resolvent A z*(A*Q)*S*Pᴴ*resolvent A z =
      (resolvent A z*A*Q)*S*(Pᴴ*resolvent A z) := by simp only [Matrix.mul_assoc]
  change ‖matrixCoefficient p q (resolvent (A+(A*Q)*Pᴴ) z)-_‖ ≤ _
  rw [hw.2,matrixCoefficient_add]
  change ‖matrixCoefficient p q (resolvent A z)+
    matrixCoefficient p q (resolvent A z*(A*Q)*S*Pᴴ*resolvent A z)-_‖ ≤ _
  rw [hid]
  calc
    _ = ‖(matrixCoefficient p q (resolvent A z)-z⁻¹*matrixCoefficient p q 1)+
        matrixCoefficient p q ((resolvent A z*A*Q)*S*(Pᴴ*resolvent A z))‖ := by
      congr 1
      ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add (le_refl _) hc)

#print axioms finite_right_isotropic_error_bound
end SpectralRadiusUpperTail
