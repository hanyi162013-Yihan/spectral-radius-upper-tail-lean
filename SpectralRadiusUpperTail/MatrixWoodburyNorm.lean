import SpectralRadiusUpperTail.MatrixResolventWoodbury

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.L2Operator
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

lemma rectangular_woodbury_correction_bound (R : Matrix n n ℂ) (U : Matrix n ι ℂ)
    (S : Matrix ι ι ℂ) (V : Matrix ι n ℂ)
    (M K L : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hR : ‖R‖ ≤ M) (hU : ‖U‖ ≤ K) (hS : ‖S‖ ≤ 2) (hV : ‖V‖ ≤ L) :
    ‖R*U*S*V*R‖ ≤ 2*M^2*K*L := by
  have h1 : ‖R*U‖ ≤ M*K := (Matrix.l2_opNorm_mul R U).trans
    (mul_le_mul hR hU (norm_nonneg U) hM)
  have h2 : ‖R*U*S‖ ≤ (M*K)*2 := (Matrix.l2_opNorm_mul (R*U) S).trans
    (mul_le_mul h1 hS (norm_nonneg S) (mul_nonneg hM hK))
  have h3 : ‖R*U*S*V‖ ≤ ((M*K)*2)*L := (Matrix.l2_opNorm_mul (R*U*S) V).trans
    (mul_le_mul h2 hV (norm_nonneg V) (by positivity))
  have h4 := (Matrix.l2_opNorm_mul (R*U*S*V) R).trans
    (mul_le_mul h3 hR (norm_nonneg R) (by positivity))
  exact h4.trans_eq (by ring)

lemma matrix_woodbury_norm_bound (A : Matrix n n ℂ) (U : Matrix n ι ℂ) (V : Matrix ι n ℂ)
    (z : ℂ) (hz : z ∈ resolventSet ℂ A)
    (M K L : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hR : ‖resolvent A z‖ ≤ M) (hU : ‖U‖ ≤ K) (hV : ‖V‖ ≤ L)
    (hsmall : ‖V*resolvent A z*U‖ ≤ 1/2) :
    z ∈ resolventSet ℂ (A+U*V) ∧ ‖resolvent (A+U*V) z‖ ≤ M+2*M^2*K*L := by
  have hb := matrix_neumann_inverse_bound (V*resolvent A z*U) hsmall
  have hw := matrix_resolvent_woodbury A U V z hz hb.1
  refine ⟨hw.1,?_⟩
  rw [hw.2]
  exact (norm_add_le _ _).trans (add_le_add hR
    (rectangular_woodbury_correction_bound (resolvent A z) U _ V M K L hM hK hL hR hU hb.2 hV))

#print axioms rectangular_woodbury_correction_bound
#print axioms matrix_woodbury_norm_bound
end SpectralRadiusUpperTail
