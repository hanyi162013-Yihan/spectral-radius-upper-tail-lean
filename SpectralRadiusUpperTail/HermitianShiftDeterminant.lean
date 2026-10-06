import SpectralRadiusUpperTail.MatrixQuadraticShift
import Mathlib.Analysis.Matrix.Order

namespace SpectralRadiusUpperTail
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

lemma hermitian_cfc_determinant (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.IsHermitian)
    (f : ℝ → ℝ) : (cfc f H).det = ∏ i, ((f (hH.eigenvalues i)) : 𝕂) := by
  rw [hH.cfc_eq]
  simp [Matrix.IsHermitian.cfc, -Unitary.conjStarAlgAut_apply]

lemma hermitian_shift_determinant (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.IsHermitian)
    (s : ℝ) : (H+(s : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂)).det =
      ∏ i, ((hH.eigenvalues i+s : ℝ) : 𝕂) := by
  have he : cfc (fun t : ℝ => t+s) H = H+(s : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂) := by
    rw [cfc_add_const s (fun t : ℝ => t) H continuousOn_id hH.isSelfAdjoint,
      cfc_id' ℝ H hH.isSelfAdjoint]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one]
    ext i j
    exact RCLike.real_smul_eq_coe_mul s ((1 : Matrix (Fin n) (Fin n) 𝕂) i j)
  rw [← he]
  exact hermitian_cfc_determinant H hH _

lemma posSemidef_shift_det_norm (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.PosSemidef)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖(H+(s : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂)).det‖ =
      ∏ i, (hH.isHermitian.eigenvalues i+s) := by
  rw [hermitian_shift_determinant H hH.isHermitian, norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [RCLike.norm_ofReal, abs_of_nonneg (add_nonneg (hH.eigenvalues_nonneg i) hs)]

lemma posSemidef_shift_det_lower (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.PosSemidef)
    (s : ℝ) (hs : 0 ≤ s) :
    s^n ≤ ‖(H+(s : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂)).det‖ ∧
      ‖H.det‖ ≤ ‖(H+(s : 𝕂) • (1 : Matrix (Fin n) (Fin n) 𝕂)).det‖ := by
  rw [posSemidef_shift_det_norm H hH s hs]
  constructor
  · simpa using Finset.prod_le_prod (fun _ _ => hs)
      (fun i (_ : i ∈ Finset.univ) => le_add_of_nonneg_left (hH.eigenvalues_nonneg i))
  · have he := posSemidef_shift_det_norm H hH 0 le_rfl
    simp only [RCLike.ofReal_zero, zero_smul, add_zero] at he
    rw [he]
    exact Finset.prod_le_prod (fun i _ => hH.eigenvalues_nonneg i)
      (fun i _ => le_add_of_nonneg_right hs)

#print axioms hermitian_cfc_determinant
#print axioms hermitian_shift_determinant
#print axioms posSemidef_shift_det_norm
#print axioms posSemidef_shift_det_lower
end SpectralRadiusUpperTail
