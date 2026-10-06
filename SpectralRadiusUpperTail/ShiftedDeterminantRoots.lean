import SpectralRadiusUpperTail.MatrixOperatorComparison
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.L2Operator

lemma shiftedDeterminant_roots {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Matrix.det (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A) =
      (A.charpoly.roots.map (fun w => z-w)).prod := by
  have he : z • (1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.scalar (Fin n) z := by
    ext i j
    simp [Matrix.scalar, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  rw [he, ← Matrix.eval_charpoly]
  exact (IsAlgClosed.splits A.charpoly).eval_eq_prod_roots_of_monic A.charpoly_monic z

lemma shiftedDeterminant_log_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (hz : ∀ w ∈ A.charpoly.roots, z ≠ w) :
    Real.log ‖Matrix.det (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A)‖ =
      (A.charpoly.roots.map (fun w => Real.log ‖z-w‖)).sum := by
  rw [shiftedDeterminant_roots]
  have hnorm : ‖(A.charpoly.roots.map (fun w => z-w)).prod‖ =
      (A.charpoly.roots.map (fun w => ‖z-w‖)).prod := by
    simpa [Multiset.map_map, Function.comp_def] using
      (map_multiset_prod (normHom : ℂ →*₀ ℝ).toMonoidHom (A.charpoly.roots.map (fun w => z-w)))
  rw [hnorm, Real.log_multiset_prod]
  · simp only [Multiset.map_map, Function.comp_def]
  · intro t ht
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp ht
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hz w hw))

lemma charpoly_root_norm_le_operator {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (w : ℂ) (hw : w ∈ A.charpoly.roots) :
    ‖w‖ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hs : w ∈ spectrum ℂ A := Matrix.mem_spectrum_of_isRoot_charpoly
    ((Polynomial.mem_roots A.charpoly_monic.ne_zero).mp hw)
  simpa only [Matrix.l2_opNorm_toEuclideanCLM] using spectrum.norm_le_norm_of_mem hs

#print axioms shiftedDeterminant_roots
#print axioms shiftedDeterminant_log_norm
#print axioms charpoly_root_norm_le_operator
end SpectralRadiusUpperTail
