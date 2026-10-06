import SpectralRadiusUpperTail.HermitianEigenbasisEnergy
import Mathlib.Analysis.Convex.Jensen

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma orthonormalBasis_coefficient_squares {n : ℕ}
    (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (v : EuclideanSpace ℂ (Fin n)) : ∑ i, ‖e.repr v i‖^2 = ‖v‖^2 := by
  rw [← EuclideanSpace.norm_sq_eq, e.repr.norm_map]

lemma orthonormalBasis_overlap_column {n : ℕ}
    (e d : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (j : Fin n) :
    ∑ i, ‖d.repr (e i) j‖^2 = 1 := by
  have he : ∀ i, ‖d.repr (e i) j‖ = ‖e.repr (d j) i‖ := by
    intro i
    simp only [OrthonormalBasis.repr_apply_apply]
    exact norm_inner_symm _ _
  simp_rw [he]
  rw [orthonormalBasis_coefficient_squares, d.orthonormal.1 j]
  norm_num

lemma hermitian_rayleigh_jensen {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1) :
    f ((inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re) ≤
      ∑ j, ‖hH.eigenvectorBasis.repr v j‖^2*f (hH.eigenvalues j) := by
  have henergy := hermitian_eigenbasis_energy H hH (hH.eigenvectorBasis.repr v)
  simp only [LinearIsometryEquiv.symm_apply_apply] at henergy
  have hsum : ∑ j, ‖hH.eigenvectorBasis.repr v j‖^2 = 1 := by
    rw [orthonormalBasis_coefficient_squares, hv]
    norm_num
  have hj := hf.map_sum_le (t := Finset.univ)
    (w := fun j => ‖hH.eigenvectorBasis.repr v j‖^2)
    (p := hH.eigenvalues) (fun j _ => sq_nonneg _) hsum (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, mul_comm, henergy] using hj

lemma hermitian_basis_jensen {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (∑ i, f ((inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) H (e i))).re)) ≤
      ∑ j, f (hH.eigenvalues j) := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    hermitian_rayleigh_jensen H hH f hf (e i) (e.orthonormal.1 i))
  apply hh.trans_eq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul, orthonormalBasis_overlap_column, one_mul]

#print axioms orthonormalBasis_coefficient_squares
#print axioms orthonormalBasis_overlap_column
#print axioms hermitian_rayleigh_jensen
#print axioms hermitian_basis_jensen
end SpectralRadiusUpperTail
