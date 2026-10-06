import SpectralRadiusUpperTail.GramEigenvalueLower
import SpectralRadiusUpperTail.HermitianMinimumEnergy

namespace SpectralRadiusUpperTail
open scoped BigOperators ComplexOrder MatrixOrder

lemma hermitian_energy_le_maximum {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (i : Fin n) (hi : ∀ j, hH.eigenvalues j ≤ hH.eigenvalues i)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1) :
    (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re ≤ hH.eigenvalues i := by
  let w := hH.eigenvectorBasis.repr v
  have he := hermitian_eigenbasis_energy H hH w
  simp only [w, LinearIsometryEquiv.symm_apply_apply] at he
  rw [he]
  have hw : ∑ j, ‖w j‖^2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, LinearIsometryEquiv.norm_map, hv]
    norm_num
  calc
    _ ≤ ∑ j, hH.eigenvalues i*‖w j‖^2 :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hi j) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum, hw, mul_one]

lemma gram_maximum_opNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hi : ∀ j, (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j ≤
      (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖^2 ≤
      (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i := by
  let H := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  have hh : 0 ≤ H.eigenvalues i := by rw [gram_eigenvalue_energy]; positivity
  have hb : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ Real.sqrt (H.eigenvalues i) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro v hv
    have he := hermitian_energy_le_maximum (A.conjTranspose*A) H i hi v hv
    have heg : (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) (A.conjTranspose*A) v)).re =
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A v‖^2 := by
      convert! matrix_gram_energy A v using 1
    rw [heg] at he
    exact (Real.le_sqrt (norm_nonneg _) hh).mpr he
  have hs := Real.sq_sqrt hh
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖^2 ≤ H.eigenvalues i
  nlinarith [mul_self_le_mul_self (norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) A)) hb]

lemma gram_exists_maximum {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ i : Fin n, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖^2 ≤
      (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
  exact ⟨i, gram_maximum_opNorm A i (fun j => hi j (Finset.mem_univ j))⟩

#print axioms hermitian_energy_le_maximum
#print axioms gram_maximum_opNorm
#print axioms gram_exists_maximum
end SpectralRadiusUpperTail
