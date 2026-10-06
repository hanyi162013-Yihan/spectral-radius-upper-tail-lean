import SpectralRadiusUpperTail.HermitianEigenbasisEnergy

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma hermitian_minimum_le_energy {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (i : Fin n) (hi : ∀ j, hH.eigenvalues i ≤ hH.eigenvalues j)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1) :
    hH.eigenvalues i ≤ (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re := by
  let w := hH.eigenvectorBasis.repr v
  have he := hermitian_eigenbasis_energy H hH w
  simp only [w, LinearIsometryEquiv.symm_apply_apply] at he
  rw [he]
  have hw : ∑ j, ‖w j‖^2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, LinearIsometryEquiv.norm_map, hv]
    norm_num
  calc
    hH.eigenvalues i = ∑ j, hH.eigenvalues i*‖w j‖^2 := by rw [← Finset.mul_sum, hw, mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hi j) (sq_nonneg _))

lemma hermitian_exists_minimum {n : ℕ} (hn : 0 < n)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ∃ i : Fin n, ∀ j, hH.eigenvalues i ≤ hH.eigenvalues j := by
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ hH.eigenvalues
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

#print axioms hermitian_minimum_le_energy
#print axioms hermitian_exists_minimum
end SpectralRadiusUpperTail
