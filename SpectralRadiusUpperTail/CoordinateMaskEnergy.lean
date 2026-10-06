import SpectralRadiusUpperTail.GaussianProductReplacement
import SpectralRadiusUpperTail.LargeCoordinateSet

namespace SpectralRadiusUpperTail
open scoped BigOperators

noncomputable def coordinateMask {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℂ) (j : Fin n) : ℂ :=
  if j ∈ I then v j else 0

lemma coordinateMask_energy {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℂ) :
    (∑ j, ‖coordinateMask I v j‖^2) = I.sum (fun j => ‖v j‖^2) := by
  have he (j : Fin n) : ‖coordinateMask I v j‖^2 = if j ∈ I then ‖v j‖^2 else 0 := by
    by_cases hj : j ∈ I <;> simp [coordinateMask, hj]
  simp_rw [he]
  exact Finset.sum_ite_mem_eq I _

lemma coordinateMask_norm_le {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℂ) (j : Fin n) :
    ‖coordinateMask I v j‖ ≤ ‖v j‖ := by
  by_cases hj : j ∈ I <;> simp [coordinateMask, hj]

lemma coordinateMask_energy_le {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℂ) :
    (∑ j, ‖coordinateMask I v j‖^2) ≤ ∑ j, ‖v j‖^2 := by
  rw [coordinateMask_energy]
  exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖v j‖)

lemma coordinateMask_compl_energy {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℂ) :
    (∑ j, ‖coordinateMask I v j‖^2)+(∑ j, ‖coordinateMask Iᶜ v j‖^2) = ∑ j, ‖v j‖^2 := by
  rw [coordinateMask_energy, coordinateMask_energy, Finset.sum_add_sum_compl]

lemma selected_sum_split {n : ℕ} (I : Finset (Fin n)) (v x y : Fin n → ℂ) :
    (∑ j, v j*(if j ∈ I then x j else y j)) =
      (∑ j, coordinateMask I v j*x j)+(∑ j, coordinateMask Iᶜ v j*y j) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ I <;> simp [coordinateMask, hj]

lemma selected_cube_error_bound {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℂ)
    (C d : ℝ) (hC : 0 ≤ C) (hd : 0 ≤ d) (hv : ∑ j, ‖v j‖^2 ≤ 1)
    (hsmall : ∀ j, j ∉ I → ‖v j‖ ≤ d) :
    (∑ j, if j ∈ I then 0 else C*‖v j‖^3) ≤ C*d := by
  have he (j : Fin n) : (if j ∈ I then 0 else C*‖v j‖^3) = C*‖coordinateMask Iᶜ v j‖^3 := by
    by_cases hj : j ∈ I <;> simp [coordinateMask, hj]
  simp_rw [he]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left ?_ hC
  apply coefficient_cube_sum_le _ d hd ?_ ((coordinateMask_energy_le Iᶜ v).trans hv)
  intro j
  by_cases hj : j ∈ I
  · simpa [coordinateMask, hj] using hd
  · simpa [coordinateMask, hj] using hsmall j hj

#print axioms coordinateMask
#print axioms coordinateMask_energy
#print axioms coordinateMask_norm_le
#print axioms coordinateMask_energy_le
#print axioms coordinateMask_compl_energy
#print axioms selected_sum_split
#print axioms selected_cube_error_bound
end SpectralRadiusUpperTail
