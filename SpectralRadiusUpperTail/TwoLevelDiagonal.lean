import SpectralRadiusUpperTail.PositiveDiagonalEnergy

namespace SpectralRadiusUpperTail
open scoped BigOperators

noncomputable def twoLevelDiagonal {n : ℕ} (I : Finset (Fin n)) (c : ℝ) (j : Fin n) : ℝ :=
  if j ∈ I then c else c+1

lemma twoLevelDiagonal_pos {n : ℕ} (I : Finset (Fin n)) (c : ℝ) (hc : 0 < c) (j : Fin n) :
    0 < twoLevelDiagonal I c j := by unfold twoLevelDiagonal; split_ifs <;> linarith

lemma twoLevelDiagonal_product {n : ℕ} (I : Finset (Fin n)) (c : ℝ) :
    (∏ j, twoLevelDiagonal I c j) = c^I.card*(c+1)^(n-I.card) := by
  rw [← Finset.prod_mul_prod_compl I]
  have hI : I.prod (twoLevelDiagonal I c) = c^I.card := by
    calc
      _ = I.prod (fun _ => c) := Finset.prod_congr rfl (fun j hj => if_pos hj)
      _ = _ := by simp
  have hJ : Iᶜ.prod (twoLevelDiagonal I c) = (c+1)^(n-I.card) := by
    calc
      _ = Iᶜ.prod (fun _ => c+1) := Finset.prod_congr rfl (fun j hj => if_neg (Finset.mem_compl.mp hj))
      _ = _ := by simp [Finset.card_compl]
  rw [hI, hJ]

lemma twoLevelDiagonal_energy {n : ℕ} (I : Finset (Fin n)) (c : ℝ)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1) :
    (∑ j, twoLevelDiagonal I c j*‖v j‖^2) = c+Iᶜ.sum (fun j => ‖v j‖^2) := by
  have hI : I.sum (fun j => twoLevelDiagonal I c j*‖v j‖^2) = c*I.sum (fun j => ‖v j‖^2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j hj => by rw [twoLevelDiagonal, if_pos hj])
  have hJ : Iᶜ.sum (fun j => twoLevelDiagonal I c j*‖v j‖^2) =
      (c+1)*Iᶜ.sum (fun j => ‖v j‖^2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j hj => by rw [twoLevelDiagonal, if_neg (Finset.mem_compl.mp hj)])
  have he : I.sum (fun j => ‖v j‖^2)+Iᶜ.sum (fun j => ‖v j‖^2) = 1 := by
    rw [Finset.sum_add_sum_compl, ← EuclideanSpace.norm_sq_eq, hv]
    norm_num
  rw [← Finset.sum_add_sum_compl I, hI, hJ]
  have hh := congrArg (fun t : ℝ => c*t) he
  nlinarith only [hh]

lemma twoLevelDiagonal_ratio {n : ℕ} (I : Finset (Fin n)) (c : ℝ) (hc : 0 < c) :
    c^n*(∏ j, twoLevelDiagonal I c j)⁻¹ = (c/(c+1))^(n-I.card) := by
  rw [twoLevelDiagonal_product]
  have hc1 : c+1 ≠ 0 := by positivity
  have he : n = I.card+(n-I.card) := by
    have hh := Finset.card_le_univ I
    simp only [Fintype.card_fin] at hh
    omega
  have hepow : c^n = c^I.card*c^(n-I.card) := by
    rw [← pow_add, ← he]
  rw [hepow]
  rw [div_pow]
  field_simp

#print axioms twoLevelDiagonal
#print axioms twoLevelDiagonal_pos
#print axioms twoLevelDiagonal_product
#print axioms twoLevelDiagonal_energy
#print axioms twoLevelDiagonal_ratio
end SpectralRadiusUpperTail
