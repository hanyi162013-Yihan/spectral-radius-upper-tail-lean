import SpectralRadiusUpperTail.RankOneTargetBound

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable (𝕂 : Type*) [RCLike 𝕂]

def flatUnitDirections (n : ℕ) (L : ℝ) : Set (Fin n → 𝕂) :=
  {v | (∑ i, ‖v i‖^2) ≤ 1 ∧ (0 < n → (∑ i, ‖v i‖^2) = 1) ∧
    ∀ i, ‖v i‖ ≤ L/Real.sqrt (n : ℝ)}

lemma constant_direction_energy (n : ℕ) (hn : 0 < n) :
    (∑ _i : Fin n, ‖((Real.sqrt (n : ℝ))⁻¹ : 𝕂)‖^2) = 1 := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [norm_inv,RCLike.norm_ofReal,abs_of_nonneg (Real.sqrt_nonneg _),
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,inv_pow,hs]
  exact mul_inv_cancel₀ hn'

lemma flatUnitDirections_nonempty (n : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    (flatUnitDirections 𝕂 n L).Nonempty := by
  let v : Fin n → 𝕂 := fun _ => ((Real.sqrt (n : ℝ))⁻¹ : 𝕂)
  have hu : 0 < n → (∑ i, ‖v i‖^2) = 1 := constant_direction_energy 𝕂 n
  refine ⟨v,?_,hu,?_⟩
  · by_cases hn : 0 < n
    · exact (hu hn).le
    · have hn0 : n = 0 := by omega
      subst n
      simp
  · intro i
    dsimp [v]
    rw [norm_inv,RCLike.norm_ofReal,abs_of_nonneg (Real.sqrt_nonneg _),← one_div]
    exact div_le_div_of_nonneg_right hL (Real.sqrt_nonneg _)

#print axioms flatUnitDirections
#print axioms constant_direction_energy
#print axioms flatUnitDirections_nonempty
end SpectralRadiusUpperTail
