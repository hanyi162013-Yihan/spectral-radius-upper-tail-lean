import SpectralRadiusUpperTail.BoundedCoordinateSets
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

noncomputable def largeCoordinateSet {n : ℕ} (d : ℝ) (v : Fin n → ℂ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => d < ‖v j‖)

lemma largeCoordinateSet_small {n : ℕ} (d : ℝ) (v : Fin n → ℂ) (j : Fin n)
    (hj : j ∉ largeCoordinateSet d v) : ‖v j‖ ≤ d := by
  simpa only [largeCoordinateSet, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hj

lemma largeCoordinateSet_card_bound {n : ℕ} (d : ℝ) (hd : 0 < d)
    (v : Fin n → ℂ) (hv : ∑ j, ‖v j‖^2 ≤ 1) :
    ((largeCoordinateSet d v).card : ℝ) ≤ 1/d^2 := by
  let I := largeCoordinateSet d v
  have hs : (I.card : ℝ)*d^2 ≤ 1 := by
    calc
      _ = I.sum (fun _ => d^2) := by simp
      _ ≤ I.sum (fun j => ‖v j‖^2) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : d < ‖v j‖ := (Finset.mem_filter.mp hj).2
        exact pow_le_pow_left₀ hd.le hj'.le 2
      _ ≤ ∑ j, ‖v j‖^2 := Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg _)
      _ ≤ 1 := hv
  exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr hs

lemma largeCoordinateSet_uniform_card (d : ℝ) (hd : 0 < d) :
    ∃ M : ℕ, ∀ n : ℕ, ∀ v : Fin n → ℂ, (∑ j, ‖v j‖^2) ≤ 1 →
      (largeCoordinateSet d v).card ≤ M := by
  obtain ⟨M, hM⟩ := exists_nat_ge (1/d^2)
  refine ⟨M, ?_⟩
  intro n v hv
  exact_mod_cast (largeCoordinateSet_card_bound d hd v hv).trans hM

lemma complement_coordinate_energy_bounds {n : ℕ} (I : Finset (Fin n))
    (v : Fin n → ℂ) (hv : ∑ j, ‖v j‖^2 ≤ 1) :
    0 ≤ Iᶜ.sum (fun j => ‖v j‖^2) ∧ Iᶜ.sum (fun j => ‖v j‖^2) ≤ 1 := by
  exact ⟨Finset.sum_nonneg (fun j _ => sq_nonneg _),
    (Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖v j‖)).trans hv⟩

#print axioms largeCoordinateSet
#print axioms largeCoordinateSet_small
#print axioms largeCoordinateSet_card_bound
#print axioms largeCoordinateSet_uniform_card
#print axioms complement_coordinate_energy_bounds
end SpectralRadiusUpperTail
