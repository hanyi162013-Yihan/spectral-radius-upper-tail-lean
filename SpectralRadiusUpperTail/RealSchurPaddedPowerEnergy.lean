import SpectralRadiusUpperTail.RealSchurBlockMomentBudget

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- Sum of squared Frobenius norms of all blocks of the actual padded
conditional Schur product-model power. -/
noncomputable def realSchurPaddedPowerBlockEnergy {N : ℕ}
    (n k : ℕ) (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, ‖((realSchurPaddedMatrix n B z)^k) i j‖^2

/-- The full padded product-model power has a finite second moment with
only a polynomial block-count prefactor. -/
theorem real_schur_padded_power_energy_bound {N : ℕ}
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hN : N ≤ n)
    (η ρ : ℝ) (hη : 0 < η) (hR : 0 < ρ+η)
    (B : Fin N → RealSchurBlockData)
    (hB : ∀ i, realSchurDataAdmissible (B i))
    (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ) :
    Integrable (realSchurPaddedPowerBlockEnergy n k B)
      (realSchurGlobalLaw n B) ∧
    (∫ z, realSchurPaddedPowerBlockEnergy n k B z
      ∂realSchurGlobalLaw n B) ≤
      (N : ℝ)^2 *
        ((2+2/((n : ℝ)*η^2))*(n : ℝ)*(ρ+η)^(2*k)*
          Real.exp (3*((4*(2+2/((n : ℝ)*η^2))/(ρ+η)^2)*
            (k : ℝ)^2)^((1 : ℝ)/3))) := by
  let M : ℝ := (2+2/((n : ℝ)*η^2))*(n : ℝ)*(ρ+η)^(2*k)*
    Real.exp (3*((4*(2+2/((n : ℝ)*η^2))/(ρ+η)^2)*
      (k : ℝ)^2)^((1 : ℝ)/3))
  have hblock (i j : Fin N) :
      Integrable (fun z => ‖((realSchurPaddedMatrix n B z)^k) i j‖^2)
        (realSchurGlobalLaw n B) ∧
      (∫ z, ‖((realSchurPaddedMatrix n B z)^k) i j‖^2
        ∂realSchurGlobalLaw n B) ≤ M := by
    have heq (z) := realSchurPaddedPower_gaussian_sum n k hk B z i j
    have hi := (real_schur_block_path_second_moment
      n k hn η ρ hη B hB hmod i j).1
    have hb := real_schur_block_power_second_moment_bound
      n k hn hN η ρ hη hR B hB hmod i j
    constructor
    · simpa only [heq] using hi
    · simpa only [heq, M] using hb
  have hInt : Integrable (realSchurPaddedPowerBlockEnergy n k B)
      (realSchurGlobalLaw n B) := by
    unfold realSchurPaddedPowerBlockEnergy
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (hblock i j).1
  constructor
  · exact hInt
  · calc
      (∫ z, realSchurPaddedPowerBlockEnergy n k B z
        ∂realSchurGlobalLaw n B) =
        ∑ i : Fin N, ∑ j : Fin N,
          ∫ z, ‖((realSchurPaddedMatrix n B z)^k) i j‖^2
            ∂realSchurGlobalLaw n B := by
        unfold realSchurPaddedPowerBlockEnergy
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro i hi
          rw [integral_finsetSum]
          intro j hj
          exact (hblock i j).1
        · intro i hi
          apply integrable_finsetSum
          intro j hj
          exact (hblock i j).1
      _ ≤ ∑ _i : Fin N, ∑ _j : Fin N, M := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact (hblock i j).2
      _ = (N : ℝ)^2 * M := by simp [pow_two]; ring
      _ = _ := rfl

#print axioms real_schur_padded_power_energy_bound
end SpectralRadiusUpperTail
