import SpectralRadiusUpperTail.RealSchurPaddedPowerEnergy
import SpectralRadiusUpperTail.SchurBlockFlatten

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix.Norms.Frobenius

/-- The block energy is the genuine squared Frobenius norm of the power
of the flattened padded real matrix. -/
theorem realSchurPaddedPowerBlockEnergy_eq_flattened_norm_sq {N : ℕ}
    (n k : ℕ) (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) :
    realSchurPaddedPowerBlockEnergy n k B z =
      ‖(flattenSchurBlocks (realSchurPaddedMatrix n B z))^k‖^2 := by
  rw [← flattenSchurBlocks_pow, flattenSchurBlocks_norm_sq]
  rfl

theorem real_schur_flattened_power_second_moment_bound {N : ℕ}
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hN : N ≤ n)
    (η ρ : ℝ) (hη : 0 < η) (hR : 0 < ρ+η)
    (B : Fin N → RealSchurBlockData)
    (hB : ∀ i, realSchurDataAdmissible (B i))
    (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ) :
    Integrable (fun z =>
      ‖(flattenSchurBlocks (realSchurPaddedMatrix n B z))^k‖^2)
      (realSchurGlobalLaw n B) ∧
    (∫ z, ‖(flattenSchurBlocks (realSchurPaddedMatrix n B z))^k‖^2
      ∂realSchurGlobalLaw n B) ≤
      (N : ℝ)^2 *
        ((2+2/((n : ℝ)*η^2))*(n : ℝ)*(ρ+η)^(2*k)*
          Real.exp (3*((4*(2+2/((n : ℝ)*η^2))/(ρ+η)^2)*
            (k : ℝ)^2)^((1 : ℝ)/3))) := by
  have hf : realSchurPaddedPowerBlockEnergy n k B =
      fun z => ‖(flattenSchurBlocks (realSchurPaddedMatrix n B z))^k‖^2 := by
    funext z
    exact realSchurPaddedPowerBlockEnergy_eq_flattened_norm_sq n k B z
  simpa only [hf] using
    real_schur_padded_power_energy_bound n k hn hk hN η ρ hη hR B hB hmod

#print axioms realSchurPaddedPowerBlockEnergy_eq_flattened_norm_sq
#print axioms real_schur_flattened_power_second_moment_bound
end SpectralRadiusUpperTail
