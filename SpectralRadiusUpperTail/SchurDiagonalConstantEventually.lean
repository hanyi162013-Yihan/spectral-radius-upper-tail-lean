import SpectralRadiusUpperTail.SchurUniformBudget
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- For fixed positive Schur buffer, the diagonal-block moment constant is
eventually at most four. -/
theorem eventually_schur_diagonal_constant_le_four
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      2+2/((n : ℝ)*η^2) ≤ 4 := by
  have hη2 : 0 < η^2 := sq_pos_of_pos hη
  have ht : Tendsto (fun n : ℕ => (n : ℝ)*η^2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hη2
  filter_upwards [ht.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
  have hden : 0 < (n : ℝ)*η^2 := by linarith
  have hq : 2/((n : ℝ)*η^2) ≤ 2 :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  linarith

#print axioms eventually_schur_diagonal_constant_le_four
end SpectralRadiusUpperTail
