import SpectralRadiusUpperTail.RealSchurFixedStartFamily
import SpectralRadiusUpperTail.SchurFiniteMomentBudget
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The numerical path budget also controls a fixed starting block. The
extra factor four in the reference budget harmlessly absorbs the exact
Gaussian bridge variance. -/
theorem schur_fixed_start_moment_budget {N : ℕ} (n k : ℕ)
    (hn : 0 < n) (hN : N ≤ n) (i : Fin N)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 < R) :
    (∑ l ∈ Finset.range (k+1),
      (Fintype.card {p : IncreasingBlockPath N l // p.val 0 = i} : ℝ) *
        C^(l+1) * (1/(n : ℝ))^l * (k.choose l : ℝ)^2 *
          R^(2*(k-l))) ≤
      C*(n : ℝ)*R^(2*k)*
        Real.exp (3*((4*C/R^2)*(k : ℝ)^2)^((1 : ℝ)/3)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  calc
    _ ≤ ∑ l ∈ Finset.range (k+1),
        (n.choose (l+1) : ℝ) * C^(l+1) *
          (4/(n : ℝ))^l * (k.choose l : ℝ)^2 *
          R^(2*(k-l)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hcard :
          (Fintype.card {p : IncreasingBlockPath N l // p.val 0 = i} : ℝ) ≤
            (n.choose (l+1) : ℝ) := by
        exact_mod_cast (schurFixedStartPath_card_le i).trans
          (Nat.choose_le_choose (l+1) hN)
      have hpow : (1/(n : ℝ))^l ≤ (4/(n : ℝ))^l := by
        gcongr
        · norm_num
      gcongr
    _ ≤ _ := schur_finite_moment_budget n k hn C R hC hR

#print axioms schur_fixed_start_moment_budget
end SpectralRadiusUpperTail
