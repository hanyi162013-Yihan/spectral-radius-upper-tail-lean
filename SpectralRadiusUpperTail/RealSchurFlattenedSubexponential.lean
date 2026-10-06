import SpectralRadiusUpperTail.RealSchurFlattenedPowerEnergy
import SpectralRadiusUpperTail.SchurDiagonalConstantEventually
import SpectralRadiusUpperTail.SchurUniformBudget
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Topology

/-- The full product-model matrix power has only a subexponential second-moment
loss, uniformly over all admissible diagonal block data of radius at most `ρ`.
The ambient matrix here is the flattened padded real Schur matrix. -/
theorem real_schur_flattened_power_subexponential
    (k : ℕ → ℕ) (α η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α)) :
    ∀ᶠ n : ℕ in atTop, ∀ (N : ℕ) (B : Fin N → RealSchurBlockData)
      (ρ : ℝ), 0 < k n → N ≤ n →
      (∀ i, realSchurDataAdmissible (B i)) →
      (∀ i, realSchurDataRadius (B i) ≤ ρ) →
      0 ≤ ρ →
      (∫ z, ‖(flattenSchurBlocks (realSchurPaddedMatrix n B z))^(k n)‖^2
        ∂realSchurGlobalLaw n B) ≤
        Real.exp ((n : ℝ)*ε)*(ρ+η)^(2*k n) := by
  let C : ℝ := 3*(16/η^2)^((1 : ℝ)/3)
  have hpre := schur_prefactor_le_exp k α (2/3) C 4 3
    (by norm_num) (by norm_num) (by norm_num) hk ε hε
  filter_upwards [hpre, eventually_schur_diagonal_constant_le_four η hη,
    eventually_gt_atTop 0] with n hpre hC4 hn N B ρ hk0 hN hB hmod hρ
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hR : 0 < ρ+η := add_pos_of_nonneg_of_pos hρ hη
  have hRη : η ≤ ρ+η := by linarith
  let D : ℝ := 2+2/((n : ℝ)*η^2)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hD4 : D ≤ 4 := hC4
  have hN2 : (N : ℝ)^2 ≤ (n : ℝ)^2 := by
    gcongr
  have hden : 0 < (ρ+η)^2 := sq_pos_of_pos hR
  have hηden : 0 < η^2 := sq_pos_of_pos hη
  have hrad : η^2 ≤ (ρ+η)^2 := pow_le_pow_left₀ hη.le hRη 2
  have hquot : 4*D/(ρ+η)^2 ≤ 16/η^2 := by
    apply (div_le_div_iff₀ hden hηden).mpr
    have hp : 0 ≤ (4-D)*η^2 := mul_nonneg (by linarith) hηden.le
    nlinarith
  have hroot :
      ((4*D/(ρ+η)^2)*(k n : ℝ)^2)^((1 : ℝ)/3) ≤
        (16/η^2)^((1 : ℝ)/3)*(k n : ℝ)^((2 : ℝ)/3) := by
    have hh := Real.rpow_le_rpow
      (show 0 ≤ (4*D/(ρ+η)^2)*(k n : ℝ)^2 by positivity)
      (mul_le_mul_of_nonneg_right hquot (sq_nonneg _))
      (show (0 : ℝ) ≤ 1/3 by norm_num)
    rw [schur_cuberoot_scaling (16/η^2) (by positivity)] at hh
    exact hh
  have hmain := (real_schur_flattened_power_second_moment_bound
    n (k n) hn hk0 hN η ρ hη hR B hB hmod).2
  have hfactor :
      (N : ℝ)^2 * (D*(n : ℝ)*(ρ+η)^(2*k n)*
        Real.exp (3*((4*D/(ρ+η)^2)*(k n : ℝ)^2)^((1 : ℝ)/3))) ≤
      4*(n : ℝ)^3*(ρ+η)^(2*k n)*
        Real.exp (C*(k n : ℝ)^((2 : ℝ)/3)) := by
    have he :
        Real.exp (3*((4*D/(ρ+η)^2)*(k n : ℝ)^2)^((1 : ℝ)/3)) ≤
          Real.exp (C*(k n : ℝ)^((2 : ℝ)/3)) := by
      apply Real.exp_le_exp.mpr
      dsimp [C]
      nlinarith
    calc
      _ ≤ (n : ℝ)^2 * (4*(n : ℝ)*(ρ+η)^(2*k n)*
          Real.exp (C*(k n : ℝ)^((2 : ℝ)/3))) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ (N : ℝ)^2 * (D*(n : ℝ)*(ρ+η)^(2*k n)*
      Real.exp (3*((4*D/(ρ+η)^2)*(k n : ℝ)^2)^((1 : ℝ)/3))) := by
        simpa only [D] using hmain
    _ ≤ 4*(n : ℝ)^3*(ρ+η)^(2*k n)*
      Real.exp (C*(k n : ℝ)^((2 : ℝ)/3)) := hfactor
    _ ≤ Real.exp ((n : ℝ)*ε)*(ρ+η)^(2*k n) := by
      have hh := mul_le_mul_of_nonneg_right hpre
        (pow_nonneg hR.le (2*k n))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hh

#print axioms real_schur_flattened_power_subexponential
end SpectralRadiusUpperTail
