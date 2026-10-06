import SpectralRadiusUpperTail.AlgebraLiePowerError
import Mathlib.Analysis.SpecificLimits.Basic

namespace SpectralRadiusUpperTail
open Filter Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A]

/-- Explicit O(1/n) Lie-product error without a commutativity assumption. -/
theorem algebra_lie_product_error (a b : A) (n : ℕ)
    (hn : ‖a‖+‖b‖ ≤ ((n+1 : ℕ) : ℝ)) :
    ‖(NormedSpace.exp (((n+1 : ℕ) : ℝ)⁻¹ • a)*
        NormedSpace.exp (((n+1 : ℕ) : ℝ)⁻¹ • b))^(n+1)-NormedSpace.exp (a+b)‖ ≤
      (Real.exp (‖a‖+‖b‖)*(Real.exp 1+4)*(‖a‖+‖b‖)^2)/((n+1 : ℕ) : ℝ) := by
  let K := ‖a‖+‖b‖
  let q : ℝ := ((n+1 : ℕ) : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hK : 0 ≤ K := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hi : 0 ≤ q⁻¹ := inv_nonneg.mpr hq.le
  have hsmall : q⁻¹*K ≤ 1 := by
    calc
      _ ≤ q⁻¹*q := mul_le_mul_of_nonneg_left hn hi
      _ = 1 := inv_mul_cancel₀ hq.ne'
  have hp := algebra_lie_power_error a b q⁻¹ hi hsmall n
  have he : q*q⁻¹ = 1 := mul_inv_cancel₀ hq.ne'
  change ‖_-NormedSpace.exp ((q*q⁻¹) • (a+b))‖ ≤ _ at hp
  rw [he, one_smul] at hp
  have hnt : (n : ℝ)*q⁻¹ ≤ 1 := by
    calc
      _ ≤ q*q⁻¹ := mul_le_mul_of_nonneg_right (by dsimp [q]; simp) hi
      _ = 1 := he
  have hExp : Real.exp ((n : ℝ)*q⁻¹*K) ≤ Real.exp K :=
    Real.exp_le_exp.mpr (by simpa using mul_le_mul_of_nonneg_right hnt hK)
  calc
    _ ≤ q*Real.exp ((n : ℝ)*q⁻¹*K)*((Real.exp 1+4)*(q⁻¹*K)^2) := hp
    _ ≤ q*Real.exp K*((Real.exp 1+4)*(q⁻¹*K)^2) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hExp hq.le)
      positivity
    _ = _ := by change _ = (Real.exp K*(Real.exp 1+4)*K^2)/q; field_simp

/-- Lie's product formula in any real Banach algebra with unit norm one. -/
theorem algebra_lie_product_tendsto (a b : A) :
    Tendsto (fun n : ℕ => (NormedSpace.exp (((n+1 : ℕ) : ℝ)⁻¹ • a)*
        NormedSpace.exp (((n+1 : ℕ) : ℝ)⁻¹ • b))^(n+1))
      atTop (𝓝 (NormedSpace.exp (a+b))) := by
  let C := Real.exp (‖a‖+‖b‖)*(Real.exp 1+4)*(‖a‖+‖b‖)^2
  have hlim : Tendsto (fun n : ℕ => C/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div, mul_zero] using
      tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hev : ∀ᶠ n : ℕ in atTop, ‖a‖+‖b‖ ≤ ((n+1 : ℕ) : ℝ) := by
    obtain ⟨N,hN⟩ := exists_nat_ge (‖a‖+‖b‖)
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN.trans (by exact_mod_cast (show N ≤ n+1 by omega))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [hev] with n hn
  exact algebra_lie_product_error a b n hn

#print axioms algebra_lie_product_error
#print axioms algebra_lie_product_tendsto
end SpectralRadiusUpperTail
