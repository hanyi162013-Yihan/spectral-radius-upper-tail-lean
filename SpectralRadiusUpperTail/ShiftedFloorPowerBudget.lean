import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- A fixed sufficiently small radius buffer costs an arbitrarily small
exponential factor for powers of degree proportional to dimension. -/
theorem exists_small_buffer_floor_power_bound
    (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ,
      (1+η)^(2*⌊α*(n : ℝ)⌋₊) ≤ Real.exp ((n : ℝ)*δ) := by
  let η : ℝ := δ/(2*α)
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η,hη,?_⟩
  intro n
  have hfloor : (⌊α*(n : ℝ)⌋₊ : ℝ) ≤ α*(n : ℝ) :=
    Nat.floor_le (mul_nonneg hα.le (Nat.cast_nonneg n))
  have hlog0 : 0 ≤ Real.log (1+η) := Real.log_nonneg (by linarith)
  have hlog : Real.log (1+η) ≤ η := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1+η)]
  have harg : 2*(⌊α*(n : ℝ)⌋₊ : ℝ)*Real.log (1+η) ≤ (n : ℝ)*δ := by
    calc
      _ ≤ (2*(α*(n : ℝ)))*Real.log (1+η) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfloor (by norm_num)) hlog0
      _ ≤ (2*(α*(n : ℝ)))*η :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by dsimp [η]; field_simp
  have hpow : (1+η)^(2*⌊α*(n : ℝ)⌋₊) =
      Real.exp (2*(⌊α*(n : ℝ)⌋₊ : ℝ)*Real.log (1+η)) := by
    rw [show 2*(⌊α*(n : ℝ)⌋₊ : ℝ) =
        ((2*⌊α*(n : ℝ)⌋₊ : ℕ) : ℝ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by linarith : 0 < 1+η)]
  rw [hpow]
  exact Real.exp_le_exp.mpr harg

#print axioms exists_small_buffer_floor_power_bound
end SpectralRadiusUpperTail
