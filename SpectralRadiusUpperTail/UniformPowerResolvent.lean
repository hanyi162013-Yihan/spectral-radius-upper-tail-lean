import SpectralRadiusUpperTail.ScaledPowerResolvent
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- One finite-power bound and an operator-norm bound yield a uniform exterior
resolvent bound. This is deterministic; the iid power bound is not assumed proved. -/
lemma uniform_resolvent_of_power_bound {𝕂 R : Type*} [NontriviallyNormedField 𝕂]
    [NormedRing R] [NormedAlgebra 𝕂 R] [CompleteSpace R] [NormOneClass R]
    (a : R) (r M : ℝ) (hr : 0 < r) (hA : ‖a‖ ≤ M) (m : ℕ)
    (hp : ‖a^m‖ ≤ r^m/2) :
    ∀ z : 𝕂, r ≤ ‖z‖ → z ∈ resolventSet 𝕂 a ∧
      ‖resolvent a z‖ ≤ (2*∑ j ∈ Finset.range m, (M/r)^j)/r := by
  intro z hz
  have hzn : 0 < ‖z‖ := hr.trans_le hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzn
  have hM : 0 ≤ M := (norm_nonneg a).trans hA
  have hp' : ‖a^m‖ ≤ ‖z‖^m/2 := hp.trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hr.le hz m) (by norm_num))
  have hs : ‖(z⁻¹ • a)^m‖ ≤ 1/2 := by
    rw [smul_pow, norm_smul, norm_pow, norm_inv, inv_pow]
    calc
      (‖z‖^m)⁻¹*‖a^m‖ = ‖a^m‖/(‖z‖^m) := by ring
      _ ≤ 1/2 := (div_le_iff₀ (pow_pos hzn m)).2 (by linarith)
  have hx : ‖z⁻¹ • a‖ ≤ M/r := by
    rw [norm_smul, norm_inv]
    calc
      ‖z‖⁻¹*‖a‖ = ‖a‖/‖z‖ := by ring
      _ ≤ M/‖z‖ := div_le_div_of_nonneg_right hA hzn.le
      _ ≤ M/r := div_le_div_of_nonneg_left hM hr hz
  have hsum : (∑ j ∈ Finset.range m, ‖z⁻¹ • a‖^j) ≤
      ∑ j ∈ Finset.range m, (M/r)^j :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) hx j)
  refine ⟨mem_resolventSet_of_power_norm a z m (by nlinarith [pow_pos hzn m]), ?_⟩
  exact (resolvent_norm_of_scaled_power a z hz0 m hs).trans
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hzn.le).trans
      (div_le_div_of_nonneg_left (by positivity) hr hz))

#print axioms uniform_resolvent_of_power_bound
end SpectralRadiusUpperTail
