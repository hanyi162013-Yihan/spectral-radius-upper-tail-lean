import SpectralRadiusUpperTail.FinitePowerInverseBound

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Quantitative exterior resolvent control from one scaled finite-power bound. -/
lemma resolvent_norm_of_scaled_power {𝕂 R : Type*} [NontriviallyNormedField 𝕂]
    [NormedRing R] [NormedAlgebra 𝕂 R] [CompleteSpace R] [NormOneClass R]
    (a : R) (z : 𝕂) (hz : z ≠ 0) (m : ℕ) (hp : ‖(z⁻¹ • a)^m‖ ≤ 1/2) :
    ‖resolvent a z‖ ≤ (2*∑ j ∈ Finset.range m, ‖z⁻¹ • a‖^j)/‖z‖ := by
  have hb := (inverse_one_sub_power_bound (𝕂 := 𝕂) (z⁻¹ • a) m hp).2
  have he : z • resolvent a z = Ring.inverse (1-z⁻¹ • a) := by
    simpa [Units.smul_def, resolvent] using
      (spectrum.units_smul_resolvent_self (r := Units.mk0 z hz) (a := a))
  rw [← he, norm_smul] at hb
  apply (le_div_iff₀ (norm_pos_iff.mpr hz)).2
  simpa only [mul_comm] using hb

#print axioms resolvent_norm_of_scaled_power
end SpectralRadiusUpperTail
