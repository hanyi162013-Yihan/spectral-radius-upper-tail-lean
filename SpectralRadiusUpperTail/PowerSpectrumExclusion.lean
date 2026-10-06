import Mathlib.Analysis.Normed.Algebra.Spectrum

namespace SpectralRadiusUpperTail

/-- A finite power-norm bound excludes spectral points without a normality assumption. -/
lemma mem_resolventSet_of_power_norm {𝕂 R : Type*} [NontriviallyNormedField 𝕂]
    [NormedRing R] [NormedAlgebra 𝕂 R] [CompleteSpace R] [NormOneClass R]
    (a : R) (z : 𝕂) (m : ℕ) (h : ‖a^m‖ < ‖z‖^m) :
    z ∈ resolventSet 𝕂 a := by
  by_contra hz
  have hs : z ∈ spectrum 𝕂 a := hz
  have hp := spectrum.norm_le_norm_of_mem (spectrum.pow_mem_pow a m hs)
  rw [norm_pow] at hp
  exact (not_lt_of_ge hp) h

/-- Uniform exterior exclusion follows from one suitable finite-power bound.
Obtaining that bound for actual iid matrices is a separate probabilistic input. -/
lemma exterior_resolventSet_of_power_norm {𝕂 R : Type*} [NontriviallyNormedField 𝕂]
    [NormedRing R] [NormedAlgebra 𝕂 R] [CompleteSpace R] [NormOneClass R]
    (a : R) (r : ℝ) (hr : 0 ≤ r) (m : ℕ) (h : ‖a^m‖ < r^m) :
    ∀ z : 𝕂, r ≤ ‖z‖ → z ∈ resolventSet 𝕂 a := by
  intro z hz
  exact mem_resolventSet_of_power_norm a z m
    (h.trans_le (pow_le_pow_left₀ hr hz m))

#print axioms mem_resolventSet_of_power_norm
#print axioms exterior_resolventSet_of_power_norm
end SpectralRadiusUpperTail
