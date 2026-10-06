import SpectralRadiusUpperTail.RealGinibreWeightedFirstUpper
import SpectralRadiusUpperTail.RealGinibreWeightedDominantUpper
import SpectralRadiusUpperTail.RealGinibreWeightedNonrealRate
import SpectralRadiusUpperTail.ExponentialPrefactorBudget
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set Metric Filter
open scoped Topology

/-- Sum of the explicit finite real-Ginibre one-point expressions weighted
by a radial power outside the unit disk. The factors of two account for the
two signs of the real eigenvalues. Identification with Gaussian matrix
eigenvalue expectations is a separate finite-dimensional theorem. -/
noncomputable def realGinibreWeightedOnePointEnvelope (n k : ℕ) : ℝ :=
  2*(∫ x in Ioi (1 : ℝ), x^(2*k)*realGinibreFirstDensity n x) +
  2*(∫ x in Ioi (1 : ℝ), x^(2*k)*realGinibreDominantDensity n x) +
    (∫ z : ℂ in {z | 1 < ‖z‖},
      ‖z‖^(2*k)*realGinibreNonrealDensityAt n z)

/-- The complete explicit scalar one-point envelope has the candidate
linear-power upper exponent of the real Gaussian spectral radius. -/
theorem realGinibreWeightedOnePointEnvelope_upper_eventual
    (k : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      realGinibreWeightedOnePointEnvelope n (k n) ≤
        Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
  let ε : ℝ := δ/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  filter_upwards [realGinibreFirstDensity_weighted_upper_eventual
      k α hα hk ε hε,
    realGinibreDominantDensity_weighted_upper_eventual
      k α hα hk ε hε,
    realGinibreNonrealDensityAt_weighted_upper_eventual
      k α hα hk ε hε,
    eventually_exp_prefactor_absorb 5 (powerRate 1 α+ε) ε
      (by norm_num) hε]
    with n hfirst hdom hnonreal habsorb
  calc
    realGinibreWeightedOnePointEnvelope n (k n) ≤
        5*Real.exp ((n : ℝ)*(powerRate 1 α+ε)) := by
      unfold realGinibreWeightedOnePointEnvelope
      linarith
    _ ≤ Real.exp ((n : ℝ)*(powerRate 1 α+ε+ε)) := habsorb
    _ = _ := by congr 1; dsimp [ε]; ring

#print axioms realGinibreWeightedOnePointEnvelope_upper_eventual
end SpectralRadiusUpperTail
