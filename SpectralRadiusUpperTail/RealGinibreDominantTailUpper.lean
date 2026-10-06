import SpectralRadiusUpperTail.RealGinibreDominantDecay
import SpectralRadiusUpperTail.RealGinibreDominantIntegrable
import SpectralRadiusUpperTail.RightTailIntegralComparison
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- Integrating the dominant real-eigenvalue one-point term costs only a
factor of order `1/n` beyond its value at the target radius. -/
theorem realGinibreDominantTailUpper (n : ℕ) (hn : 3 ≤ n)
    (r : ℝ) (hr : 1 < r) :
    (∫ x : ℝ in Ioi r, realGinibreDominantDensity n x) ≤
      realGinibreCoreDensity n r / ((n : ℝ)*(r-1/r)) := by
  have hrpos : 0 < r := by linarith
  have hs : 0 < r - 1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have ha : 0 < (n : ℝ)*(r-1/r) :=
    mul_pos (Nat.cast_pos.mpr (by omega)) hs
  have hi := realGinibreDominantDensity_integrableOn n hn r hr
  apply right_tail_integral_le_of_exp_envelope
    (fun x => realGinibreDominantDensity n x) r
    (realGinibreCoreDensity n r) ((n : ℝ)*(r-1/r)) ha hi
  intro x hx
  convert realGinibreDominantDensity_decay n hn r x hr (le_of_lt hx) using 1 <;> ring

#print axioms realGinibreDominantTailUpper
end SpectralRadiusUpperTail
