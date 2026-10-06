import SpectralRadiusUpperTail.RealGinibreCoreDecay
import SpectralRadiusUpperTail.RealGinibreDominantDensity

namespace SpectralRadiusUpperTail

/-- The entire dominant real-eigenvalue density term inherits the
integrable envelope of its Gamma-normalized core. -/
theorem realGinibreDominantDensity_decay (n : ℕ) (hn : 3 ≤ n)
    (r x : ℝ) (hr : 1 < r) (hrx : r ≤ x) :
    realGinibreDominantDensity n x ≤ realGinibreCoreDensity n r *
      Real.exp (-(n : ℝ)*(r-1/r)*(x-r)) := by
  have hx : 1 ≤ x := le_trans (le_of_lt hr) hrx
  exact (realGinibreDominantDensity_bounds n hn x hx).2.trans
    (realGinibreCoreDensity_decay n (by omega) r x hr hrx)

#print axioms realGinibreDominantDensity_decay
end SpectralRadiusUpperTail
