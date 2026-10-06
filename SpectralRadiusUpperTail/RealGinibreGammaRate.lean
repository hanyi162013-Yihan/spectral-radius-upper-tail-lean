import SpectralRadiusUpperTail.HalfGammaLower
import SpectralRadiusUpperTail.Rate

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- The logarithm per dimension of the Gamma-normalized real-eigenvalue
factor, written so the Stirling term is explicit. -/
noncomputable def realGinibreGammaLogCore (n : ℕ) (r : ℝ) : ℝ :=
  -(Real.log (Real.Gamma ((n : ℝ)/2+1))/(n : ℝ)-
      Real.log ((n : ℝ)/2)/2) +
    (1-1/(n : ℝ))*Real.log r-r^2/2

theorem realGinibreGammaLogCore_limit (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n : ℕ => realGinibreGammaLogCore n r)
      atTop (𝓝 (-rate 1 r)) := by
  have hi : Tendsto (fun n : ℕ => (1 : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have h2 : Tendsto (fun n : ℕ => (1-1/(n : ℝ))*Real.log r)
      atTop (𝓝 (Real.log r)) := by
    simpa using (h1.sub hi).mul_const (Real.log r)
  have h := (half_gamma_rate_limit.neg.add h2).sub_const (r^2/2)
  convert h using 1
  · funext n
    rfl
  · unfold rate
    ring

#print axioms realGinibreGammaLogCore_limit
end SpectralRadiusUpperTail
