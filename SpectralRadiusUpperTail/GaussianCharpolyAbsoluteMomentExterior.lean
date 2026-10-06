import SpectralRadiusUpperTail.GaussianCharpolyMean
import SpectralRadiusUpperTail.GaussianCharpolySecondMomentExterior
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The absolute shifted determinant has precisely the expected exponential
scale outside the square-root dimension. The two inequalities have only a
polynomial gap, which vanishes on the logarithmic scale divided by dimension. -/
theorem gaussian_charpoly_absolute_moment_exterior_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ℝ) (hx : 0 < x) (hscale : (Fintype.card ι : ℝ) ≤ x^2) :
    x^(Fintype.card ι) ≤
      (∫ z : ι × ι → ℝ,
        |(Matrix.of z.curry).charpoly.eval x|
        ∂Measure.pi (fun _ => standardNormal)) ∧
    (∫ z : ι × ι → ℝ,
        |(Matrix.of z.curry).charpoly.eval x|
        ∂Measure.pi (fun _ => standardNormal)) ≤
      ((Fintype.card ι : ℝ)+2) / 2 * x^(Fintype.card ι) := by
  classical
  let N := Fintype.card ι
  let μ : Measure (ι × ι → ℝ) := Measure.pi (fun _ => standardNormal)
  let f : (ι × ι → ℝ) → ℝ := fun z => (Matrix.of z.curry).charpoly.eval x
  let a : ℝ := x^N
  have ha : 0 < a := pow_pos hx _
  have hfi : Integrable f μ := gaussian_charpoly_integrable x
  have hsi : Integrable (fun z => (f z)^2) μ :=
    (gaussian_charpoly_second_moment_principalMinorSum x).1
  have hai : Integrable (fun z => |f z|) μ := hfi.abs
  have hmean : (∫ z, f z ∂μ) = a := gaussian_charpoly_mean x
  have hsecond : (∫ z, (f z)^2 ∂μ) ≤ ((N : ℝ)+1)*a^2 := by
    have hb := gaussian_charpoly_second_moment_exterior_bound x hx.le hscale
    change (∫ z, (f z)^2 ∂μ) ≤ ((N : ℝ)+1)*x^(2*N) at hb
    convert hb using 1
    dsimp [a]
    rw [mul_comm 2 N, pow_mul]
  constructor
  · calc
      a = |∫ z, f z ∂μ| := by rw [hmean, abs_of_pos ha]
      _ ≤ ∫ z, |f z| ∂μ := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm f :
            ‖∫ z, f z ∂μ‖ ≤ ∫ z, ‖f z‖ ∂μ)
  · have hpoint (z : ι × ι → ℝ) :
        2*a*|f z| ≤ a^2+(f z)^2 := by
      simpa only [sq_abs] using two_mul_le_add_sq a |f z|
    have hint : Integrable (fun z => a^2+(f z)^2) μ :=
      (integrable_const _).add hsi
    have hleft : Integrable (fun z => 2*a*|f z|) μ :=
      hai.const_mul _
    have h := integral_mono hleft hint hpoint
    rw [integral_const_mul,
      integral_add (integrable_const _) hsi, integral_const] at h
    have hprob : μ.real Set.univ = 1 := by simp [μ]
    rw [hprob, one_smul] at h
    have hbound : 2*a*(∫ z, |f z| ∂μ) ≤ ((N : ℝ)+2)*a^2 := by
      calc
        _ ≤ a^2 + ∫ z, (f z)^2 ∂μ := h
        _ ≤ ((N : ℝ)+2)*a^2 := by nlinarith [hsecond]
    dsimp [a] at *
    nlinarith [hbound]

#print axioms gaussian_charpoly_absolute_moment_exterior_bound
end SpectralRadiusUpperTail
