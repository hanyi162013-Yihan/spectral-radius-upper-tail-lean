import SpectralRadiusUpperTail.RealSchurMixedUpperGaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

/-- The independent finite Gaussian array is genuinely integrable,
so its real integral can safely be converted to a nonnegative integral. -/
theorem realSchurMixedIndependentGaussianIntegrable
    (ι : Type*) [Fintype ι] :
    Integrable (fun u : ι → ℝ =>
      Real.exp (-(∑ p : ι, (u p)^2)/2)) := by
  classical
  have hw (u : ι → ℝ) :
      Real.exp (-(∑ p : ι, (u p)^2)/2) =
        ∏ p : ι, Real.exp (-(1/2 : ℝ)*(u p)^2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    ring
  simp_rw [hw]
  rw [volume_pi]
  exact Integrable.fintype_prod (ι := ι) (E := ℝ)
    (μ := fun _ => (volume : Measure ℝ))
    (f := fun _ x => Real.exp (-(1/2 : ℝ)*x^2)) (fun _ => by
    simpa only [one_div] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)))

theorem realSchurMixedIndependentGaussianLIntegral
    (ι : Type*) [Fintype ι] :
    (∫⁻ u : ι → ℝ,
      ENNReal.ofReal (Real.exp (-(∑ p : ι, (u p)^2)/2))) =
        ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^ (Fintype.card ι)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (realSchurMixedIndependentGaussianIntegrable ι)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  rw [realSchurMixedIndependentGaussianIntegral]

/-- All strictly upper Gaussian entries integrate to their exact
finite normalizer in the nonnegative-integral convention. -/
theorem realSchurMixedStrictUpperGaussianLIntegral
    {r : ℕ} (s : Fin r → ℕ) :
    (∫⁻ u : RealSchurMixedStrictUpperEntry s → ℝ,
      ENNReal.ofReal
        (Real.exp (-(∑ p : RealSchurMixedStrictUpperEntry s,
          (u p)^2)/2))) =
        ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
          (Fintype.card (RealSchurMixedStrictUpperEntry s))) :=
  realSchurMixedIndependentGaussianLIntegral _

/-- A fixed diagonal array contributes its Gaussian energy, while the
free strictly-upper array contributes the exact independent normalizer. -/
theorem realSchurMixedGaussianWeight_lintegral_upper
    {r : ℕ} (s : Fin r → ℕ)
    (d : RealSchurMixedDiagonalEntry s → ℝ) :
    (∫⁻ u : RealSchurMixedStrictUpperEntry s → ℝ,
      ENNReal.ofReal
        (realMatrixGaussianWeight (RealSchurMixedCoord s)
          (realSchurMixedUpperEntryJoin s d u))) =
      ENNReal.ofReal
        (Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s,
          (d p)^2)/2)) *
        ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
          (Fintype.card (RealSchurMixedStrictUpperEntry s))) := by
  simp_rw [realSchurMixedGaussianWeight_join]
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul']
  · rw [realSchurMixedStrictUpperGaussianLIntegral]
  · simp

#print axioms realSchurMixedIndependentGaussianIntegrable
#print axioms realSchurMixedIndependentGaussianLIntegral
#print axioms realSchurMixedGaussianWeight_lintegral_upper
end SpectralRadiusUpperTail
