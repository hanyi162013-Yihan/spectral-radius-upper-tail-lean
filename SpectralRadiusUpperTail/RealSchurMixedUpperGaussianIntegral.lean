import SpectralRadiusUpperTail.RealSchurMixedUpperEnergy
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- The Gaussian integration of any independent finite real entry array.
The normalizer is exact, including for an empty array. -/
theorem realSchurMixedIndependentGaussianIntegral
    (ι : Type*) [Fintype ι] :
    (∫ u : ι → ℝ,
      Real.exp (-(∑ p : ι, (u p)^2)/2)) =
        (Real.sqrt (2*Real.pi)) ^ (Fintype.card ι) := by
  classical
  have hw (u : ι → ℝ) :
      Real.exp (-(∑ p : ι, (u p)^2)/2) =
        ∏ p : ι, Real.exp (-(1/2 : ℝ)*(u p)^2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    ring
  simp_rw [hw]
  rw [integral_fintype_prod_volume_eq_pow
    (ι := ι) (fun x : ℝ => Real.exp (-(1/2 : ℝ)*x^2)),
    integral_gaussian]
  congr 1
  congr 1
  ring

/-- The same Gaussian normalizer is unchanged by an arbitrary translation
of every matrix-entry coordinate. -/
theorem realSchurMixedIndependentGaussianIntegral_shift
    (ι : Type*) [Fintype ι] (a : ι → ℝ) :
    (∫ u : ι → ℝ,
      Real.exp (-(∑ p : ι, (a p + u p)^2)/2)) =
        (Real.sqrt (2*Real.pi)) ^ (Fintype.card ι) := by
  have h (u : ι → ℝ) :
      Real.exp (-(∑ p : ι, (a p + u p)^2)/2) =
        Real.exp (-(∑ p : ι, ((u+a) p)^2)/2) := by
    congr 1
    apply congrArg (fun z : ℝ => -z/2)
    apply Finset.sum_congr rfl
    intro p _
    simp [Pi.add_apply, add_comm]
  simp_rw [h]
  change (∫ u : ι → ℝ,
    (fun v : ι → ℝ => Real.exp (-(∑ p : ι, (v p)^2)/2)) (u+a)) = _
  calc
    _ = (∫ u : ι → ℝ, Real.exp (-(∑ p : ι, (u p)^2)/2)) :=
      integral_add_right_eq_self
        (fun v : ι → ℝ => Real.exp (-(∑ p : ι, (v p)^2)/2)) a
    _ = _ := realSchurMixedIndependentGaussianIntegral ι

/-- Integrating the independent strictly-upper Schur entries contributes
only the expected Gaussian normalizer. -/
theorem realSchurMixedStrictUpperGaussianIntegral
    {m : ℕ} (s : Fin m → ℕ) :
    (∫ u : RealSchurMixedStrictUpperEntry s → ℝ,
      Real.exp (-(∑ p : RealSchurMixedStrictUpperEntry s, (u p)^2)/2)) =
        (Real.sqrt (2*Real.pi)) ^
          (Fintype.card (RealSchurMixedStrictUpperEntry s)) :=
  realSchurMixedIndependentGaussianIntegral _

/-- Once the diagonal blocks are fixed, all strictly-upper block entries
integrate out as independent standard real Gaussian variables. -/
theorem realSchurMixedGaussianWeight_integral_upper
    {m : ℕ} (s : Fin m → ℕ)
    (d : RealSchurMixedDiagonalEntry s → ℝ) :
    (∫ u : RealSchurMixedStrictUpperEntry s → ℝ,
      realMatrixGaussianWeight (RealSchurMixedCoord s)
        (realSchurMixedUpperEntryJoin s d u)) =
      Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s, (d p)^2)/2) *
        (Real.sqrt (2*Real.pi)) ^
          (Fintype.card (RealSchurMixedStrictUpperEntry s)) := by
  simp_rw [realSchurMixedGaussianWeight_join]
  rw [integral_const_mul, realSchurMixedStrictUpperGaussianIntegral]

#print axioms realSchurMixedStrictUpperGaussianIntegral
#print axioms realSchurMixedIndependentGaussianIntegral_shift
#print axioms realSchurMixedGaussianWeight_integral_upper
end SpectralRadiusUpperTail
