import SpectralRadiusUpperTail.RealMatrixNonrealPairCount
import SpectralRadiusUpperTail.RealGaussianRootCountSignSymmetry
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

noncomputable def realGaussianUpperNonrealExteriorCount
    (n : ℕ) (r : ℝ) (x : (Fin n × Fin n) → ℝ) : ℝ :=
  (realMatrixUpperNonrealExteriorCount
    ((1/Real.sqrt (n : ℝ)) • entryMatrix x) r : ℕ)

theorem realGaussianNonrealExteriorCount_eq_two_upper (n : ℕ)
    (r : ℝ) (x : (Fin n × Fin n) → ℝ) :
    realGaussianExteriorCount n r 2 x =
      2*realGaussianUpperNonrealExteriorCount n r x := by
  have h := realMatrixNonrealExteriorCount_eq_two_upper
    ((1/Real.sqrt (n : ℝ)) • entryMatrix x) r
  have hc := congrArg (fun m : ℕ => (m : ℝ)) h
  simpa [realGaussianExteriorCount, matrixExteriorRootCount,
    realGaussianUpperNonrealExteriorCount] using hc

theorem realGaussianNonrealExteriorCount_measurable_of_upper
    (n : ℕ) (r : ℝ)
    (hUpper : Measurable (realGaussianUpperNonrealExteriorCount n r)) :
    Measurable (realGaussianExteriorCount n r 2) := by
  have heq : realGaussianExteriorCount n r 2 =
      (fun x => 2*realGaussianUpperNonrealExteriorCount n r x) :=
    funext (realGaussianNonrealExteriorCount_eq_two_upper n r)
  rw [heq]
  exact measurable_const.mul hUpper

/-- The radius right-tail LDP needs the nonreal one-point estimate only in
the upper half-plane. Root conjugation supplies the other half. -/
theorem real_gaussian_radius_rate_of_upper_half_one_point
    (r : ℝ) (hr : 1 < r)
    (hMeasPos : ∀ n, Measurable (realGaussianExteriorCount n r 0))
    (hMeasUpper : ∀ n,
      Measurable (realGaussianUpperNonrealExteriorCount n r))
    (hPos : ∀ n, 3 ≤ n →
      (∫ x, realGaussianExteriorCount n r 0 x ∂gaussianMatrixLaw n) =
        realGinibreRealPositiveTailMass n r)
    (hUpper : ∀ n, 3 ≤ n →
      (∫ x, realGaussianUpperNonrealExteriorCount n r x
        ∂gaussianMatrixLaw n) ≤
          realGinibreNonrealExteriorMass n r) :
    Tendsto (fun n : ℕ => Real.log ((gaussianMatrixLaw n).real
      {x | r < realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix x)}) /
      (n : ℝ)) atTop (𝓝 (-rate 1 r)) := by
  apply real_gaussian_radius_rate_of_two_one_point_classes r hr
    hMeasPos
    (fun n => realGaussianNonrealExteriorCount_measurable_of_upper n r
      (hMeasUpper n))
    hPos
  intro n hn
  have heq : realGaussianExteriorCount n r 2 =
      (fun x => 2*realGaussianUpperNonrealExteriorCount n r x) :=
    funext (realGaussianNonrealExteriorCount_eq_two_upper n r)
  rw [heq, integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hUpper n hn) (by norm_num)

#print axioms realGaussianNonrealExteriorCount_eq_two_upper
#print axioms real_gaussian_radius_rate_of_upper_half_one_point
end SpectralRadiusUpperTail
