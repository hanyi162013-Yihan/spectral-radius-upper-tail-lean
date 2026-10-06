import SpectralRadiusUpperTail.RealMatrixNonrealPairPower
import SpectralRadiusUpperTail.RealGaussianWeightedSignSymmetry
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

noncomputable def realGaussianUpperNonrealExteriorPower (n k : ℕ)
    (x : (Fin n × Fin n) → ℝ) : ℝ :=
  realMatrixUpperNonrealExteriorPower
    ((1/Real.sqrt (n : ℝ)) • entryMatrix x) k

theorem realGaussianNonrealExteriorPower_eq_two_upper (n k : ℕ)
    (x : (Fin n × Fin n) → ℝ) :
    realGaussianNonrealExteriorPower n k x =
      2*realGaussianUpperNonrealExteriorPower n k x := by
  simpa only [realGaussianNonrealExteriorPower,
    realGaussianUpperNonrealExteriorPower] using
    realMatrixNonrealExteriorPower_eq_two_upper
      ((1/Real.sqrt (n : ℝ)) • entryMatrix x) k

theorem realGaussianNonrealExteriorPower_integrable_of_upper (n k : ℕ)
    (hUpper : Integrable (realGaussianUpperNonrealExteriorPower n k)
      (gaussianMatrixLaw n)) :
    Integrable (realGaussianNonrealExteriorPower n k)
      (gaussianMatrixLaw n) := by
  have heq : realGaussianNonrealExteriorPower n k =
      (fun x => 2*realGaussianUpperNonrealExteriorPower n k x) :=
    funext (realGaussianNonrealExteriorPower_eq_two_upper n k)
  rw [heq]
  exact hUpper.const_mul 2

theorem realGaussianNonrealExteriorPower_mean_eq_two_upper (n k : ℕ) :
    (∫ x, realGaussianNonrealExteriorPower n k x
      ∂gaussianMatrixLaw n) =
      2*(∫ x, realGaussianUpperNonrealExteriorPower n k x
        ∂gaussianMatrixLaw n) := by
  have heq : realGaussianNonrealExteriorPower n k =
      (fun x => 2*realGaussianUpperNonrealExteriorPower n k x) :=
    funext (realGaussianNonrealExteriorPower_eq_two_upper n k)
  rw [heq, integral_const_mul]

/-- Only the upper-half-plane nonreal weighted one-point input remains,
alongside the positive-real input and actual Schur comparison. -/
theorem gaussianPowerUpperInput_of_upper_half_weighted_onePoint
    (hPosInt : ∀ n k, 3 ≤ n →
      Integrable (realGaussianPositiveRealExteriorPower n k)
        (gaussianMatrixLaw n))
    (hUpperInt : ∀ n k, 3 ≤ n →
      Integrable (realGaussianUpperNonrealExteriorPower n k)
        (gaussianMatrixLaw n))
    (hPos : ∀ n k, 3 ≤ n →
      (∫ x, realGaussianPositiveRealExteriorPower n k x
        ∂gaussianMatrixLaw n) ≤
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreFirstDensity n x) +
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreDominantDensity n x))
    (hUpper : ∀ n k, 3 ≤ n →
      2*(∫ x, realGaussianUpperNonrealExteriorPower n k x
        ∂gaussianMatrixLaw n) ≤
        (∫ z : ℂ in {z | 1 < ‖z‖},
          ‖z‖^(2*k)*realGinibreNonrealDensityAt n z))
    (hSchur : GaussianSchurPowerComparisonInput) :
    GaussianPowerUpperInput := by
  apply gaussianPowerUpperInput_of_two_weighted_onePoint_classes
    hPosInt
    (fun n k hn => realGaussianNonrealExteriorPower_integrable_of_upper
      n k (hUpperInt n k hn))
    hPos
  · intro n k hn
    rw [realGaussianNonrealExteriorPower_mean_eq_two_upper]
    exact hUpper n k hn
  · exact hSchur

#print axioms realGaussianNonrealExteriorPower_eq_two_upper
#print axioms realGaussianNonrealExteriorPower_integrable_of_upper
#print axioms gaussianPowerUpperInput_of_upper_half_weighted_onePoint
end SpectralRadiusUpperTail
