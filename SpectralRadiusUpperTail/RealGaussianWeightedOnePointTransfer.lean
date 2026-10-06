import SpectralRadiusUpperTail.MatrixExteriorRootPowerPartition
import SpectralRadiusUpperTail.RealGaussianWeightedRadiusInterface
import SpectralRadiusUpperTail.RealGaussianSchurPowerConditional
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

noncomputable def realGaussianPositiveRealExteriorPower (n k : ℕ)
    (x : (Fin n × Fin n) → ℝ) : ℝ :=
  matrixPositiveRealExteriorPower
    (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) k

noncomputable def realGaussianNegativeRealExteriorPower (n k : ℕ)
    (x : (Fin n × Fin n) → ℝ) : ℝ :=
  matrixNegativeRealExteriorPower
    (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) k

noncomputable def realGaussianNonrealExteriorPower (n k : ℕ)
    (x : (Fin n × Fin n) → ℝ) : ℝ :=
  matrixNonrealExteriorPower
    (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) k

theorem realGaussianExteriorRootPower_partition (n k : ℕ)
    (x : (Fin n × Fin n) → ℝ) :
    realGaussianExteriorRootPower n k x =
      realGaussianPositiveRealExteriorPower n k x +
      realGaussianNegativeRealExteriorPower n k x +
      realGaussianNonrealExteriorPower n k x := by
  simpa only [realGaussianExteriorRootPower,
    realGaussianPositiveRealExteriorPower,
    realGaussianNegativeRealExteriorPower,
    realGaussianNonrealExteriorPower] using
    matrixExteriorRootPower_partition
      (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) k

/-- Three finite-dimensional weighted one-point identities, one for each
root class, suffice for the combined envelope needed by the Gaussian
power-moment argument. The identities themselves remain to be derived
from the Gaussian matrix law. -/
theorem realGaussianExteriorRootPower_onePoint_transfer (n k : ℕ)
    (hPosInt : Integrable (realGaussianPositiveRealExteriorPower n k)
      (gaussianMatrixLaw n))
    (hNegInt : Integrable (realGaussianNegativeRealExteriorPower n k)
      (gaussianMatrixLaw n))
    (hNonInt : Integrable (realGaussianNonrealExteriorPower n k)
      (gaussianMatrixLaw n))
    (hPos : (∫ x, realGaussianPositiveRealExteriorPower n k x
      ∂gaussianMatrixLaw n) ≤
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreFirstDensity n x) +
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreDominantDensity n x))
    (hNeg : (∫ x, realGaussianNegativeRealExteriorPower n k x
      ∂gaussianMatrixLaw n) ≤
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreFirstDensity n x) +
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreDominantDensity n x))
    (hNon : (∫ x, realGaussianNonrealExteriorPower n k x
      ∂gaussianMatrixLaw n) ≤
        (∫ z : ℂ in {z | 1 < ‖z‖},
          ‖z‖^(2*k)*realGinibreNonrealDensityAt n z)) :
    Integrable (realGaussianExteriorRootPower n k) (gaussianMatrixLaw n) ∧
    (∫ x, realGaussianExteriorRootPower n k x
      ∂gaussianMatrixLaw n) ≤
        realGinibreWeightedOnePointEnvelope n k := by
  have heq : realGaussianExteriorRootPower n k =
      (fun x => realGaussianPositiveRealExteriorPower n k x +
        realGaussianNegativeRealExteriorPower n k x +
        realGaussianNonrealExteriorPower n k x) :=
    funext (realGaussianExteriorRootPower_partition n k)
  constructor
  · rw [heq]
    exact (hPosInt.add hNegInt).add hNonInt
  · rw [heq]
    change (∫ x, ((realGaussianPositiveRealExteriorPower n k +
      realGaussianNegativeRealExteriorPower n k) +
      realGaussianNonrealExteriorPower n k) x ∂gaussianMatrixLaw n) ≤
        realGinibreWeightedOnePointEnvelope n k
    rw [integral_add' (hPosInt.add hNegInt) hNonInt,
      integral_add' hPosInt hNegInt]
    unfold realGinibreWeightedOnePointEnvelope
    linarith

/-- A concrete three-class version of the remaining finite-dimensional
Gaussian input. It uses the product-model-to-actual-Schur comparison as a
separate assumption and does not assume a Gaussian spectral-radius LDP. -/
theorem gaussianPowerUpperInput_of_three_weighted_onePoint_classes
    (hPosInt : ∀ n k, 3 ≤ n →
      Integrable (realGaussianPositiveRealExteriorPower n k)
        (gaussianMatrixLaw n))
    (hNegInt : ∀ n k, 3 ≤ n →
      Integrable (realGaussianNegativeRealExteriorPower n k)
        (gaussianMatrixLaw n))
    (hNonInt : ∀ n k, 3 ≤ n →
      Integrable (realGaussianNonrealExteriorPower n k)
        (gaussianMatrixLaw n))
    (hPos : ∀ n k, 3 ≤ n →
      (∫ x, realGaussianPositiveRealExteriorPower n k x
        ∂gaussianMatrixLaw n) ≤
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreFirstDensity n x) +
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreDominantDensity n x))
    (hNeg : ∀ n k, 3 ≤ n →
      (∫ x, realGaussianNegativeRealExteriorPower n k x
        ∂gaussianMatrixLaw n) ≤
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreFirstDensity n x) +
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreDominantDensity n x))
    (hNon : ∀ n k, 3 ≤ n →
      (∫ x, realGaussianNonrealExteriorPower n k x
        ∂gaussianMatrixLaw n) ≤
        (∫ z : ℂ in {z | 1 < ‖z‖},
          ‖z‖^(2*k)*realGinibreNonrealDensityAt n z))
    (hSchur : GaussianSchurPowerComparisonInput) :
    GaussianPowerUpperInput := by
  apply gaussianPowerUpperInput_of_onePoint_and_schur
  · intro n k hn
    exact (realGaussianExteriorRootPower_onePoint_transfer n k
      (hPosInt n k hn) (hNegInt n k hn) (hNonInt n k hn)
      (hPos n k hn) (hNeg n k hn) (hNon n k hn)).1
  · intro n k hn
    exact (realGaussianExteriorRootPower_onePoint_transfer n k
      (hPosInt n k hn) (hNegInt n k hn) (hNonInt n k hn)
      (hPos n k hn) (hNeg n k hn) (hNon n k hn)).2
  · exact hSchur

#print axioms realGaussianExteriorRootPower_partition
#print axioms realGaussianExteriorRootPower_onePoint_transfer
#print axioms gaussianPowerUpperInput_of_three_weighted_onePoint_classes
end SpectralRadiusUpperTail
