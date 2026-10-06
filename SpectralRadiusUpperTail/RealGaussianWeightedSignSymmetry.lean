import SpectralRadiusUpperTail.MatrixCharpolyNegRoots
import SpectralRadiusUpperTail.GaussianMatrixSignSymmetry
import SpectralRadiusUpperTail.RealGaussianWeightedOnePointTransfer
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- For an individual real matrix, reversing the sign of every entry swaps
the positive- and negative-real weighted root statistics. -/
theorem realGaussianPositiveRealExteriorPower_neg (n k : ℕ)
    (x : (Fin n × Fin n) → ℝ) :
    realGaussianPositiveRealExteriorPower n k (-x) =
      realGaussianNegativeRealExteriorPower n k x := by
  have hmatrix :
      (((1/Real.sqrt (n : ℝ)) • entryMatrix (-x)).map Complex.ofRealHom) =
        -(((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) := by
    ext i j
    simp [entryMatrix, Matrix.smul_apply, Matrix.map_apply]
  change matrixPositiveRealExteriorPower
      (((1/Real.sqrt (n : ℝ)) • entryMatrix (-x)).map Complex.ofRealHom) k =
    matrixNegativeRealExteriorPower
      (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) k
  rw [hmatrix, matrixPositiveRealExteriorPower_neg]

/-- The two real half-line weighted expectations coincide under the actual
finite Gaussian matrix law. -/
theorem realGaussianWeightedRealHalflines_equal (n k : ℕ)
    (hPos : Integrable (realGaussianPositiveRealExteriorPower n k)
      (gaussianMatrixLaw n)) :
    (∫ x, realGaussianNegativeRealExteriorPower n k x
      ∂gaussianMatrixLaw n) =
    (∫ x, realGaussianPositiveRealExteriorPower n k x
      ∂gaussianMatrixLaw n) := by
  let μ := gaussianMatrixLaw n
  have hmap : μ.map (fun x : (Fin n × Fin n) → ℝ => -x) = μ :=
    gaussianMatrixLaw_map_neg n
  have hposMap : AEStronglyMeasurable
      (realGaussianPositiveRealExteriorPower n k)
      (μ.map (fun x : (Fin n × Fin n) → ℝ => -x)) := by
    rw [hmap]
    exact hPos.aestronglyMeasurable
  calc
    (∫ x, realGaussianNegativeRealExteriorPower n k x ∂μ) =
        ∫ x, realGaussianPositiveRealExteriorPower n k (-x) ∂μ := by
      congr 1
      funext x
      exact (realGaussianPositiveRealExteriorPower_neg n k x).symm
    _ = ∫ x, realGaussianPositiveRealExteriorPower n k x
        ∂(μ.map (fun x : (Fin n × Fin n) → ℝ => -x)) := by
      exact (integral_map (by fun_prop) hposMap).symm
    _ = _ := by rw [hmap]

theorem realGaussianNegativeRealExteriorPower_integrable (n k : ℕ)
    (hPos : Integrable (realGaussianPositiveRealExteriorPower n k)
      (gaussianMatrixLaw n)) :
    Integrable (realGaussianNegativeRealExteriorPower n k)
      (gaussianMatrixLaw n) := by
  let μ := gaussianMatrixLaw n
  have hmap : μ.map (fun x : (Fin n × Fin n) → ℝ => -x) = μ :=
    gaussianMatrixLaw_map_neg n
  have hPosMap : Integrable (realGaussianPositiveRealExteriorPower n k)
      (μ.map (fun x : (Fin n × Fin n) → ℝ => -x)) := by
    rwa [hmap]
  have hcomp := hPosMap.comp_aemeasurable (by fun_prop :
    AEMeasurable (fun x : (Fin n × Fin n) → ℝ => -x) μ)
  apply hcomp.congr
  filter_upwards [] with x
  exact (realGaussianPositiveRealExteriorPower_neg n k x)

/-- The negative-real one-point input is redundant: Gaussian sign symmetry
reduces the weighted power upper bound to the positive-real and nonreal
finite-dimensional formulas plus the actual-Schur transfer. -/
theorem gaussianPowerUpperInput_of_two_weighted_onePoint_classes
    (hPosInt : ∀ n k, 3 ≤ n →
      Integrable (realGaussianPositiveRealExteriorPower n k)
        (gaussianMatrixLaw n))
    (hNonInt : ∀ n k, 3 ≤ n →
      Integrable (realGaussianNonrealExteriorPower n k)
        (gaussianMatrixLaw n))
    (hPos : ∀ n k, 3 ≤ n →
      (∫ x, realGaussianPositiveRealExteriorPower n k x
        ∂gaussianMatrixLaw n) ≤
        (∫ x in Set.Ioi (1 : ℝ),
          x^(2*k)*realGinibreFirstDensity n x) +
        (∫ x in Set.Ioi (1 : ℝ),
          x^(2*k)*realGinibreDominantDensity n x))
    (hNon : ∀ n k, 3 ≤ n →
      (∫ x, realGaussianNonrealExteriorPower n k x
        ∂gaussianMatrixLaw n) ≤
        (∫ z : ℂ in {z | 1 < ‖z‖},
          ‖z‖^(2*k)*realGinibreNonrealDensityAt n z))
    (hSchur : GaussianSchurPowerComparisonInput) :
    GaussianPowerUpperInput := by
  apply gaussianPowerUpperInput_of_three_weighted_onePoint_classes
    hPosInt
    (fun n k hn => realGaussianNegativeRealExteriorPower_integrable n k
      (hPosInt n k hn))
    hNonInt hPos
  · intro n k hn
    rw [realGaussianWeightedRealHalflines_equal n k (hPosInt n k hn)]
    exact hPos n k hn
  · exact hNon
  · exact hSchur

#print axioms realGaussianPositiveRealExteriorPower_neg
#print axioms realGaussianWeightedRealHalflines_equal
#print axioms realGaussianNegativeRealExteriorPower_integrable
#print axioms gaussianPowerUpperInput_of_two_weighted_onePoint_classes
end SpectralRadiusUpperTail
