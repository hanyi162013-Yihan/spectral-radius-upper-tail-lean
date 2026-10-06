import SpectralRadiusUpperTail.RealGaussianRootPowerIntegrable
import SpectralRadiusUpperTail.MatrixExteriorSubstatBounds
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

theorem realGaussianPositiveRealExteriorPower_integrable
    (n k : ℕ) (hn : 0 < n) :
    Integrable (realGaussianPositiveRealExteriorPower n k)
      (gaussianMatrixLaw n) := by
  apply (realGaussianExteriorRootPower_integrable n k hn).mono'
    (realGaussianPositiveRealExteriorPower_aemeasurable n k hn).aestronglyMeasurable
  filter_upwards [] with x
  let A : Matrix (Fin n) (Fin n) ℂ :=
    (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom)
  have hp := matrixPositiveRealExteriorPower_nonneg_le_total A k
  change ‖matrixPositiveRealExteriorPower A k‖ ≤
    matrixExteriorRootPower A k
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp.1] using hp.2

theorem realGaussianUpperNonrealExteriorPower_integrable
    (n k : ℕ) (hn : 0 < n) :
    Integrable (realGaussianUpperNonrealExteriorPower n k)
      (gaussianMatrixLaw n) := by
  apply (realGaussianExteriorRootPower_integrable n k hn).mono'
    (realGaussianUpperNonrealExteriorPower_aemeasurable n k hn).aestronglyMeasurable
  filter_upwards [] with x
  let A : Matrix (Fin n) (Fin n) ℝ :=
    (1/Real.sqrt (n : ℝ)) • entryMatrix x
  have hp := realMatrixUpperNonrealExteriorPower_nonneg_le_total A k
  change ‖realMatrixUpperNonrealExteriorPower A k‖ ≤
    matrixExteriorRootPower (A.map Complex.ofRealHom) k
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp.1] using hp.2

#print axioms realGaussianPositiveRealExteriorPower_integrable
#print axioms realGaussianUpperNonrealExteriorPower_integrable
end SpectralRadiusUpperTail
