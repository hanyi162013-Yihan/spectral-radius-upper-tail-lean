import SpectralRadiusUpperTail.MatrixExteriorRootPowerFrobenius
import SpectralRadiusUpperTail.RealGaussianWeightedStatsAE
import SpectralRadiusUpperTail.DominatedMatrixTail
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix.Norms.Frobenius

theorem realGaussianExteriorRootPower_le_scaledFrobenius
    (n k : ℕ) (x : (Fin n × Fin n) → ℝ) :
    realGaussianExteriorRootPower n k x ≤
      (n : ℝ)*(1+scaledFrobeniusPowerSquared
        (1/Real.sqrt (n : ℝ)) k x) := by
  have h := matrixExteriorRootPower_le_dim_frobeniusPower
    (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) k
  rw [complexified_frobenius_power_norm, real_frobenius_norm_sq] at h
  simpa only [realGaussianExteriorRootPower,
    scaledFrobeniusPowerSquared] using h

theorem realGaussianExteriorRootPower_integrable
    (n k : ℕ) (hn : 0 < n) :
    Integrable (realGaussianExteriorRootPower n k)
      (gaussianMatrixLaw n) := by
  have hFrob : Integrable
      (scaledFrobeniusPowerSquared (1/Real.sqrt (n : ℝ)) k)
      (gaussianMatrixLaw n) := by
    exact product_scaledFrobeniusPowerSquared_integrable
      (fun _ => standardNormal)
      (fun _ k => standardNormal_pow_integrable k)
      (1/Real.sqrt (n : ℝ)) k
  have henv : Integrable
      (fun x : (Fin n × Fin n) → ℝ =>
        (n : ℝ)*(1+scaledFrobeniusPowerSquared
          (1/Real.sqrt (n : ℝ)) k x))
      (gaussianMatrixLaw n) :=
    ((integrable_const _).add hFrob).const_mul (n : ℝ)
  apply henv.mono'
    (realGaussianExteriorRootPower_aemeasurable n k hn).aestronglyMeasurable
  filter_upwards [] with x
  have hroot0 : 0 ≤ realGaussianExteriorRootPower n k x :=
    matrixExteriorRootPower_nonneg _ k
  have hfrob0 : 0 ≤ scaledFrobeniusPowerSquared
      (1/Real.sqrt (n : ℝ)) k x :=
    scaledFrobeniusPowerSquared_nonneg _ _ _
  have henv0 : 0 ≤ (n : ℝ)*(1+scaledFrobeniusPowerSquared
      (1/Real.sqrt (n : ℝ)) k x) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hroot0,
    abs_of_nonneg henv0] using
      realGaussianExteriorRootPower_le_scaledFrobenius n k x

#print axioms realGaussianExteriorRootPower_le_scaledFrobenius
#print axioms realGaussianExteriorRootPower_integrable
end SpectralRadiusUpperTail
