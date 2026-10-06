import SpectralRadiusUpperTail.MatrixExteriorRootPower
import SpectralRadiusUpperTail.SpectralMeasurable
import SpectralRadiusUpperTail.MatrixMoments
import SpectralRadiusUpperTail.RealGinibreWeightedOnePointEnvelope
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- Exterior root-power statistic of the actual normalized real Gaussian
matrix, before taking any expectation. -/
noncomputable def realGaussianExteriorRootPower (n k : ℕ)
    (x : (Fin n × Fin n) → ℝ) : ℝ :=
  matrixExteriorRootPower
    (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) k

noncomputable def realGaussianClippedRadiusPower (n k : ℕ)
    (x : (Fin n × Fin n) → ℝ) : ℝ :=
  (max 1 (realMatrixRadius
    ((1/Real.sqrt (n : ℝ)) • entryMatrix x)))^(2*k)

theorem realGaussianClippedRadiusPower_le_rootPower
    (n k : ℕ) (hn : 0 < n) (x : (Fin n × Fin n) → ℝ) :
    realGaussianClippedRadiusPower n k x ≤
      1+realGaussianExteriorRootPower n k x := by
  simpa only [realGaussianClippedRadiusPower,
    realGaussianExteriorRootPower, realMatrixRadius] using
    matrix_clipped_radius_power_le_exterior_sum hn
      (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) k

theorem realGaussianClippedRadiusPower_measurable (n k : ℕ) :
    Measurable (realGaussianClippedRadiusPower n k) := by
  have hm : Measurable (fun x : (Fin n × Fin n) → ℝ =>
      realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix x)) :=
    realMatrixRadius_measurable.comp
      (scaled_entryMatrix_continuous (1/Real.sqrt (n : ℝ))).measurable
  unfold realGaussianClippedRadiusPower
  exact (measurable_const.max hm).pow_const _

theorem realGaussianClippedRadiusPower_integrable
    (n k : ℕ) (hn : 0 < n)
    (hroot : Integrable (realGaussianExteriorRootPower n k)
      (gaussianMatrixLaw n)) :
    Integrable (realGaussianClippedRadiusPower n k)
      (gaussianMatrixLaw n) := by
  have hupper : Integrable
      (fun x => 1+realGaussianExteriorRootPower n k x)
      (gaussianMatrixLaw n) := (integrable_const _).add hroot
  apply hupper.mono'
    (realGaussianClippedRadiusPower_measurable n k).aestronglyMeasurable
  filter_upwards [] with x
  have hroot0 : 0 ≤ realGaussianExteriorRootPower n k x :=
    matrixExteriorRootPower_nonneg _ k
  have hclip0 : 0 ≤ realGaussianClippedRadiusPower n k x := by
    unfold realGaussianClippedRadiusPower
    have hbase : 0 ≤ max 1 (realMatrixRadius
        ((1/Real.sqrt (n : ℝ)) • entryMatrix x)) :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
    exact pow_nonneg hbase _
  have h := realGaussianClippedRadiusPower_le_rootPower n k hn x
  simpa only [Real.norm_eq_abs, abs_of_nonneg hclip0,
    abs_of_nonneg (by linarith : 0 ≤ 1+realGaussianExteriorRootPower n k x)]
    using h

/-- A weighted one-point expectation bound transfers to the clipped
spectral-radius power of the actual Gaussian matrix. The finite-dimensional
one-point identity itself remains an explicit input. -/
theorem realGaussianClippedRadiusPower_integral_le_rootPower
    (n k : ℕ) (hn : 0 < n)
    (hroot : Integrable (realGaussianExteriorRootPower n k)
      (gaussianMatrixLaw n)) :
    (∫ x, realGaussianClippedRadiusPower n k x ∂gaussianMatrixLaw n) ≤
      1+(∫ x, realGaussianExteriorRootPower n k x
        ∂gaussianMatrixLaw n) := by
  have hupper : Integrable
      (fun x => 1+realGaussianExteriorRootPower n k x)
      (gaussianMatrixLaw n) := (integrable_const _).add hroot
  have hclip := realGaussianClippedRadiusPower_integrable n k hn hroot
  have hmono := integral_mono hclip hupper
    (fun x => realGaussianClippedRadiusPower_le_rootPower n k hn x)
  rw [integral_add (integrable_const _) hroot] at hmono
  simpa only [integral_const, probReal_univ, one_smul] using hmono

theorem realGaussianClippedRadiusPower_integral_le_onePointEnvelope
    (n k : ℕ) (hn : 0 < n)
    (hroot : Integrable (realGaussianExteriorRootPower n k)
      (gaussianMatrixLaw n))
    (hidentity : (∫ x, realGaussianExteriorRootPower n k x
      ∂gaussianMatrixLaw n) ≤ realGinibreWeightedOnePointEnvelope n k) :
    (∫ x, realGaussianClippedRadiusPower n k x ∂gaussianMatrixLaw n) ≤
      1+realGinibreWeightedOnePointEnvelope n k := by
  exact (realGaussianClippedRadiusPower_integral_le_rootPower n k hn hroot).trans
    (add_le_add_right hidentity 1)

#print axioms realGaussianClippedRadiusPower_le_rootPower
#print axioms realGaussianClippedRadiusPower_measurable
#print axioms realGaussianClippedRadiusPower_integrable
#print axioms realGaussianClippedRadiusPower_integral_le_rootPower
#print axioms realGaussianClippedRadiusPower_integral_le_onePointEnvelope
end SpectralRadiusUpperTail
