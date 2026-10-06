import SpectralRadiusUpperTail.RealGaussianWeightedRadiusInterface
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable def realGaussianShiftedRadiusPower (n k : ℕ) (η : ℝ)
    (x : (Fin n × Fin n) → ℝ) : ℝ :=
  (max 1 (realMatrixRadius
    ((1/Real.sqrt (n : ℝ)) • entryMatrix x))+η)^(2*k)

/-- Adding a nonnegative radius buffer costs at most a deterministic factor
because the clipped radius is at least one. -/
theorem realGaussianShiftedRadiusPower_le_clipped
    (n k : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (x : (Fin n × Fin n) → ℝ) :
    realGaussianShiftedRadiusPower n k η x ≤
      (1+η)^(2*k)*realGaussianClippedRadiusPower n k x := by
  let R : ℝ := max 1 (realMatrixRadius
    ((1/Real.sqrt (n : ℝ)) • entryMatrix x))
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := by linarith
  have hη1 : 0 ≤ 1+η := by linarith
  have hle : R+η ≤ (1+η)*R := by
    have hh := mul_le_mul_of_nonneg_left hR hη
    nlinarith
  change (R+η)^(2*k) ≤ (1+η)^(2*k)*R^(2*k)
  calc
    _ ≤ ((1+η)*R)^(2*k) :=
      pow_le_pow_left₀ (by linarith) hle _
    _ = _ := by rw [mul_pow]

theorem realGaussianShiftedRadiusPower_measurable
    (n k : ℕ) (η : ℝ) :
    Measurable (realGaussianShiftedRadiusPower n k η) := by
  have hm : Measurable (fun x : (Fin n × Fin n) → ℝ =>
      realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix x)) :=
    realMatrixRadius_measurable.comp
      (scaled_entryMatrix_continuous (1/Real.sqrt (n : ℝ))).measurable
  unfold realGaussianShiftedRadiusPower
  exact ((measurable_const.max hm).add_const η).pow_const _

/-- Conditional on integrability of the exterior root-power statistic,
the buffered radius moment is controlled by the clipped radius moment. -/
theorem realGaussianShiftedRadiusPower_integral_le
    (n k : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 ≤ η)
    (hroot : Integrable (realGaussianExteriorRootPower n k)
      (gaussianMatrixLaw n)) :
    (∫ x, realGaussianShiftedRadiusPower n k η x
      ∂gaussianMatrixLaw n) ≤
      (1+η)^(2*k)*
        (∫ x, realGaussianClippedRadiusPower n k x
          ∂gaussianMatrixLaw n) := by
  have hclip := realGaussianClippedRadiusPower_integrable n k hn hroot
  have hfactor : 0 ≤ (1+η)^(2*k) := pow_nonneg (by linarith) _
  have henv : Integrable
      (fun x => (1+η)^(2*k)*realGaussianClippedRadiusPower n k x)
      (gaussianMatrixLaw n) := hclip.const_mul _
  have hshift : Integrable (realGaussianShiftedRadiusPower n k η)
      (gaussianMatrixLaw n) := by
    apply henv.mono'
      (realGaussianShiftedRadiusPower_measurable n k η).aestronglyMeasurable
    filter_upwards [] with x
    have hR : 0 ≤ max 1 (realMatrixRadius
        ((1/Real.sqrt (n : ℝ)) • entryMatrix x)) :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
    have hleft : 0 ≤ realGaussianShiftedRadiusPower n k η x := by
      unfold realGaussianShiftedRadiusPower
      exact pow_nonneg (add_nonneg hR hη) _
    have hright : 0 ≤ (1+η)^(2*k)*
        realGaussianClippedRadiusPower n k x := by
      apply mul_nonneg hfactor
      unfold realGaussianClippedRadiusPower
      exact pow_nonneg hR _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleft,
      abs_of_nonneg hright] using
        realGaussianShiftedRadiusPower_le_clipped n k η hη x
  have hmono := integral_mono hshift henv
    (fun x => realGaussianShiftedRadiusPower_le_clipped n k η hη x)
  simpa only [integral_const_mul] using hmono

#print axioms realGaussianShiftedRadiusPower_le_clipped
#print axioms realGaussianShiftedRadiusPower_measurable
#print axioms realGaussianShiftedRadiusPower_integral_le
end SpectralRadiusUpperTail
