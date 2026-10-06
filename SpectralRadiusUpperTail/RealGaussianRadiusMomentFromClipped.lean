import SpectralRadiusUpperTail.ShiftedFloorPowerBudget
import SpectralRadiusUpperTail.RealGaussianRadiusMomentBoundary
import SpectralRadiusUpperTail.RealGaussianRootPowerIntegrable

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The actual clipped-radius moment upper estimate is sufficient for the
buffered moment interface. All required Gaussian integrability is proved. -/
theorem gaussianRadiusMomentUpperInput_of_clipped
    (hclip : ∀ α : ℝ, 0 < α → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop,
        (∫ a, realGaussianClippedRadiusPower n ⌊α*(n : ℝ)⌋₊ a
          ∂gaussianMatrixLaw n) ≤
            Real.exp ((n : ℝ)*(powerRate 1 α+δ))) :
    GaussianRadiusMomentUpperInput := by
  intro α hα δ hδ
  have hhalf : 0 < δ/2 := by linarith
  obtain ⟨η,hη,hfactor⟩ := exists_small_buffer_floor_power_bound α (δ/2) hα hhalf
  refine ⟨η,hη,?_⟩
  filter_upwards [eventually_gt_atTop 0, hclip α hα (δ/2) hhalf] with n hn hc
  have hclip0 : 0 ≤ ∫ a, realGaussianClippedRadiusPower n ⌊α*(n : ℝ)⌋₊ a
      ∂gaussianMatrixLaw n := by
    apply integral_nonneg
    intro a
    unfold realGaussianClippedRadiusPower
    exact pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) _
  calc
    _ ≤ (1+η)^(2*⌊α*(n : ℝ)⌋₊)*
        (∫ a, realGaussianClippedRadiusPower n ⌊α*(n : ℝ)⌋₊ a
          ∂gaussianMatrixLaw n) :=
      realGaussianShiftedRadiusPower_integral_le n _ hn η hη.le
        (realGaussianExteriorRootPower_integrable n _ hn)
    _ ≤ Real.exp ((n : ℝ)*(δ/2))*
        (∫ a, realGaussianClippedRadiusPower n ⌊α*(n : ℝ)⌋₊ a
          ∂gaussianMatrixLaw n) :=
      mul_le_mul_of_nonneg_right (hfactor n) hclip0
    _ ≤ Real.exp ((n : ℝ)*(δ/2))*
        Real.exp ((n : ℝ)*(powerRate 1 α+δ/2)) :=
      mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

#print axioms gaussianRadiusMomentUpperInput_of_clipped
end SpectralRadiusUpperTail
