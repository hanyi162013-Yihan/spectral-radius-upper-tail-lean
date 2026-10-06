import SpectralRadiusUpperTail.RealGaussianSchurPowerConditional
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Scalar Gaussian radius-moment estimate supplied by the real-Ginibre
spectral-radius LDP together with control of the unbounded tail. This is
an explicit external input here: the LDP-to-moment argument is not yet
formalized from the actual Gaussian law. Only an upper bound is needed. -/
def GaussianRadiusMomentUpperInput : Prop :=
  ∀ α : ℝ, 0 < α → ∀ δ : ℝ, 0 < δ →
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      (∫ x, realGaussianShiftedRadiusPower n ⌊α*(n : ℝ)⌋₊ η x
        ∂gaussianMatrixLaw n) ≤
        Real.exp ((n : ℝ)*(powerRate 1 α+δ))

/-- The two logically separate Gaussian inputs used in the manuscript
imply exactly the power upper bound needed by the real matching theorem. -/
theorem gaussianPowerUpperInput_of_radiusMoment_and_schur
    (hRadius : GaussianRadiusMomentUpperInput)
    (hSchur : GaussianSchurPowerComparisonInput) :
    GaussianPowerUpperInput := by
  intro α hα δ hδ
  have hhalf : 0 < δ/2 := by linarith
  obtain ⟨η,hη,hMoment⟩ := hRadius α hα (δ/2) hhalf
  have hSchurEv := hSchur α hα η hη (δ/2) hhalf
  filter_upwards [hMoment, hSchurEv] with n hm hs
  calc
    gaussianPowerMoment n ⌊α*(n : ℝ)⌋₊ ≤
        Real.exp ((n : ℝ)*(δ/2)) *
          (∫ x, realGaussianShiftedRadiusPower n
            ⌊α*(n : ℝ)⌋₊ η x ∂gaussianMatrixLaw n) := hs
    _ ≤ Real.exp ((n : ℝ)*(δ/2)) *
        Real.exp ((n : ℝ)*(powerRate 1 α+δ/2)) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = Real.exp ((n : ℝ)*(powerRate 1 α+δ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

#print axioms gaussianPowerUpperInput_of_radiusMoment_and_schur
end SpectralRadiusUpperTail
