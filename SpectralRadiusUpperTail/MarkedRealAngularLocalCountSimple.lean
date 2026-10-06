import SpectralRadiusUpperTail.MarkedRealAngularNormalizerRatio
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- In the local count bound, all Gaussian coordinates except the
marked first column cancel from the partition function. -/
theorem markedRealAngularLocalCountLower_simple
    (m : ℕ) (b : ℝ) :
    markedRealAngularLocalCountLower m b =
      (∫⁻ ω, markedRealAngularWeight m ω) *
        (∫⁻ x : ℝ,
          if b < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              markedRealGaussianCharpolyMoment m x
          else 0) *
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m+1)))⁻¹ := by
  let d : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2+m))
  have hd : d ≠ ∞ := by
    dsimp [d]
    exact ENNReal.ofReal_ne_top
  have hscalar :
      (∫⁻ x : ℝ,
        if b < x then
          ENNReal.ofReal (Real.exp (-x^2/2)) * d *
            markedRealGaussianCharpolyMoment m x
        else 0) =
      (∫⁻ x : ℝ,
        if b < x then
          ENNReal.ofReal (Real.exp (-x^2/2)) *
            markedRealGaussianCharpolyMoment m x
        else 0) * d := by
    calc
      (∫⁻ x : ℝ,
        if b < x then
          ENNReal.ofReal (Real.exp (-x^2/2)) * d *
            markedRealGaussianCharpolyMoment m x
        else 0) =
        ∫⁻ x : ℝ,
          (if b < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              markedRealGaussianCharpolyMoment m x
          else 0) * d := by
          apply lintegral_congr
          intro x
          by_cases hb : b < x
          · simp only [if_pos hb]
            ac_rfl
          · simp [hb]
      _ = _ := by
        rw [lintegral_mul_const' _ _ hd]
  unfold markedRealAngularLocalCountLower
  change (∫⁻ ω, markedRealAngularWeight m ω) *
      (∫⁻ x : ℝ,
        if b < x then
          ENNReal.ofReal (Real.exp (-x^2/2)) * d *
            markedRealGaussianCharpolyMoment m x
        else 0) *
      (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^
        ((Fintype.card
          (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)))⁻¹ = _
  rw [hscalar]
  calc
    (∫⁻ ω, markedRealAngularWeight m ω) *
        ((∫⁻ x : ℝ,
          if b < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              markedRealGaussianCharpolyMoment m x
          else 0) * d) *
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^
          ((Fintype.card
            (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)))⁻¹ =
      (∫⁻ ω, markedRealAngularWeight m ω) *
        (∫⁻ x : ℝ,
          if b < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              markedRealGaussianCharpolyMoment m x
          else 0) *
        (d * (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^
          ((Fintype.card
            (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)))⁻¹) := by
      ac_rfl
    _ = _ := by
      rw [show d * (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^
            ((Fintype.card
              (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)))⁻¹ =
          (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m+1)))⁻¹ from
        markedRealAngular_gaussianNormalizer_ratio m]

#print axioms markedRealAngularLocalCountLower_simple
end SpectralRadiusUpperTail
