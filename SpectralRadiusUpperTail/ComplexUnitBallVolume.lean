import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace SpectralRadiusUpperTail
open MeasureTheory Metric

theorem complex_unit_ball_volume_real :
    (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
  simp [Measure.real, Complex.volume_ball]

#print axioms complex_unit_ball_volume_real
end SpectralRadiusUpperTail
