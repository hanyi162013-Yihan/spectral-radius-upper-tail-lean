import SpectralRadiusUpperTail.MarkedRealGaussianCharpolyMoment
import SpectralRadiusUpperTail.GaussianCharpolyAbsoluteMomentExterior
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- The nonnegative moment in the local Schur formula is the ordinary
finite Gaussian expectation used in the sharp exterior bound. -/
theorem markedRealGaussianCharpolyMoment_eq_ofReal_integral
    (m : ℕ) (x : ℝ) :
    markedRealGaussianCharpolyMoment m x =
      ENNReal.ofReal
        (∫ a : (Fin m × Fin m) → ℝ,
          |(Matrix.of a.curry).charpoly.eval x|
            ∂Measure.pi (fun _ => standardNormal)) := by
  classical
  exact (ofReal_integral_eq_lintegral_ofReal
    (gaussian_charpoly_integrable (ι := Fin m) x).abs
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))).symm

theorem markedRealGaussianCharpolyMoment_lt_top
    (m : ℕ) (x : ℝ) :
    markedRealGaussianCharpolyMoment m x < ∞ := by
  rw [markedRealGaussianCharpolyMoment_eq_ofReal_integral]
  exact ENNReal.ofReal_lt_top

#print axioms markedRealGaussianCharpolyMoment_eq_ofReal_integral
#print axioms markedRealGaussianCharpolyMoment_lt_top
end SpectralRadiusUpperTail
