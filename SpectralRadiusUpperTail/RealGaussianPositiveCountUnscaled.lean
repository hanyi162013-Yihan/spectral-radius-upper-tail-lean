import SpectralRadiusUpperTail.MarkedRealStereoNormalizedCount
import SpectralRadiusUpperTail.MarkedRealStereoAngularNormalization
import SpectralRadiusUpperTail.MarkedRealHemisphereCoefficient
import SpectralRadiusUpperTail.GaussianMarkedRealUnscaledWeight
import SpectralRadiusUpperTail.MarkedRealGaussianPositiveCountArea

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- The marked real-root tail under the actual iid Gaussian matrix law
equals the explicit one-point integral, with all angular constants evaluated. -/
theorem realGaussian_markedRootCount_unscaled
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∫⁻ a : (Fin (m+1) × Fin (m+1)) → ℝ,
      markedRealSimpleRootCount m b
        (Matrix.reindex (markedRealIndexEquiv m)
          (markedRealIndexEquiv m) (Matrix.of a.curry))
        ∂gaussianMatrixLaw (m+1)) =
      ∫⁻ x in Set.Ioi b, gaussianMarkedRealUnscaledWeight m x := by
  rw [realGaussian_markedRootCount_stereo_moment m hm b,
    markedRealStereoAngularWeight_lintegral]
  let c : ℝ := (2 : ℝ)^(-(((m : ℝ)+1)/2)) / Real.Gamma (((m : ℝ)+1)/2)
  have hcoef :
      ENNReal.ofReal ((Real.sqrt Real.pi)^(m+1) / Real.Gamma (((m : ℝ)+1)/2)) *
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m+1)))⁻¹ = ENNReal.ofReal c := by
    simpa only [Nat.cast_add, Nat.cast_one, c] using
      markedRealHemisphere_gaussianColumnCoefficient_ennreal (m+1) (by omega)
  have hI : (∫⁻ x : ℝ, if b < x then
      ENNReal.ofReal (Real.exp (-x^2/2)) * markedRealGaussianCharpolyMoment m x else 0) =
      ∫⁻ x in Set.Ioi b,
        ENNReal.ofReal (Real.exp (-x^2/2)) * markedRealGaussianCharpolyMoment m x := by
    simpa only [Set.indicator, Set.mem_Ioi] using
      lintegral_indicator (μ := (volume : Measure ℝ)) measurableSet_Ioi
        (fun x => ENNReal.ofReal (Real.exp (-x^2/2)) * markedRealGaussianCharpolyMoment m x)
  rw [mul_right_comm _ _ ((ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m+1)))⁻¹),
    hcoef, hI, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  exact (mul_assoc _ _ _).symm

/-- Positive exterior real-root expectation, with the unscaled cutoff
appropriate to a matrix divided by sqrt(m+1). -/
theorem realGaussian_positiveCount_unscaled
    (m : ℕ) (hm : 0 < m) (r : ℝ) :
    ENNReal.ofReal
      (∫ a, realGaussianExteriorCount (m+1) r 0 a ∂gaussianMatrixLaw (m+1)) =
      ∫⁻ x in Set.Ioi (r * Real.sqrt ((m+1 : ℕ) : ℝ)),
        gaussianMarkedRealUnscaledWeight m x := by
  rw [← realGaussianExteriorCount_lintegral_eq_ofReal_expectation
    (m+1) (by omega) r 0]
  calc
    _ = ∫⁻ a, markedRealSimpleRootCount m (r*Real.sqrt ((m+1 : ℕ) : ℝ))
        (Matrix.reindex (markedRealIndexEquiv m)
          (markedRealIndexEquiv m) (Matrix.of a.curry)) ∂gaussianMatrixLaw (m+1) := by
      apply lintegral_congr_ae
      filter_upwards [markedRealSimpleRootCount_eq_exteriorCount_ae m hm r] with a ha
      exact ha.symm
    _ = _ := realGaussian_markedRootCount_unscaled m hm _

#print axioms realGaussian_markedRootCount_unscaled
#print axioms realGaussian_positiveCount_unscaled
end SpectralRadiusUpperTail
