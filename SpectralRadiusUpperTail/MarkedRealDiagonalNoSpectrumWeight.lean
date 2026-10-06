import SpectralRadiusUpperTail.MarkedRealDiagonalExplicitWeight
import SpectralRadiusUpperTail.MarkedRealDiagonalSimpleSpectrumAE
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix BigOperators

/-- The same scalar/complement Gaussian integrand after the null
simple-spectrum exception has been removed. -/
noncomputable def markedRealNoSpectrumDiagonalWeight
    (m : ℕ) (b : ℝ) (z : ℝ × ((Fin m × Fin m) → ℝ)) : ℝ≥0∞ :=
  let H : Matrix (Fin m) (Fin m) ℝ := Matrix.of z.2.curry
  if b < z.1 then
    ENNReal.ofReal |(H - z.1 • (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
      (ENNReal.ofReal
        (Real.exp (-(z.1^2 + ∑ ij : Fin m × Fin m, (z.2 ij)^2)/2)) *
        ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
          (Fintype.card
            (RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m)))))
  else 0

theorem markedRealExplicitDiagonalWeight_eq_noSpectrum_ae
    (m : ℕ) (b : ℝ) :
    markedRealExplicitDiagonalWeight m b =ᵐ[volume]
      markedRealNoSpectrumDiagonalWeight m b := by
  filter_upwards [markedRealDiagonal_simpleSpectrum_ae_volume m] with z hs
  by_cases hb : b < z.1
  · simp [markedRealExplicitDiagonalWeight,
      markedRealNoSpectrumDiagonalWeight, hs, hb]
  · simp [markedRealExplicitDiagonalWeight,
      markedRealNoSpectrumDiagonalWeight, hb]

theorem markedRealExplicitDiagonalWeight_lintegral_noSpectrum
    (m : ℕ) (b : ℝ) :
    (∫⁻ z, markedRealExplicitDiagonalWeight m b z) =
      ∫⁻ z, markedRealNoSpectrumDiagonalWeight m b z := by
  exact lintegral_congr_ae
    (markedRealExplicitDiagonalWeight_eq_noSpectrum_ae m b)

#print axioms markedRealExplicitDiagonalWeight_lintegral_noSpectrum
end SpectralRadiusUpperTail
