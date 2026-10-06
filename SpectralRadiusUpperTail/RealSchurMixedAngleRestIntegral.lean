import SpectralRadiusUpperTail.RealSchurMixedCoordinateProductVolume
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- The exact coordinate-volume separation needed for a rank-layer
Schur integral: the angular array is independent of all upper entries,
while the diagonal and free upper entries may still be coupled. -/
theorem realSchurMixed_lintegral_angleRest
    {r : ℕ} (s : Fin r → ℕ)
    (F : (RealSchurMixedOrbitIndex s → ℝ) → ℝ≥0∞)
    (G : ((RealSchurMixedDiagonalEntry s → ℝ) ×
      (RealSchurMixedStrictUpperEntry s → ℝ)) → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ x : RealSchurMixedTangent s,
      F x.1 * G (realSchurMixedUpperEntryEquiv s x.2)
        ∂realSchurMixedCoordinateVolume s) =
      (∫⁻ ω, F ω) * (∫⁻ z, G z) := by
  let K : ((RealSchurMixedOrbitIndex s → ℝ) ×
      ((RealSchurMixedDiagonalEntry s → ℝ) ×
        (RealSchurMixedStrictUpperEntry s → ℝ))) → ℝ≥0∞ :=
    fun z => F z.1 * G z.2
  have hK : Measurable K := by
    dsimp [K]
    fun_prop
  have hmp : MeasurePreserving (realSchurMixedTangentEntries s)
      (realSchurMixedCoordinateVolume s) volume :=
    ⟨realSchurMixedTangentEntries_measurable s,
      realSchurMixedCoordinateVolume_entryProduct s⟩
  change (∫⁻ x, K (realSchurMixedTangentEntries s x)
      ∂realSchurMixedCoordinateVolume s) = _
  rw [hmp.lintegral_comp hK]
  change (∫⁻ z : ((RealSchurMixedOrbitIndex s → ℝ) ×
      ((RealSchurMixedDiagonalEntry s → ℝ) ×
        (RealSchurMixedStrictUpperEntry s → ℝ))),
        F z.1 * G z.2
          ∂((volume : Measure (RealSchurMixedOrbitIndex s → ℝ)).prod
            (volume : Measure ((RealSchurMixedDiagonalEntry s → ℝ) ×
              (RealSchurMixedStrictUpperEntry s → ℝ))))) = _
  exact lintegral_prod_mul hF.aemeasurable hG.aemeasurable

#print axioms realSchurMixed_lintegral_angleRest
end SpectralRadiusUpperTail
