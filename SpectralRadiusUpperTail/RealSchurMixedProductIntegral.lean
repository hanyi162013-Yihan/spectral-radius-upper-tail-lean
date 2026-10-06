import SpectralRadiusUpperTail.RealSchurMixedCoordinateProductVolume
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- Nonnegative integration in fixed mixed-Schur coordinates separates
exactly into lower, diagonal-block, and strict-upper-block entry integrals. -/
theorem realSchurMixed_lintegral_entryProduct
    {m : ℕ} (s : Fin m → ℕ)
    (F : (RealSchurMixedOrbitIndex s → ℝ) → ℝ≥0∞)
    (G : (RealSchurMixedDiagonalEntry s → ℝ) → ℝ≥0∞)
    (H : (RealSchurMixedStrictUpperEntry s → ℝ) → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H) :
    (∫⁻ x : RealSchurMixedTangent s,
      F (realSchurMixedTangentEntries s x).1 *
        (G (realSchurMixedTangentEntries s x).2.1 *
          H (realSchurMixedTangentEntries s x).2.2)
      ∂realSchurMixedCoordinateVolume s) =
      (∫⁻ ω, F ω) * ((∫⁻ d, G d) * (∫⁻ u, H u)) := by
  let K : ((RealSchurMixedOrbitIndex s → ℝ) ×
      ((RealSchurMixedDiagonalEntry s → ℝ) ×
        (RealSchurMixedStrictUpperEntry s → ℝ))) → ℝ≥0∞ :=
    fun z => F z.1 * (G z.2.1 * H z.2.2)
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
      F z.1 * (G z.2.1 * H z.2.2)
        ∂((volume : Measure (RealSchurMixedOrbitIndex s → ℝ)).prod
          ((volume : Measure (RealSchurMixedDiagonalEntry s → ℝ)).prod
            (volume : Measure (RealSchurMixedStrictUpperEntry s → ℝ))))) = _
  have hGH : AEMeasurable
      (fun z : (RealSchurMixedDiagonalEntry s → ℝ) ×
        (RealSchurMixedStrictUpperEntry s → ℝ) => G z.1 * H z.2)
      ((volume : Measure (RealSchurMixedDiagonalEntry s → ℝ)).prod
        (volume : Measure (RealSchurMixedStrictUpperEntry s → ℝ))) :=
    ((hG.comp measurable_fst).mul (hH.comp measurable_snd)).aemeasurable
  calc
    _ = (∫⁻ ω, F ω) *
        (∫⁻ z : (RealSchurMixedDiagonalEntry s → ℝ) ×
            (RealSchurMixedStrictUpperEntry s → ℝ),
          G z.1 * H z.2 ∂((volume : Measure (RealSchurMixedDiagonalEntry s → ℝ)).prod
            (volume : Measure (RealSchurMixedStrictUpperEntry s → ℝ)))) :=
      lintegral_prod_mul hF.aemeasurable hGH
    _ = _ := by
      rw [lintegral_prod_mul hG.aemeasurable hH.aemeasurable]

#print axioms realSchurMixed_lintegral_entryProduct
end SpectralRadiusUpperTail
