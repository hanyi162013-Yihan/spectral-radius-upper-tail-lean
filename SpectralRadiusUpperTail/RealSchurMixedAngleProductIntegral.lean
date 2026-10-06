import SpectralRadiusUpperTail.RealSchurMixedProductIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- Separate the angular variable without separating a general
observable of the diagonal and strict-upper matrix entries. -/
theorem realSchurMixed_lintegral_angle_entryProduct
    {m : ℕ} (s : Fin m → ℕ)
    (F : (RealSchurMixedOrbitIndex s → ℝ) → ℝ≥0∞)
    (K : ((RealSchurMixedDiagonalEntry s → ℝ) ×
      (RealSchurMixedStrictUpperEntry s → ℝ)) → ℝ≥0∞)
    (hF : Measurable F) (hK : Measurable K) :
    (∫⁻ x : RealSchurMixedTangent s,
      F (realSchurMixedTangentEntries s x).1 * K (realSchurMixedTangentEntries s x).2
        ∂realSchurMixedCoordinateVolume s) =
      (∫⁻ w, F w) * (∫⁻ d, ∫⁻ u, K (d,u)) := by
  have hmp : MeasurePreserving (realSchurMixedTangentEntries s)
      (realSchurMixedCoordinateVolume s) volume :=
    ⟨realSchurMixedTangentEntries_measurable s,realSchurMixedCoordinateVolume_entryProduct s⟩
  let H := fun z : (RealSchurMixedOrbitIndex s → ℝ) ×
      ((RealSchurMixedDiagonalEntry s → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ)) =>
    F z.1*K z.2
  have hH : Measurable H := (hF.comp measurable_fst).mul (hK.comp measurable_snd)
  change (∫⁻ x, H (realSchurMixedTangentEntries s x) ∂realSchurMixedCoordinateVolume s)=_
  rw [hmp.lintegral_comp hH]
  change (∫⁻ z, F z.1*K z.2 ∂((volume : Measure (RealSchurMixedOrbitIndex s → ℝ)).prod
    ((volume : Measure (RealSchurMixedDiagonalEntry s → ℝ)).prod
      (volume : Measure (RealSchurMixedStrictUpperEntry s → ℝ)))))=_
  rw [lintegral_prod_mul hF.aemeasurable hK.aemeasurable,
    lintegral_prod K hK.aemeasurable]

#print axioms realSchurMixed_lintegral_angle_entryProduct
end SpectralRadiusUpperTail
