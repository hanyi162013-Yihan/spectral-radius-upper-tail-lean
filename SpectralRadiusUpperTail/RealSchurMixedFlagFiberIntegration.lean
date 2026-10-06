import SpectralRadiusUpperTail.RealSchurMixedFlagFullFiber
import SpectralRadiusUpperTail.RealSchurMixedProductIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

theorem realSchurMixedFlagCodedSource_mem_iff_entries
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (x : RealSchurMixedTangent s) :
    x ∈ realSchurMixedFlagCodedSource s hs c hc R k code ↔
      (realSchurMixedTangentEntries s x).1 ∈ realSchurMixedFlagAnglePatch s hs c hc R k ∧
        (realSchurMixedTangentEntries s x).2.1 ∈ realSchurMixedDiagonalCodeSource s code := by
  have hx : realSchurMixedFiberPoint s x.1
      (realSchurMixedUpperEntryEquiv s x.2).1
      (realSchurMixedUpperEntryEquiv s x.2).2 = x := by
    apply Prod.ext
    · rfl
    · exact (realSchurMixedUpperEntryEquiv s).symm_apply_apply x.2
  have h := realSchurMixedFlagCodedSource_full_fiber s hs c hc R k code x.1
    (realSchurMixedUpperEntryEquiv s x.2).1 (realSchurMixedUpperEntryEquiv s x.2).2
  simpa only [hx, realSchurMixedTangentEntries] using h

/-- Exact product integration over the actual coded source. There is
no restriction or indicator on the strict-upper integration variable. -/
theorem realSchurMixedFlagCodedSource_lintegral_product
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (F : (RealSchurMixedOrbitIndex s → ℝ) → ℝ≥0∞)
    (G : (RealSchurMixedDiagonalEntry s → ℝ) → ℝ≥0∞)
    (H : (RealSchurMixedStrictUpperEntry s → ℝ) → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H) :
    (∫⁻ x in realSchurMixedFlagCodedSource s hs c hc R k code,
      F (realSchurMixedTangentEntries s x).1 *
        (G (realSchurMixedTangentEntries s x).2.1 *
          H (realSchurMixedTangentEntries s x).2.2)
        ∂realSchurMixedCoordinateVolume s) =
      (∫⁻ w in realSchurMixedFlagAnglePatch s hs c hc R k, F w) *
        ((∫⁻ d in realSchurMixedDiagonalCodeSource s code, G d) * (∫⁻ u, H u)) := by
  classical
  let A := realSchurMixedFlagAnglePatch s hs c hc R k
  let D := realSchurMixedDiagonalCodeSource s code
  let S := realSchurMixedFlagCodedSource s hs c hc R k code
  have hA : MeasurableSet A := measurableSet_realSchurMixedFlagAnglePatch s hs c hc R k
  have hD : MeasurableSet D := measurableSet_realSchurMixedDiagonalCodeSource s code
  have hS : MeasurableSet S := measurableSet_realSchurMixedFlagCodedSource s hs c hc R k code
  have hpoint (x : RealSchurMixedTangent s) :
      S.indicator (fun x => F (realSchurMixedTangentEntries s x).1 *
        (G (realSchurMixedTangentEntries s x).2.1 *
          H (realSchurMixedTangentEntries s x).2.2)) x =
      A.indicator F (realSchurMixedTangentEntries s x).1 *
        (D.indicator G (realSchurMixedTangentEntries s x).2.1 *
          H (realSchurMixedTangentEntries s x).2.2) := by
    have hm : x ∈ S ↔ (realSchurMixedTangentEntries s x).1 ∈ A ∧
        (realSchurMixedTangentEntries s x).2.1 ∈ D :=
      realSchurMixedFlagCodedSource_mem_iff_entries s hs c hc R k code x
    by_cases ha : (realSchurMixedTangentEntries s x).1 ∈ A <;>
      by_cases hd : (realSchurMixedTangentEntries s x).2.1 ∈ D <;>
        simp [hm, ha, hd]
  change (∫⁻ x in S, F (realSchurMixedTangentEntries s x).1 *
    (G (realSchurMixedTangentEntries s x).2.1 * H (realSchurMixedTangentEntries s x).2.2)
      ∂realSchurMixedCoordinateVolume s) = _
  rw [← lintegral_indicator hS]
  simp_rw [hpoint]
  rw [realSchurMixed_lintegral_entryProduct s (A.indicator F) (D.indicator G) H
    (hF.indicator hA) (hG.indicator hD) hH,
    lintegral_indicator hA, lintegral_indicator hD]

#print axioms realSchurMixedFlagCodedSource_mem_iff_entries
#print axioms realSchurMixedFlagCodedSource_lintegral_product
end SpectralRadiusUpperTail
