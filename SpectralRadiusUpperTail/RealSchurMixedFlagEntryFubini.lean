import SpectralRadiusUpperTail.RealSchurMixedAngleProductIntegral
import SpectralRadiusUpperTail.RealSchurMixedFlagFiberIntegration

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- Tonelli on a selected coded source, for a general observable of
the diagonal and strict-upper entries. The inner integral ranges over
the entire strict-upper array. -/
theorem realSchurMixedFlagCodedSource_lintegral_entry_fubini
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (F : (RealSchurMixedOrbitIndex s → ℝ) → ℝ≥0∞)
    (K : ((RealSchurMixedDiagonalEntry s → ℝ) ×
      (RealSchurMixedStrictUpperEntry s → ℝ)) → ℝ≥0∞)
    (hF : Measurable F) (hK : Measurable K) :
    (∫⁻ x in realSchurMixedFlagCodedSource s hs c hc R k code,
      F (realSchurMixedTangentEntries s x).1*K (realSchurMixedTangentEntries s x).2
        ∂realSchurMixedCoordinateVolume s) =
      (∫⁻ w in realSchurMixedFlagAnglePatch s hs c hc R k, F w) *
        (∫⁻ d in realSchurMixedDiagonalCodeSource s code, ∫⁻ u, K (d,u)) := by
  classical
  let A := realSchurMixedFlagAnglePatch s hs c hc R k
  let D := realSchurMixedDiagonalCodeSource s code
  let S := realSchurMixedFlagCodedSource s hs c hc R k code
  have hA : MeasurableSet A := measurableSet_realSchurMixedFlagAnglePatch s hs c hc R k
  have hD : MeasurableSet D := measurableSet_realSchurMixedDiagonalCodeSource s code
  have hS : MeasurableSet S := measurableSet_realSchurMixedFlagCodedSource s hs c hc R k code
  let K' := (Prod.fst ⁻¹' D).indicator K
  have hK' : Measurable K' := hK.indicator (hD.preimage measurable_fst)
  have hpoint (x : RealSchurMixedTangent s) :
      S.indicator (fun x => F (realSchurMixedTangentEntries s x).1 *
        K (realSchurMixedTangentEntries s x).2) x =
      A.indicator F (realSchurMixedTangentEntries s x).1 *
        K' (realSchurMixedTangentEntries s x).2 := by
    have hm : x ∈ S ↔ (realSchurMixedTangentEntries s x).1 ∈ A ∧
        (realSchurMixedTangentEntries s x).2.1 ∈ D :=
      realSchurMixedFlagCodedSource_mem_iff_entries s hs c hc R k code x
    by_cases ha : (realSchurMixedTangentEntries s x).1 ∈ A <;>
      by_cases hd : (realSchurMixedTangentEntries s x).2.1 ∈ D <;>
        simp [K',Set.mem_preimage,hm,ha,hd]
  change (∫⁻ x in S, F (realSchurMixedTangentEntries s x).1 *
    K (realSchurMixedTangentEntries s x).2 ∂realSchurMixedCoordinateVolume s)=_
  rw [← lintegral_indicator hS]
  simp_rw [hpoint]
  rw [realSchurMixed_lintegral_angle_entryProduct s (A.indicator F) K' (hF.indicator hA) hK',
    lintegral_indicator hA]
  congr 1
  have hinner (d : RealSchurMixedDiagonalEntry s → ℝ) :
      (∫⁻ u, K' (d,u))=D.indicator (fun d => ∫⁻ u, K (d,u)) d := by
    by_cases hd : d ∈ D <;> simp [K',Set.mem_preimage,hd]
  simp_rw [hinner]
  exact lintegral_indicator hD _

#print axioms realSchurMixedFlagCodedSource_lintegral_entry_fubini
end SpectralRadiusUpperTail
