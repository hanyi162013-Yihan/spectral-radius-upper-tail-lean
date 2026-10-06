import SpectralRadiusUpperTail.RealSchurMixedRegularPatchIntegration
import SpectralRadiusUpperTail.RealSchurMixedRegularOpenLocus
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- A fixed sequence of disjoint entry-coordinate patches covers exactly
the open regular chart locus selected for one block shape. -/
theorem exists_realSchurMixedRegularEntryLocusSequence
    {m : ℕ} (s : Fin m → ℕ) (c₀ : RealSchurMixedRegularFrame s) :
    ∃ c : ℕ → RealSchurMixedRegularFrame s,
      (⋃ k, realSchurMixedRegularEntryPatch c k) =
        realSchurMixedEntryEquiv s '' realSchurMixedRegularChartLocus s := by
  obtain ⟨c,hc⟩ := exists_realSchurMixedRegularChartLocusSequence s c₀
  refine ⟨c, ?_⟩
  calc
    (⋃ k, realSchurMixedRegularEntryPatch c k) =
        realSchurMixedEntryEquiv s ''
          (⋃ k, realSchurMixedRegularFirstPatch c k) := by
            rw [Set.image_iUnion]
            rfl
    _ = realSchurMixedEntryEquiv s '' (⋃ k, (c k).chart.target) := by
      rw [iUnion_realSchurMixedRegularFirstPatch]
    _ = _ := by rw [hc]

/-- Exact Gaussian integration over the whole open regular mixed-Schur
chart locus. The theorem does not assert that this locus has full
Gaussian measure, nor does it evaluate the remaining block integrals. -/
theorem exists_realSchurMixed_gaussian_lintegral_regular_locus
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c₀ : RealSchurMixedRegularFrame s) :
    ∃ c : ℕ → RealSchurMixedRegularFrame s,
      ∀ g : RealSchurMixedTangent s → ℝ≥0∞,
        ∫⁻ y in realSchurMixedEntryEquiv s '' realSchurMixedRegularChartLocus s,
            ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y) * g y
            ∂realSchurMixedCoordinateVolume s =
          ∑' k, ∫⁻ x in realSchurMixedRegularFirstSource c k,
            ENNReal.ofReal (realSchurMixedJacobianWeight s (c k).T x) *
              (ENNReal.ofReal (realMatrixGaussianWeight
                (RealSchurMixedCoord s) ((c k).T+x.2.val)) *
                g (realSchurMixedRotatedEntryCoordinates s (c k).T (c k).Q
                  (c k).orthogonal x))
            ∂realSchurMixedCoordinateVolume s := by
  obtain ⟨c,hc⟩ := exists_realSchurMixedRegularEntryLocusSequence s c₀
  refine ⟨c, ?_⟩
  intro g
  rw [← hc]
  exact realSchurMixed_gaussian_lintegral_regular_patch_sum s hs c g

/-- The single remaining coverage assumption is explicit: if the
regular chart locus has full entry-volume measure, the same sum computes
the unrestricted Gaussian matrix integral. -/
theorem exists_realSchurMixed_gaussian_lintegral_full_of_ae_locus
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c₀ : RealSchurMixedRegularFrame s)
    (hfull : ∀ᵐ y ∂realSchurMixedCoordinateVolume s,
      y ∈ realSchurMixedEntryEquiv s '' realSchurMixedRegularChartLocus s) :
    ∃ c : ℕ → RealSchurMixedRegularFrame s,
      ∀ g : RealSchurMixedTangent s → ℝ≥0∞,
        ∫⁻ y, ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y) * g y
            ∂realSchurMixedCoordinateVolume s =
          ∑' k, ∫⁻ x in realSchurMixedRegularFirstSource c k,
            ENNReal.ofReal (realSchurMixedJacobianWeight s (c k).T x) *
              (ENNReal.ofReal (realMatrixGaussianWeight
                (RealSchurMixedCoord s) ((c k).T+x.2.val)) *
                g (realSchurMixedRotatedEntryCoordinates s (c k).T (c k).Q
                  (c k).orthogonal x))
            ∂realSchurMixedCoordinateVolume s := by
  obtain ⟨c,hc⟩ := exists_realSchurMixed_gaussian_lintegral_regular_locus s hs c₀
  refine ⟨c, ?_⟩
  intro g
  calc
    _ = ∫⁻ y in realSchurMixedEntryEquiv s '' realSchurMixedRegularChartLocus s,
          ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y) * g y
          ∂realSchurMixedCoordinateVolume s := by
          rw [Measure.restrict_eq_self_of_ae_mem hfull]
    _ = _ := hc g

#print axioms exists_realSchurMixed_gaussian_lintegral_regular_locus
#print axioms exists_realSchurMixed_gaussian_lintegral_full_of_ae_locus
end SpectralRadiusUpperTail
