import SpectralRadiusUpperTail.RealSchurMixedRegularPatchIntegration
import SpectralRadiusUpperTail.RealSchurMixedRegularChartSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator BigOperators

/-- The characteristic-root count at a rotated chart point is exactly
the sum of current diagonal-block counts in entry coordinates. -/
theorem realSchurMixedRegularFrame_rotated_countP
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : RealSchurMixedRegularFrame s)
    (x : RealSchurMixedTangent s)
    (p : ℂ → Prop) [DecidablePred p] :
    Multiset.countP p
      (((realSchurMixedEntryEquiv s).symm
        (realSchurMixedRotatedEntryCoordinates s c.T c.Q c.orthogonal x)).charpoly.aroots ℂ) =
      ∑ i : Fin m, Multiset.countP p
        (((c.T+x.2.val).toSquareBlock
          (fun z : RealSchurMixedCoord s => z.1) i).charpoly.aroots ℂ) := by
  rw [realSchurMixedRotatedEntryCoordinates_eq,
    LinearEquiv.symm_apply_apply]
  exact realSchurMixed_rotatedExpCoordinates_aroots_countP
    s hs c.T c.Q c.upper c.orthogonal x p

/-- On the represented regular locus, the Gaussian expected root count
is a disjoint sum of local Schur integrals whose statistic is already
reduced to diagonal blocks. The remaining integration is not evaluated. -/
theorem realSchurMixed_gaussian_rootCount_regular_patch_sum
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : ℕ → RealSchurMixedRegularFrame s)
    (p : ℂ → Prop) [DecidablePred p] :
    ∫⁻ y in ⋃ k, realSchurMixedRegularEntryPatch c k,
        ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y) *
          (Multiset.countP p
            (((realSchurMixedEntryEquiv s).symm y).charpoly.aroots ℂ) : ℝ≥0∞)
        ∂realSchurMixedCoordinateVolume s =
      ∑' k, ∫⁻ x in realSchurMixedRegularFirstSource c k,
        ENNReal.ofReal (realSchurMixedJacobianWeight s (c k).T x) *
          (ENNReal.ofReal (realMatrixGaussianWeight
            (RealSchurMixedCoord s) ((c k).T+x.2.val)) *
            ((∑ i : Fin m, Multiset.countP p
              ((((c k).T+x.2.val).toSquareBlock
                (fun z : RealSchurMixedCoord s => z.1) i).charpoly.aroots ℂ)) : ℝ≥0∞))
        ∂realSchurMixedCoordinateVolume s := by
  have h := realSchurMixed_gaussian_lintegral_regular_patch_sum s hs c
    (fun y => (Multiset.countP p
      (((realSchurMixedEntryEquiv s).symm y).charpoly.aroots ℂ) : ℝ≥0∞))
  simpa only [realSchurMixedRegularFrame_rotated_countP s hs,
    Nat.cast_sum] using h

#print axioms realSchurMixed_gaussian_rootCount_regular_patch_sum
end SpectralRadiusUpperTail
