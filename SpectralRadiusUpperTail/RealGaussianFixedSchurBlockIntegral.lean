import SpectralRadiusUpperTail.RealGaussianFixedSchurCountExpectation
import SpectralRadiusUpperTail.RealGaussianFixedSchurBlockCount
import SpectralRadiusUpperTail.RealSchurFixedGaussianChartWeight
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- The actual first-chart Gaussian integral, with both the density and
the exterior root statistic reduced to its block-upper coordinates. -/
noncomputable def realGaussianFixedSchurBlockPatchIntegral
    {n : ℕ} (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ)
    (r : ℝ) (i : Fin 3) : ℝ≥0∞ :=
  ∫⁻ t in realSchurFixedChartPatchSource (c k)
      (realSchurFixedMixedFirstPatch c k),
    ENNReal.ofReal (realSchurMixedJacobianWeight
      (realSchurListBlockSize (c k).shape) (c k).frame.T t) *
      (ENNReal.ofReal
        (realMatrixGaussianWeight (RealSchurMixedCoord
          (realSchurListBlockSize (c k).shape))
          ((c k).frame.T+t.2.val) /
          (Real.sqrt (2*Real.pi))^(n*n)) *
        ENNReal.ofReal
          (realSchurFixedDiagonalExteriorCount (c k) t r i : ℝ))
    ∂realSchurMixedCoordinateVolume
      (realSchurListBlockSize (c k).shape)

theorem realGaussianFixedSchurPatchIntegral_exteriorCount
    {n : ℕ} (hn : 0 < n)
    (c : ℕ → RealSchurFixedChartIndex n) (k : ℕ)
    (r : ℝ) (i : Fin 3) :
    realGaussianFixedSchurPatchIntegral c k
      (fun x => ENNReal.ofReal (realGaussianExteriorCount n r i x)) =
        realGaussianFixedSchurBlockPatchIntegral c k r i := by
  unfold realGaussianFixedSchurPatchIntegral
    realGaussianFixedSchurBlockPatchIntegral
  apply lintegral_congr
  intro t
  change ENNReal.ofReal (realSchurMixedJacobianWeight
      (realSchurListBlockSize (c k).shape) (c k).frame.T t) *
      (realGaussianFixedDensity n
        (realSchurFixedChartOutputEntries (c k) t) *
        ENNReal.ofReal (realGaussianExteriorCount n r i
          (realSchurFixedChartOutputEntries (c k) t))) = _
  rw [realGaussianFixedDensity_fixedChartOutput,
    realGaussianExteriorCount_fixedChartOutput hn]

/-- The actual exterior-count expectations are exact sums of explicit
block-upper integrals. Evaluating these sums to the two Edelman
one-point expressions is the remaining finite-dimensional task. -/
theorem exists_realGaussianExteriorCountBlockExpectation
    (n : ℕ) (hn : 0 < n) :
    ∃ c : ℕ → RealSchurFixedChartIndex n,
      ∀ (r : ℝ) (i : Fin 3),
        ENNReal.ofReal (∫ x, realGaussianExteriorCount n r i x
          ∂gaussianMatrixLaw n) =
          ∑' k, realGaussianFixedSchurBlockPatchIntegral c k r i := by
  obtain ⟨c,hc⟩ := exists_realGaussianExteriorCountSchurExpectation n hn
  refine ⟨c, ?_⟩
  intro r i
  rw [hc r i]
  congr 1
  funext k
  exact realGaussianFixedSchurPatchIntegral_exteriorCount hn c k r i

#print axioms exists_realGaussianExteriorCountBlockExpectation
end SpectralRadiusUpperTail
