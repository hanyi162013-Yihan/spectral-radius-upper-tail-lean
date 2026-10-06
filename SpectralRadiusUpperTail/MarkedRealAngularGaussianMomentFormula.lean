import SpectralRadiusUpperTail.MarkedRealGaussianCharpolyMoment
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- Complete fixed-chart Gaussian formula: every real-root rank layer
adds to an angular mass times the actual lower-dimensional iid-Gaussian
absolute characteristic-polynomial moment. Global angular chart gluing
is a separate step. -/
theorem markedRealAngularRank_gaussian_area_tsum_moment
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∑' k : ℕ,
      ∫⁻ y in
        realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
          (markedRealAngularPositiveSource m ×ˢ
            markedRealUpperRankSource m k b),
        ENNReal.ofReal
          (realSchurMixedGaussianCoordinateWeight
            (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      (∫⁻ ω, markedRealAngularWeight m ω) *
        (∫⁻ x : ℝ,
          if b < x then
            ENNReal.ofReal (Real.exp (-x^2/2)) *
              ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^
                (Fintype.card
                  (RealSchurMixedStrictUpperEntry
                    (markedRealTwoBlockSizes m)))) *
              ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2)) *
              markedRealGaussianCharpolyMoment m x
          else 0) := by
  rw [markedRealAngularRank_gaussian_area_tsum_charpoly m hm b]
  congr 1
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall
    (fun x => markedRealCharpolyKernel_lintegral_complement m b x)

#print axioms markedRealAngularRank_gaussian_area_tsum_moment
end SpectralRadiusUpperTail
